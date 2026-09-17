"""Exact finite-group negative control for the polymer hard core.

Z_2 replaces SU(N).  A link carries U_l in {+1,-1}; the product uniform measure over
{+1,-1}^L IS the product Haar measure of Z_2, and observables reading disjoint link
blocks are independent under it, verbatim as in WilsonReal.block_integral_factor.

The plaquette holonomy is the product of its boundary links, and the Wilson density
    phi_p(U) = 1 - (1/N) Re tr hol_p(U)
becomes, at N = 1 with the sign representation,  phi_p = 1 - h_p  in {0, 2}.
That is exactly the range [0,2] the Lean bound assumes.

Everything is a Fraction in the variable x = exp(-2*beta).  beta >= 0  <=>  0 < x <= 1.
    exp(-beta*phi_p) = x if h_p = -1 else 1
    w_p = exp(-beta*phi_p) - 1 = (x-1) if h_p = -1 else 0
"""
from fractions import Fraction as Fr
from itertools import product, combinations


# ---------------------------------------------------------------- geometries
def chain(n):
    """n plaquettes in a line; plaquette i has boundary links {i, i+1}."""
    return n + 1, [frozenset({i, i + 1}) for i in range(n)]


def star(m):
    """m plaquettes all sharing the central link 0; plaquette i has {0, i}."""
    return m + 1, [frozenset({0, i}) for i in range(1, m + 1)]


def sheet(n):
    """n plaquettes in a line but link-disjoint: no plaquette touches another."""
    return 2 * n, [frozenset({2 * i, 2 * i + 1}) for i in range(n)]


def ring(n):
    """n plaquettes in a CYCLE; plaquette i has links {i, (i+1) mod n}.

    Unlike chain(), the boundary vectors are linearly DEPENDENT over F_2 -- their sum
    is zero, so prod_i h_i = 1 identically.  That is the Z_2 analogue of the Bianchi
    identity on a closed surface, and it is what makes the connected correlation
    NONZERO.  On chain() the h_i are independent and every connected correlator
    vanishes, which would make the reorganisation test vacuous.
    """
    return n, [frozenset({i, (i + 1) % n}) for i in range(n)]


# ---------------------------------------------------------------- model
class Model:
    def __init__(self, geom, x):
        self.L, self.bd = geom
        self.P = len(self.bd)
        self.x = Fr(x)
        self.configs = list(product([1, -1], repeat=self.L))
        self.norm = Fr(1, len(self.configs))
        self._zwc, self._spc = {}, {}
        # h[c][p] in {+1,-1}
        self.h = []
        for U in self.configs:
            row = []
            for b in self.bd:
                v = 1
                for l in b:
                    v *= U[l]
                row.append(v)
            self.h.append(row)

    def phi(self, ci, p):
        return Fr(1 - self.h[ci][p])          # 0 or 2

    def w(self, ci, p):
        return (self.x - 1) if self.h[ci][p] == -1 else Fr(0)

    def zw(self, D, E):
        key = (D, E)
        v = self._zwc.get(key)
        if v is None:
            v = self._zw(D, E)
            self._zwc[key] = v
        return v

    def _zw(self, D, E):
        """zw bd beta D E = int (prod_{p in D} phi_p) * prod_{p in E} w_p  d(Haar)."""
        tot = Fr(0)
        for ci in range(len(self.configs)):
            t = Fr(1)
            for p in D:
                t *= self.phi(ci, p)
                if t == 0:
                    break
            if t != 0:
                for p in E:
                    t *= self.w(ci, p)
                    if t == 0:
                        break
            tot += t
        return tot * self.norm

    def subPart(self, W):
        W = frozenset(W)
        v = self._spc.get(W)
        if v is None:
            v = self._subPart(W)
            self._spc[W] = v
        return v

    def _subPart(self, W):
        """Z_W = int prod_{p in W} exp(-beta phi_p) d(Haar)."""
        tot = Fr(0)
        for ci in range(len(self.configs)):
            t = Fr(1)
            for p in W:
                if self.h[ci][p] == -1:
                    t *= self.x
            tot += t
        return tot * self.norm

    # ------------------------------------------------------------ combinatorics
    def touch(self, p, q):
        return len(self.bd[p] & self.bd[q]) > 0

    def degree(self):
        """max_p #{q : touch p q}  -- the K of the bound (counts p itself)."""
        return max(sum(1 for q in range(self.P) if self.touch(p, q)) for p in range(self.P))

    def outsideOf(self, A):
        return frozenset(p for p in range(self.P)
                         if all(not self.touch(p, a) for a in A))

    def compOf(self, V, a):
        """a's touch-reachable component inside V."""
        V = set(V)
        seen, stack = {a} & V, [a] if a in V else []
        while stack:
            u = stack.pop()
            for v in V:
                if v not in seen and self.touch(u, v):
                    seen.add(v)
                    stack.append(v)
        return frozenset(seen)

    def subsets(self, S):
        S = sorted(S)
        for k in range(len(S) + 1):
            for c in combinations(S, k):
                yield frozenset(c)

    def pairTerm(self, p0, pd, E, F):
        return (self.zw(frozenset({p0, pd}), E) * self.zw(frozenset(), F)
                - self.zw(frozenset({p0}), E) * self.zw(frozenset({pd}), F))


# ---------------------------------------------------------------- checks
def check_outside_sum_is_subpart(m):
    """ sum_{E subseteq W} zw(empty, E)  ==  Z_W    (the Lean identity) """
    bad = []
    for W in m.subsets(range(m.P)):
        lhs = sum((m.zw(frozenset(), E) for E in m.subsets(W)), Fr(0))
        rhs = m.subPart(W)
        if lhs != rhs:
            bad.append((W, lhs, rhs))
    return bad


def ratio(m, A):
    Om = m.outsideOf(A)
    return m.subPart(Om) / m.subPart(frozenset(range(m.P))), Om


def check_ratio(m, K=None):
    """returns list of (A, ratio, lower_ok, upper_ok, |Omega^c|, bound)"""
    if K is None:
        K = m.degree()
    out = []
    for A in m.subsets(range(m.P)):
        if not A:
            continue
        r, Om = ratio(m, A)
        oc = m.P - len(Om)
        bound = m.x ** (-K * len(A))
        out.append((tuple(sorted(A)), r, Fr(1) <= r, r <= bound, oc, bound))
    return out


def check_core_factorisation(m, p0, pd):
    """pairTerm(E,F) == pairTerm(E&A,F&A) * zw(0,E\\A) * zw(0,F\\A),  A = comp(p0)."""
    bad = 0
    tested = 0
    for E in m.subsets(range(m.P)):
        for F in m.subsets(range(m.P)):
            V = set(E) | set(F) | {p0, pd}
            A = m.compOf(V, p0)
            if pd not in A:
                continue                       # non-bridging: handled by the involution
            tested += 1
            lhs = m.pairTerm(p0, pd, E, F)
            rhs = (m.pairTerm(p0, pd, frozenset(E) & A, frozenset(F) & A)
                   * m.zw(frozenset(), frozenset(E) - A)
                   * m.zw(frozenset(), frozenset(F) - A))
            if lhs != rhs:
                bad += 1
    return tested, bad


def check_reorganisation(m, p0, pd):
    """The whole claim:
         D = N({p0,pd})Z - N({p0})N({pd})
           = sum over CORES (X,Y) of pairTerm(X,Y) * Z_{Omega(A)}^2 ,
       so   corrConn = D/Z^2 = sum_cores pairTerm(X,Y) * (Z_Omega/Z)^2 .
    """
    allP = frozenset(range(m.P))
    N2 = sum((m.zw(frozenset({p0, pd}), E) for E in m.subsets(allP)), Fr(0))
    N0 = sum((m.zw(frozenset({p0}), E) for E in m.subsets(allP)), Fr(0))
    Nd = sum((m.zw(frozenset({pd}), E) for E in m.subsets(allP)), Fr(0))
    Z = sum((m.zw(frozenset(), E) for E in m.subsets(allP)), Fr(0))
    D = N2 * Z - N0 * Nd

    # direct double sum, split into bridging / non-bridging
    bridging = Fr(0)
    nonbridging = Fr(0)
    for E in m.subsets(allP):
        for F in m.subsets(allP):
            V = set(E) | set(F) | {p0, pd}
            t = m.pairTerm(p0, pd, E, F)
            if pd in m.compOf(V, p0):
                bridging += t
            else:
                nonbridging += t

    # core resummation
    core_sum = Fr(0)
    cores = []
    for X in m.subsets(allP):
        for Y in m.subsets(allP):
            V = set(X) | set(Y) | {p0, pd}
            A = m.compOf(V, p0)
            if pd not in A:
                continue
            if not (set(X) <= A and set(Y) <= A):
                continue
            ZO = m.subPart(m.outsideOf(A))
            core_sum += m.pairTerm(p0, pd, X, Y) * ZO * ZO
            cores.append((tuple(sorted(X)), tuple(sorted(Y)), tuple(sorted(A))))
    return dict(D=D, Z=Z, bridging=bridging, nonbridging=nonbridging,
                core_sum=core_sum, ncores=len(cores),
                corr=D / (Z * Z))


def hdr(s):
    print()
    print("=" * 78)
    print(s)
    print("=" * 78)


if __name__ == "__main__":
    X = Fr(1, 2)          # beta = (log 2)/2 > 0

    hdr("1.  sum_{E subseteq W} zw(0,E) == Z_W   (the identity the Lean proof rests on)")
    for name, g in [("chain(4)", chain(4)), ("star(4)", star(4)), ("sheet(3)", sheet(3)),
                    ("ring(5)", ring(5)), ("ring(6)", ring(6))]:
        m = Model(g, X)
        bad = check_outside_sum_is_subpart(m)
        print(f"  {name:10s} P={m.P:2d} L={m.L:2d}  subsets checked={2**m.P:4d}  mismatches={len(bad)}")

    hdr("2.  NON-VACUITY: constrained and unconstrained outside sums genuinely differ")
    for name, g in [("chain(6)", chain(6)), ("star(5)", star(5))]:
        m = Model(g, X)
        Zfull = m.subPart(frozenset(range(m.P)))
        for A in [frozenset({0}), frozenset({0, 1})]:
            if max(A) >= m.P:
                continue
            Om = m.outsideOf(A)
            ZO = m.subPart(Om)
            print(f"  {name:9s} A={sorted(A)}  Omega={sorted(Om)}  "
                  f"Z_Omega={ZO}  Z={Zfull}  Z_Omega/Z={ZO/Zfull}  equal={ZO==Zfull}")

    hdr("3.  THE BOUND:  1 <= Z_Omega(A)/Z <= x^(-K|A|),  x=exp(-2b), K=touch degree")
    for name, g in [("chain(4)", chain(4)), ("chain(6)", chain(6)),
                    ("chain(8)", chain(8)), ("star(5)", star(5)), ("sheet(4)", sheet(4)),
                    ("ring(6)", ring(6)), ("ring(8)", ring(8)), ("ring(10)", ring(10))]:
        m = Model(g, X)
        K = m.degree()
        rows = check_ratio(m)
        lo = all(r[2] for r in rows)
        up = all(r[3] for r in rows)
        worst = max(rows, key=lambda r: r[1])
        print(f"  {name:9s} P={m.P:2d} K={K}  lower(1<=r) all_ok={lo}  upper(r<=x^-K|A|) all_ok={up}")
        print(f"             worst A={worst[0]} ratio={worst[1]} = {float(worst[1]):.6f} "
              f"bound={worst[5]} |Omega^c|={worst[4]}")

    hdr("4.  VOLUME INDEPENDENCE: same A, growing lattice -> ratio does NOT grow")
    for n in (5, 6, 7, 8, 9, 10, 11, 12, 13, 14):
        m = Model(ring(n), X)
        A = frozenset({0})
        r, Om = ratio(m, A)
        print(f"  ring({n:2d})  P={m.P:2d} L={m.L:2d}  Z_Omega/Z = {r} = {float(r):.10f}   "
              f"bound x^-K|A| = {float(m.x ** (-m.degree()))}")

    hdr("5.  FAILURE 1 -- drop  beta >= 0  (take x>1, i.e. beta<0)")
    for name, g in [("chain(4)", chain(4)), ("star(4)", star(4))]:
        m = Model(g, Fr(2))       # x = 2  ->  beta = -(log 2)/2 < 0
        rows = check_ratio(m)
        lo = [r for r in rows if not r[2]]
        up = [r for r in rows if not r[3]]
        print(f"  {name:9s} x=2 (beta<0):  lower bound fails for {len(lo)}/{len(rows)} cores, "
              f"upper bound fails for {len(up)}/{len(rows)} cores")
        if up:
            a = up[0]
            print(f"             e.g. A={a[0]}: ratio={a[1]}={float(a[1]):.6f} > bound={a[5]}={float(a[5]):.6f}")

    hdr("6.  FAILURE 2 -- drop the touch-degree hypothesis (use K=3 on a high-degree geometry)")
    for m_pl in (3, 5, 8, 10, 12):
        m = Model(star(m_pl), X)
        A = frozenset({1})
        r, Om = ratio(m, A)
        Ktrue, Kwrong = m.degree(), 3
        ok_true = r <= m.x ** (-Ktrue * len(A))
        ok_wrong = r <= m.x ** (-Kwrong * len(A))
        print(f"  star({m_pl:2d})  K_true={Ktrue:2d}  ratio={float(r):.4f}  "
              f"bound(K_true)={float(m.x**(-Ktrue)):9.2f} holds={ok_true}   "
              f"bound(K=3)={float(m.x**(-3)):.2f} holds={ok_wrong}")

    hdr("7.  CORE/OUTSIDE FACTORISATION (an independent check of pairTerm_eq_core_mul_outside)")
    for name, g, p0, pd in [("chain(4)", chain(4), 0, 3), ("chain(5)", chain(5), 0, 4),
                            ("ring(5)", ring(5), 0, 2), ("ring(6)", ring(6), 0, 3)]:
        m = Model(g, X)
        tested, bad = check_core_factorisation(m, p0, pd)
        print(f"  {name:9s} p0={p0} pd={pd}  bridging pairs tested={tested}  mismatches={bad}")

    hdr("8.  THE WHOLE REORGANISATION:  D = sum_cores pairTerm(X,Y) * Z_Omega(A)^2")
    for name, g, p0, pd in [("chain(4)", chain(4), 0, 3),
                            ("ring(5)", ring(5), 0, 2),
                            ("ring(6)", ring(6), 0, 3),
                            ("ring(7)", ring(7), 0, 3)]:
        m = Model(g, X)
        d = check_reorganisation(m, p0, pd)
        print(f"  {name}: D={d['D']}   (D=0 means the test is VACUOUS here)")
        print(f"           non-bridging double sum = {d['nonbridging']}  (must be 0)")
        print(f"           bridging double sum     = {d['bridging']}   equals D: {d['bridging']==d['D']}")
        print(f"           core resummation        = {d['core_sum']}   equals D: {d['core_sum']==d['D']}")
        print(f"           #cores={d['ncores']}   corrConn = D/Z^2 = {float(d['corr']):.10e}")

    hdr("9.  THE PAYOFF: |corrConn| against the volume-free core bound, growing lattice")
    print("    corrConn = sum_cores pairTerm(X,Y) * (Z_Omega(A)/Z)^2 ,  |ratio| <= x^(-K|A|)")
    for n in (5, 6, 7, 8):
        m = Model(ring(n), X)
        p0, pd = 0, min(3, n - 2)
        allP = frozenset(range(m.P))
        Z = m.subPart(allP)
        K = m.degree()
        tot = Fr(0)
        naive = Fr(0)
        for Xs in m.subsets(allP):
            for Ys in m.subsets(allP):
                V = set(Xs) | set(Ys) | {p0, pd}
                A = m.compOf(V, p0)
                if pd not in A or not (set(Xs) <= A and set(Ys) <= A):
                    continue
                pt = m.pairTerm(p0, pd, Xs, Ys)
                r = m.subPart(m.outsideOf(A)) / Z
                tot += pt * r * r
                naive += abs(pt) * m.x ** (-2 * K * len(A))
        d = check_reorganisation(m, p0, pd)
        print(f"  ring({n}) p0={p0} pd={pd}: corrConn={float(d['corr']):+.6e}  "
              f"resummed={float(tot):+.6e}  match={tot == d['corr']}")
        print(f"            volume-free core bound sum_cores|pairTerm|*x^(-2K|A|) = {float(naive):.6e}"
              f"   holds={abs(d['corr']) <= naive}")

    hdr("10. STRONG COUPLING: the core bound stops growing with the volume once beta is small")
    print("    x = exp(-2b);  x=63/64 is b = (1/2)ln(64/63) = 0.00787..., well inside the regime")
    for xv in (Fr(1, 2), Fr(7, 8), Fr(63, 64)):
        print(f"    --- x = {xv}  (beta = {0.5 * __import__('math').log(1 / float(xv)):.5f}) ---")
        for n in (5, 6, 7, 8):
            m = Model(ring(n), xv)
            p0, pd = 0, 3
            allP = frozenset(range(m.P))
            Z = m.subPart(allP)
            K = m.degree()
            naive = Fr(0)
            for Xs in m.subsets(allP):
                for Ys in m.subsets(allP):
                    V = set(Xs) | set(Ys) | {p0, pd}
                    A = m.compOf(V, p0)
                    if pd not in A or not (set(Xs) <= A and set(Ys) <= A):
                        continue
                    naive += abs(m.pairTerm(p0, pd, Xs, Ys)) * m.x ** (-2 * K * len(A))
            dd = check_reorganisation(m, p0, pd)
            print(f"      ring({n}) P={n:2d}  |corrConn|={float(abs(dd['corr'])):.4e}   "
                  f"core bound={float(naive):.6e}   holds={abs(dd['corr']) <= naive}")
