# 8. The finite-box route

A second route to a gap of the periodic transfer $T_\beta$, independent of the bootstrap and not used by Theorem 1.1. The action is $S=\sum_{p\ \text{ordered}}(1-\tfrac1N\operatorname{Re}\operatorname{tr}U_p)$, so $\beta_W=2\beta$; the spacing attached to a coupling is the two-loop formula $a(\beta)=u^{51/121}e^{-u/2}$, $u=48\pi^2\beta/(11N^2)$, with maximum at $\beta_\ast(N)=17N^2/(88\pi^2)$ (a bookkeeping device at small $\beta$). $T_\beta$ has a gap at lattice rate $\mu$ if $\langle T_\beta x,T_\beta x\rangle\le e^{-2\mu}\langle x,x\rangle$ on the vacuum complement, and at physical rate $M$ if at lattice rate $Ma(\beta)$.

## 8.1 From a box read to a transfer gap

> Theorem 8.1 (finite-size criterion). For a non-negative symmetric form $B$ and $B$-self-adjoint idempotents $h_i$ with patch weights of total $a_1$, squared total $a_2$, and pair weights within $w_{ij}$ of $b$ (row and column sums of $w$ at most $e$) on non-commuting pairs, a patch gap $\gamma B(A_kx,x)\le B(A_kx,A_kx)$ gives $(\gamma a_1-a_2+b-e)B(Hx,x)\le b\,B(Hx,Hx)$ for $H=\sum h_i$.

This is the algebra of Knabe's argument [Knabe] (related criteria: [GossetMozgunov], [Lemm20], [LX], [Anshu], [Young]; for Gibbs samplers [KastoryanoBrandao]). For the heat bath, $h_\ell=\mathrm{id}-E_\ell$ in the $L^2$ form of the torus state on periodic gauge-invariant observables.

> Theorem 8.2 (box patches). For $0/1$ box patches of side $n$ the constant divided by $b$ is $\kappa_n(\gamma)=(\gamma n^2-40n+36)/(n-1)^2$, positive exactly when $\gamma>(40n-36)/n^2$.

So at the patch gap $\gamma=1$ of $\beta=0$ the $0/1$ criterion holds only for $n\ge40$; a weighted profile on side $15$ (finitely many integer weights, checked in the kernel) lowers the threshold below $\gamma_{15}=759/10000$.

> Theorem 8.3 (light cone and clustering). For the lazy heat bath $T=\mathrm{id}-K^{-1}H$ with neighbour sets of size at most $z$: $\|h_\ell T^mf\|\le\|f\|y^{-k}(1+2zy/K)^m$ at distance $k$ from the support of $f$, and under a form gap $c$ the covariance of separated observables is bounded free of $K$, hence of the volume.

This is a Lieb–Robinson bound [LiebRobinson], [NachtergaeleSims] for the discrete-time chain, with the pattern of [GuionnetZegarlinski], [StroockZegarlinski].

> Theorem 8.4 (box gap to transfer gap). If the box condition holds on every even torus of side at least $2n$ with the profile weights and $\gamma$ above the profile threshold, $T_{\beta_0}$ has a gap at lattice rate $\mu=-\log r(21,c_0)>0$, $\mu\le\min(c_0,1)/508\le1/508$, $c_0$ the Knabe constant.

## 8.2 The box gap at small coupling

> Theorem 8.5 (box gaps for $SU(2)$ and $SU(3)$). On side $15$ with the profile: $SU(2)$ at $\beta=3/40$ with $\gamma=58/625$; $SU(3)$ at $\beta_\ast(3)=153/(88\pi^2)$ with $\gamma=367/2500$; $SU(2)$ at every $\beta\in[0,83/1000]$ ($\beta_W\le0.166$) with $\gamma=953/12500$; $SU(3)$ at every $\beta\in[0,19/100]$ ($\beta_W\le0.38$) with $\gamma=41/500$. All exceed $\gamma_{15}$.

The constants come from exact two-link correlation bounds with Haar moments in closed form; a Holley–Stroock bound [HolleyStroock] on the whole box is proved but passes $\gamma_{15}$ only near $\beta\approx2\cdot10^{-6}$, and for general $N$ the linear bound reaches $\gamma_{15}$ only at $\beta\le7.6\cdot10^{-6}$.

> Theorem 8.6 (the lattice gap at those couplings). At each coupling of Theorem 8.5 the heat-bath generator of every even periodic torus of extent at least $30$ has a form gap $c_0(\gamma)$ uniform in the extent, and $T_\beta$ contracts the vacuum complement by $e^{-\min(c_0,1)/508}$; for every $N$ there is $\beta_{\mathrm{sc}}>0$ below which $T_{\beta_0}$ has a gap at every box rate with no box input.

A lattice gap at sufficiently strong coupling is classical [OsterwalderSeiler], [Seiler82]; Theorem 8.6 states explicit couplings with rational constants, with a machine-checked proof. The lattice mass is at most $1/508$, about $1.3\cdot10^{-9}$ to $2.6\cdot10^{-7}$ at the proved constants (computed outside Lean), at one infinite-volume state, both couplings on the strong side of the crossover.

## 8.3 The ultraviolet step and one cube

The route concludes a weaker statement than $\mathrm{CS}(N)$: $\mathcal C(L)$, a per-step gap at rate $e^{-(c/L)a_m}$ and a non-trivial vacuum of the reconstruction from separated-point Schwinger functions at the two-loop couplings, stating no Osterwalder–Schrader axiom. Its inputs are the ultraviolet step (UV), a loss budget carrying a gap at physical rate from octave to octave below $a(\beta_0)$, and three continuum inputs: (B1) a uniform bound on separated connected Schwinger functions; (B2) convergence of one two-point kernel; (B3) its asymptotic-freedom form.

> Theorem 8.7 (the box route). For $N\ge2$, $\mathrm{BLG}(\beta_0,15,\gamma)$ with $\gamma\ge\gamma_{15}$, (UV) at the rate of Theorem 8.4, (B1), (B2) and (B3) give $\mathcal C(L)$; in particular at the couplings of Theorem 8.5.

> Theorem 8.8 (the ultraviolet step is the branch gap). Given a gap at $\beta_0$, (UV) at some rate holds exactly when $T_\beta$ has a gap at one physical rate at every coupling of the weak branch; a gap on finitely many octaves and another on the rest give (UV).

> Theorem 8.9 (bounded seed). If at every coupling of the branch some window has $D_\beta(w)\le1/1000$ at physical size $2^wa(\beta)\le C$, the branch gap holds at rate $(\log2)/C$, (S) holds, and with (B1)–(B3) $\mathcal C(L)$ holds.

(S) gives seeds at frequently large $\beta$ with no bound on their physical size, so it does not give (UV). The lowest octave alone asks a gap on $[0.0817,0.3165]$ at $SU(2)$ and $[0.1762,0.7119]$ at $SU(3)$ (computed); Theorem 8.5 enters it by a sliver and covers no full octave.

The reduction of the ultraviolet step to a contraction on one cube of fixed physical size is due to Bhattacharjee, Bhattacharya, Lockwood, Romanov and Singha Roy [BBLRS-v444] (unrefereed); Theorem 8.10 formalizes a variant of its lattice step: the condition is posed on the ungauged measure rather than in their forest gauge, summed over the translates of the box by $\mathbb Z^4$ and grouped by the direction of the inside link rather than by class, with a stronger bound on each entry, and the gap is reached through a Poincaré inequality rather than their Wasserstein contraction, at a smaller rate. Our statements are compatible with the no-go of Bhattacharjee and Bhattacharya [BB] (unrefereed): the rate is in physical units, so no spacing-uniform lattice gap is asserted, and a box of bounded physical side would give one, so the side must grow as the spacing falls. The condition $\mathrm{Cube}(\beta,n,\alpha)$, of Dobrushin–Shlosman type [DobrushinShlosman85], asks on the ungauged measure that the total influence of the outside on the box means of interior-gauge-invariant tests be at most $\alpha n^4$ per direction.

> Theorem 8.10 (one cube). If $\mathrm{Cube}(\beta,n,\alpha)$, $\alpha<1$, holds on all large tori, $T_\beta$ has a gap at lattice rate $\rho(\alpha)/n$, $\rho(\alpha)=\tfrac1{810}\sqrt{c/(389376+c)}$, $c=(1-\alpha)/256$; the cube at bounded physical size along the branch gives the branch gap at rate $\rho(\alpha)/\ell$, hence (UV) and, with (B1)–(B3), $\mathcal C(L)$; and the cube and the bounded seed may be mixed along the branch.

No Lean statement depends on the correctness of their work. The only instance of the cube condition proved is $\beta=0$, and neither the cube nor the bounded seed is shown to imply the other.
