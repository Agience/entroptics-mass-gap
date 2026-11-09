# 2. The observer and its continuum theory

## 2.1 The picture (argued)

A local observer reads the world through a boundary of finite capacity [Bekenstein73], [Bekenstein81], so it resolves finitely many cells of positive size: it is an aperture of finite resolution (argued). Two readings of this motivate proved statements. A view carried by finitely many modes has autocorrelation $\sum_kP_km_k^\tau$, which either keeps a mode of unit modulus or decays at the positive rate $-\log\max|m_k|$ (elementary); a finite aperture therefore favours a gap, and the problem is that the rate stay positive in physical units as the substrate is refined (argued). This is what the doubling defect of section 5 reads at one physical scale. And the energy a fixed physical region holds should stay bounded at every spacing, because the factor $a^{-4}$ of the energy density cancels against the region's volume in lattice cells (argued); this is the cube bound (C) of section 2.4 and the moment clause of (E). A band limit with a vanishing remainder is not stated: the flowed heat-kernel spectrum has no compact support, so the finite-information content is stated as boundedness of the measured count (section 3), not as an exact projection.

## 2.2 The smearing step

Let $G=SU(N)$. For a link $U_\mu(x)$ let $S_1,\dots,S_6$ be its six staples. One step replaces every link at once by the polar factor of $X=U_\mu(x)+c\sum_iS_i$ with its determinant phase removed, $0\le c$, $(1+6c)^N<2$; then $|\det(1+E)-1|<1$ for $X=U(1+E)$, so $X$ is invertible and the phase returns it to $SU(N)$. The step is continuous, gauge covariant, inverted when its inputs are, and independent of the staple order (derived on paper at general $N$; formalized at $N=2$). At $N=2$ the polar factor of a quaternion matrix is $X/\sqrt{\det X}$, and the step is defined on $0\le c<\tfrac16$.

> Theorem 2.1 (the $SU(2)$ step). Let $0\le c<\tfrac16$. If a $2\times2$ quaternion-form matrix $V=W+E$ has $W\in SU(2)$ and $E$ of quaternion norm below $1$, then $\det V\ne0$ and $V/\sqrt{\operatorname{Re}\det V}\in SU(2)$. The step $(W,S_1,\dots,S_6)\mapsto V/\sqrt{\det V}$, $V=W+c\sum_iS_i$, is a continuous map $SU(2)\times SU(2)^6\to SU(2)$, gauge covariant ($W\mapsto gWh^{-1}$, $S_i\mapsto gS_ih^{-1}$ gives $g(\cdot)h^{-1}$), inverted when its inputs are, and independent of the order of the staples.

> Theorem 2.2 (reflection). Applied to every link of a configuration on $\mathbb Z^4$ at once, the step commutes with the reflection through the plane $x_\tau=0$ in every direction $\tau$.

For small abelian fields the step multiplies each mode of the curl-curl operator by $1-\eta\lambda$, $|1-\eta\lambda|\le1$, $\eta=c/(1+6c)$, and at $SU(2)$ it obeys $s(P')\le(1+96\eta^2)(s(P)+\Sigma(P))$, so flat regions stay flat (both derived on paper, not formalized).

## 2.3 The observer as a configuration flow

The observer at step $k$ runs $n_k$ steps, each output link computed from steps run only inside the box of half-width $R_k$ around it (measured on link midpoints, so the reflection maps boxes to boxes), the outside held fixed.

> Theorem 2.3 (range independent of the number of steps). Let $0\le c<\tfrac16$. (i) If every link near a link of $S$ lies in $A$, two configurations agreeing on $A$ still agree on $A$ after any number of steps run on $S$ with the outside fixed. (ii) The output at $l$ of $n$ steps run on the links based within $R$ of the base of $l$ depends only on the links based within $R+1$ of it, for every $n$; on the midpoint box of half-width $R$ the same argument gives range $R+3$ (Theorem 2.4).

> Theorem 2.4 (the observer). For any sequences $(n_k)$, $(R_k)$, the observer $V_k$ is a configuration flow of $SU(2)$ lattice gauge theory on $\mathbb Z^4$: continuous, gauge covariant, commuting with the time reflection in every direction, with lattice range $R_k+3$. If eventually $a_k(R_k+3)\le r$, the flow has physical range $r$.

The observer fixes its step count by its own scale, $n_k^2\langle e\rangle_k(n_k)=w$, the step analogue of $t^2\langle E(t)\rangle$ [Luscher] (defined; the theorems hold for every $(n_k)$). Theorems 2.5 to 2.14, and the theorems of sections 3 and 4 that do not name a particular flow, are stated for an arbitrary configuration flow with the properties they name, so the observer is one candidate witness; whether it meets the moment clause of (E) is open.

## 2.4 Schwinger functions and the cube energy

A schedule is couplings $\beta_k$ and spacings $a_k$ with states $\nu_k$ the periodic Wilson states at $\beta_k$. Theorems 2.5 to 2.13 are stated at the two-loop couplings, $a_k=a(1)/2^{k+1}$ and $\beta_k$ with $a(\beta_k)=a_k$; Theorem 2.14 carries the parts it lists to every coupling sequence. For a field $O$ and a bounded test function $g$ of bounded support the smeared field is $\phi_k(F,g)=a_k^4\sum_xg(a_kx)F_k\circ T_x$, $F_k$ the observer's reading of $O$; Schwinger functions are moments of products of these, and limits are taken along $\mathcal U$. The energy density is $E_k(O)=a_k^{-4}(O\circ V_k-s_k(O))$ on a reflection-closed class of non-negative fields; the class used is the plaquette class, the Wilson densities $1-\tfrac1N\operatorname{Re}\operatorname{tr}U_p$ of single plaquettes and their reflections. The canonical factor cancels against the cell volume, so the uniform bound on smeared moments is a statement about plain cube sums:

(C) for every $O$ in the class, $R\ge0$ and $p$, the cube energy $\mathcal E_k(R)=\sum_{a_kx\in[-R,R]^4}O\circ V_k\circ T_x$ has $\nu_k(\mathcal E_k(R)^{2p})$ bounded eventually in $k$.

(C) is a statement about the state, not about configurations: the step fixes every configuration with links in the centre (Theorem 2.15), and one such configuration reads $2$ on a plaquette.

> Theorem 2.5 (the uniform bound is the cube energy). On a reflection-closed class of non-negative fields with reflection-invariant subtractions $|s_k|\le Sa_k^4$, the smeared moments of the energy density are bounded eventually in $k$ for every test function and order if and only if (C) holds.

> Theorem 2.6 (the unit cube). For a non-negative field, $\nu_k(\mathcal E_k(R)^{2p})\le((2R+1)^4)^{2p}\nu_k(\mathcal E_k(1)^{2p})$. If $\nu_k(e^{t\mathcal E_k(1)})\le C$ eventually for one $t>0$, then eventually $\nu_k(\mathcal E_k(R)^{2p})\le((2R+1)^4)^{2p}(2p)!\,t^{-2p}C$.

## 2.5 The Euclidean and Osterwalder–Schrader structure

Reflection positivity of the Wilson state at every real coupling, with the physical range of the flow, makes every reflected Gram sum of products beyond the range non-negative; the reflection form reconstructs a Hilbert space generated by the observer's fields alone, with a vacuum and positive transfers.

> Theorem 2.7 (Euclidean structure). At every $SU(N)$ the limit Schwinger functions of the observer's fields are unchanged under permutations of the family, translations by $a_mn$ ($n\in\mathbb Z^4$) and axis reflections. Given the uniform bound they have non-negative reflected Gram sums on products beyond the range; the form is the same at every dyadic step, $T_m=T_{m+1}^2$ on the products, and each $T_m$ is positive.

> Theorem 2.8 (continuous time). Given the uniform bound and the range, $T_{m+1}^2=T_m$ on $\mathcal H$, $T_0$ has trivial kernel, and $T(t)=T_0^{t/a_0}$ is a semigroup of positive self-adjoint contractions with $T(na_m)=T_m^n$, strongly continuous on $[0,\infty)$, norm continuous on $(0,\infty)$, fixing $\Omega$.

The generator $H$ of the semigroup, $Hu=\lim_{t\to0^+}t^{-1}(u-T(t)u)$ (formally $-a_0^{-1}\log T_0$), is self-adjoint and non-negative; the Hamiltonian gap of the target is a gap of this $H$.

> Theorem 2.9 (hypercubic invariance). For the energy density of a flow commuting with the axis permutations, the Schwinger functions at every step and in the limit are invariant under every word in the axis permutations and reflections; at hypercubic-scalar fields, under the $384$ signed permutations of $\mathbb R^4$.

The plaquette density summed over its $384$ hypercubic images gives the symmetrized plaquette class, on which (E) and Theorem 1.1 are stated; for a flow commuting with the axis permutations, (C) on the plaquette class gives (C) on it.

> Theorem 2.10 (Osterwalder–Schrader structure). Assume (C). Then (OS0 on each cube) $|S_n(g_1,\dots,g_n)|\le K\prod_i\|g_i\|_\infty$ for tests in $[-R,R]^4$, with $K=1+n(2n)!\,t^{-2n}C$ for one field of the class under an exponential cube moment; the Schwinger functions are multilinear and sup-norm continuous on each cube; (OS1) invariant under every real translation of uniformly continuous tests and under axis reflections; (OS3) symmetric; (OS2) reflection positive beyond the range.

> Theorem 2.11 (growth). For a field $O$ of a non-negative reflection-closed class, if $\nu_k(e^{t\mathcal E_k(1)})\le C$ eventually, then the Schwinger functions of $O$ satisfy $|S_n(g_1,\dots,g_n)|\le\alpha\gamma^n(n!)^2\prod_iM_i(2R_i+3)^4$ for $|g_i|\le M_i$ supported in $[-R_i,R_i]^4$, with $\alpha=1+C$, $\gamma=8(1+t^{-1})^2$: the Osterwalder–Schrader linear growth form.

> Theorem 2.12 (Schwartz test functions). Under the hypothesis of Theorem 2.11: (i) $|S_n|\le(1+n(2n)!\,t^{-2n}C)\prod_i8192\|g_i\|_5$ with $\|g\|_K=\sup(1+\|y\|_\infty)^K|g(y)|$; (ii) the truncations converge; (iii) the limit agrees with $S_n$ on compactly supported tests and obeys (i) in Schwartz seminorms; (iv) it extends to a multilinear tempered distribution in each slot. (v) Under the factorial cube moments with one $t$ and $C$ for the whole class (as one exponential moment uniform over the class gives), the extension to continuous decaying functions is invariant under real translations, reflection positive beyond the range, and $SO(4)$-invariant whenever the compactly supported functions are; with a transfer gap at one step and a non-zero connected pairing it forms one linked Euclidean datum (Hilbert space, semigroup with its gap, the monomials as vectors).

## 2.6 Rotations from one rotation

The rotation $P$ by $(\tfrac35,\tfrac45)$ in the $(0,1)$ plane has an angle irrational in units of $2\pi$ (its powers are $(3+4i)^n/5^n$ with $(3+4i)^n\equiv3+4i\pmod5$); the coordinate-plane rotations of $(0,1)$, $(1,2)$, $(2,3)$ generate $SO(4)$, and signed permutations conjugate $P$ into each plane; (C) makes the Schwinger functions continuous in the rotation.

> Theorem 2.13 (rotation invariance from one rotation). On a non-negative reflection-closed class with (C), read through a flow commuting with the axis permutations, invariance of the limit Schwinger functions of the hypercubic-scalar fields under $P$, on uniformly continuous tests, gives invariance under all of $SO(4)$ on them; in particular for the symmetrized plaquette class.

Invariance under $P$ is the restoration of rotation symmetry in its smallest form; it is not proved.

## 2.7 Over a compact group, at a general schedule

> Theorem 2.14 (the schedule along a coupling sequence). For every compact gauge group and every coupling sequence, the schedule with spacings $a(1)/2^{k+1}$ and the periodic Wilson states is reflection positive and invariant under lattice translations, dyadic time shifts and axis permutations; at every such schedule, given the uniform bound and the range, the reconstruction carries a semigroup of positive self-adjoint contractions with spectrum in $[0,1]$ fixing the vacuum, the cube moments follow from one unit-cube exponential moment, the Schwartz extension exists, and the generator is self-adjoint.

> Theorem 2.15 (centre configurations are fixed). At $SU(2)$, with $c\in[0,\tfrac16)$, the observer flow at every number of steps and radius fixes every configuration with all links in $\{\pm1\}$.

(C) is not proved for any flow at which the target can hold: the flat flow meets it and the target fails there, and at the identity flow a plaquette floor of order $1/\beta^2$ defeats its class-uniform form, the class moments (Theorem 4.28).
