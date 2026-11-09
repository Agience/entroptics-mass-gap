# 3. The count

In the frame an aperture holds a finite number of modes, read from the spectrum of what it sees (§E-3.1, §E-3.2). Here that count does mathematical work: if each mode of the observer's screen is hypercontractive relative to its own variance, the reading's variance gives every even moment through the Rényi count of order ½, and for the single-reading closure no order above ½ does. None of the hypotheses of Theorems 3.8 and 3.9 is proved at any coupling of the interacting theory.

## 3.1 The screen and its modes

Let $\nu$ be a state on $C(X,\mathbb R)$, $X$ compact. A screen is a finite family $F=(F_y)_{y\in\iota}$ of real continuous functions; its Gram matrix $G_{yz}=\nu(F_yF_z)=U\operatorname{diag}(\lambda)U^{\mathsf T}$ has modes $e_\alpha=\sum_yU_{y\alpha}F_y$.

> Theorem 3.1 (modes). (i) $\nu(e_\alpha e_\beta)=\lambda_\alpha\delta_{\alpha\beta}$, so $\lambda_\alpha\ge0$; (ii) $F_y=\sum_\alpha U_{y\alpha}e_\alpha$ and $\sum_\alpha\lambda_\alpha=\sum_y\nu(F_y^2)$; (iii) every column of $U$ is a unit eigenvector of $G$.

The counts of a spectrum are the Shannon count $e^{\mathrm H}$, the Rényi counts $R_\alpha$ (with $R_{1/2}=(\sum\sqrt{p_k})^2$ and $R_2=1/\sum p_k^2$), and the level counts $n_i(a)=\#\{k:p_k>a^{2(i+1)}\}$ for a ladder $a\in(0,1)$; none has a witness to choose. The observer's screen at aperture $s$ and step $k$ is the connected flowed reading of a channel translated over the box $\{0,\dots,n_s-1\}^4$, $n_s=\lceil s/a_k\rceil$, of fixed physical side; each reading reads only the translate of the flow's light cone around the channel's support. The library [S] reads the whole family through one function, `renyi_count(weights, order)`, with order ½ as its default because of Theorems 3.3 and 3.6.

## 3.2 Every moment from one variance

> Theorem 3.2 (Minkowski through the modes). If $\nu(e_\alpha^{2p})\le C\lambda_\alpha^p$ for every $\alpha$, then $\nu((\sum_\alpha c_\alpha e_\alpha)^{2p})\le C(\sum_\alpha|c_\alpha|\sqrt{\lambda_\alpha})^{2p}$.

> Theorem 3.3 (the count turns one variance into every moment). If every reading of a finite screen has the moments of one function $G_0$ and every mode satisfies $\nu(e_\alpha^{2p})\le C\lambda_\alpha^p$, then $\nu(G_0^{2p})\le C(R_{1/2}(\lambda)\,\nu(G_0^2))^p$. At the observer's screen, with translation invariance of the state at step $k$, the connected flowed reading satisfies $\nu_k(F^{2p})\le C(R_{1/2}\nu_k(F^2))^p$.

Idea: Theorem 3.2 at one site, averaged over the $n$ sites; Cauchy–Schwarz on a unit column gives $\sum_y|U_{y\alpha}|\le\sqrt n$, and $\sum\lambda=n\,\nu(G_0^2)$, so the volume cancels. The constants are $C$ and the count; neither the box nor the step enters otherwise.

## 3.3 The count cannot be dropped, and which count

> Theorem 3.4 (the load-bearing tests). On $\{\pm1\}^m$ with the uniform state: (i) $n$ equal weights have $R_{1/2}=n$; (ii) every Walsh character has $\nu(\chi_S^{2p})=\nu(\chi_S^2)^p$, yet $F=\sum_S\chi_S$ has $\nu(F^4)=2^m\nu(F^2)^2$; (iii) with $t_i=\exp(-2^i/2^{m+1})$ the screen $(\prod_{i\in S}t_i\,\chi_S)_S$ has one-dimensional eigenspaces, every unit eigenvector's mode satisfies $\nu(e^{2p})=\lambda^p$, and $\nu(F^4)\ge(3/2)^m\nu(F^2)^2$. So no constant bounds the fourth moment by the squared variance uniformly in $m$.

> Theorem 3.5 (the counts compared). (i) $R_\beta\le R_\alpha$ for $0<\alpha\le\beta$; in particular $R_2\le e^{\mathrm H}\le R_{1/2}$. (ii) For every $B$ some spectrum has $e^{\mathrm H}\le e^2$ and $R_{1/2}\ge B$. (iii) If $n_i(a)\le c\,e^{\mathrm H}(i+1)^r$ for every $i$, then $R_{1/2}\le(c\,e^{\mathrm H}(1-a)\sum_i(i+1)^ra^i)^2$.

The library's measured count is the Shannon count; (i) and (ii) say it bounds the count the moments need from below and does not control it, and (iii) says what does.

## 3.4 Order ½ is sharp

The closure holds at order $\alpha$ if for every $p$ and $C$ there is $C'$ such that every finite family of pairwise uncorrelated functions $e_a$ on every compact space and state, with $\nu(e_a^{2p})\le C\nu(e_a^2)^p$, has $F=\sum_ae_a$ with $\nu(F^{2p})\le C'(R_\alpha(\lambda)\nu(F^2))^p$.

> Theorem 3.6 (order ½ is sharp). The single-reading closure, read through $R_\alpha$ with one constant, holds for every $\alpha\in(0,\tfrac12]$ (with $C'=C$, since $R_{1/2}\le R_\alpha$) and fails for every $\alpha>\tfrac12$, $\alpha=1$ included; ½ is the greatest order at which it holds. For the screen closure of Theorem 3.3 only the case $\alpha\le\tfrac12$ is proved.

Idea of the failure: a spike screen on $\{\pm1\}^m$ with one mode of weight $1-\varepsilon$, $\varepsilon=2^{-m(1-\alpha)/\alpha}/2$, spread over $2^m-1$ further modes, keeps $R_\alpha$ bounded while the reading at $(+1,\dots,+1)$ is of order $2^{m\gamma/2}$, $\gamma=(2\alpha-1)/\alpha$; at $p=\lceil2/\gamma\rceil$ a uniform $C'$ would bound $2^m$. For $\alpha\ge\tfrac34$ the spike of order $\tfrac34$ serves, since $R_\alpha\le R_{3/4}$. The failure is at an order that grows as $\alpha\downarrow\tfrac12$; whether it already holds at the fourth moment for $\alpha\in(\tfrac12,\tfrac23]$ is not proved.

## 3.5 The free flowed spectrum

On the Dirichlet box with $J$ modes per direction, side $L$ and $d=2m$ dimensions, the flowed spectrum is $w_ke^{-2t\mu_k}$, $\mu_k$ the lattice Laplacian levels.

> Theorem 3.7 (the free flowed spectrum). Let $\tau\le2t/L^2$. (i) If the top weight sits at the lowest mode and $\log(w_{k_0}/w_k)\le\kappa(2t\mu_k-2t\mu_{k_0})$, then $e^{\mathrm H}\le A_\kappa^2e((1/\tau+\pi^2)/4)^m$, the level counts grow polynomially and $R_{1/2}\le A_\kappa^2e^2e^{\mathrm H}$, with $A_\kappa$ explicit and no constant depending on $J$. (ii) The massless propagator weight $1/\mu$ meets (i) at $\kappa=1/(4d\tau)$, uniformly in the zoom, though its global weight ratio is unbounded. (iii) Under $R_{1/2}\le c\,e^{\mathrm H}$ all orders in $[\tfrac12,1]$ agree up to $c$. (iv) If every screen of the observer is such a spectrum, the count clause H3 of Definition 3.1 (section 3.6) holds. (v) The polynomial growth is load-bearing: some heat spectrum fails it at every top mode.

The bounds hold while the flow time relative to the aperture stays bounded below; a flow time fixed in lattice units is not covered. That the observer's screens in the Wilson state have such spectra is not proved. On Villain $U(1)$ with the linear flow the interacting-to-free ratio of the sorted spectra is unbounded along the zoom while the count itself survives, so the missing input is the count stated one-sided, not a comparison with the free field (argued).

## 3.6 The count on the existence side

Definition 3.1 (the aperture count). At a flow family $(W_s)$ and an aperture $b$: (H1) a per-mode bound $\nu_k((\sum_yv_yF_y)^{2p})\le((2p)!)^{\lceil d_j/4\rceil}(C\lambda)^p$ at every unit eigenvector $v$, every aperture $s\le b$ and channel $j$ of canonical dimension $d_j$; (H2) every channel's variance at most $(\sigma_j\bar g^2(s)^{\kappa_j}/s^{d_j})^2$, $\bar g^2$ the one-loop running coupling at the aperture, and the plaquette reading's variance and mean bounded at $b$; (H3) $e^{\mathrm H}\le D$ and $n_i(a)\le c\,e^{\mathrm H}(i+1)^r$; (af) the trace kernel settles onto its tree value times the running coupling squared.

> Theorem 3.8 (the count carries the moments). Under the aperture count, every channel's moments obey $\nu_k(F^{2p})\le((2p)!)^{\lceil d_j/4\rceil}(\lambda_0\sigma_j\bar g^2(s)^{\kappa_j}/s^{d_j})^{2p}$ with $\lambda_0=\sqrt{\max(C\bar R,1)}$, $\bar R$ from Theorem 3.5 (iii); it gives the coincident-point substrate core; and with (S) and, along every tower near $u_0=0^+$, the settling window reading (the window reading $2^km(\beta_k)$ eventually finite and, from some $k_0$, moved by each step by at most $(2^{-k}/\ell)^\eta$ for some $\ell,\eta>0$) and the flow-side bundle (a flow family of physical range with the strong small-flow-time expansion, settling along the zoom, covariance, the Ward identity, non-degeneracy, generation and the three-point clause, each read through the family; Theorem 4.33) with the count in its moment slot, $\mathrm{CS}(N)$ holds.

The Wick factor is needed already in degree one, and on the spin cube the finite-chaos bound [Bonami] gives H1 with $C=e^{2\lceil d_j/4\rceil}$ for degree $q\le d_j/2$ (proved). Theorem 1.1 does not use Theorem 3.8.

The moment clause of (E) asks, for every field of the symmetrized plaquette class, $\nu_k((\sum_{x\in[-R,R]^4}O\circ V_k\circ T_x)^{2p})\le((2R+1)^4)^{2p}(2p)!\,t^{-2p}C_0$: a factorial bound on single-site moments of order $a_k^4$. On a screen of fixed physical side $\rho$ consider (ModeHyper) a per-mode bound with Wick factor $(2p)!$; (CountBound) $R_{1/2}\le\bar R$; (PhysVar) variance at most $(\sigma a_k^4)^2$; (PhysMean) mean at most $E\,a_k^4$, each eventually and over the class.

> Theorem 3.9 (the moment clause from the count). (i) On a shift-invariant schedule and a non-negative class, the four statements give the factorial cube-moment bound, with $C_0=2$, $t=1/(5^4\cdot2Z)$, $Z=\max(\sqrt{C\bar R}|\sigma|,|E|,1)$. (ii) In particular, along any coupling sequence, for the symmetrized plaquette class and every flow, they give the moment clause of (E). (iii) On a non-negative class, one exponential moment at one site in physical units, $\nu_k(\exp((s/a_k^4)F_k))\le C$, gives (PhysMean) and (PhysVar).

The count replaces the one-site exponential moment of Theorem 6.6 by the per-mode bound and the count bound; it carries content only where the screen's spectrum is concentrated (on a diagonal Gram matrix the count grows like the volume). It discharges nothing of (E) by itself, and the count gives no bound on the doubling defect.

## 3.7 A finite aperture holds a finite count

The frame's central claim is that an aperture of fixed physical size holds a finite count of modes at every zoom. In the setting of the Entroptics library, a signal on $N$ sites read through a window of $T$ consecutive sites and a band of $W$ consecutive frequencies, it is proved (Theorem 3.15). For the Wilson measure it reduces to one property of the bare plaquette field.

> Theorem 3.10 (the count on the box). (i) For any state and any orthonormal frame of the box, the order-½ count of the screen's Gram spectrum is at most the count of its diagonal in that frame; in the Dirichlet sine frame this is the two-point form of the count bound. (ii) A screen smoothed by the heat kernel at fixed physical time $\theta$ has count at most $R_{\mathrm{heat}}(\theta)\,Q$ along the zoom, whenever the bare plaquette covariance on the box has operator norm $c$ with $c\sum_\beta e^{-2\theta\mu_\beta}\le Q\sum_y\nu_k(F_y^2)$. (iii) That ratio holds, with $Q=K_0R_{\mathrm{heat}}(\theta)$, if the bare correlator is non-negative on the box and $\sum_zC(z)\le K_0C(0)$ with one $K_0$, eventually along the zoom.

> Theorem 3.11 (reflection positivity signs the correlator on the axes). For the symmetrized plaquette class, the correlator $\Gamma(n)=\nu(F\,T_{ne_\tau}F)$ in every lattice direction is non-negative at even lags beyond twice the support depth for every compact group (site reflection); for $SU(N)$ (site and link reflection) it is non-negative, non-increasing and log-convex at every lag beyond twice the support depth, and the same holds for slice sums.

The heat-smoothed screen is not an observer flow of (E), which acts on configurations; Theorem 3.10 (i) connects the count of any admissible flow to the moment clause through Theorem 3.9. Positivity off the axes is not known for $SU(N)$ (for compact $U(1)$ it is Ginibre's inequality), and the uniform $K_0$ needs short-distance control of the plaquette two-point function: the transfer gap's rate shrinks along the two-loop couplings and cannot supply it.

> Theorem 3.12 (the conditional variance bounds the lowest mode below). At $SU(N)$, releasing the links of a sparse set one at a time, the variance of the lowest-mode field is at least the sum of the one-link conditional variances of its local pieces. Hence the count bound for the heat screen follows from one inequality: the operator norm of the bare covariance on the box at most a fixed multiple of that sum, eventually along the two-loop couplings.

Theorem 3.12 excludes, without reflection positivity, the profile $\Gamma(0)=1$, $\Gamma(\pm1)=-\tfrac12$, which satisfies every constraint of Theorem 3.11 and has vanishing lowest-mode variance (argued); reflection positivity alone does not close the weaker form. The remaining inequality reads, at zero momentum, $\sum_zC_k(z)\le K\,\nu_k(\mathrm{cv}_lA_l)$: the plaquette correlator summed over separations is at most a fixed multiple of one link's conditional variance, uniformly as the coupling grows. Its short-distance part is free of the coupling: at every coupling and every state, if each plaquette variance on the box is at most $\kappa$ times the floor and each row sum beyond a fixed radius is at most $\kappa'$ times it, the operator norm is at most $(n\kappa+\kappa')$ times the floor, $n$ the number of sites within that radius. Neither hypothesis is proved: the first is the per-link floor, $\nu_k(\mathrm{cv}_lA_l)$ at least a fixed fraction of the plaquette variance, argued at Gaussian order only; the second is the tail. Along the two-loop couplings the box grows like $2^k$ while $\beta_k$ grows like $k$, so a comparison at one scale loses a factor at each of about $k$ scales; every single-scale tool in the formalization (Holley–Stroock, Bakry–Émery, Dobrushin influence) degrades with $\beta$ (argued). Controlling the tail with one constant is the multiscale problem of Bałaban's renormalization group [Balaban87], which is not formalized here.

> Theorem 3.13 (self-similar control beyond the seed). If $\beta>0$, $w_0\ge1$ and $D_\beta(w_0)<1/1000$, the per-site action susceptibility $\chi_{2^{w_0+m}}(\beta)$ of the periodic torus is bounded uniformly in $m$. The proof splits $\chi$ into dyadic shells, identifies each shell with the second $\beta$-derivative of the doubling defect, and bounds it by interpolation against the doubly exponential decay of the defect in the basin.

> Theorem 3.14 (the small windows leave the basin). For $N\ge2$ and every bound $W$, eventually in $\beta$, every window $1\le w\le W$ has $D_\beta(w)>1/1000$; hence any seed window tends to infinity with $\beta$.

Theorem 3.13, a self-similar induction on dyadic shells, controls the scales beyond the seed window. The seed window lies beyond the correlation length, so the scales the tail needs, from the lattice spacing up to the correlation length, are exactly those the induction does not reach, and by Theorem 3.14 it cannot be run downward: the small windows are never in the basin at large coupling, so the recursion has nothing to start from. What the fine scales need is a relative bound on the finite-size free energy at weak coupling, the perturbative content of the renormalization group.

> Theorem 3.15 (a finite aperture holds a finite count). On $\mathbb Z_N$ let $A=P_SB_\Omega P_S$, with $S$ a window of $T$ consecutive sites and $\Omega$ a band of $W$ consecutive frequencies, $1\le T\le N$, $1\le W\le N$. The eigenvalues of $A$ lie in $[0,1]$, their sum is $TW/N$, the plunge mass $\sum\lambda(1-\lambda)$ is at most $\tfrac12(9+\log\min(T,W))$, and the number of eigenvalues above $\tfrac12$ differs from $TW/N$ by at most $9+\log\min(T,W)$.

This is the finite, discrete form of the count of time- and band-limiting [Slepian78, LandauWidom80], proved in the Lean of the Entroptics library [S]. The $9$ is computed: $4(3/2)^2$, from the crossover of the two bounds on the band kernel. The count is the area $TW/N$ of the aperture, up to a logarithm; it does not depend on what is read through it. Theorems 3.10 to 3.14 ask the same of the Wilson field, where the screen's modes are not exact frequencies and the open part is the tail.
