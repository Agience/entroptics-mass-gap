# A Finite-Volume Route to the Mass Gap of the OpenAI Yang–Mills Construction

### Reflection-positive clustering on its lattice tori, its passage to the continuum, and the inputs that remain

Ikailo John Sessford, Ikailo Inc., `john@ikailo.com`
ORCID [0009-0002-0150-4027](https://orcid.org/0009-0002-0150-4027)

*Pre-print. 2026-11-12.*

Text CC BY 4.0; code Apache-2.0.

---

> Companion paper to *The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution* [MG], in the same repository and release; it uses the Lean library `MassGap` of [MG], and each theorem here is a numbered theorem of [MG], section 4.8. It addresses the open questions of the Yang–Mills group's assessment [YMGAssess1] of the OpenAI construction [OpenAIYM]. Every theorem is formalized; what is not proved is stated as a named hypothesis. The mass gap is not proved.

## Abstract

OpenAI's construction of pure Yang–Mills theory [OpenAIYM], assessed by the Yang–Mills group [YMGAssess1], gives a Wightman theory as a subsequential scaling limit of four-dimensional Wilson lattice gauge theory and leaves a uniform mass gap (their open question 3) and the uniqueness of its vacuum open. We give a formalized route from one finite-volume inequality on its own lattice family to those questions. We prove that its Wilson laws, gauge groups and Haar measures are those of [MG] at twice the coupling. We prove that a seed, a bound on the doubling defect $16\log Z(n)-\log Z(2n)$ of the torus at a side $n$ of bounded physical size, gives every torus of its family, at every gauge group, a transfer gap and a reflection-positive clustering bound uniform in the spacing and the volume, for observables of the shape of its insertions. We prove that, given the seed, a reflection of its tokens with reflected tests, a bound on its smeared reflected correlations and vanishing thermal remainders, its lattice correlations satisfy a floored uniform decay at rate $\log2/\ell$; that this decay passes through its limits and, with stated inputs on its phase decomposition, identifies its components; and that its Euclidean semigroup, built from its public spectral fields, has a gap at least the rate at which its field vectors cluster. A version of the decay without floors is refuted by its own short-distance law. The seed, the moment bound, the thermal remainder and the clustering of its selected phase are open.

## Keywords

Yang–Mills theory; mass gap; lattice gauge theory; reflection positivity; transfer operator; Osterwalder–Schrader reconstruction; Lean 4.

## Mathematics Subject Classification (2020)

81T13, 81T25, 82B20, 03B35.

# 1. Introduction

## 1.1 The construction and its open questions

The construction of [OpenAIYM] chooses, for every closed matrix group with simple non-abelian Lie algebra, one Wilson lattice family whose bare coupling runs with $\beta/\log(1/a)$ tending to a positive slope. Along a subsequence of torus sizes its renormalized correlations converge, first in the spacing at fixed physical volume and then in the volume; the limit decomposes into component theories, each satisfying the Osterwalder–Schrader axioms with clustering and reconstructing to a Wightman theory. The assessment [YMGAssess1] lists as open, among others: convergence and uniqueness of the infinite-volume limit (question 1) and a uniform mass gap, with exponential decay of correlations and a spectral gap of the Hamiltonian (question 3); in its §6.2 it notes that clustering of the undecomposed limit would identify the components and make the vacuum unique.

## 1.2 What this paper proves

All statements are theorems of the Lean library of [MG]; section 8 maps them to declarations. Open inputs appear as named hypotheses.

1. The shared object (Theorem A). The Wilson laws of [OpenAIYM] are the laws of [MG] at twice the coupling, by a measure-preserving equivalence of configuration types; $SU(N)$ is one of its gauge groups and its Haar measure is that of [MG]. Its proved trace law gives a kernel satisfying the asymptotic-freedom clause of the target of [MG] (Theorem B).
2. The seed and the torus gap (Theorem C). A seed at an even side $n$ gives the transfer operator of every torus of its family of even side at least $2n$, at every gauge group, a gap of at least $\log2/n$ per step; on its schedule the seed side $2\,\mathrm{den}_m$ has physical size $2$.
3. Clustering (Theorem D). From the seed, the connected correlation of observables of slabs of slices with the time links between them, the shape of its insertions, decays at rate $\log2/\ell$ uniformly in the torus, with constants that are reflected Wilson moments of the observables themselves and no bound on their size, except one thermal-remainder term.
4. The rate of the decay (Theorem E). From the seed, a reflection of its tokens with reflected tests, a bound on its smeared reflected correlations and vanishing thermal remainders, its lattice correlations satisfy a floored uniform decay (U) at rate $\log2/\ell$.
5. The passage to the continuum (Theorems F, G). (U) passes through its limits; with stated inputs on its components, the components equal the mixture. A version of (U) without floors contradicts its short-distance law.
6. The Hamiltonian (Theorem H). Its Euclidean semigroup $e^{-tH}$, built from its public spectral fields, satisfies every hypothesis of a clustering-to-gap theorem except clustering; its zero-energy subspace is the vacuum line; clustering of its field vectors at rate $m$ gives $E\{0<p_0<m\}=0$.

## 1.3 What is open

- The seed along its couplings: the doubling defect at a side of bounded physical size at most $1/1000$, at every large cutoff. It is a variant of the open statement (S) of [MG] and is not proved at any large coupling.
- The bound $K_0$ on its smeared reflected correlations, uniform over the reflection planes that the construction fixes, with the reflection of its tokens and tests stated as named hypotheses.
- The vanishing of the thermal remainders along its order of limits.
- The inputs on its phase decomposition of Theorem G, and the clustering of the Euclidean readings of its selected phase in Theorem H.

Independence of the subsequence is not reached.

## 1.4 Relation to [MG]

[MG] reduces a formalized existence-and-gap target to three open statements (S), (M), (E) about its own continuum construction. On the route of this paper existence is the construction of [OpenAIYM], and neither (E) nor (M) is used.

# 2. The shared object

The construction of [OpenAIYM] and the development of [MG] share one object, the periodic Wilson law on a finite cubic torus. Write $\beta$ for the coupling of [MG], whose action sums $1-\operatorname{Re}\operatorname{tr}\rho(U_p)/d$ over ordered plaquettes.

> Theorem A ([MG, Theorem 4.44]). On every periodic lattice the action of [MG] is twice the sum over unordered planes used in [OpenAIYM]; the normalized Wilson laws agree at $\beta_{\rm OAI}=2\beta$, and every expectation of [MG] at $\beta$ is the integral against their law at $2\beta$. A measurable equivalence of the configuration types carries plaquettes to plaquettes and the law of [MG] at $\beta$ to the law of [OpenAIYM] at $2\beta$ on their own configuration type, for every $\sigma$-finite single-link measure. $SU(N)$ is one of their gauge groups, with Lie algebra $\mathfrak{su}(N)$, and their Haar probability measure is carried to the Haar probability measure of [MG].

With the conversion $\beta_{\rm OAI}=d\,\beta_{\rm lgt}$ of [YMGAssess1] this reads $\beta_{\rm lgt}=2\beta/d$ in the normalization of [DouglasLGT].

> Theorem B ([MG, Theorem 4.45]). For every compact simple group, $c_{\rm AF}=12\dim\mathfrak g/(\pi^4b_0^2)=(2/b_0)^2\cdot3\dim\mathfrak g/\pi^4$, $b_0=11h^\vee/(48\pi^2)$. A complex kernel $S$ with $r^8\log^2(1/r)\,S(r)\to3\dim\mathfrak g/\pi^4$ as $r\to0^+$, the form of the trace law of [OpenAIYM], gives the kernel $c^2\operatorname{Re}S$, $c=\pm2/b_0$, that satisfies the asymptotic-freedom clause of the target of [MG].

The constant $c_{\rm AF}$ of [MG] was fixed from perturbation theory, independently of [OpenAIYM]; that the target's kernel is their trace kernel at the normalization $\operatorname{tr}F^2\leftrightarrow\pm(2/b_0)\Theta$ is not formalized.

# 3. The seed and the torus gap

The doubling defect of the cubic torus at side $n$ and coupling $\beta$ is $D_\beta[n]=16\log Z_\beta(n)-\log Z_\beta(2n)$, a finite-size free energy with the bulk cancelled. The seed at side $n$ is $D_\beta[n]\le1/1000$. In [MG] the seed squares under doubling ($D(2n)\le250\,D(n)^2$) and, through the trace facts of the transfer kernel, gives a gap of the transfer operator on every torus of side $2^kn$ [MG, Theorems 5.6, 5.7, 4.43]; one further step of real ratio between $1$ and $4$ after the dyadic climb reaches every even side at least $2n$.

> Theorem C ([MG, Theorem 4.46]). Let $\ell>0$, let $G$ be a gauge group of [MG, section 4.7] (in [OpenAIYM], every closed subgroup of $U(n+1)$, with their Haar measure), and let a $G$ lattice family have spacings $a_m$, couplings $\beta_{m,p}$ in the normalization of [OpenAIYM] and cubic tori of even sides $L_{m,p}\ge2n_m$, with $n_m\ge2$ even and $n_ma_m\le\ell$. If $\beta_{m,p}\ge0$ and $D_{\beta_{m,p}/2}[n_m]\le1/1000$ for all large $m$ and all $p$, then for all large $m$ and all $p$ the law of [OpenAIYM] on the torus at $(m,p)$ is the image of the law of [MG] at $\beta_{m,p}/2$, whose transfer operator, on all of $L^2$ of the slice and in every sector, has a unit top eigenvector $\psi$ and satisfies $\|K^{n_m}f\|\le\tfrac12\|K\|^{n_m}\|f\|$ for $f\perp\psi$: a gap of at least $\log2/\ell$ in physical units, uniform in the spacing and the volume.

In the schedule of [OpenAIYM] the spacing is $1/\mathrm{den}_m$ with $\mathrm{den}_m$ odd and the side is a multiple of $4\,\mathrm{den}_m$, so $n_m=2\,\mathrm{den}_m$ meets the side hypothesis with $\ell=2$ on every torus of their family. The seed itself, along their couplings, is open: it is not proved at any large coupling.

# 4. Clustering on their tori

> Theorem D ([MG, Theorem 4.47]). Under the hypotheses of Theorem C, for all large $m$ and all $p$:
>
> (i) on the torus of side $L_{m,p}$ the transfer $K$ has a unit eigenvector $\psi$ with eigenvalue $c$, $\lvert c\rvert=\lVert K\rVert\ne0$, with $\lvert\langle u,K^tw\rangle/c^t-\langle u,\psi\rangle\langle w,\psi\rangle\rvert\le2e^{-(\log2/\ell)\,t\,a_m}\lVert u\rVert\lVert w\rVert$ for every lag $t$;
>
> (ii) for bounded measurable functions $a,b$ of the spatial links of one time slice, with bounds $A,B$, $\lvert\langle a_0b_t\rangle-\langle a_0\rangle\langle b_t\rangle\rvert\le6AB\,(2^{-\lfloor t/n_m\rfloor}+2^{-\lfloor(L_{m,p}-t)/n_m\rfloor})$; the same bound, with $L_{m,p}-t$ replaced by $L_{m,p}-w-w'-t$, holds for bounded measurable functions of slabs of $w+1$ and $w'+1$ consecutive slices with the time links between them ($w,w'$ even and positive), with both separations counted from the slab edges, when $4(w+w')+8n_m\le L_{m,p}$;
>
> (iii) in reflection-positivity form, the two separated terms of that correlation are at most $2^{-\lfloor (j+1)/n_m\rfloor}\sqrt{R_f R_{\theta g}}$ and $2^{-\lfloor (j'+1)/n_m\rfloor}\sqrt{R_{\theta f}R_g}$, where $R_f$ is the reflected reading of $f$ at a separation $s$ fixed in lattice units, $t=s+j+1$, $L_{m,p}-w-w'-t=s+j'+1$, and $\theta f$ is $f$ read on the time-reflected slab; the wrap-around term is at most $2^{-\lfloor (j+1)/n_m\rfloor-\lfloor (j'+1)/n_m\rfloor}\sqrt{H_fH_g}+(\lvert\alpha_f\rvert+\sqrt{H_f})(\lvert\alpha_g\rvert+\sqrt{H_g})\,2^{-\lfloor L'/n_m\rfloor/2}$, $L'=(L_{m,p}-w-w')/2$, with $H_f$ the Hilbert–Schmidt reflected reading and $\alpha_f$ the vacuum one-point reading;
>
> (iv) on the cubic torus of side $L_{m,p}\ge8n_m$ every reading in (iii) is bounded by a Wilson moment $\langle f_0\,(\theta f)_s\rangle$ of $f$ with its reflection on the same torus, times $1+\sigma_0$, $\sigma_0\le2^{-\lfloor L_{m,p}/(2n_m)\rfloor}$, except the term $\sqrt{D_L(f)D_L(g)}$, where the thermal remainder $D_L(f)\ge0$ is the part of the reflected moment of $f$ that the vacuum does not carry.

No bound on the size of $f$ or $g$ enters the constants of (iii) and (iv), which is what the renormalized insertions of [OpenAIYM] require: their size grows as the spacing decreases, while their reflected moments at a fixed physical separation are separated two-point quantities. The slabs of (ii)–(iv) have the shape of their insertions, which read the links of a finite stencil. That $D_L$ vanishes along their order of limits is not proved.

The proof works at the level of the transfer kernel. A slab observable is a kernel insertion; time reflection of the slab is the transpose of its kernel, by inversion invariance of the Haar measure; a Hölder inequality for traces of kernel products, proved directly at kernel level, controls the wrap-around; and the trace identity of the torus turns kernel traces into Wilson correlations.

# 5. From the tori to their continuum theory

The objects of [OpenAIYM] used here are restated in Lean from its public statement, line for line: the Wilson family, its finite moments, smearing and convergence clause, its regularity clause, and the fields of its hierarchy and reconstruction that are read.

## 5.1 The floored uniform decay

> Theorem E ([MG, Theorem 4.52]). Let $\ell>0$, and let their family satisfy their regularity and convergence clauses, with at least one insertion in the first group. Suppose that every torus side of their family is even, as on their schedule, and, eventually along their order of limits: $\beta\ge0$ and the seed holds at their couplings on even sides $n\ge2$ with $na\le\ell$; for every $\delta,\varepsilon>0$ a constant $K_0$ bounds the reflected moments of the slab observables built from their smeared insertions by $K_0\lVert t\rVert_1^2$; and their thermal remainders are at most $\eta\lVert t_1\rVert_1\lVert t_2\rVert_1$ for every $\eta>0$. Then for every pair of groups of insertions, every $\delta,\varepsilon>0$ and tests whose second group lies at least $\tau\ge\delta$ later in time than the first, with points within each group at least $\varepsilon$ apart, the smeared connected lattice correlation is at most $K\lVert t_1\rVert_1\lVert t_2\rVert_1e^{-\mu\tau}$ eventually along their order of limits, with $\mu=\log2/\ell$ and $K=4(8K_0(e^{\mu\delta/2}+1)+1)$: the floored uniform decay (U).

The proof places two slabs of slices around the supports of the two tests on each torus; moves their time axis to the transfer axis and their first slab to slice $0$ by invariance of their law; reads their smeared insertions as window-local observables from their stencils; factorizes the tensor test; splits the complex correlation into four real ones; applies Theorem D(iv) to each; and converts lattice gaps to physical time. Under a reflection of their tokens, stated as a named hypothesis, and given reflected tests at the reflection planes the placement fixes, whose existence is an input, the reflected moments are smeared moments of their insertions paired with the reflected insertions under their law; so the hypothesis on $K_0$ is a bound on their own smeared correlations, uniform over those planes. These moments are nonnegative by reflection positivity on each torus, and their order of volumes tends to infinity by their convergence clause; both are proved. The hypothesis on $K_0$ asks for a bound, uniform in the test, on their reflected correlations at configurations whose groups may spread arbitrarily far; their public statement bounds their correlations only on compact sets of separated configurations, so the hypothesis is not supplied by it. It asks for boundedness, and Theorem E returns exponential decay at the rate of the seed.

## 5.2 Through their limits and their phases

> Theorem F ([MG, Theorems 4.48, 4.50 (i)]). A bound $\lvert c_{m,p}(\tau)\rvert\le Ce^{-\mu\tau}$ holding for all large $m$ and all $p$ holds for every limit taken first in $m$, along any filter tending to infinity, possibly depending on $p$, and then in $p$. Consequently, for a hierarchy of [OpenAIYM] satisfying its lattice convergence, representation, mixture, continuity, full-support, normalization and smoothness clauses, (U) gives, for every $\delta,\varepsilon>0$, a bound $Ke^{-\mu\tau}$ on the connected mixed correlation of [OpenAIYM] at separated points whose groups keep their points $\varepsilon$ apart, with the second group at least $\tau\ge\delta$ later than the first.

> Theorem G ([MG, Theorems 4.48 (i), 4.50 (ii), (iii)]). (i) For such a hierarchy, if (U) holds for every pair of groups of insertions with $\mu>0$, the components of [OpenAIYM] cluster in time, observables carry a conjugation, the component correlations are uniformly bounded and the mixed correlation is invariant under time translation, then every component correlation equals the mixed correlation at every separated configuration: the identification of [YMGAssess1, §6.2]. (ii) The floors of (U) are necessary: a bound with one constant at every gap, including $\tau=0$, together with the identification of (i), contradicts their short-distance law for the trace, whose amplitude is positive.

Part (ii) is why (U) is stated with constants depending on a minimum gap and a minimum separation: a connected two-point function bounded at coincident points is excluded for a field of positive dimension, and their trace law exhibits one.

# 6. Their Euclidean semigroup and the gap

> Theorem H ([MG, Theorems 4.49, 4.51]). For a Wightman theory with the fields of the public statement of [OpenAIYM] (spectral representation, positive energy, unique vacuum, normalized and cyclic vacuum, dense domain, vacuum invariance), $S(t)=\int e^{-tp_0}\,dE(p)$, $t\ge0$, over its energy-momentum spectral measure $E$ is a family of bounded self-adjoint operators with $S(0)=1$, $S(s+t)=S(s)S(t)$, $\lVert S(t)\rVert\le1$ and $S(t)\Omega=\Omega$, and the span of its field vectors is dense. The zero-energy subspace $E\{p_0\le0\}$ is the line of $\Omega$. If every pair of field vectors $v,w$ has $\lvert\langle v,S(t)w\rangle-\langle v,\Omega\rangle\langle\Omega,w\rangle\rvert\le C_{v,w}e^{-mt}$ with $m>0$, then $\lVert S(t)u\rVert\le e^{-mt}\lVert u\rVert$ for $u\perp\Omega$, $E\{0<p_0<m\}=0$, the generator $H$ has $\langle u,Hu\rangle\ge m\lVert u\rVert^2$ on its domain orthogonal to $\Omega$, and its kernel is the line of $\Omega$.

Mathlib has no integral against a projection-valued measure; the functional calculus used is built for bounded measurable weights from the spectral representation of [OpenAIYM], through simple-function approximation and the Riesz representation.

The clustering hypothesis is stated on their Minkowski-smeared field vectors, the only dense set their public statement provides. That these readings are the Euclidean values of their selected correlations is their Osterwalder–Schrader reconstruction; it is not restated here, and the clustering of those values is an input.

# 7. Against their open questions

| Question of [YMGAssess1, §8] | Proved here | Named input | Not addressed |
|---|---|---|---|
| 1. Convergence and uniqueness of the infinite-volume limit | Under (U) and the component inputs, every component equals the mixture (Theorem G), the identification of their §6.2 | (U) via Theorem E; component clustering, conjugation, uniform bound, time invariance | Independence of the subsequence |
| 2. A probability measure for the continuum theory | — | — | Not addressed |
| 3. A uniform mass gap | On each torus of their family, from the seed: a transfer gap and clustering at rate $\log2/\ell$, uniform in the spacing and the volume (Theorems C, D); (U) at that rate (Theorem E); passage through their limits (Theorem F); a spectral gap from clustering of their Euclidean semigroup (Theorem H) | The seed along their couplings; the reflection of their tokens and tests; the bound $K_0$ on their smeared reflected correlations; vanishing thermal remainders; clustering of their selected Euclidean readings | Carrying the rate of (U) to their selected phase without the clustering input |
| 4. Wilson loops and the area law | — | — | Not addressed |
| 5. Single-particle states | — | — | Not addressed |

# 8. Lean

Every theorem of this paper is a numbered theorem of [MG]: A–H are [MG, Theorems 4.44–4.52] as cited. The declarations, their open hypotheses and the modules are listed in the rows 4.44–4.52 of the theorem-to-Lean map of [MG] (`research/paper/v3/04-reduction.lean-map.md`) and in `research/FORMALIZATION.md`. The modules of this route are `OpenAIDictionary`, `OpenAIConfig`, `OpenAIBridgeSides`, `OpenAIBridgeCluster`, `OpenAIBridgeUniform`, `OpenAIBridgeGroups`, `OpenAIBridgeSlab`, `OpenAIBridgeRP`, `OpenAIBridgeCubic`, `OpenAIBridgeCompose`, `OpenAIBridgeGlue`, `OpenAIBridgeLimits`, `OpenAILink`, `OpenAIBridgeGap` and `OpenAISemigroup`, under `research/lean/MassGap/`.

The library builds on Lean 4.31.0 with the pinned Mathlib; it has no `sorry`, and its theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The definitions of [OpenAIYM] that are used are restated in these modules with file and line citations of its public statement, since its development (Lean 4.32.0) cannot be imported. Build instructions are in the repository README, section "Lean".

# 9. References

[DouglasLGT] M. R. Douglas, *lgt: Lattice Gauge Theory in Lean 4*, <https://github.com/mrdouglasny/lgt>, commit b8793ccf6a51e00e9e2b1685ba191b8626e37137 (Lean 4 toolchain leanprover/lean4:v4.30.0), 22 July 2026, headline theorems in the module LGT/MassGap/StrongCoupling.lean, Apache-2.0. Software; unrefereed; no DOI.

[MG] I. J. Sessford, *The Mass Gap of $SU(N)$ Gauge Theory Seen by an Observer of Fixed Physical Resolution*, release v0.4.1 of <https://github.com/Agience/entroptics-mass-gap>, Zenodo concept DOI <https://doi.org/10.5281/zenodo.22652660>, 2026. The main paper of this repository; its Lean library `MassGap` carries the theorems of this paper. Unrefereed preprint with software.

[OpenAIYM] OpenAI, *Wilson Yang–Mills construction*, Lean 4 development submitted to the Yang–Mills group on 28 October 2026, <https://github.com/yang-mills-group/OpenAI-YM-20261028>, commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464 (Lean 4 toolchain leanprover/lean4:v4.32.0), headline theorem in the module Solution.lean, Apache-2.0. Software; unrefereed; no DOI.

[YMGAssess1] Yang–Mills group, *Validation of the OpenAI Yang–Mills construction*, assessment 1, 10 November 2026, <https://github.com/yang-mills-group/YM>, commit 55ba9fc36293b3f4d52c6b1f813169a0be76ee98, file docs/assessment-1.pdf (SHA-256 8e658c00900bf723cbe90436eb1f78fca4f287e008a85c21fdceaf59e61db219). Unrefereed.
