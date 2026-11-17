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

- The seed at the running spacing: the doubling defect of $SU(N)$ at a side of bounded physical size at most $1/1000$, at every large coupling. When the image of its gauge group is $SU(N)$ and its couplings follow the running schedule, which exists for every family's spacing, it gives the seed along its couplings (Theorem E). For $SU(2)$ it is equivalent to a bound on the doubling defect at one physical length: a bound on the doubling defect of the torus of one physical side, uniform as the coupling grows. It is a variant of the open statement (S) of [MG] and is not proved at any large coupling.
- The bound on its finite lattice moments of an insertion list followed by its reflection, at separated configurations in the box of the volume, uniform in the spacing, the volume, the reflection plane and the spread of the points, which gives the bound $K_0$ on its smeared reflected correlations; the placement of the reflection planes clear of the supports of its tests is proved. The reflection of its tokens and tests is stated as named hypotheses.
- The vanishing of the thermal remainders along its order of limits. Each remainder is at most the gap contraction over part of its separations times a reflected moment at the shorter separations on a torus shortened in time ([MG, Theorem 4.56]), with no bound on the supremum of its insertions. Shortening by $q'+1=nj$ steps with $j=\lfloor\sqrt{\lfloor h/n\rfloor}\rfloor$ and $h$ the half-side, so that $q'+1$ is at most the fraction $1/j$ of $h$, the contraction $(1/2)^{2j}$ tends to zero as the period grows ([MG, Theorem 4.57]); the excited weight there is at most $1$ and the input is a bound on the reflected moments on those shortened tori, uniform along its order of limits, which holds with the bound $B^2$ when its insertions are at most $B$ times the transfer power over their steps, with $B$ uniform along its order of limits. Its law is stated on cubic tori and does not give it.
- The inputs on its phase decomposition of Theorem G (component clustering, conjugation, the uniform component bound and covariance of the insertions), and the clustering of the Euclidean readings of its selected phase in Theorem H.

Independence of the subsequence is not reached.

## 1.4 Relation to [MG]

[MG] reduces a formalized existence-and-gap target to three open statements (S), (M), (E) about its own continuum construction. On the route of this paper existence is the construction of [OpenAIYM], and neither (E) nor (M) is used.
