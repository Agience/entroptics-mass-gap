import Mathlib
import MassGap.ClayG
import MassGap.GaugeG2

/-!
# MassGap.AbelianGen — an abelian generator at every instantiated group

`CompReduceG.AbelianGenG G` asks for a `d × d` matrix `H` whose every real multiple is in
`GaugeLie.lieGen` and with `Re tr H² ≠ 0`. This module proves it at every group with a `GaugeLie`
instance, and discharges the `hab` input of `ClayG.clayStatementAtG_GS` there.

## The trace

`re_trace_mul_self_pos`: for a Hermitian `H`, `Re tr H² = ∑ᵢₖ |Hᵢₖ|²`, positive as soon as `H ≠ 0`.
So at each group `Re tr H² ≠ 0` follows from `H` Hermitian and nonzero.

## The generators

* `SU(N)`, `N ≥ 2`: `suH p q = E_pp − E_qq` at `p = 0`, `q = 1`; Hermitian, traceless.
* `SO(n)`, `n ≥ 5`, and `SO(3)`: `soH p q = i E_qp − i E_pq` at `p = 0`, `q = 1`; Hermitian,
  `Hᵀ = −H`.
* compact `Sp(n)`: `uspH n i₀`, the block matrix `diag(D, −D)` with `D = E_{i₀i₀}`, reindexed along
  `finSumFinEquiv` as `GaugeInstances.Jsp` is; Hermitian, and `H J + J Hᵀ = 0` from the block
  product with `J = [[0, −1], [1, 0]]` and `Dᵀ = D`.
* `G₂`: `GaugeG2.cartanM`, in `lieGen` with `cartanM ≠ 0` by `GaugeG2.lieGen_cartanM`.

Each `lieGen` predicate is closed under real multiples: Hermitian (`IsHermitian.smul` at a real
scalar), `tr`, `ᵀ`, `X J + J Xᵀ` and the derivation condition of `φ` are real-linear in `X`.

## The capstone

`ClayAtGFromGS G` is the conclusion `ClayStatementAtG G W (SymPlaqClassG G)` of
`ClayG.clayStatementAtG_GS` under all of its inputs except `hab`, quantified as there.
`clayAtGFromGS_of_abelianGenG` is `clayStatementAtG_GS` with `hab` held fixed; the per-group
theorems `clayStatementAtG_GS_SU`, `_SO`, `_SO3`, `_USp`, `_G2` supply it.

DERIVED (module-wide): `0`, `1` the two indices of the generators and the vanishing values; `2`,
`3`, `5` the least or fixed dimensions of the instances; `4` the dimension.
-/

noncomputable section

namespace MassGap.AbelianGen

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayTreeG
  MassGap.ClayStatementG MassGap.ClayWiringG MassGap.FlowG MassGap.TimeGroupG
  MassGap.EnergyBoundG MassGap.ObserverOSG MassGap.ObserverLinkedG MassGap.SymPlaqG
  MassGap.InputsG MassGap.CompReduceG MassGap.LinkReduce MassGap.LinkReduceG Filter
open scoped Topology Matrix

/-! ## 1. The trace of a Hermitian square -/

/-- **`Re tr H² > 0` for a nonzero Hermitian `H`**: `Re tr H² = ∑ᵢ ∑ₖ |Hᵢₖ|²`, since
`Hₖᵢ = conj Hᵢₖ`, and one entry is nonzero.

DERIVED: `0` the excluded matrix and the lower bound. -/
theorem re_trace_mul_self_pos {m : Type} [Fintype m] {H : Matrix m m ℂ} (hH : H.IsHermitian)
    (h0 : H ≠ 0) : 0 < (Matrix.trace (H * H)).re := by
  obtain ⟨i₀, k₀, hik⟩ : ∃ i k, H i k ≠ 0 := by
    by_contra hcon
    apply h0
    ext i k
    by_contra hik
    exact hcon ⟨i, k, hik⟩
  have hsum : (Matrix.trace (H * H)).re = ∑ i, ∑ k, Complex.normSq (H i k) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have hc : H k i = (starRingEnd ℂ) (H i k) := (hH.apply k i).symm
    rw [hc, Complex.mul_conj, Complex.ofReal_re]
  rw [hsum]
  calc (0 : ℝ) < Complex.normSq (H i₀ k₀) := Complex.normSq_pos.mpr hik
    _ ≤ ∑ k, Complex.normSq (H i₀ k) :=
        Finset.single_le_sum (f := fun k => Complex.normSq (H i₀ k))
          (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ k₀)
    _ ≤ ∑ i, ∑ k, Complex.normSq (H i k) :=
        Finset.single_le_sum (f := fun i => ∑ k, Complex.normSq (H i k))
          (fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀)

/-! ## 2. Closure of the predicates under real multiples -/

section Smul

variable {m : Type} {M : Matrix m m ℂ}

/-- A real multiple of a Hermitian matrix is Hermitian. DERIVED: no numeral. -/
theorem herm_smul (h : M.IsHermitian) (a : ℝ) : (a • M).IsHermitian :=
  h.smul (star_trivial a)

/-- A real multiple of a traceless matrix is traceless. DERIVED: `0` the trace. -/
theorem trace_smul_eq_zero [Fintype m] (h : M.trace = 0) (a : ℝ) : (a • M).trace = 0 := by
  rw [Matrix.trace_smul, h, smul_zero]

/-- A real multiple of an antisymmetric matrix is antisymmetric. DERIVED: no numeral. -/
theorem transpose_smul_eq_neg (h : M.transpose = -M) (a : ℝ) :
    (a • M).transpose = -(a • M) := by
  rw [Matrix.transpose_smul, h, smul_neg]

/-- `X J + J Xᵀ = 0` is closed under real multiples. DERIVED: `0` the relation. -/
theorem symp_smul_eq_zero [Fintype m] {J : Matrix m m ℂ} (h : M * J + J * M.transpose = 0) (a : ℝ) :
    (a • M) * J + J * (a • M).transpose = 0 := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h, smul_zero]

end Smul

/-! ## 3. The generators -/

section Generators

variable {m : Type} [DecidableEq m]

/-- `E_pp − E_qq`. DERIVED: `1` the unit entries. -/
def suH (p q : m) : Matrix m m ℂ := Matrix.single p p 1 - Matrix.single q q 1

/-- `suH p q` is Hermitian. DERIVED: no numeral. -/
theorem suH_herm (p q : m) : (suH p q).IsHermitian := by
  rw [Matrix.IsHermitian, suH, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
    Matrix.conjTranspose_single, star_one]

/-- `suH p q` is traceless. DERIVED: `0` the trace. -/
theorem suH_trace [Fintype m] (p q : m) : (suH p q).trace = 0 := by
  rw [suH, Matrix.trace_sub, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same, sub_self]

/-- `suH p q ≠ 0` at `p ≠ q`: its `(p, p)` entry is `1`. DERIVED: `0` the excluded matrix. -/
theorem suH_ne_zero {p q : m} (hpq : p ≠ q) : suH p q ≠ 0 := by
  intro h
  have he := congrFun (congrFun h p) p
  simp [suH, Matrix.sub_apply, Ne.symm hpq] at he

/-- `i E_qp − i E_pq`. DERIVED: no numeral. -/
def soH (p q : m) : Matrix m m ℂ := Matrix.single q p Complex.I - Matrix.single p q Complex.I

/-- `soH p q` is Hermitian: `conj i = −i`. DERIVED: no numeral. -/
theorem soH_herm (p q : m) : (soH p q).IsHermitian := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [Matrix.IsHermitian, soH, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
    Matrix.conjTranspose_single, hI, ← Matrix.single_neg, ← Matrix.single_neg]
  abel

/-- `(soH p q)ᵀ = −soH p q`. DERIVED: no numeral. -/
theorem soH_transpose (p q : m) : (soH p q).transpose = -soH p q := by
  rw [soH, Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single, neg_sub]

/-- `soH p q ≠ 0` at `p ≠ q`: its `(q, p)` entry is `i`. DERIVED: `0` the excluded matrix. -/
theorem soH_ne_zero {p q : m} (hpq : p ≠ q) : soH p q ≠ 0 := by
  intro h
  have he := congrFun (congrFun h q) p
  simp [soH, Matrix.sub_apply, hpq] at he

end Generators

section Symplectic

variable (n : ℕ)

/-- The block matrix `diag(D, −D)`, `D = E_{i₀i₀}`, over `Fin n ⊕ Fin n`. DERIVED: `1` the unit
entry. -/
def uspB (i₀ : Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks (Matrix.single i₀ i₀ 1) 0 0 (-Matrix.single i₀ i₀ 1)

/-- `uspB` reindexed along `finSumFinEquiv`, as `GaugeInstances.Jsp` is. DERIVED: no numeral. -/
def uspH (i₀ : Fin n) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (uspB n i₀)

/-- `uspB` is Hermitian. DERIVED: no numeral. -/
theorem uspB_herm (i₀ : Fin n) : (uspB n i₀).IsHermitian := by
  simp only [Matrix.IsHermitian, uspB, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_single, Matrix.conjTranspose_zero, star_one]

/-- `uspH` is Hermitian. DERIVED: no numeral. -/
theorem uspH_herm (i₀ : Fin n) : (uspH n i₀).IsHermitian := by
  rw [Matrix.IsHermitian, uspH, Matrix.conjTranspose_reindex, (uspB_herm n i₀).eq]

/-- **`uspH` satisfies the `Sp(n)` relation** `H J + J Hᵀ = 0` at `J = GaugeInstances.Jsp n`: in
blocks, `diag(D, −D) J + J diag(D, −D)ᵀ = [[0, Dᵀ − D], [Dᵀ − D, 0]]` and `Dᵀ = D`.

DERIVED: `0` the relation. -/
theorem uspH_symp (i₀ : Fin n) :
    uspH n i₀ * MassGap.GaugeInstances.Jsp n
      + MassGap.GaugeInstances.Jsp n * (uspH n i₀).transpose = 0 := by
  have hB : uspB n i₀ * Matrix.J (Fin n) ℂ + Matrix.J (Fin n) ℂ * (uspB n i₀).transpose = 0 := by
    simp only [uspB, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add, Matrix.transpose_single, Matrix.transpose_neg, Matrix.transpose_zero]
    simp [Matrix.fromBlocks_zero]
  unfold uspH MassGap.GaugeInstances.Jsp
  rw [Matrix.transpose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  ext i j
  have he := congrFun (congrFun hB (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.zero_apply] using he

/-- `uspH ≠ 0`: its entry at `finSumFinEquiv (inl i₀)` on the diagonal is `1`.
DERIVED: `0` the excluded matrix. -/
theorem uspH_ne_zero (i₀ : Fin n) : uspH n i₀ ≠ 0 := by
  intro h
  have he := congrFun (congrFun h (finSumFinEquiv (Sum.inl i₀))) (finSumFinEquiv (Sum.inl i₀))
  simp [uspH, uspB, Matrix.reindex_apply, Matrix.submatrix_apply] at he

end Symplectic

/-! ## 4. The `G₂` derivation condition under real multiples -/

open MassGap.GaugeG2 in
/-- **`lieGen` of `G₂` is closed under real multiples**: Hermitian and antisymmetric by §2, and the
derivation condition `φ(Xx, y, z) + φ(x, Xy, z) + φ(x, y, Xz) = 0` is linear in `X`, `φ` being
trilinear.

DERIVED: no numeral. -/
theorem lieGen_smul_G2 {M : Matrix (Fin (GaugeGroup.dim G2)) (Fin (GaugeGroup.dim G2)) ℂ}
    (h : GaugeLie.lieGen (G := G2) M) (a : ℝ) : GaugeLie.lieGen (G := G2) (a • M) := by
  obtain ⟨hH, hT, hD⟩ := h
  refine ⟨herm_smul hH a, transpose_smul_eq_neg hT a, fun x y z => ?_⟩
  have hxyz := hD x y z
  simp only [phi3, e3] at hxyz
  simp only [phi3, e3, Matrix.smul_mulVec, Pi.smul_apply, Complex.real_smul]
  linear_combination (a : ℂ) * hxyz

/-! ## 5. `AbelianGenG` at every instantiated group -/

section Abelian

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

/-- **`AbelianGenG G` from a nonzero Hermitian `H` whose real multiples are in `lieGen`**: the
trace clause is `re_trace_mul_self_pos`.

DERIVED: `0` the excluded matrix. -/
theorem abelianGenG_of_herm (H : Matrix (Fin (GaugeGroup.dim G)) (Fin (GaugeGroup.dim G)) ℂ)
    (hH : H.IsHermitian) (h0 : H ≠ 0) (hgen : ∀ a : ℝ, GaugeLie.lieGen (G := G) (a • H)) :
    AbelianGenG G :=
  ⟨H, hgen, (re_trace_mul_self_pos hH h0).ne'⟩

end Abelian

/-- **`AbelianGenG (SU N)`, `N ≥ 2`**, at `H = suH 0 1 = diag(1, −1, 0, …)`: Hermitian, traceless,
nonzero.

DERIVED: `0`, `1` the two indices; `2` the least `N`. -/
theorem abelianGenG_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] : AbelianGenG (MassGap.SUN.SU N) := by
  have h2 : 2 ≤ N := Fact.out
  have hpq : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  exact abelianGenG_of_herm (G := MassGap.SUN.SU N) (suH _ _) (suH_herm _ _) (suH_ne_zero hpq)
    fun a => ⟨herm_smul (suH_herm _ _) a, trace_smul_eq_zero (suH_trace _ _) a⟩

/-- **`AbelianGenG (SO n)`, `n ≥ 5`**, at `H = soH 0 1 = i(E₁₀ − E₀₁)`: Hermitian, `Hᵀ = −H`,
nonzero.

DERIVED: `0`, `1` the two indices; `5` the least `n`. -/
theorem abelianGenG_SO (n : ℕ) [NeZero n] [Fact (5 ≤ n)] :
    AbelianGenG (MassGap.GaugeInstances.SO n) := by
  have h5 : 5 ≤ n := Fact.out
  have hpq : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  exact abelianGenG_of_herm (G := MassGap.GaugeInstances.SO n) (soH _ _) (soH_herm _ _)
    (soH_ne_zero hpq) fun a =>
      ⟨herm_smul (soH_herm _ _) a, transpose_smul_eq_neg (soH_transpose _ _) a⟩

/-- **`AbelianGenG (SO 3)`** at `H = soH 0 1 = i(E₁₀ − E₀₁)`: Hermitian, `Hᵀ = −H`, nonzero.

DERIVED: `0`, `1` the two indices; `3` the dimension. -/
theorem abelianGenG_SO3 : AbelianGenG (MassGap.GaugeInstances.SO 3) := by
  have hpq : (0 : Fin 3) ≠ 1 := by decide
  exact abelianGenG_of_herm (G := MassGap.GaugeInstances.SO 3) (soH _ _) (soH_herm _ _)
    (soH_ne_zero hpq) fun a =>
      ⟨herm_smul (soH_herm _ _) a, transpose_smul_eq_neg (soH_transpose _ _) a⟩

/-- **`AbelianGenG (USp n)`** at `H = uspH n 0 = diag(E₀₀, −E₀₀)` in the blocks of
`GaugeInstances.Jsp`: Hermitian, `H J + J Hᵀ = 0`, nonzero.

DERIVED: `0` the index. -/
theorem abelianGenG_USp (n : ℕ) [NeZero n] : AbelianGenG (MassGap.GaugeInstances.USp n) := by
  have i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  exact abelianGenG_of_herm (G := MassGap.GaugeInstances.USp n) (uspH n i₀) (uspH_herm n i₀)
    (uspH_ne_zero n i₀) fun a =>
      ⟨herm_smul (uspH_herm n i₀) a, symp_smul_eq_zero (uspH_symp n i₀) a⟩

/-- **`AbelianGenG G2`** at `H = GaugeG2.cartanM`: in `lieGen` and nonzero by
`GaugeG2.lieGen_cartanM`, every real multiple in `lieGen` by `lieGen_smul_G2`.

DERIVED: no numeral. -/
theorem abelianGenG_G2 : AbelianGenG MassGap.GaugeG2.G2 := by
  obtain ⟨hgen, h0⟩ := MassGap.GaugeG2.lieGen_cartanM
  have hH : (MassGap.GaugeG2.cartanM).IsHermitian := And.left hgen
  exact abelianGenG_of_herm (G := MassGap.GaugeG2.G2) MassGap.GaugeG2.cartanM hH h0
    fun a => lieGen_smul_G2 hgen a

/-! ## 6. The capstone with `hab` discharged -/

section Capstone

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
  [GaugeSimple G] [GaugeLie G]

variable (G) in
/-- **The conclusion of `ClayG.clayStatementAtG_GS` under all of its inputs except `hab`**, bound as
there: `ClayStatementAtG G W (SymPlaqClassG G)` for every `W`, the observer inputs and transfer
gap, the mixing `ρ` with its clauses, the kernel `Gk`, the composites `Cs` with their data and link
`wC`, the index map `e` with its two clauses, and the cross reading `hX`.

DERIVED: `0` the plane and the step; `4` the dimension. -/
def ClayAtGFromGS : Prop :=
  ∀ (W : ConfFlowG G) {t C₀ : ℝ} (ht : 0 < t)
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r)
    (hNT : FlowConnectedNonzeroG (canonSched G)
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)) 0 r)
    {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1)
    (hg : TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
      (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
      (uniformBoundFG_energy0G (canonSched G) schedOS_canonSched W (symPlaqG_refl G)
        symPlaqG_nonneg (cube_of_classMomentsG (canonSched G) W hU)) 0 hphys 0) ρ₀)
    (ρ : RenormMixG G) (_hRie : ρ.Riemann)
    (_hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixCG ρ k trC b • (ρ.op b).1
        = Ztr k • (symG (plaqFieldG (G := G) ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * (canonSched G).a k ^ 4) atTop (𝓝 (constsG G).cTr))
    (_hCov : TensorCovG (canonSched G) ρ)
    (_hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTieG ρ Mb Zc
        ∧ Tendsto (fun k => zAct (Zc k) epsC id * (canonSched G).a k ^ 4) atTop
          (𝓝 (constsG G).cTop))
    (Gk : ℝ → ℝ) (_hK : TwoPointKernelG (canonSched G) ρ Gk)
    (_hAF : AFCoefficientG (constsG G) Gk)
    (_hNG : NonGaussianTG (canonSched G) ρ) (_hWard : WardTG (canonSched G) ρ)
    (Cs : CompositesG G)
    (wC : TSepG Cs.Ix 0 → (obsXG' W ht hU hphys hNT hρ0 hρ1 hg).base.H)
    (e : Idx4 → Cs.Ix) (_he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (_he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (_hCD : CompDataG Cs) (_hCO : CompOSG (canonSched G) Cs)
    (_hLC : LinkCG (canonSched G) (obsXG' W ht hU hphys hNT hρ0 hρ1 hg) Cs wC)
    (_hX : ∀ (P : TSep 0) (Q : MarginMonoDG G (SymPlaqClassG G) 0 r),
      Tendsto (fun k => mixLatTG (canonSched G) ρ
          (energyMapG (canonSched G) W (SymPlaqClassG G)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (wOfC e wC P) ((obsXG' W ht hU hphys hNT hρ0 hρ1 hg).cvec Q)
          = (mixTG (canonSched G) ρ (energyMapG (canonSched G) W (SymPlaqClassG G)) 0
              P.1 Q.1.1 : ℂ)),
    ClayStatementAtG G W (SymPlaqClassG G)

/-- **`ClayAtGFromGS G` from `AbelianGenG G`**: `ClayG.clayStatementAtG_GS` at `hab`.

DERIVED: no numeral. -/
theorem clayAtGFromGS_of_abelianGenG (hab : AbelianGenG G) : ClayAtGFromGS G := by
  intro W t C₀ ht hU r hphys hNT ρ₀ hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK hAF hNG hWard Cs wC e
    he1 he2 hCD hCO hLC hX
  exact MassGap.ClayG.clayStatementAtG_GS W ht hU hphys hNT hρ0 hρ1 hg ρ hRie hTie hCov hCT Gk hK
    hAF hNG hWard Cs wC e he1 he2 hCD hCO hLC hX hab

end Capstone

/-- **`ClayG.clayStatementAtG_GS` at `SU(N)`, `N ≥ 2`, with `hab` discharged.** DERIVED: `2` the
least `N`. -/
theorem clayStatementAtG_GS_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] :
    ClayAtGFromGS (MassGap.SUN.SU N) :=
  clayAtGFromGS_of_abelianGenG (abelianGenG_SU N)

/-- **`ClayG.clayStatementAtG_GS` at `SO(n)`, `n ≥ 5`, with `hab` discharged.** DERIVED: `5` the
least `n`. -/
theorem clayStatementAtG_GS_SO (n : ℕ) [NeZero n] [Fact (5 ≤ n)] :
    ClayAtGFromGS (MassGap.GaugeInstances.SO n) :=
  clayAtGFromGS_of_abelianGenG (abelianGenG_SO n)

/-- **`ClayG.clayStatementAtG_GS` at `SO(3)` with `hab` discharged.** DERIVED: `3` the dimension. -/
theorem clayStatementAtG_GS_SO3 : ClayAtGFromGS (MassGap.GaugeInstances.SO 3) :=
  clayAtGFromGS_of_abelianGenG abelianGenG_SO3

/-- **`ClayG.clayStatementAtG_GS` at compact `Sp(n)` with `hab` discharged.** DERIVED: no
numeral. -/
theorem clayStatementAtG_GS_USp (n : ℕ) [NeZero n] :
    ClayAtGFromGS (MassGap.GaugeInstances.USp n) :=
  clayAtGFromGS_of_abelianGenG (abelianGenG_USp n)

/-- **`ClayG.clayStatementAtG_GS` at `G₂` with `hab` discharged.** DERIVED: no numeral. -/
theorem clayStatementAtG_GS_G2 : ClayAtGFromGS MassGap.GaugeG2.G2 :=
  clayAtGFromGS_of_abelianGenG abelianGenG_G2

end MassGap.AbelianGen

end

#print axioms MassGap.AbelianGen.re_trace_mul_self_pos
#print axioms MassGap.AbelianGen.herm_smul
#print axioms MassGap.AbelianGen.trace_smul_eq_zero
#print axioms MassGap.AbelianGen.transpose_smul_eq_neg
#print axioms MassGap.AbelianGen.symp_smul_eq_zero
#print axioms MassGap.AbelianGen.suH_herm
#print axioms MassGap.AbelianGen.suH_trace
#print axioms MassGap.AbelianGen.suH_ne_zero
#print axioms MassGap.AbelianGen.soH_herm
#print axioms MassGap.AbelianGen.soH_transpose
#print axioms MassGap.AbelianGen.soH_ne_zero
#print axioms MassGap.AbelianGen.uspB_herm
#print axioms MassGap.AbelianGen.uspH_herm
#print axioms MassGap.AbelianGen.uspH_symp
#print axioms MassGap.AbelianGen.uspH_ne_zero
#print axioms MassGap.AbelianGen.lieGen_smul_G2
#print axioms MassGap.AbelianGen.abelianGenG_of_herm
#print axioms MassGap.AbelianGen.abelianGenG_SU
#print axioms MassGap.AbelianGen.abelianGenG_SO
#print axioms MassGap.AbelianGen.abelianGenG_SO3
#print axioms MassGap.AbelianGen.abelianGenG_USp
#print axioms MassGap.AbelianGen.abelianGenG_G2
#print axioms MassGap.AbelianGen.clayAtGFromGS_of_abelianGenG
#print axioms MassGap.AbelianGen.clayStatementAtG_GS_SU
#print axioms MassGap.AbelianGen.clayStatementAtG_GS_SO
#print axioms MassGap.AbelianGen.clayStatementAtG_GS_SO3
#print axioms MassGap.AbelianGen.clayStatementAtG_GS_USp
#print axioms MassGap.AbelianGen.clayStatementAtG_GS_G2
