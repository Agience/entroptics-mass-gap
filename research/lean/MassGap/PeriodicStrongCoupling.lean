import Mathlib
import MassGap.StrongCouplingGap
import MassGap.WeakCouplingWindow

/-!
# MassGap.PeriodicStrongCoupling — the transfer gap at the periodic state at strong coupling

`StrongCouplingGap.norm_Tq_le_of_orth` contracts the vacuum complement at rate `coreRate 64 β` at
the free-boundary `mixCube` limit state. `StrongCouplingGap.decay_of_orth`, the per-vector decay
behind it, takes reflection invariance, reflection positivity and shift invariance of the state as
hypotheses, which `PeriodicState` supplies at `periodicState`; the one step that reads the `mixCube`
convergence is `GeneralDecay.nu_connected_shift_abs_le_obs`, and inside it the one finite-volume input is
`BoxCube.stateFree_connected_abs_le_of_cubes`: the cluster bound
`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` read on a free box. That cluster bound is
stated for an arbitrary finite carrier `bd`, so it reads on the periodic lattice
`WilsonHypercubic.bd (d := 4) (n := M + 1)` too, with touch degree at most `16 * 4`
(`StrongCoupling.touchDeg_bd_le`), whatever the extent.

This file supplies the periodic reading and passes it to `PeriodicState.periodicState`:

* `torusCube b R` — the periodic plaquettes whose base site sits at forward offset at most `R` from
  `b` on every axis. It holds the halo of every link strictly inside the cube of side `R` at a lift
  of `b` (`linkHalo_subset_torusCube`), is touch-connected from `((e, e), b)`
  (`torus_reach_from_base`), and has at most `16 (R + 1)⁴` plaquettes (`card_torusCube_le`).
* `torus_not_mem_ball` — two base plaquettes whose sites differ by `D > k` along `τ`, on a circle of
  `M + 1 ≥ 2D` sites, are more than `k` touch-steps apart.
* `torusState_connected_abs_le_of_cubes` — the periodic counterpart of
  `BoxCube.stateFree_connected_abs_le_of_cubes`, with the same right side.
* `periodic_connected_shift_abs_le_obs` — the counterpart of
  `GeneralDecay.nu_connected_shift_abs_le_obs` at `periodicState hN β`: the torus bound holds for all
  large extents, and `PeriodicReduce.tendsto_torusConn` carries it along `periodicUltra hN β`.
* `decay_of_orth_of_conn` — `StrongCouplingGap.decay_of_orth` with the pairing bound as a
  hypothesis on the state rather than derived from `mixCube` convergence.

`periodic_gapAt_strong_coupling` is the result: there is `β₀ > 0` such that at every `0 < β < β₀`,
`TransferGap.GapAt (periodicGaugeInvData τ p hN β) (coreRate 64 β)` with `0 < coreRate 64 β < 1`.
`periodic_clayGapAt_strong_coupling` and `periodic_torusLagClear_strong_coupling` restate it through
`GapStep.periodic_clayGapAt_of_gapAt` and `WeakCouplingWindow.torusLagClear_of_gapAt`.
-/

namespace MassGap.PeriodicStrongCoupling

open MassGap

/-! ## 1. Residues -/

section Residue

/-- `finMod M d` has value `d` when `0 ≤ d < M + 1`.

DERIVED: `0` is the lower end of the residue range; the `1` in `M + 1` is `InfiniteLattice.finMod`'s
successor writing the extent. -/
theorem val_finMod_of_lt (M : ℕ) (d : ℤ) (h0 : 0 ≤ d) (h1 : d < (M : ℤ) + 1) :
    (((InfiniteLattice.finMod M d : Fin (M + 1)) : ℕ) : ℤ) = d := by
  show (((d % ((M : ℤ) + 1)).toNat : ℕ) : ℤ) = d
  rw [Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

#print axioms val_finMod_of_lt

end Residue

/-! ## 2. Cubes of plaquettes on the periodic lattice -/

section TorusCube

variable {n : ℕ} [NeZero n]

/-- A periodic site lies in the cube of side `R` based at `b`: its forward offset `s i - b i`, read in
`[0, n)`, is at most `R` on every axis.

DERIVED: the `4` is the spacetime dimension indexing the axes. -/
def TInCube (b : WilsonHypercubic.Site 4 n) (R : ℕ) (s : WilsonHypercubic.Site 4 n) : Prop :=
  ∀ i : Fin 4, ((s i - b i : Fin n) : ℕ) ≤ R

open scoped Classical in
/-- The periodic plaquettes based in the cube of side `R` at `b`, every plane included.

DERIVED: the `4` is the spacetime dimension. -/
noncomputable def torusCube (b : WilsonHypercubic.Site 4 n) (R : ℕ) :
    Finset (WilsonHypercubic.Plaq 4 n) :=
  Finset.univ.filter (fun q => TInCube b R q.2)

open scoped Classical in
/-- Membership in `torusCube`, unfolded.

DERIVED: the `4` is the spacetime dimension. -/
theorem mem_torusCube {b : WilsonHypercubic.Site 4 n} {R : ℕ} {q : WilsonHypercubic.Plaq 4 n} :
    q ∈ torusCube b R ↔ TInCube b R q.2 := by
  unfold torusCube; simp

#print axioms mem_torusCube

/-- Every plaquette based at `b` lies in `torusCube b R`: its offset is `0`.

DERIVED: the `4` is the spacetime dimension. -/
theorem mem_torusCube_base (b : WilsonHypercubic.Site 4 n) (R : ℕ) (c d : Fin 4) :
    ((c, d), b) ∈ torusCube b R :=
  mem_torusCube.mpr (fun i => by
    show ((b i - b i : Fin n) : ℕ) ≤ R
    simp)

#print axioms mem_torusCube_base

/-- `shift μ (unshift μ x) = x` on the periodic lattice; `StrongCoupling.unshift_shift` is the other
order.

DERIVED: the `4` is the spacetime dimension. -/
theorem shift_unshift (μ : Fin 4) (x : WilsonHypercubic.Site 4 n) :
    WilsonHypercubic.shift μ (StrongCoupling.unshift μ x) = x := by
  unfold StrongCoupling.unshift WilsonHypercubic.shift
  rw [Function.update_self, Function.update_idem]
  simp

#print axioms shift_unshift

/-- **Periodic plaquettes at one site are touch-connected** inside any `V` holding every plaquette
at that site: `((a, b), s)` shares `(a, s)` with `((a, c), s)`, which shares `(c, s)` with
`((c, d), s)`. No plane is excluded, the diagonal ones included.

DERIVED: the `4` is the spacetime dimension. -/
theorem torus_reach_same_site {V : Finset (WilsonHypercubic.Plaq 4 n)}
    (s : WilsonHypercubic.Site 4 n) (hV : ∀ a b : Fin 4, ((a, b), s) ∈ V) (a b c d : Fin 4) :
    StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) V ((a, b), s) ((c, d), s) := by
  have h1 : StrongCoupling.Touch (WilsonHypercubic.bd (d := 4) (n := n)) ((a, b), s) ((a, c), s) :=
    ⟨(a, s), by simp [StrongCoupling.linkSupp, WilsonHypercubic.bd],
      by simp [StrongCoupling.linkSupp, WilsonHypercubic.bd]⟩
  have h2 : StrongCoupling.Touch (WilsonHypercubic.bd (d := 4) (n := n)) ((a, c), s) ((c, d), s) :=
    ⟨(c, s), by simp [StrongCoupling.linkSupp, WilsonHypercubic.bd],
      by simp [StrongCoupling.linkSupp, WilsonHypercubic.bd]⟩
  have r1 : StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) V
      ((a, b), s) ((a, c), s) := Relation.ReflTransGen.single ⟨hV a b, hV a c, h1⟩
  have r2 : StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) V
      ((a, c), s) ((c, d), s) := Relation.ReflTransGen.single ⟨hV a c, hV c d, h2⟩
  exact Relation.ReflTransGen.trans r1 r2

#print axioms torus_reach_same_site

/-- The summed forward offset of `s` from `b`, the induction measure for connectivity.

DERIVED: the `4` is the spacetime dimension indexing the axes. -/
def tDepth (b s : WilsonHypercubic.Site 4 n) : ℕ := ∑ i : Fin 4, ((s i - b i : Fin n) : ℕ)

/-- **Every plaquette of `torusCube b R` is reachable from `((e, e), b)` inside it.** By induction on
the summed offset of its site: at offset zero the site is `b` and `torus_reach_same_site` applies;
otherwise some axis `i` has positive offset, one periodic step back along `i` stays in the cube with
offset one less, and the plaquette `((i, i), unshift i s)` shares `(i, s)` with `((i, i), s)`.

DERIVED: the `4` is the spacetime dimension. -/
theorem torus_reach_from_base (b : WilsonHypercubic.Site 4 n) (R : ℕ) (e : Fin 4) :
    ∀ D : ℕ, ∀ q : WilsonHypercubic.Plaq 4 n, q ∈ torusCube b R → tDepth b q.2 = D →
      StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) (torusCube b R)
        ((e, e), b) q := by
  intro D
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨⟨c, d⟩, s⟩ := q
    have hd' : ∑ i : Fin 4, ((s i - b i : Fin n) : ℕ) = 0 := hd
    have hs : s = b := by
      funext i
      have hi : ((s i - b i : Fin n) : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff.mp hd') i (Finset.mem_univ i)
      have h0 : s i - b i = 0 := Fin.ext (hi.trans (Fin.val_zero n).symm)
      exact sub_eq_zero.mp h0
    rw [hs]
    exact torus_reach_same_site b (fun a' b' => mem_torusCube_base b R a' b') e e c d
  | succ D ih =>
    intro q hq hd
    obtain ⟨⟨c, d⟩, s⟩ := q
    have hin : TInCube b R s := mem_torusCube.mp hq
    have hd' : ∑ j : Fin 4, ((s j - b j : Fin n) : ℕ) = D + 1 := hd
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, 0 < ((s i - b i : Fin n) : ℕ) := by
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ j : Fin 4, ((s j - b j : Fin n) : ℕ) = 0 :=
        Finset.sum_eq_zero (fun j _ => by have := hcon j; omega)
      omega
    obtain ⟨s', hs'⟩ : ∃ s' : WilsonHypercubic.Site 4 n, s' = StrongCoupling.unshift i s :=
      ⟨_, rfl⟩
    have hkey : ((s' i - b i : Fin n) : ℕ) + 1 = ((s i - b i : Fin n) : ℕ) := by
      have e1 : s' i - b i + 1 = s i - b i := by
        rw [hs']
        unfold StrongCoupling.unshift
        rw [Function.update_self, sub_right_comm, sub_add_cancel]
      rcases StrongCoupling.val_add_one_cases (s' i - b i) with h | ⟨h, _⟩
      · rw [e1] at h; omega
      · rw [e1] at h; omega
    have hj : ∀ j : Fin 4, j ≠ i → s' j = s j := fun j hne => by
      rw [hs']
      exact Function.update_of_ne hne _ _
    have hin' : TInCube b R s' := fun j => by
      by_cases hji : j = i
      · rw [hji]
        have := hin i
        omega
      · rw [hj j hji]
        exact hin j
    have hdepth : tDepth b s' = D := by
      show ∑ j : Fin 4, ((s' j - b j : Fin n) : ℕ) = D
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hd' ⊢
      have hrest : ∑ j ∈ Finset.univ.erase i, ((s' j - b j : Fin n) : ℕ)
          = ∑ j ∈ Finset.univ.erase i, ((s j - b j : Fin n) : ℕ) :=
        Finset.sum_congr rfl (fun j hj' => by rw [hj j (Finset.ne_of_mem_erase hj')])
      rw [hrest]
      omega
    have hr : ((i, i), s') ∈ torusCube b R := mem_torusCube.mpr hin'
    have ht : ((i, i), s) ∈ torusCube b R := mem_torusCube.mpr hin
    have h1 := ih ((i, i), s') hr hdepth
    have hsh : WilsonHypercubic.shift i s' = s := by
      rw [hs']
      exact shift_unshift i s
    have htouch : StrongCoupling.Touch (WilsonHypercubic.bd (d := 4) (n := n))
        ((i, i), s') ((i, i), s) := by
      refine ⟨(i, s), ?_, by simp [StrongCoupling.linkSupp, WilsonHypercubic.bd]⟩
      have h2 : (i, WilsonHypercubic.shift i s')
          ∈ StrongCoupling.linkSupp (WilsonHypercubic.bd (d := 4) (n := n)) ((i, i), s') := by
        simp [StrongCoupling.linkSupp, WilsonHypercubic.bd]
      rwa [hsh] at h2
    have h2 : StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) (torusCube b R)
        ((i, i), s') ((i, i), s) := Relation.ReflTransGen.single ⟨hr, ht, htouch⟩
    have h3 : StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := n)) (torusCube b R)
        ((i, i), s) ((c, d), s) :=
      torus_reach_same_site s (fun a' b' => mem_torusCube.mpr hin) i i c d
    exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans h2 h3)

#print axioms torus_reach_from_base

/-- **`torusCube b R` has at most `16 (R + 1)⁴` plaquettes**, whatever the extent: a plaquette is
determined by its plane and its offsets from `b`.

DERIVED: `16` is the number of ordered direction pairs `4 · 4`; `R + 1` offsets per axis, `1` for
offset zero; the exponent `4` is the spacetime dimension. -/
theorem card_torusCube_le (b : WilsonHypercubic.Site 4 n) (R : ℕ) :
    (torusCube b R).card ≤ 16 * (R + 1) ^ 4 := by
  classical
  let T : Finset ((Fin 4 × Fin 4) × (Fin 4 → ℕ)) :=
    (Finset.univ : Finset (Fin 4 × Fin 4)) ×ˢ
      Fintype.piFinset (fun _ : Fin 4 => Finset.range (R + 1))
  have hmaps : ∀ q ∈ torusCube b R,
      ((q : WilsonHypercubic.Plaq 4 n).1, fun i => ((q.2 i - b i : Fin n) : ℕ)) ∈ T := by
    intro q hq
    have hin := mem_torusCube.mp hq
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun i => ?_)⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hin i))
  have hinj : Set.InjOn
      (fun q : WilsonHypercubic.Plaq 4 n => (q.1, fun i => ((q.2 i - b i : Fin n) : ℕ)))
      (torusCube b R : Set (WilsonHypercubic.Plaq 4 n)) := by
    intro q _ q' _ h
    have h1 : q.1 = q'.1 := by
      have h' := congrArg Prod.fst h
      exact h'
    have h2 : ∀ i : Fin 4, q.2 i = q'.2 i := fun i => by
      have hi : ((q.2 i - b i : Fin n) : ℕ) = ((q'.2 i - b i : Fin n) : ℕ) :=
        congrFun (congrArg Prod.snd h) i
      exact sub_left_inj.mp (Fin.ext hi)
    exact Prod.ext h1 (funext h2)
  have hle : (torusCube b R).card ≤ T.card := Finset.card_le_card_of_injOn
    (fun q : WilsonHypercubic.Plaq 4 n => (q.1, fun i => ((q.2 i - b i : Fin n) : ℕ))) hmaps hinj
  have hT : T.card = 16 * (R + 1) ^ 4 := by
    simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_piFinset, Finset.card_range, Finset.prod_const]
  omega

#print axioms card_torusCube_le

/-- **`Touch` moves the circle distance of a `τ`-coordinate from `c` by at most one.** The periodic
form of `StrongCoupling.axisLvl_lipschitz`, measured from `c` instead of from `0`: the shared link
sits within one step of both plaquettes' sites (`StrongCoupling.link_site_coord`).

DERIVED: the `1` is one lattice step; the `4` is the spacetime dimension. -/
theorem circDist_sub_lipschitz (τ : Fin 4) (c : Fin n) (p q : WilsonHypercubic.Plaq 4 n)
    (h : StrongCoupling.Touch (WilsonHypercubic.bd (d := 4) (n := n)) p q) :
    StrongCoupling.circDist (q.2 τ - c) ≤ StrongCoupling.circDist (p.2 τ - c) + 1 := by
  obtain ⟨⟨a, b⟩, x⟩ := p
  obtain ⟨⟨c', e⟩, y⟩ := q
  obtain ⟨⟨ld, ls⟩, hp, hq⟩ := h
  have hP := StrongCoupling.link_site_coord τ a b x ld ls hp
  have hQ := StrongCoupling.link_site_coord τ c' e y ld ls hq
  show StrongCoupling.circDist (y τ - c) ≤ StrongCoupling.circDist (x τ - c) + 1
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ
  · rw [← hP, ← hQ]; omega
  · have h1 : StrongCoupling.circDist (y τ - c) ≤ StrongCoupling.circDist (y τ - c + 1) + 1 :=
      StrongCoupling.circDist_le_succ (y τ - c)
    have e1 : y τ - c + 1 = x τ - c := by rw [sub_add_eq_add_sub, ← hQ, hP]
    rw [e1] at h1
    exact h1
  · have h1 : StrongCoupling.circDist (x τ - c + 1) ≤ StrongCoupling.circDist (x τ - c) + 1 :=
      StrongCoupling.circDist_succ_le (x τ - c)
    have e1 : x τ - c + 1 = y τ - c := by rw [sub_add_eq_add_sub, ← hP, hQ]
    rw [e1] at h1
    exact h1
  · have hxy : x τ = y τ := StrongCoupling.fin_add_one_inj (by rw [← hP, ← hQ])
    rw [hxy]; omega

#print axioms circDist_sub_lipschitz

end TorusCube

/-! ## 3. Cubes read through the reduction modulo the extent -/

section Reduce

/-- **The halo of links strictly inside a cube lies in the periodic cube.** For `S` with every link
coordinate in `[x₀ i + 1, x₀ i + R]` and `R < M + 1`, every periodic plaquette using a link of
`S.image (linkMod M)` is based at forward offset at most `R` from `siteMod M x₀`: its site is the
link's site or one step below it on each axis (`StrongCoupling.link_site_coord`).

DERIVED: the `1` is the one lattice step between a plaquette's base and its farthest link, and the
successor in `M + 1`; the `4` is the spacetime dimension. -/
theorem linkHalo_subset_torusCube (M : ℕ) (x₀ : InfiniteLattice.ISite) (R : ℕ)
    (hR : (R : ℤ) < (M : ℤ) + 1) (S : Finset InfiniteLattice.ILink)
    (hS : ∀ l ∈ S, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R) :
    StrongCoupling.linkHalo (WilsonHypercubic.bd (d := 4) (n := M + 1))
        (S.image (InfiniteLattice.linkMod M))
      ⊆ torusCube (InfiniteLattice.siteMod M x₀) R := by
  intro q hq
  obtain ⟨⟨a, b⟩, s⟩ := q
  obtain ⟨t, ht, htS⟩ := StrongCoupling.mem_linkHalo.mp hq
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp htS
  refine mem_torusCube.mpr (fun i => ?_)
  show ((s i - InfiniteLattice.finMod M (x₀ i) : Fin (M + 1)) : ℕ) ≤ R
  have hc := StrongCoupling.link_site_coord i a b s (InfiniteLattice.linkMod M l).1
    (InfiniteLattice.linkMod M l).2 ht
  have hb := hS l hl i
  rcases hc with h | h
  · have hs : s i = InfiniteLattice.finMod M (l.2 i) := h.symm
    rw [hs, ← PeriodicState.finMod_sub]
    have hv := val_finMod_of_lt M (l.2 i - x₀ i) (by omega) (by omega)
    omega
  · have hs : s i = InfiniteLattice.finMod M (l.2 i - 1) := by
      rw [PeriodicState.finMod_sub, PeriodicState.finMod_one]
      have h' : InfiniteLattice.finMod M (l.2 i) = s i + 1 := h
      rw [h', add_sub_cancel_right]
    rw [hs, ← PeriodicState.finMod_sub]
    have hv := val_finMod_of_lt M (l.2 i - 1 - x₀ i) (by omega) (by omega)
    omega

#print axioms linkHalo_subset_torusCube

/-- **Two sites `D > k` apart along `τ` on a circle of `M + 1 ≥ 2D` sites put their plaquettes more
than `k` touch-steps apart.** The level `circDist (q.2 τ − finMod (x₀ τ))` is `0` at the first base
plaquette, rises by at most one per touch (`circDist_sub_lipschitz`), and is `D` at the second, so
`StrongCoupling.lvl_le_of_mem_ball` excludes it from the `k`-ball.

DERIVED: the `2` is the two ways round the circle, the shorter of which is `D` exactly when
`2D ≤ M + 1`; the `1` is the successor writing the extent; the `4` is the spacetime dimension. -/
theorem torus_not_mem_ball (M : ℕ) (x₀ y₀ : InfiniteLattice.ISite) (τ e c d : Fin 4) (k : ℕ)
    (hk : (k : ℤ) < y₀ τ - x₀ τ) (hM : 2 * (y₀ τ - x₀ τ) ≤ (M : ℤ) + 1) :
    ((c, d), InfiniteLattice.siteMod M y₀)
      ∉ StrongCoupling.ball (WilsonHypercubic.bd (d := 4) (n := M + 1))
          ((e, e), InfiniteLattice.siteMod M x₀) k := by
  intro hmem
  have hlvl := StrongCoupling.lvl_le_of_mem_ball (WilsonHypercubic.bd (d := 4) (n := M + 1))
    ((e, e), InfiniteLattice.siteMod M x₀)
    (fun q : WilsonHypercubic.Plaq 4 (M + 1) =>
      StrongCoupling.circDist (q.2 τ - InfiniteLattice.siteMod M x₀ τ))
    ((congrArg StrongCoupling.circDist (sub_self (InfiniteLattice.siteMod M x₀ τ))).trans
      StrongCoupling.circDist_zero)
    (fun p q ht => circDist_sub_lipschitz τ _ p q ht) k _ hmem
  have h2 : StrongCoupling.circDist
      (InfiniteLattice.siteMod M y₀ τ - InfiniteLattice.siteMod M x₀ τ) ≤ k := hlvl
  have hsub : InfiniteLattice.siteMod M y₀ τ - InfiniteLattice.siteMod M x₀ τ
      = InfiniteLattice.finMod M (y₀ τ - x₀ τ) :=
    (PeriodicState.finMod_sub M (y₀ τ) (x₀ τ)).symm
  rw [hsub] at h2
  have hv := val_finMod_of_lt M (y₀ τ - x₀ τ) (by omega) (by omega)
  have hlt : k < StrongCoupling.circDist (InfiniteLattice.finMod M (y₀ τ - x₀ τ)) := by
    unfold StrongCoupling.circDist
    exact lt_min (by omega) (by omega)
  omega

#print axioms torus_not_mem_ball

variable {N : ℕ}

/-- An observable of `ℤ⁴` local on `S`, read on the periodic lattice of extent `M + 1`, is local on
the reduced links `S.image (linkMod M)`: `pullback M` is continuous and reads `W` only at `linkMod M l`.

DERIVED: no numeral in the statement; `M` is the caller's. -/
theorem localOnLinks_torusObs (M : ℕ) (F : C(GibbsSpec.IConf (SUN.SU N), ℝ))
    {S : Finset InfiniteLattice.ILink}
    (hF : InfiniteLattice.IsLocalOn S (F : GibbsSpec.IConf (SUN.SU N) → ℝ)) :
    StrongCoupling.LocalOnLinks (Nc := N) (S.image (InfiniteLattice.linkMod M))
      (PeriodicState.torusObs M F) := by
  refine StrongCoupling.localOnLinks_of_continuous
    (F.continuous.comp (InfiniteLattice.continuous_pullback (m := M))) (fun U V hUV => ?_)
  exact hF (InfiniteLattice.pullback M U) (InfiniteLattice.pullback M V)
    (fun l hl => hUV (InfiniteLattice.linkMod M l) (Finset.mem_image_of_mem _ hl))

#print axioms localOnLinks_torusObs

/-- A continuous observable read on the periodic lattice is bounded by its sup norm.

DERIVED: the `4` is the spacetime dimension; the `1` is the successor writing the extent. -/
theorem abs_torusObs_le (M : ℕ) (F : C(GibbsSpec.IConf (SUN.SU N), ℝ))
    (W : WilsonHypercubic.Link 4 (M + 1) → SUN.SU N) :
    |PeriodicState.torusObs M F W| ≤ ‖F‖ := by
  show |F (InfiniteLattice.pullback M W)| ≤ ‖F‖
  simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (InfiniteLattice.pullback M W)

#print axioms abs_torusObs_le

/-- **The periodic cluster bound for two local observables, anchored on cubes.** `N ≠ 0`, `f` local
on `Sf` and `g` on `Sg`, the links of `Sf` strictly inside the cube of side `R` at `x₀` and those of
`Sg` strictly inside the one at `y₀`, the bases more than `k` apart along `τ` with
`32 (R + 1)⁴ ≤ k + 2`, and the extent `M + 1` at least twice that separation. Then at every `0 ≤ β`
with `coreRate 64 β < 1`, in the periodic Wilson state of extent `M + 1`,

    |⟨f g⟩ − ⟨f⟩⟨g⟩|  ≤  coreConstG (2 ‖f‖ ‖g‖) 64 β U · coreRate 64 β ^ (k + 2 − U),
    U = 32 (R + 1)⁴,

the right side of `BoxCube.stateFree_connected_abs_le_of_cubes`, independent of `M`.
`StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` at the periodic carrier with anchors
`torusCube (siteMod M x₀) R` and `torusCube (siteMod M y₀) R`.

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`), and the `4` in `Fin 4` and in `(d := 4)` is that spacetime dimension; `32 = 2 · 16` is two cubes of at most `16 (R + 1)⁴` plaquettes (`card_torusCube_le`), with the
exponent `4` the dimension; the `2` in `2 ‖f‖ ‖g‖` is `pairTermObs_abs_le`'s two products; the `2`
in `k + 2` is the two base plaquettes; the `2` in `2 * (y₀ τ − x₀ τ)` is the two ways round the
circle; `0` is the excluded rank in `hN` and the sign of `β`; `1` is the geometric threshold, the
strict-inside margin, the successor writing the extent, and in `R + 1` the offset zero. -/
theorem torusState_connected_abs_le_of_cubes (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (M : ℕ)
    (f g : C(GibbsSpec.IConf (SUN.SU N), ℝ)) {Sf Sg : Finset InfiniteLattice.ILink}
    (hfl : InfiniteLattice.IsLocalOn Sf (f : GibbsSpec.IConf (SUN.SU N) → ℝ))
    (hgl : InfiniteLattice.IsLocalOn Sg (g : GibbsSpec.IConf (SUN.SU N) → ℝ))
    {x₀ y₀ : InfiniteLattice.ISite} {R : ℕ}
    (hcf : ∀ l ∈ Sf, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R)
    (hcg : ∀ l ∈ Sg, ∀ i : Fin 4, y₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ y₀ i + R)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1) (τ : Fin 4) (k : ℕ)
    (hk : (k : ℤ) < y₀ τ - x₀ τ) (hM : 2 * (y₀ τ - x₀ τ) ≤ (M : ℤ) + 1)
    (hu : 32 * (R + 1) ^ 4 ≤ k + 2) :
    |PeriodicState.torusState hN M β (f * g)
        - PeriodicState.torusState hN M β f * PeriodicState.torusState hN M β g|
      ≤ StrongCoupling.coreConstG (2 * (‖f‖ * ‖g‖)) (16 * 4) β (32 * (R + 1) ^ 4)
        * StrongCoupling.coreRate (16 * 4) β ^ (k + 2 - 32 * (R + 1) ^ 4) := by
  classical
  have hpow : R + 1 ≤ (R + 1) ^ 4 := Nat.le_self_pow (by norm_num) (R + 1)
  have hkR : R ≤ k := by omega
  have hRM : (R : ℤ) < (M : ℤ) + 1 := by omega
  -- the periodic state's connected correlation is the carrier's
  have hconv : PeriodicState.torusState hN M β (f * g)
        - PeriodicState.torusState hN M β f * PeriodicState.torusState hN M β g
      = StrongCoupling.wilsonCorrConnObs (Nc := N) (WilsonHypercubic.bd (d := 4) (n := M + 1))
          (PeriodicState.torusObs M f) (PeriodicState.torusObs M g) β := rfl
  rw [hconv]
  -- the reduced supports are disjoint
  have hab : Disjoint (Sf.image (InfiniteLattice.linkMod M))
      (Sg.image (InfiniteLattice.linkMod M)) := by
    rw [Finset.disjoint_left]
    intro t htf htg
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp htf
    obtain ⟨l', hl', he⟩ := Finset.mem_image.mp htg
    have hτ : InfiniteLattice.finMod M (l'.2 τ) = InfiniteLattice.finMod M (l.2 τ) :=
      congrFun (congrArg Prod.snd he) τ
    have h0 : InfiniteLattice.finMod M (l'.2 τ - l.2 τ) = 0 := by
      rw [PeriodicState.finMod_sub, hτ, sub_self]
    have hv0 : ((InfiniteLattice.finMod M (l'.2 τ - l.2 τ) : Fin (M + 1)) : ℕ) = 0 := by
      simp [h0]
    have hb := hcf l hl τ
    have hb' := hcg l' hl' τ
    have hv := val_finMod_of_lt M (l'.2 τ - l.2 τ) (by omega) (by omega)
    omega
  -- anchors
  have ha : ((τ, τ), InfiniteLattice.siteMod M x₀) ∈ torusCube (InfiniteLattice.siteMod M x₀) R :=
    mem_torusCube_base _ R τ τ
  have hb : ((τ, τ), InfiniteLattice.siteMod M y₀) ∈ torusCube (InfiniteLattice.siteMod M y₀) R :=
    mem_torusCube_base _ R τ τ
  have hAo := linkHalo_subset_torusCube M x₀ R hRM Sf hcf
  have hBo := linkHalo_subset_torusCube M y₀ R hRM Sg hcg
  have hconnA : ∀ q ∈ torusCube (InfiniteLattice.siteMod M x₀) R,
      StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := M + 1))
        (torusCube (InfiniteLattice.siteMod M x₀) R) ((τ, τ), InfiniteLattice.siteMod M x₀) q :=
    fun q hq => torus_reach_from_base _ R τ _ q hq rfl
  have hconnB : ∀ q ∈ torusCube (InfiniteLattice.siteMod M y₀) R,
      StrongCoupling.Reach (WilsonHypercubic.bd (d := 4) (n := M + 1))
        (torusCube (InfiniteLattice.siteMod M y₀) R) ((τ, τ), InfiniteLattice.siteMod M y₀) q :=
    fun q hq => torus_reach_from_base _ R τ _ q hq rfl
  have hkb := torus_not_mem_ball M x₀ y₀ τ τ τ τ k hk hM
  have hcard : (torusCube (InfiniteLattice.siteMod M x₀) R
      ∪ torusCube (InfiniteLattice.siteMod M y₀) R).card ≤ 32 * (R + 1) ^ 4 := by
    have h1 := card_torusCube_le (InfiniteLattice.siteMod M x₀) R
    have h2 := card_torusCube_le (InfiniteLattice.siteMod M y₀) R
    have h3 := Finset.card_union_le (torusCube (InfiniteLattice.siteMod M x₀) R)
      (torusCube (InfiniteLattice.siteMod M y₀) R)
    omega
  have hbase := StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball hN
    (WilsonHypercubic.bd (d := 4) (n := M + 1)) hab
    (localOnLinks_torusObs M f hfl) (localOnLinks_torusObs M g hgl)
    (abs_torusObs_le M f) (abs_torusObs_le M g) hAo hBo ha hb hconnA hconnB hβ (16 * 4)
    (StrongCoupling.touchDeg_bd_le (dim := 4) (n := M + 1)) hr k hkb (le_trans hcard hu)
  refine le_trans hbase ?_
  have hC : (0 : ℝ) ≤ 2 * (‖f‖ * ‖g‖) := by positivity
  have hr0 : 0 ≤ StrongCoupling.coreRate (16 * 4) β := StrongCoupling.coreRate_nonneg _ hβ
  have hCC := BoxCube.coreConstG_le_of_le hC hβ hr hcard
  have hpow' := StrongCoupling.pow_le_pow_of_le_one_asm hr0 hr.le
    (Nat.sub_le_sub_left hcard (k + 2))
  have hCK : (0 : ℝ) ≤ StrongCoupling.coreConstG (2 * (‖f‖ * ‖g‖)) (16 * 4) β
      (32 * (R + 1) ^ 4) := by
    unfold StrongCoupling.coreConstG StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - StrongCoupling.coreRate (16 * 4) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)) this.le
  exact mul_le_mul hCC hpow' (pow_nonneg hr0 _) hCK

#print axioms torusState_connected_abs_le_of_cubes

end Reduce

/-! ## 4. The pairing bound at the periodic state -/

section Periodic

variable {N : ℕ}

/-- **The connected reflected-shifted pairing of a general local observable decays in
`periodicState hN β`.** For `x` continuous and local on a finite `S ⊆ posHalf τ p` there is a `U`
depending on `S` alone such that for every `m` with `U ≤ m + 2`, at `0 ≤ β` with
`coreRate 64 β < 1`,

    |ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)|  ≤  coreConstG (2 ‖x‖²) 64 β U · coreRate 64 β ^ (m + 2 − U),

`ν = periodicState hN β`: the conclusion of `GeneralDecay.nu_connected_shift_abs_le_obs` with the
periodic state in place of the `mixCube` limit. The cubes are those of that proof
(`GeneralDecay.exists_cube_posHalf`); `torusState_connected_abs_le_of_cubes` bounds
`PeriodicReduce.torusConn τ p hN β j x m` once `j ≥ m + R`, and `PeriodicReduce.tendsto_torusConn`
with `PeriodicState.periodicUltra_le` carries the bound to the limit.

DERIVED: `16 * 4` is the periodic touch-degree bound; the `4` in `Fin 4` is the spacetime dimension;
`2` in `2 * p` is the reflection plane's
doubling and in `2 ‖x‖²` the two products of `pairTermObs_abs_le`; the `2` in `m + 2` is the two
base plaquettes; `0` is the sign hypotheses and the excluded rank; `1` is the geometric
threshold. -/
theorem periodic_connected_shift_abs_le_obs (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1)
    (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) {S : Finset InfiniteLattice.ILink}
    (hS : (S : Set InfiniteLattice.ILink) ⊆ HalfSpaceAlgebra.posHalf τ p)
    (hx : InfiniteLattice.IsLocalOn S (x : GibbsSpec.IConf (SUN.SU N) → ℝ)) :
    ∃ U : ℕ, ∀ m : ℕ, U ≤ m + 2 →
      |PeriodicState.periodicState hN β (LatticeReflection.ireflObs τ (2 * p) x
            * (⇑(ReflectionShift.ishiftObsL τ))^[m] x)
        - PeriodicState.periodicState hN β (LatticeReflection.ireflObs τ (2 * p) x)
          * PeriodicState.periodicState hN β ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)|
        ≤ StrongCoupling.coreConstG (2 * (‖x‖ * ‖x‖)) (16 * 4) β U
          * StrongCoupling.coreRate (16 * 4) β ^ (m + 2 - U) := by
  classical
  obtain ⟨x₀, R, hx₀τ, hR, hin⟩ := GeneralDecay.exists_cube_posHalf τ p S hS
  refine ⟨32 * (R + 1 + 1) ^ 4, fun m hm => ?_⟩
  set Sf := S.image (LatticeReflection.ireflLink τ (2 * p)) with hSfdef
  set Sg := S.image (InfiniteShift.ishiftLink τ)^[m] with hSgdef
  let xr : GibbsSpec.ISite := Function.update x₀ τ (p - 1 - R)
  let yr : GibbsSpec.ISite := Function.update x₀ τ (p - 1 + m)
  have hpow : 1 ≤ (R + 1 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hcf : ∀ l ∈ Sf, ∀ i : Fin 4, xr i + 1 ≤ l.2 i ∧ l.2 i ≤ xr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (GeneralDecay.ireflLink_coord τ (2 * p) l₀).2 i
    have hb := hin l₀ hl₀ i
    have hbτ := hin l₀ hl₀ τ
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [xr, Function.update_self, if_true]
      split <;> push_cast <;> constructor <;> omega
    · simp only [xr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hcg : ∀ l ∈ Sg, ∀ i : Fin 4, yr i + 1 ≤ l.2 i ∧ l.2 i ≤ yr i + (R + 1 : ℕ) := by
    intro l hl i
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    have hc := (GeneralDecay.iterate_ishiftLink_coord τ m l₀).2 i
    have hb := hin l₀ hl₀ i
    rw [hc]
    by_cases hi : i = τ
    · subst hi
      simp only [yr, Function.update_self, if_true]
      push_cast; constructor <;> omega
    · simp only [yr, Function.update_of_ne hi, hi, if_false]
      push_cast; constructor <;> omega
  have hfl : InfiniteLattice.IsLocalOn Sf
      (LatticeReflection.ireflObs τ (2 * p) x : GibbsSpec.IConf (SUN.SU N) → ℝ) :=
    HalfSpaceAlgebra.isLocalOn_ireflObs τ (2 * p) hx
  have hgl := GeneralDecay.isLocalOn_iterate_ishiftObsL τ x hx m
  have hxy : yr τ - xr τ = (m : ℤ) + R := by
    simp only [xr, yr, Function.update_self]; omega
  have hk : ((m : ℕ) : ℤ) < yr τ - xr τ := by rw [hxy]; omega
  have hr0 : 0 ≤ StrongCoupling.coreRate (16 * 4) β := StrongCoupling.coreRate_nonneg _ hβ
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      |PeriodicReduce.torusConn τ p hN β j x m|
        ≤ StrongCoupling.coreConstG (2 * (‖x‖ * ‖x‖)) (16 * 4) β (32 * (R + 1 + 1) ^ 4)
          * StrongCoupling.coreRate (16 * 4) β ^ (m + 2 - 32 * (R + 1 + 1) ^ 4) := by
    refine Filter.eventually_atTop.mpr ⟨m + R, fun j hj => ?_⟩
    have hM : 2 * (yr τ - xr τ) ≤ ((2 * j + 1 : ℕ) : ℤ) + 1 := by
      rw [hxy]; push_cast; omega
    have hbox := torusState_connected_abs_le_of_cubes hN hβ (2 * j + 1)
      (LatticeReflection.ireflObs τ (2 * p) x) ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)
      hfl hgl hcf hcg hr τ m hk hM hm
    refine le_trans hbox (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 _))
    refine GeneralDecay.coreConstG_mono_C ?_ hr _
    have hf := WilsonTransferReduction.norm_ireflObs_le τ (2 * p) x
    have hg := GeneralDecay.norm_iterate_ishiftObsL_le τ x m
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
    have := mul_le_mul hf hg (norm_nonneg _) hx0
    linarith
  haveI : ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (PeriodicState.periodicUltra hN β).neBot'
  exact le_of_tendsto (PeriodicReduce.tendsto_torusConn τ p hN β x m).abs
    (hev.filter_mono (PeriodicState.periodicUltra_le hN β))

#print axioms periodic_connected_shift_abs_le_obs

end Periodic

/-! ## 5. From the pairing bound to the contraction -/

section Contraction

open MassGap.Transfer MassGap.GNSHilbert

variable {N : ℕ}

/-- **Every vector orthogonal to the vacuum decays at rate `coreRate 64 β`, for any state carrying the
pairing bound.** `StrongCouplingGap.decay_of_orth` with its one state-specific input,
`GeneralDecay.nu_connected_shift_abs_le_obs`, replaced by the hypothesis `hconn` of the same form; the
proof is that one's.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `2` is
the reflection plane's doubling in `2 * p`, the doubling in `2 ‖x‖²` and the `2` of `m + 2`; `0` is
the coupling's lower end and the vacuum pairing; `1` is the geometric threshold. -/
theorem decay_of_orth_of_conn (τ : Fin 4) (p : ℤ) {β : ℝ} (hβ : 0 < β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : DLRLimit.State (GibbsSpec.IConf (SUN.SU N)))
    (hinv : InfiniteReflection.IsReflectionInvariant
      (LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : InfiniteReflection.ReflPositiveOn
      (LatticeReflection.latticeReflection τ (2 * p))
      (HalfSpaceAlgebra.halfSpaceAlg (G := SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(GibbsSpec.IConf (SUN.SU N), ℝ), ν (ReflectionShift.ishiftObsL τ f) = ν f)
    (hconn : ∀ (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) (S : Finset InfiniteLattice.ILink),
      (S : Set InfiniteLattice.ILink) ⊆ HalfSpaceAlgebra.posHalf τ p →
      InfiniteLattice.IsLocalOn S (x : GibbsSpec.IConf (SUN.SU N) → ℝ) →
      ∃ U : ℕ, ∀ m : ℕ, U ≤ m + 2 →
        |ν (LatticeReflection.ireflObs τ (2 * p) x * (⇑(ReflectionShift.ishiftObsL τ))^[m] x)
          - ν (LatticeReflection.ireflObs τ (2 * p) x)
            * ν ((⇑(ReflectionShift.ishiftObsL τ))^[m] x)|
          ≤ StrongCoupling.coreConstG (2 * (‖x‖ * ‖x‖)) (16 * 4) β U
            * StrongCoupling.coreRate (16 * 4) β ^ (m + 2 - U))
    (y : GNS (StrongCouplingGap.Dg τ p ν hinv hpos hnu).toReflForm)
    (hy : (inner ℝ (StrongCouplingGap.Dg τ p ν hinv hpos hnu).vacGNS y : ℝ) = 0) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((StrongCouplingGap.Dg τ p ν hinv hpos hnu).Tq ^ n) y‖
      ≤ K * StrongCoupling.coreRate (16 * 4) β ^ n := by
  classical
  have hρ0 : 0 < StrongCoupling.coreRate (16 * 4) β := StrongCouplingGap.coreRate_pos _ hβ
  obtain ⟨a, rfl⟩ : ∃ a, GNS.mk (StrongCouplingGap.Dg τ p ν hinv hpos hnu).toReflForm a = y :=
    Submodule.Quotient.mk_surjective _ y
  have hmean : ν (a : C(GibbsSpec.IConf (SUN.SU N), ℝ)) = 0 := by
    rw [← StrongCouplingGap.inner_vacGNS_mk_gaugeInv τ p ν hinv hpos hnu a]; exact hy
  obtain ⟨S, hS, hloc⟩ := (Submodule.mem_inf.mp a.2).1
  obtain ⟨U, hU⟩ := hconn (a : C(GibbsSpec.IConf (SUN.SU N), ℝ)) S hS hloc
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = max (StrongCoupling.coreConstG
      (2 * (‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖
        * ‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖)) (16 * 4) β U)
      (‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖
        * ‖(a : C(GibbsSpec.IConf (SUN.SU N), ℝ))‖) := ⟨_, rfl⟩
  have hC : 0 ≤ Cm := by
    rw [hCm]; exact le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
  refine ClayCapstone.absolute_decay_of_form_decay (StrongCouplingGap.Dg τ p ν hinv hpos hnu) a
    hρ0.le (K := Cm / StrongCoupling.coreRate (16 * 4) β ^ U) (fun n => ?_)
  have hform := GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu a (2 * n)
  have hshift : ν ((⇑(ReflectionShift.ishiftObsL τ))^[2 * n]
      (a : C(GibbsSpec.IConf (SUN.SU N), ℝ))) = 0 := by
    rw [GaugeInvariantAlgebra.state_iterate_shift_eq ν τ hnu]; exact hmean
  rw [hform]
  refine StrongCouplingGap.le_div_pow_mul_pow hρ0 hr.le hC (fun hj => ?_) ?_
  · have h := hU (2 * n) hj
    rw [hshift, mul_zero, sub_zero] at h
    exact le_trans (le_abs_self _) (le_trans h
      (mul_le_mul_of_nonneg_right (hCm ▸ le_max_left _ _) (pow_nonneg hρ0.le _)))
  · refine le_trans (le_abs_self _) (le_trans (ν.abs_le_norm _) ?_)
    refine le_trans (norm_mul_le _ _) (le_trans ?_ (hCm ▸ le_max_right _ _))
    exact mul_le_mul (WilsonTransferReduction.norm_ireflObs_le τ (2 * p) _)
      (GeneralDecay.norm_iterate_ishiftObsL_le τ _ (2 * n)) (norm_nonneg _) (norm_nonneg _)

#print axioms decay_of_orth_of_conn

/-- **Every vector orthogonal to the vacuum of the periodic data decays at rate `coreRate 64 β`**, at
`0 < β` with `coreRate 64 β < 1`. `decay_of_orth_of_conn` at `periodicState hN β`, its three state
facts from `PeriodicState`, and the pairing bound `periodic_connected_shift_abs_le_obs`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank, the coupling's lower end and the vacuum pairing; `1` is the geometric threshold. -/
theorem periodic_decay_of_orth (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1)
    (y : GNS (PeriodicState.periodicGaugeInvData τ p hN β).toReflForm)
    (hy : (inner ℝ (PeriodicState.periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((PeriodicState.periodicGaugeInvData τ p hN β).Tq ^ n) y‖
      ≤ K * StrongCoupling.coreRate (16 * 4) β ^ n :=
  decay_of_orth_of_conn τ p hβ hr (PeriodicState.periodicState hN β)
    (PeriodicState.periodicState_reflInvariant hN β τ (2 * p))
    (PeriodicState.periodicState_reflPositive hN β τ p)
    (PeriodicState.periodicState_shift hN β τ)
    (fun x _S hS hx => periodic_connected_shift_abs_le_obs hN hβ.le τ p hr x hS hx) y hy

#print axioms periodic_decay_of_orth

/-- **One transfer step contracts the vacuum complement of the periodic data by `coreRate 64 β`**:
`‖Tq y‖ ≤ coreRate 64 β · ‖y‖`. `periodic_decay_of_orth` and
`SecondEigenvalue.norm_le_of_absolute_iterate_bound`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank, the coupling's lower end and the vacuum pairing; `1` is the geometric threshold. -/
theorem periodic_norm_Tq_le_of_orth (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1)
    (y : GNS (PeriodicState.periodicGaugeInvData τ p hN β).toReflForm)
    (hy : (inner ℝ (PeriodicState.periodicGaugeInvData τ p hN β).vacGNS y : ℝ) = 0) :
    ‖(PeriodicState.periodicGaugeInvData τ p hN β).Tq y‖
      ≤ StrongCoupling.coreRate (16 * 4) β * ‖y‖ := by
  obtain ⟨K, hK⟩ := periodic_decay_of_orth τ p hN hβ hr y hy
  exact SecondEigenvalue.norm_le_of_absolute_iterate_bound
    (PeriodicState.periodicGaugeInvData τ p hN β).Tq
    (PeriodicState.periodicGaugeInvData τ p hN β).Tq_isSymmetric
    (StrongCouplingGap.coreRate_pos _ hβ).le hK

#print axioms periodic_norm_Tq_le_of_orth

/-- **`GapAt` at the periodic data at rate `coreRate 64 β`**, at every `0 < β` with
`coreRate 64 β < 1`: `periodic_norm_Tq_le_of_orth` and `GNSCompare.gapAt_of_tq_contracts`.

DERIVED: `16 * 4` is the touch-degree bound; the `4` in `Fin 4` is the spacetime dimension; `0` is
the excluded rank and the coupling's lower end; `1` is the geometric threshold. -/
theorem periodic_gapAt_of_coreRate (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1) :
    TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
      (StrongCoupling.coreRate (16 * 4) β) :=
  GNSCompare.gapAt_of_tq_contracts _ (StrongCouplingGap.coreRate_pos _ hβ).le
    (fun y hy => periodic_norm_Tq_le_of_orth τ p hN hβ hr y hy)

#print axioms periodic_gapAt_of_coreRate

end Contraction

/-! ## 6. The gap at strong coupling -/

section Headline

variable {N : ℕ}

/-- **The transfer gap at the periodic state at strong coupling.** There is `β₀ > 0` such that at
every `0 < β < β₀` the rate `r = coreRate 64 β` satisfies `0 < r < 1` and
`TransferGap.GapAt (periodicGaugeInvData τ p hN β) r`. `β₀` is the existential `b` of
`StrongCoupling.core_rate_lt_one_of_small_hypercubic` at dimension `4`.

DERIVED: `16 * 4` is the periodic touch-degree bound (`StrongCoupling.touchDeg_bd_le` at dimension
`4`); the `4` in `Fin 4` is the spacetime dimension; `0` is the excluded rank, the lower end of `β₀`, `β` and the rate; `1` is the geometric
threshold the rate must beat. -/
theorem periodic_gapAt_strong_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ →
      0 < StrongCoupling.coreRate (16 * 4) β ∧ StrongCoupling.coreRate (16 * 4) β < 1
        ∧ TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
            (StrongCoupling.coreRate (16 * 4) β) := by
  obtain ⟨b, hb, hsmall⟩ := StrongCoupling.core_rate_lt_one_of_small_hypercubic 4
  exact ⟨b, hb, fun β hβ hβb =>
    ⟨StrongCouplingGap.coreRate_pos _ hβ, hsmall β hβ.le hβb,
      periodic_gapAt_of_coreRate τ p hN hβ (hsmall β hβ.le hβb)⟩⟩

#print axioms periodic_gapAt_strong_coupling

/-- **`PeriodicClayGapAt` at strong coupling.** At `2 ≤ N` there is `β₀ > 0` such that at every
`0 < β < β₀`, `PeriodicContent.PeriodicClayGapAt τ p hN β (coreRate 64 β)`:
`periodic_gapAt_strong_coupling` and `GapStep.periodic_clayGapAt_of_gapAt`.

DERIVED: `16 * 4` is the periodic touch-degree bound; the `4` in `Fin 4` is the spacetime dimension;
`2` is the least rank with a non-zero Haar
variance of the real trace (`GapStep.periodic_clayGapAt_of_gapAt`'s); `0` is the excluded rank and
the lower end of `β₀` and `β`. -/
theorem periodic_clayGapAt_strong_coupling (τ : Fin 4) (p : ℤ) (hN2 : 2 ≤ N) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ →
      PeriodicContent.PeriodicClayGapAt τ p hN β (StrongCoupling.coreRate (16 * 4) β) := by
  obtain ⟨β₀, hβ₀, h⟩ := periodic_gapAt_strong_coupling (N := N) τ p hN
  exact ⟨β₀, hβ₀, fun β hβ hβb =>
    GapStep.periodic_clayGapAt_of_gapAt τ p hN2 hN hβ.le (h β hβ hβb).1 (h β hβ hβb).2.1
      (h β hβ hβb).2.2⟩

#print axioms periodic_clayGapAt_strong_coupling

/-- **`TorusLagClear` at strong coupling, at every lag.** There is `β₀ > 0` such that at every
`0 < β < β₀` and every lag `m`, `ChessboardRead.TorusLagClear τ p hN β m (coreRate 64 β)`:
`periodic_gapAt_strong_coupling` and `WeakCouplingWindow.torusLagClear_of_gapAt`.

DERIVED: `16 * 4` is the periodic touch-degree bound; the `4` in `Fin 4` is the spacetime dimension;
`0` is the excluded rank and the lower end of `β₀` and `β`. -/
theorem periodic_torusLagClear_strong_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ → ∀ m : ℕ,
      ChessboardRead.TorusLagClear τ p hN β m (StrongCoupling.coreRate (16 * 4) β) := by
  obtain ⟨β₀, hβ₀, h⟩ := periodic_gapAt_strong_coupling (N := N) τ p hN
  exact ⟨β₀, hβ₀, fun β hβ hβb m =>
    WeakCouplingWindow.torusLagClear_of_gapAt τ p hN β (h β hβ hβb).1.le (h β hβ hβb).2.2 m⟩

#print axioms periodic_torusLagClear_strong_coupling

/-- **The base of the coupling tower.** At `1 ≤ N` there is `β₀ > 0` such that at every `0 < β < β₀`
and every `M ≤ −log (coreRate 64 β) / aRun N β`, the periodic data has `GapAt` at rate
`e^{−M·aRun N β}` — the base `GapStep.periodic_clay_tower` takes, at physical rate `M`
(`periodic_gapAt_strong_coupling`, `GapStep.gapAt_mono`: `coreRate 64 β ≤ e^{−M·aRun N β}`).

DERIVED: `16 * 4` is the periodic touch-degree bound; the `4` in `Fin 4` is the spacetime dimension;
`1` is the least colour count, for `AsymptoticScaling.aRun_pos`; `0` is the excluded rank and the
lower end of `β₀` and `β`. -/
theorem periodic_tower_base (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ → ∀ M : ℝ,
      M ≤ -Real.log (StrongCoupling.coreRate (16 * 4) β) / AsymptoticScaling.aRun N β →
      TransferGap.GapAt (PeriodicState.periodicGaugeInvData τ p hN β)
        (Real.exp (-(M * AsymptoticScaling.aRun N β))) := by
  obtain ⟨β₀, hβ₀, h⟩ := periodic_gapAt_strong_coupling (N := N) τ p hN
  refine ⟨β₀, hβ₀, fun β hβ hβb M hM => ?_⟩
  obtain ⟨hc0, _, hg⟩ := h β hβ hβb
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN1 hβ
  have hMa : M * AsymptoticScaling.aRun N β ≤ -Real.log (StrongCoupling.coreRate (16 * 4) β) :=
    (le_div_iff₀ ha).mp hM
  have hle : StrongCoupling.coreRate (16 * 4) β ≤ Real.exp (-(M * AsymptoticScaling.aRun N β)) := by
    rw [← Real.exp_log hc0]
    exact Real.exp_le_exp.mpr (by linarith)
  exact GapStep.gapAt_mono _ hc0.le hle hg

#print axioms periodic_tower_base

end Headline

end MassGap.PeriodicStrongCoupling
