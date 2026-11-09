import Mathlib
import MassGap.ClayStatement

/-!
# MassGap.FlowComposites — what the target fixes about the composites, and what a flowed choice buys

`ClayStatementAtExt` is `∃ τ r X ρ G w C wC, ClayData … ∧ Ext …`: the composite family `C : Composites N`
and its vectors `wC` are chosen by the prover, like the tensor's mixing `ρ`. The target fixes only the clauses
the chosen objects must meet. This module reads those clauses for the question: can the prover choose
composites built from the observer's own flowed fields, so that the composite inputs of
the `SU(2)` target that read the renormalised fields (`WardT`, `ObsLower`, and from
`hcomp` `BoundC`, `OS0C`, `OS1C`, `CovC`, `CompNondeg`) follow from
`MultiScale` and the observer's clauses?

## 1. What the target fixes (read from `ClayStatement`)

* `Composites N` carries `Ix`, `cl`, a step-independent `bare : Ix → LField`, a step-dependent
  `ren : ℕ → Ix → LField` and `rep`. `LField` is a gauge-invariant field local on some finite set of links;
  `W.fieldMap k O` is one (`ConfFlow` has finite range at each step), so a flowed field is an admissible value
  of `ren k i`.
* `Tied`: each `bare i` has classical leading term `g^{#F} cl i` at dimension `cdim (cl i)`.
* `RenTri`: at every step `ren k i` is a finite combination of `1` and bare fields of dimension
  `≤ cdim (cl i)`, and every bare field of dimension `≤ d` is a combination of `1` and the `ren k` of dimension
  `≤ d`.
* `TIn`: indices `e α` with `cl (e α) = Re tr F_{α₀α₁}F_{α₂α₃}` and `ren k (e α) = ∑_b M k α b · op b`, the
  tensor's mixing. `RenormMix` has a finite basis `op : B → LField`, `[Fintype B]`, independent of the step;
  `ScalarTie` fixes the trace channel to `Ztr k · sym (plaqField q0)`.
* `WardT` and `NonGaussianT` (to which `ObsLower hN z` is equivalent at `ρ = rhoD f z` given
  `SepConv`, `InputsTriage.nonGaussianT_rhoD_iff_lower`) are clauses on `ρ`; they do not mention `C`.

## 2. What is proved here

* **The tensor composites are bare, whatever `C` is.** `ren_tensor_mem_span`: under the second clause of
  `TIn`, every `ren k (e α)` lies in the span of the finitely many basis fields, a space independent of `k`
  (`finiteDimensional_tensorSpan`). `tensorSpan_le_localSub`: that span consists of fields local on one finite
  set of links `S`; so `ren_tensor_local`: one `S` serves every step and every component.
  `not_mem_tensorSpan_of_spread`: a step sequence of fields that is, for every finite `S`, at some step not
  local on `S` (as the observer's flowed fields at a range growing like `r / a_k` are, argued, not proved for an
  abstract `ConfFlow`) is not, at every step, in the tensor's space.
* **The trace composite is the bare plaquette.** `trace_ren_eq`: under `TIn` and `ScalarTie`,
  `∑_α trC α · ren k (e α) = Ztr k · sym (plaqField q0)` at every step, with `Ztr k · a_k⁴ → N/8`.
* `tensor_bare_of_clayData`: the three items above from `ClayData` at any witness.
* **The rest of the family may be flowed.** `shiftComp`: from a base family `cl : I → CMono` and a
  `ℤ`-indexed family of bare fields `B i n`, the index set `I × ℤ`, `bare (i, n) = B i n`,
  `ren k (i, n) = z · (B i (n + k) − c)`. `renTri_shiftComp`: `RenTri` holds when every `z ≠ 0` (the shift
  `n ↦ n + k` is onto `ℤ` at each `k`, which is what the invertibility half of `RenTri` asks).
  `tied_shiftComp_iff`, `covers_shiftComp`: `Tied` and `Covers` reduce to the base family.
* `obsComp`: the shift family at `B i n = W.fieldMap n.toNat (O i)` with the observer's factor `zOn D` and
  subtraction `sOn D (s0 N)`. `obsComp_ren_zero`: `ren k (i, 0)` is the observer's flowed field
  `(energy0 W D hD).map k (O i)` at every step. `renTri_obsComp`: `RenTri` holds (`zOn_ne_zero`).
  `tied_obsComp_identity`: at `ConfFlow.identity` `Tied` is that of the base fields; for a genuine `W`,
  `Tied` asks that every `O i ∘ V_n` (`n` fixed, the spacing `a → 0`) keep the classical leading term of `O i`
  (`tied_obsComp_iff`), a hypothesis on `W`.

## 3. Which inputs become derivable (argued from §2 and the definitions)

None of them (`OS1C` and `BoundC` also range over every family of `C`, so the argument below covers them).
`WardT` and `ObsLower` are statements on `ρ`, and `ρ` is fixed bare: its basis is finite
and step-independent and its trace channel is the unflowed plaquette (`trace_ren_eq`). `OS0C`, `CovC`,
`CompNondeg` quantify over every family of `C`, so they contain the families of the indices `e α`, whose
readings are the tensor's (`LinkReduce.latT_eq_sum_latC`); restricted there they give `OS0Sep`, `TensorCov`,
`TensorNondeg` of the bare `ρ` (`CompReduce.os0Sep_of_comp`, `tensorCov_of_comp`, `tensorNondeg_of_comp`),
and every mixed family pairs a bare tensor index with the other indices. A flowed choice of the remaining
indices (`obsComp`) moves none of that content. On the flowed indices `(i, 0)` alone, at `O i` in the observer's class
`D = SymPlaqClass 2`, the readings are the connected flowed readings of `energy0`, which the observer's moment
bounds control; `Covers` asks every monomial of every dimension, and `uv` gives moments only on `D`.

## 4. The blocking constraints

* `TIn` (second clause) with `RenormMix` (finite, step-independent `op`) and `ScalarTie`: the dimension-four
  composites are bare lattice fields (§2, proved).
* `Tied` with `bare` step-independent: a bare field cannot be the observer's field at physical flow time,
  whose lattice flow time `t / a_k²` grows with `k`; the shift family puts the step into the index and needs
  `Tied` of `O ∘ V_n` at each fixed `n` (proved reduction; the property of `W` is not proved).
* `RepTie` is a classical identity between `cl` and `rep`; it does not block a flowed choice.

## 5. A repair proposal (text only; the target is not edited)

PROPOSAL, not a declaration. Replace the tie `ren k (e α) = ∑_b M k α b op b` of `TIn`, and the bare reading
of the tensor in `RenormMix`, by the small-flow-time definition of renormalised composites: a flow time
`s ∈ (0, s₀]` in physical units, the flowed fields `O ∘ V_k^{(s)}`, and coefficients `c_{ij}(s)` fixed by the
classical expansion, with the composite's continuum reading the limit `s → 0⁺` of the separated continuum
readings of `∑_j c_{ij}(s) O_j ∘ V^{(s)}`. This keeps the faithful content (the renormalised composite
determined by its classical leading term, the Ward and scalar normalisations moved to the `s → 0⁺` limit) and
lets every composite be read through the observer. It does not by itself discharge `OS0C`: the kernel bound at
separation `d` needs the flowed readings controlled uniformly for `a_k² ≪ s ≲ d²`, the intermediate scales
that `MultiScale` does not state (`MultiScale` docstring §1). The substrate statement that would carry it is a
`uv` clause uniform in the flow time, with the asymptotic-freedom scaling of the moments in `s`, on a class
`D` containing every monomial's flowed field.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the tag of the observer's index, the zero field and the shift origin; `1` the unit
field and the unit factor; `4` the dimension.
-/

noncomputable section

namespace MassGap.FlowComposites

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverEnergyMoments MassGap.ObserverSymField
  MassGap.ObserverOSLinked MassGap.ClayStatement Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The tensor composites are bare -/

/-- **The fields local on `S`**, a submodule. -/
def localSub (S : Finset ILink) : Submodule ℝ C(Cfg N, ℝ) where
  carrier := {F | IsLocalOn S (F : Cfg N → ℝ)}
  add_mem' := by
    intro F G hF hG U V h
    show F U + G U = F V + G V
    rw [hF U V h, hG U V h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := by
    intro r F hF U V h
    show r * F U = r * F V
    rw [hF U V h]

/-- **The tensor's space**: the span of the basis fields of the mixing. -/
def tensorSpan (ρ : RenormMix N) : Submodule ℝ C(Cfg N, ℝ) :=
  Submodule.span ℝ (Set.range fun b => (ρ.op b).1)

/-- The tensor's space is finite-dimensional. -/
theorem finiteDimensional_tensorSpan (ρ : RenormMix N) : FiniteDimensional ℝ (tensorSpan ρ) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **Every tensor composite lies in the tensor's space**, at every step. -/
theorem ren_tensor_mem_span (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) (k : ℕ) (α : Idx4) :
    (C.ren k (e α)).1 ∈ tensorSpan ρ := by
  rw [hren]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

/-- **The tensor's space is local on one finite set of links.** -/
theorem tensorSpan_le_localSub (ρ : RenormMix N) :
    ∃ S : Finset ILink, tensorSpan ρ ≤ localSub (N := N) S := by
  classical
  choose S hS using fun b => (ρ.op b).2.1
  refine ⟨Finset.univ.biUnion S, Submodule.span_le.2 ?_⟩
  rintro _ ⟨b, rfl⟩
  exact IsLocalOn.mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ b)) (hS b)

/-- **One finite set of links carries every tensor composite at every step.** -/
theorem ren_tensor_local (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) :
    ∃ S : Finset ILink, ∀ k α, IsLocalOn S ((C.ren k (e α)).1 : Cfg N → ℝ) := by
  obtain ⟨S, hS⟩ := tensorSpan_le_localSub ρ
  exact ⟨S, fun k α => hS (ren_tensor_mem_span ρ C e hren k α)⟩

/-- **A spreading sequence is not in the tensor's space**: if for every finite `S` some `L k` is not local on
`S`, then not every `L k` lies in the tensor's space. -/
theorem not_mem_tensorSpan_of_spread (ρ : RenormMix N) (L : ℕ → C(Cfg N, ℝ))
    (hL : ∀ S : Finset ILink, ∃ k, ¬ IsLocalOn S (L k : Cfg N → ℝ)) :
    ¬ ∀ k, L k ∈ tensorSpan ρ := by
  intro h
  obtain ⟨S, hS⟩ := tensorSpan_le_localSub ρ
  obtain ⟨k, hk⟩ := hL S
  exact hk (hS (h k))

/-- **The trace composite is the bare plaquette**: under the second clause of `TIn` and `ScalarTie`,
`∑_α trC α · ren k (e α) = Ztr k · sym (plaqField q0)`, with `Ztr k · a_k⁴ → N/8`. -/
theorem trace_ren_eq (ρ : RenormMix N) (C : Composites N) (e : Idx4 → C.Ix)
    (hren : ∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1) {O : LField (MassGap.SUN.SU N)}
    (hST : ScalarTie ρ O) :
    ∃ Ztr : ℕ → ℝ, (∀ k, ∑ α, trC α • (C.ren k (e α)).1 = Ztr k • (sym (plaqField q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)) := by
  obtain ⟨hO, Ztr, hZ, hlim⟩ := hST
  subst hO
  refine ⟨Ztr, fun k => ?_, hlim⟩
  rw [← hZ k]
  simp only [hren, Finset.smul_sum, smul_smul, mixC, Finset.sum_smul]
  exact Finset.sum_comm

/-- **At any witness of `ClayData`, the tensor composites are bare**: indices `e α` of the chosen family with
the tensor's monomials, whose renormalised fields lie in the tensor's finite-dimensional space, are local on
one finite set of links at every step, and whose trace combination is the bare plaquette. -/
theorem tensor_bare_of_clayData (hN2 : 2 ≤ N) {W : ConfFlow N} {D : Set (LField (MassGap.SUN.SU N))}
    {hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {ρ : RenormMix N} {G : ℝ → ℝ} {w : TSep τ → X.base.H}
    {C : Composites N} {wC : TSepG C.Ix τ → X.base.H}
    (h : ClayData hN2 W D hD τ r X ρ G w C wC) :
    ∃ e : Idx4 → C.Ix, (∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
      ∧ (∀ k α, (C.ren k (e α)).1 ∈ tensorSpan ρ)
      ∧ (∃ S : Finset ILink, ∀ k α, IsLocalOn S ((C.ren k (e α)).1 : Cfg N → ℝ))
      ∧ ∃ Ztr : ℕ → ℝ, (∀ k, ∑ α, trC α • (C.ren k (e α)).1 = Ztr k • (sym (plaqField q0)).1)
        ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)) := by
  obtain ⟨-, -, -, hST, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨e, he, hren, -⟩, -, -, -⟩ := h
  exact ⟨e, he, ren_tensor_mem_span ρ C e hren, ren_tensor_local ρ C e hren,
    trace_ren_eq ρ C e hren hST⟩

/-! ## 2. The shift family: step-dependent renormalised fields under `RenTri` -/

/-- **The shift family**: index `I × ℤ`, `bare (i, n) = B i n`, `ren k (i, n) = z · (B i (n + k) − c)`. -/
def shiftComp (I : Type) (cl : I → CMono) (B : I → ℤ → LField (MassGap.SUN.SU N))
    (z c : ℕ → I → ℤ → ℝ) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    Composites N where
  Ix := I × ℤ
  cl p := cl p.1
  bare p := B p.1 p.2
  ren k p := scaleField ((B p.1 (p.2 + k)).sub (c k p.1 p.2)) (z k p.1 p.2)
  rep := rep

/-- **`RenTri` of the shift family** when every factor is non-zero. -/
theorem renTri_shiftComp (I : Type) (cl : I → CMono) (B : I → ℤ → LField (MassGap.SUN.SU N))
    (z c : ℕ → I → ℤ → ℝ) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ))
    (hz : ∀ k i n, z k i n ≠ 0) : (shiftComp I cl B z c rep).RenTri := by
  set C := shiftComp I cl B z c rep with hC
  constructor
  · intro k p
    have hx : (B p.1 (p.2 + k)).1 ∈ C.lowSpan C.bare (cdim (C.cl p)) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨(p.1, p.2 + k), le_refl _⟩, rfl⟩)
    have h1 : (1 : C(Cfg N, ℝ)) ∈ C.lowSpan C.bare (cdim (C.cl p)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ h1))
  · intro k d
    refine Submodule.span_le.2 ?_
    rintro _ (rfl | ⟨⟨q, hq⟩, rfl⟩)
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · have e1 : (C.bare q).1 = (z k q.1 (q.2 - k))⁻¹ • (C.ren k (q.1, q.2 - k)).1
          + c k q.1 (q.2 - k) • (1 : C(Cfg N, ℝ)) := by
        show (B q.1 q.2).1 = (z k q.1 (q.2 - k))⁻¹ • (z k q.1 (q.2 - k)
            • ((B q.1 (q.2 - k + k)).1 - c k q.1 (q.2 - k) • (1 : C(Cfg N, ℝ))))
          + c k q.1 (q.2 - k) • (1 : C(Cfg N, ℝ))
        rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ (hz _ _ _), one_smul, sub_add_cancel]
      show (C.bare q).1 ∈ C.lowSpan (C.ren k) d
      rw [e1]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨(q.1, q.2 - k), hq⟩, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))

/-- **`Tied` of the shift family** is `Tied` of every `B i n`. -/
theorem tied_shiftComp_iff (I : Type) (cl : I → CMono) (B : I → ℤ → LField (MassGap.SUN.SU N))
    (z c : ℕ → I → ℤ → ℝ) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    (shiftComp I cl B z c rep).Tied ↔ ∀ i n, ClassicalLead (B i n).1 (cdim (cl i))
      (fun A g => g ^ cnF (cl i) * cval g A (cl i)) :=
  ⟨fun h i n => h (i, n), fun h p => h p.1 p.2⟩

/-- **`Covers` of the shift family** from that of the base monomials. -/
theorem covers_shiftComp (I : Type) (cl : I → CMono) (B : I → ℤ → LField (MassGap.SUN.SU N))
    (z c : ℕ → I → ℤ → ℝ) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ))
    (h : ∀ m : CMono, m ≠ [] → (∀ p ∈ m, p.1 ≠ []) → ∃ i, cl i = m) :
    (shiftComp I cl B z c rep).Covers := by
  intro m hm hp
  obtain ⟨i, hi⟩ := h m hm hp
  exact ⟨(i, 0), hi⟩

/-! ## 3. The observer's flowed fields as a shift family -/

/-- **The observer's composites**: the shift family at `B i n = O i ∘ V_{n.toNat}`, with the observer's factor
`zOn D` and subtraction `sOn D (s0 N)`. -/
def obsComp (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (I : Type) (cl : I → CMono)
    (O : I → LField (MassGap.SUN.SU N)) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    Composites N :=
  shiftComp I cl (fun i n => W.fieldMap n.toNat (O i)) (fun k i _ => zOn D k (O i))
    (fun k i _ => sOn D (s0 N) k (O i)) rep

/-- **The index `(i, 0)` reads the observer's flowed field** `(energy0 W D hD).map k (O i)` at every step. -/
theorem obsComp_ren_zero (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (I : Type)
    (cl : I → CMono) (O : I → LField (MassGap.SUN.SU N))
    (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) (k : ℕ) (i : I) :
    (obsComp W D I cl O rep).ren k (i, 0) = (energy0 W D hD).map k (O i) := by
  have hk : ((0 : ℤ) + (k : ℤ)).toNat = k := by simp
  show scaleField ((W.fieldMap (((0 : ℤ) + (k : ℤ)).toNat) (O i)).sub (sOn D (s0 N) k (O i)))
      (zOn D k (O i)) = _
  rw [hk]
  rfl

/-- The observer's factor is non-zero. -/
theorem zOn_ne_zero (hN : N ≠ 0) (D : Set (LField (MassGap.SUN.SU N))) (k : ℕ)
    (O : LField (MassGap.SUN.SU N)) : zOn D k O ≠ 0 := by
  unfold zOn
  split_ifs
  · show (dySpacing N k ^ 4)⁻¹ ≠ 0
    exact inv_ne_zero (pow_ne_zero _ (dySpacing_pos (one_le_of_ne_zero hN) k).ne')
  · exact one_ne_zero

/-- **`RenTri` of the observer's composites.** -/
theorem renTri_obsComp (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (I : Type)
    (cl : I → CMono) (O : I → LField (MassGap.SUN.SU N))
    (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    (obsComp W D I cl O rep).RenTri :=
  renTri_shiftComp I cl _ _ _ rep fun k i _ => zOn_ne_zero hN D k (O i)

/-- **`Tied` of the observer's composites** is the classical leading term of every `O i ∘ V_n`. -/
theorem tied_obsComp_iff (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (I : Type)
    (cl : I → CMono) (O : I → LField (MassGap.SUN.SU N))
    (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    (obsComp W D I cl O rep).Tied ↔ ∀ i (n : ℤ), ClassicalLead (W.fieldMap n.toNat (O i)).1
      (cdim (cl i)) (fun A g => g ^ cnF (cl i) * cval g A (cl i)) :=
  tied_shiftComp_iff I cl _ _ _ rep

/-- **At the zero-time flow `Tied` is that of the base fields.** -/
theorem tied_obsComp_identity (D : Set (LField (MassGap.SUN.SU N))) (I : Type) (cl : I → CMono)
    (O : I → LField (MassGap.SUN.SU N)) (rep : Matrix (Fin 4) (Fin 4) ℝ → I × ℤ → (I × ℤ →₀ ℝ)) :
    (obsComp (ConfFlow.identity N) D I cl O rep).Tied ↔ ∀ i, ClassicalLead (O i).1 (cdim (cl i))
      (fun A g => g ^ cnF (cl i) * cval g A (cl i)) :=
  ⟨fun h i => h (i, 0), fun h p => h p.1⟩

end MassGap.FlowComposites

end

#print axioms MassGap.FlowComposites.finiteDimensional_tensorSpan
#print axioms MassGap.FlowComposites.ren_tensor_mem_span
#print axioms MassGap.FlowComposites.tensorSpan_le_localSub
#print axioms MassGap.FlowComposites.ren_tensor_local
#print axioms MassGap.FlowComposites.not_mem_tensorSpan_of_spread
#print axioms MassGap.FlowComposites.trace_ren_eq
#print axioms MassGap.FlowComposites.tensor_bare_of_clayData
#print axioms MassGap.FlowComposites.renTri_shiftComp
#print axioms MassGap.FlowComposites.tied_shiftComp_iff
#print axioms MassGap.FlowComposites.covers_shiftComp
#print axioms MassGap.FlowComposites.obsComp_ren_zero
#print axioms MassGap.FlowComposites.zOn_ne_zero
#print axioms MassGap.FlowComposites.renTri_obsComp
#print axioms MassGap.FlowComposites.tied_obsComp_iff
#print axioms MassGap.FlowComposites.tied_obsComp_identity
