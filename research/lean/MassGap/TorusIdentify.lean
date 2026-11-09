import Mathlib
import MassGap.RectWilson
import MassGap.ReflectPositive

/-!
# MassGap.TorusIdentify — the rectangular Wilson system at cubic extents is the tree's

Piece 1 of the finite-volume dyadic step. At constant extents `L = fun _ => M + 1`:

* `rbd_cubic` — `RectWilson.rbd` is `WilsonHypercubic.bd` (`finRotate (M + 1) k = k + 1`);
* `sysR_cubic` — `RectWilson.sysR` is `WilsonHypercubic.sysWilson N 4 (M + 1)`;
* `ZR_cubic` — `RectWilson.ZR` is the tree's periodic partition function, the normaliser of
  `ReflectPositive.EW` and hence of `PeriodicState.torusState`.
-/

namespace MassGap.TorusIdentify

open MassGap MassGap.RectWilson MassGap.WilsonHypercubic MassGap.CompactGauge

theorem rshift_cubic (M : ℕ) (i : Fin 4) (x : RSite (fun _ : Fin 4 => M + 1)) :
    rshift (fun _ => M + 1) i x = shift (d := 4) (n := M + 1) i x := by
  unfold rshift shift
  rw [finRotate_succ_apply]

theorem rbd_cubic (M : ℕ) : rbd (fun _ : Fin 4 => M + 1) = bd (d := 4) (n := M + 1) := by
  funext q
  simp only [rbd, bd, rshift_cubic]

theorem sysR_cubic (N M : ℕ) : sysR (fun _ : Fin 4 => M + 1) N = sysWilson N 4 (M + 1) := by
  unfold sysR sysWilson
  rw [rbd_cubic]

theorem ZR_cubic (N M : ℕ) (β : ℝ) :
    ZR (fun _ : Fin 4 => M + 1) N β
      = (sysWilson N 4 (M + 1)).partition (probHaar (SUN.SU N)) β := by
  unfold ZR; rw [sysR_cubic]

#print axioms ZR_cubic

end MassGap.TorusIdentify
