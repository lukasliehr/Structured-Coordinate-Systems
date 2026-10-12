import Mathlib

noncomputable section
open MeasureTheory

namespace SchauderTranslates

/-- A centered circle interval, represented intrinsically to preserve exact inversion symmetry. -/
def activationSet (p : ℝ) : Set UnitAddCircle := Metric.closedBall 0 (p / 2)

theorem activationSet_measurable (p : ℝ) : MeasurableSet (activationSet p) :=
  Metric.isClosed_closedBall.measurableSet

theorem activationSet_neg_mem (p : ℝ) (x : UnitAddCircle) :
    -x ∈ activationSet p ↔ x ∈ activationSet p := by
  simp only [activationSet, Metric.mem_closedBall]
  rw [show (0 : UnitAddCircle) = -0 by simp, dist_neg_neg, neg_zero]

theorem activationSet_measure {p : ℝ} (hp : p ≤ 1) :
    AddCircle.haarAddCircle (activationSet p) = ENNReal.ofReal p := by
  have h := AddCircle.volume_closedBall 1 (x := (0 : UnitAddCircle)) (p / 2)
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simpa only [ENNReal.ofReal_one, one_smul, show 2 * (p / 2) = p by ring,
    min_eq_right hp, activationSet] using! h

/-- The activation probability is exactly the prescribed real parameter. -/
theorem activationSet_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ x, (activationSet p).indicator (fun _ => (1 : ℝ)) x ∂AddCircle.haarAddCircle) = p := by
  rw [integral_indicator_const (μ := AddCircle.haarAddCircle) (e := (1 : ℝ))
    (activationSet_measurable p)]
  simp [measureReal_def, activationSet_measure hp1, ENNReal.toReal_ofReal hp0]

end SchauderTranslates
