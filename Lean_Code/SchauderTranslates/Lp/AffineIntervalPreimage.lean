import Lean_Code.SchauderTranslates.Lp.AffineCellMeasure

noncomputable section
open MeasureTheory

namespace SchauderTranslates.LpConstruction

theorem affineCell_strictMono (a c r : ℝ) (hr : 0 < r) :
    StrictMono (affineCell a c r hr : ℝ → ℝ) := by
  intro x y hxy
  rw [affineCell_apply, affineCell_apply]
  nlinarith

theorem affineCell_preimage_Ico (a c r : ℝ) (hr : 0 < r) (l u : ℝ) :
    (affineCell a c r hr) ⁻¹' Set.Ico l u =
      Set.Ico ((affineCell a c r hr).symm l) ((affineCell a c r hr).symm u) := by
  have hm := affineCell_strictMono a c r hr
  ext x
  change (l ≤ affineCell a c r hr x ∧ affineCell a c r hr x < u) ↔
    ((affineCell a c r hr).symm l ≤ x ∧ x < (affineCell a c r hr).symm u)
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hm.le_iff_le.mp (by simpa using hl), hm.lt_iff_lt.mp (by simpa using hu)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨by simpa using hm.le_iff_le.mpr hl, by simpa using hm.lt_iff_lt.mpr hu⟩

end SchauderTranslates.LpConstruction
