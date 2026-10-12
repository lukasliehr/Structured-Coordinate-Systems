import Lean_Code.SchauderTranslates.Lp.HaarAffineMeasure

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def affineCell (a c r : ℝ) (hr : 0 < r) : ℝ ≃ᵐ ℝ := haarAffine (c - r * a) r hr

theorem affineCell_apply (a c r : ℝ) (hr : 0 < r) (x : ℝ) :
    affineCell a c r hr x = c + r * (x - a) := by
  change c - r * a + r * x = _
  ring

theorem affineCell_symm_apply (a c r : ℝ) (hr : 0 < r) (y : ℝ) :
    (affineCell a c r hr).symm y = a + (y - c) / r := by
  change (y - (c - r * a)) / r = _
  field_simp
  <;> ring

theorem affineCell_preimage (a b c r : ℝ) (hr : 0 < r) :
    (affineCell a c r hr) ⁻¹' Set.Ico c (c + r * (b - a)) = Set.Ico a b := by
  ext x
  rw [Set.mem_preimage, affineCell_apply]
  change (c ≤ c + r * (x - a) ∧ c + r * (x - a) < c + r * (b - a)) ↔
    (a ≤ x ∧ x < b)
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> nlinarith

theorem affineCell_map_interval (a b c r : ℝ) (hr : 0 < r) :
    Measure.map (affineCell a c r hr) (volume.restrict (Set.Ico a b)) =
      ENNReal.ofReal r⁻¹ • volume.restrict (Set.Ico c (c + r * (b - a))) := by
  rw [← affineCell_preimage a b c r hr,
    ← (affineCell a c r hr).restrict_map volume (Set.Ico c (c + r * (b - a))),
    affineCell, haarAffine_map_volume, Measure.restrict_smul]

/-- An affine map of slope `r` transports the density `r dx` on one
source cell to ordinary Lebesgue measure on its target cell. -/
theorem affineCell_measurePreserving (a b c r : ℝ) (hr : 0 < r) :
    MeasurePreserving (affineCell a c r hr)
      (ENNReal.ofReal r • volume.restrict (Set.Ico a b))
      (volume.restrict (Set.Ico c (c + r * (b - a)))) := by
  constructor
  · exact (affineCell a c r hr).measurable
  · rw [Measure.map_smul, affineCell_map_interval, smul_smul,
      ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_smul]

end SchauderTranslates.LpConstruction
