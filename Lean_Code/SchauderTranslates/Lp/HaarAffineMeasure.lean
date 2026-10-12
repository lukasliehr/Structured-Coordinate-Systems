import Lean_Code.SchauderTranslates.Lp.LpMeasurableEquiv

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def haarAffine (a l : ℝ) (hl : 0 < l) : ℝ ≃ᵐ ℝ where
  toFun x := a + l * x
  invFun x := (x - a) / l
  left_inv x := by dsimp; field_simp [hl.ne'] <;> ring
  right_inv x := by dsimp; field_simp [hl.ne'] <;> ring
  measurable_toFun := measurable_const.add (measurable_const.mul measurable_id)
  measurable_invFun := (measurable_id.sub measurable_const).div_const l

def haarIntervalMeasure (a l : ℝ) : Measure ℝ := volume.restrict (Set.Ico a (a + l))

theorem haarAffine_map_volume (a l : ℝ) (hl : 0 < l) :
    Measure.map (haarAffine a l hl) volume = ENNReal.ofReal l⁻¹ • volume := by
  have he : (haarAffine a l hl : ℝ → ℝ) = (fun x => a + x) ∘ (fun x => l * x) := rfl
  rw [he, ← Measure.map_map (g := fun x : ℝ => a + x) (f := fun x : ℝ => l * x)
    (measurable_const.add measurable_id)
    (measurable_const.mul measurable_id), Real.map_volume_mul_left hl.ne',
    Measure.map_smul, (measurePreserving_add_left volume a).map_eq, abs_of_pos (inv_pos.mpr hl)]

theorem haarAffine_preimage_interval (a l : ℝ) (hl : 0 < l) :
    (haarAffine a l hl) ⁻¹' Set.Ico a (a + l) = Set.Ico (0 : ℝ) 1 := by
  ext x
  change (a ≤ a + l * x ∧ a + l * x < a + l) ↔ (0 ≤ x ∧ x < 1)
  constructor
  · rintro ⟨hx0, hx1⟩
    constructor <;> nlinarith
  · rintro ⟨hx0, hx1⟩
    constructor <;> nlinarith

theorem haarAffine_map_haarMeasure (a l : ℝ) (hl : 0 < l) :
    Measure.map (haarAffine a l hl) haarMeasure =
      ENNReal.ofReal l⁻¹ • haarIntervalMeasure a l := by
  rw [haarMeasure, ← haarAffine_preimage_interval a l hl,
    ← (haarAffine a l hl).restrict_map volume (Set.Ico a (a + l)),
    haarAffine_map_volume, Measure.restrict_smul]
  rfl

theorem haarAffine_measurePreserving (a l : ℝ) (hl : 0 < l) :
    MeasurePreserving (haarAffine a l hl) haarMeasure
      (ENNReal.ofReal l⁻¹ • haarIntervalMeasure a l) :=
  ⟨(haarAffine a l hl).measurable, haarAffine_map_haarMeasure a l hl⟩

end SchauderTranslates.LpConstruction
