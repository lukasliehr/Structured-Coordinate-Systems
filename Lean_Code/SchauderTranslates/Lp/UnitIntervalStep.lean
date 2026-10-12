import Lean_Code.SchauderTranslates.Lp.WholeCellSystems

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
variable (ab : ℝ × ℝ) (hab : ab.1 < ab.2)

include hp0 hpfin hab in
theorem intervalAtom_norm_pos : 0 < ‖intervalAtom p ab‖ := by
  rw [norm_intervalAtom p hp0 hpfin ab, max_eq_left (sub_pos.mpr hab).le]
  exact Real.rpow_pos_of_pos (sub_pos.mpr hab) _

def unitIntervalVector : LebesgueLp p := (‖intervalAtom p ab‖⁻¹ : ℝ) • intervalAtom p ab

include hp0 hpfin hab in
theorem unitIntervalVector_norm : ‖unitIntervalVector p ab‖ = 1 := by
  rw [unitIntervalVector, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (intervalAtom_norm_pos p hp0 hpfin ab hab)),
    inv_mul_cancel₀ (intervalAtom_norm_pos p hp0 hpfin ab hab).ne']

theorem unitIntervalVector_isCompactStep : IsCompactStep p (unitIntervalVector p ab) :=
  (intervalAtom_isCompactStep p ab).smul _

def unitIntervalStepData : DisjointStepData p (unitIntervalVector p ab) where
  cells := {ab}
  value _ := ‖intervalAtom p ab‖⁻¹
  length_pos cd hcd := by simpa only [Finset.mem_singleton.mp hcd] using hab
  value_ne_zero cd _ := inv_ne_zero (intervalAtom_norm_pos p hp0 hpfin ab hab).ne'
  disjoint cd hcd ef hef hne := by
    exact False.elim (hne ((Finset.mem_singleton.mp hcd).trans (Finset.mem_singleton.mp hef).symm))
  representation := by simp [unitIntervalVector]

theorem unitIntervalStepData_support :
    (unitIntervalStepData p hp0 hpfin ab hab).supportSet = Set.Ico ab.1 ab.2 := by
  simp [DisjointStepData.supportSet, unitIntervalStepData]

end SchauderTranslates.LpConstruction
