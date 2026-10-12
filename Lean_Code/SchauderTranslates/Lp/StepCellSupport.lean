import Lean_Code.SchauderTranslates.Lp.StepCellNorm

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def DisjointStepData.valueFunction {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    ℝ → ℝ := intervalSumValue D.cells D.value

def DisjointStepData.supportSet {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) : Set ℝ :=
  ⋃ ab ∈ D.cells, Set.Ico ab.1 ab.2

theorem DisjointStepData.valueFunction_ae {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    (e : ℝ → ℂ) =ᵐ[volume] fun x => (D.valueFunction x : ℂ) := by
  have h := intervalSumValue_ae p D.cells D.value
  have he := congrArg (fun f : LebesgueLp p => (f : ℝ → ℂ)) D.representation
  exact he ▸ h

theorem DisjointStepData.valueFunction_measurable {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Measurable D.valueFunction := by
  classical
  exact Finset.measurable_sum _ (fun ab _ =>
    measurable_const.mul (measurable_const.indicator measurableSet_Ico))

theorem DisjointStepData.valueFunction_on_cell {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) {ab : ℝ × ℝ} (hab : ab ∈ D.cells)
    {x : ℝ} (hx : x ∈ Set.Ico ab.1 ab.2) : D.valueFunction x = D.value ab := by
  classical
  rw [DisjointStepData.valueFunction, intervalSumValue, Finset.sum_eq_single ab]
  · simp [hx]
  · intro cd hcd hne
    have hxc : x ∉ Set.Ico cd.1 cd.2 := fun hc =>
      Set.disjoint_left.mp (D.disjoint cd hcd ab hab hne) hc hx
    simp [hxc]
  · exact fun h => False.elim (h hab)

theorem DisjointStepData.valueFunction_zero_outside {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) {x : ℝ} (hx : x ∉ D.supportSet) : D.valueFunction x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro ab hab
  have hxab : x ∉ Set.Ico ab.1 ab.2 := fun h => hx (Set.mem_iUnion₂.mpr ⟨ab, hab, h⟩)
  simp [hxab]

theorem DisjointStepData.valueFunction_ne_zero_iff {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (x : ℝ) : D.valueFunction x ≠ 0 ↔ x ∈ D.supportSet := by
  constructor
  · intro h
    by_contra hx
    exact h (D.valueFunction_zero_outside hx)
  · intro hx
    obtain ⟨ab, hab, hxab⟩ := Set.mem_iUnion₂.mp hx
    rw [D.valueFunction_on_cell hab hxab]
    exact D.value_ne_zero ab hab

theorem DisjointStepData.supportSet_measurable {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : MeasurableSet D.supportSet :=
  D.cells.measurableSet_biUnion (fun _ _ => measurableSet_Ico)

end SchauderTranslates.LpConstruction
