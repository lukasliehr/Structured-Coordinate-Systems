import Lean_Code.SchauderTranslates.Lp.StepCellSupport
import Mathlib.MeasureTheory.Measure.AEDisjoint

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- For half-open real intervals, almost-everywhere disjointness is exact
disjointness: any nonempty intersection has strictly positive length. -/
theorem ico_disjoint_of_aedisjoint (a b c d : ℝ)
    (h : AEDisjoint volume (Set.Ico a b) (Set.Ico c d)) :
    Disjoint (Set.Ico a b) (Set.Ico c d) := by
  have hz := h.eq
  rw [Set.Ico_inter_Ico, Real.volume_Ico, ENNReal.ofReal_eq_zero] at hz
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hlo : max a c ≤ x := max_le hx.1 hy.1
  have hhi : x < min b d := lt_min hx.2 hy.2
  linarith

theorem DisjointStepData.nonzero_iff_support_ae {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : ∀ᵐ x ∂volume, e x ≠ 0 ↔ x ∈ D.supportSet := by
  filter_upwards [D.valueFunction_ae] with x hx
  rw [hx]
  simpa only [ne_eq, Complex.ofReal_eq_zero] using D.valueFunction_ne_zero_iff x

theorem DisjointStepData.supportSet_aedisjoint {p : ℝ≥0∞} {e f : LebesgueLp p}
    (D : DisjointStepData p e) (E : DisjointStepData p f)
    (hef : ∀ᵐ x ∂volume, e x = 0 ∨ f x = 0) : AEDisjoint volume D.supportSet E.supportSet := by
  change volume (D.supportSet ∩ E.supportSet) = 0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [D.nonzero_iff_support_ae, E.nonzero_iff_support_ae, hef] with x hx hy hef
  rintro ⟨hD, hE⟩
  rcases hef with he | hf
  · exact (hx.mpr hD) he
  · exact (hy.mpr hE) hf

/-- Fresh step vectors with disjoint Lᵖ supports have exactly disjoint
finite unions of half-open cells. Thus later allocation keeps old cells. -/
theorem DisjointStepData.supportSet_disjoint {p : ℝ≥0∞} {e f : LebesgueLp p}
    (D : DisjointStepData p e) (E : DisjointStepData p f)
    (hef : ∀ᵐ x ∂volume, e x = 0 ∨ f x = 0) : Disjoint D.supportSet E.supportSet := by
  have hAE := D.supportSet_aedisjoint E hef
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨ab, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hab, hxab⟩ := Set.mem_iUnion.mp hx
  obtain ⟨cd, hy⟩ := Set.mem_iUnion.mp hy
  obtain ⟨hcd, hxcd⟩ := Set.mem_iUnion.mp hy
  have hD : Set.Ico ab.1 ab.2 ⊆ D.supportSet := fun y hy =>
    Set.mem_iUnion.mpr ⟨ab, Set.mem_iUnion.mpr ⟨hab, hy⟩⟩
  have hE : Set.Ico cd.1 cd.2 ⊆ E.supportSet := fun y hy =>
    Set.mem_iUnion.mpr ⟨cd, Set.mem_iUnion.mpr ⟨hcd, hy⟩⟩
  exact Set.disjoint_left.mp (ico_disjoint_of_aedisjoint _ _ _ _ (hAE.mono hD hE)) hxab hxcd

end SchauderTranslates.LpConstruction
