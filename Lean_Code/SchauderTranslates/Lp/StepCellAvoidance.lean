import Lean_Code.SchauderTranslates.Lp.StepCellGeometry
import Lean_Code.SchauderTranslates.Lp.DisjointNorm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem DisjointStepData.supportSet_aedisjoint_ico {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (a b : ℝ)
    (he : SupportedOn e (Set.Ico a b)ᶜ) :
    AEDisjoint volume D.supportSet (Set.Ico a b) := by
  change volume (D.supportSet ∩ Set.Ico a b) = 0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [D.nonzero_iff_support_ae, he] with x hx he
  rintro ⟨hD, hI⟩
  exact (hx.mpr hD) (he (by simpa using hI))

/-- Almost-everywhere avoidance by a compact step class yields exact
avoidance of a half-open interval by its permanent cell geometry. -/
theorem DisjointStepData.supportSet_disjoint_ico {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (a b : ℝ)
    (he : SupportedOn e (Set.Ico a b)ᶜ) :
    Disjoint D.supportSet (Set.Ico a b) := by
  have hAE := D.supportSet_aedisjoint_ico a b he
  apply Set.disjoint_left.mpr
  intro x hx hI
  obtain ⟨cd, hcd, hx⟩ := Set.mem_iUnion₂.mp hx
  have hD : Set.Ico cd.1 cd.2 ⊆ D.supportSet :=
    fun y hy => Set.mem_iUnion₂.mpr ⟨cd, hcd, hy⟩
  exact Set.disjoint_left.mp (ico_disjoint_of_aedisjoint _ _ _ _
    (hAE.mono hD Set.Subset.rfl)) hx hI

end SchauderTranslates.LpConstruction
