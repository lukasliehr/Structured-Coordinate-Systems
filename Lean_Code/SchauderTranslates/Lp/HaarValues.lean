import Lean_Code.SchauderTranslates.Lp.HaarOrthogonal
import Lean_Code.SchauderTranslates.Lp.DyadicSelection

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

def haarValue : HaarIndex → ℝ → ℂ
  | none => fun _ => 1
  | some ⟨n, k⟩ => fun x => (haarScale n : ℂ) *
      ((dyadicInterval (n + 1) (2 * k)).indicator (fun _ => (1 : ℂ)) x -
        (dyadicInterval (n + 1) (2 * k + 1)).indicator (fun _ => (1 : ℂ)) x)

theorem star_haarValue (i : HaarIndex) (x : ℝ) : star (haarValue i x) = haarValue i x := by
  rcases i with _ | ⟨n, k⟩ <;> simp [haarValue, Set.indicator]

theorem haarAtom_ae_value (p : ℝ≥0∞) (i : HaarIndex) :
    (haarAtom p i : ℝ → ℂ) =ᵐ[haarMeasure] haarValue i := by
  rcases i with _ | ⟨n, k⟩
  · exact haarConstant_ae_one p
  · exact haarFunction_ae p n k

theorem haarValue_zero_outside_cell (i : DyadicCell) {x : ℝ} (hx : x ∉ dyadicCellSet i) :
    haarValue (some i) x = 0 := by
  have hl : x ∉ dyadicInterval (i.1 + 1) (2 * i.2) := fun h =>
    hx (dyadicInterval_child_left_subset i.1 i.2 h)
  have hr : x ∉ dyadicInterval (i.1 + 1) (2 * i.2 + 1) := fun h =>
    hx (dyadicInterval_child_right_subset i.1 i.2 h)
  simp [haarValue, hl, hr]

/-- A Haar function whose supporting cell is not contained in a given
dyadic cell is constant on that cell. This includes the disjoint case. -/
theorem haarValue_constant_on_cell {i j : DyadicCell}
    (hnot : ¬dyadicCellSet i ⊆ dyadicCellSet j) :
    ∃ z : ℂ, ∀ x ∈ dyadicCellSet j, haarValue (some i) x = z := by
  by_cases hlevel : i.1 < j.1
  · exact haar_value_constant_on_finer_cell i.1 i.2 j.1 j.2 hlevel
  · rcases dyadicCellSet_nested_or_disjoint (Nat.le_of_not_gt hlevel) with hsub | hdis
    · exact (hnot hsub).elim
    · refine ⟨0, fun x hx => ?_⟩
      exact haarValue_zero_outside_cell i (fun hi => Set.disjoint_left.mp hdis hi hx)

end SchauderTranslates.LpConstruction
