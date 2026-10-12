import Lean_Code.SchauderTranslates.Lp.DyadicStepValues

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def dyadicBadPart (f : ℝ → ℂ) (s : Finset DyadicCell) (x : ℝ) : ℂ :=
  ∑ j ∈ s, (dyadicCellSet j).indicator (fun y => f y - dyadicCellMean f j) x

def dyadicGoodPart (f : ℝ → ℂ) (s : Finset DyadicCell) (x : ℝ) : ℂ :=
  f x - dyadicBadPart f s x

theorem dyadicBadPart_on_cell (f : ℝ → ℂ) (s : Finset DyadicCell)
    (hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet)
    {j : DyadicCell} (hj : j ∈ s) {x : ℝ} (hx : x ∈ dyadicCellSet j) :
    dyadicBadPart f s x = f x - dyadicCellMean f j := by
  classical
  unfold dyadicBadPart
  rw [Finset.sum_eq_single j]
  · simp [hx]
  · intro i hi hij
    have hxi : x ∉ dyadicCellSet i := fun h => Set.disjoint_left.mp (hd hi hj hij) h hx
    simp [hxi]
  · exact fun h => (h hj).elim

theorem dyadicBadPart_outside (f : ℝ → ℂ) (s : Finset DyadicCell) {x : ℝ}
    (hx : x ∉ ⋃ j ∈ s, dyadicCellSet j) : dyadicBadPart f s x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hxj : x ∉ dyadicCellSet j := fun h => hx (Set.mem_iUnion₂.mpr ⟨j, hj, h⟩)
  simp [hxj]

theorem dyadicGoodPart_on_cell (f : ℝ → ℂ) (s : Finset DyadicCell)
    (hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet)
    {j : DyadicCell} (hj : j ∈ s) {x : ℝ} (hx : x ∈ dyadicCellSet j) :
    dyadicGoodPart f s x = dyadicCellMean f j := by
  rw [dyadicGoodPart, dyadicBadPart_on_cell f s hd hj hx, sub_sub_cancel]

theorem dyadicGoodPart_outside (f : ℝ → ℂ) (s : Finset DyadicCell) {x : ℝ}
    (hx : x ∉ ⋃ j ∈ s, dyadicCellSet j) : dyadicGoodPart f s x = f x := by
  rw [dyadicGoodPart, dyadicBadPart_outside f s hx, sub_zero]

theorem dyadicBadPart_integrable (f : ℝ → ℂ) (hf : Integrable f haarMeasure) (s : Finset DyadicCell) :
    Integrable (dyadicBadPart f s) haarMeasure :=
  integrable_finsetSum s (fun j _ => (hf.sub (integrable_const _)).indicator
    (dyadicCellSet_measurable j))

theorem dyadicGoodPart_integrable (f : ℝ → ℂ) (hf : Integrable f haarMeasure) (s : Finset DyadicCell) :
    Integrable (dyadicGoodPart f s) haarMeasure := hf.sub (dyadicBadPart_integrable f hf s)

theorem dyadicBadPart_memLp (p : ℝ≥0∞) (f : ℝ → ℂ) (hf : MemLp f p haarMeasure)
    (s : Finset DyadicCell) : MemLp (dyadicBadPart f s) p haarMeasure :=
  memLp_finsetSum s (fun j _ => (hf.sub (memLp_const _)).indicator (dyadicCellSet_measurable j))

theorem dyadicGoodPart_memLp (p : ℝ≥0∞) (f : ℝ → ℂ) (hf : MemLp f p haarMeasure)
    (s : Finset DyadicCell) : MemLp (dyadicGoodPart f s) p haarMeasure := hf.sub (dyadicBadPart_memLp p f hf s)

theorem dyadicBadPart_cell_integral_zero (f : ℝ → ℂ) (hf : Integrable f haarMeasure)
    (s : Finset DyadicCell) (hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet)
    {j : DyadicCell} (hj : j ∈ s) :
    (∫ x in dyadicCellSet j, dyadicBadPart f s x ∂haarMeasure) = 0 := by
  rw [setIntegral_congr_fun (dyadicCellSet_measurable j)
    (fun _ hx => dyadicBadPart_on_cell f s hd hj hx)]
  exact dyadicCellMean_sub_integral_zero f hf j

/-- The good part of the finite dyadic decomposition is bounded by twice
the threshold pointwise. The root-good case is used after the trivial
large-L¹-norm case has been separated. -/
theorem dyadicGoodPart_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ) {a : ℝ} (ha : 0 ≤ a)
    (hf : (∫ x, ‖dyadicStepValue N c x‖ ∂haarMeasure) ≤ a) (x : ℝ) :
    ‖dyadicGoodPart (dyadicStepValue N c)
      (maximalDyadicCells (dyadicBadCells N (dyadicStepValue N c) a)) x‖ ≤ 2 * a := by
  let f := dyadicStepValue N c
  let s := maximalDyadicCells (dyadicBadCells N f a)
  have hd : Set.PairwiseDisjoint (s : Set DyadicCell) dyadicCellSet :=
    fun _ hi _ hj hij => maximalDyadicCells_disjoint _ hi hj hij
  by_cases hx : x ∈ dyadicBadUnion N f a
  · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    rw [dyadicGoodPart_on_cell f s hd hj hxj]
    exact norm_dyadicCellMean_le_of_parent_good f (dyadicStepValue_integrable N c)
      (dyadic_selected_level_pos N f hf hj) (dyadic_selected_parent_good N f a hj
        (dyadic_selected_level_pos N f hf hj))
  · rw [dyadicGoodPart_outside f s hx]
    exact (dyadicStepValue_outside_bad_bound N c ha hx).trans (by linarith)

end SchauderTranslates.LpConstruction
