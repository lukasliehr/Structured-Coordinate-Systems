import Lean_Code.SchauderTranslates.Lp.DyadicGoodBounds
import Lean_Code.SchauderTranslates.Lp.HaarValues

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def dyadicBadComponentLp (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure) (j : DyadicCell) : HaarLp 2 :=
  ((hf.sub (memLp_const (dyadicCellMean f j))).indicator (dyadicCellSet_measurable j)).toLp
    ((dyadicCellSet j).indicator (fun x => f x - dyadicCellMean f j))

theorem dyadicBadComponentLp_ae (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure) (j : DyadicCell) :
    (dyadicBadComponentLp f hf j : ℝ → ℂ) =ᵐ[haarMeasure]
      (dyadicCellSet j).indicator (fun x => f x - dyadicCellMean f j) := MemLp.coeFn_toLp _

theorem dyadicBadComponentLp_supported (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure) (j : DyadicCell) :
    SupportedOn (dyadicBadComponentLp f hf j) (dyadicCellSet j) := by
  filter_upwards [dyadicBadComponentLp_ae f hf j] with x hx
  intro hnot
  rw [hx, Set.indicator_of_notMem hnot]

theorem dyadicBadComponentLp_integral_zero (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure)
    (hfi : Integrable f haarMeasure) (j : DyadicCell) :
    (∫ x, dyadicBadComponentLp f hf j x ∂haarMeasure) = 0 := by
  rw [integral_congr_ae (dyadicBadComponentLp_ae f hf j),
    integral_indicator (dyadicCellSet_measurable j)]
  exact dyadicCellMean_sub_integral_zero f hfi j

def dyadicBadPartLp (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure) (s : Finset DyadicCell) : HaarLp 2 :=
  ∑ j ∈ s, dyadicBadComponentLp f hf j

theorem dyadicBadPartLp_ae (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure) (s : Finset DyadicCell) :
    (dyadicBadPartLp f hf s : ℝ → ℂ) =ᵐ[haarMeasure] dyadicBadPart f s := by
  have hall : ∀ᵐ x ∂haarMeasure, ∀ j ∈ s, dyadicBadComponentLp f hf j x =
      (dyadicCellSet j).indicator (fun y => f y - dyadicCellMean f j) x := by
    simp only [Filter.eventually_all_finset]
    intro j _
    filter_upwards [dyadicBadComponentLp_ae f hf j] with x hx
    exact hx
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s (dyadicBadComponentLp f hf)] with x hall hsum
  rw [show dyadicBadPartLp f hf s = ∑ j ∈ s, dyadicBadComponentLp f hf j from rfl, hsum]
  exact Finset.sum_congr rfl (fun j hj => hall j hj)

theorem dyadicBadComponentLp_inner_zero_of_constant (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure)
    (hfi : Integrable f haarMeasure) (i : HaarIndex) (j : DyadicCell) (z : ℂ)
    (hc : ∀ x ∈ dyadicCellSet j, haarValue i x = z) :
    inner ℂ (haarAtom 2 i) (dyadicBadComponentLp f hf j) = 0 := by
  apply haar_inner_zero_of_const_on_support _ _ (dyadicCellSet j) z _
    (dyadicBadComponentLp_supported f hf j) (dyadicBadComponentLp_integral_zero f hf hfi j)
  filter_upwards [haarAtom_ae_value 2 i] with x hx
  exact fun hxc => hx.trans (hc x hxc)

theorem dyadicBadPartLp_inner_constant_zero (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure)
    (hfi : Integrable f haarMeasure) (s : Finset DyadicCell) :
    inner ℂ (haarAtom 2 none) (dyadicBadPartLp f hf s) = 0 := by
  rw [dyadicBadPartLp, inner_sum]
  exact Finset.sum_eq_zero fun j _ =>
    dyadicBadComponentLp_inner_zero_of_constant f hf hfi none j 1 (fun _ _ => rfl)

theorem dyadicBadPartLp_inner_zero_of_not_contained (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure)
    (hfi : Integrable f haarMeasure) (s : Finset DyadicCell) (i : DyadicCell)
    (hnot : ∀ j ∈ s, ¬dyadicCellSet i ⊆ dyadicCellSet j) :
    inner ℂ (haarAtom 2 (some i)) (dyadicBadPartLp f hf s) = 0 := by
  rw [dyadicBadPartLp, inner_sum]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨z, hz⟩ := haarValue_constant_on_cell (hnot j hj)
  exact dyadicBadComponentLp_inner_zero_of_constant f hf hfi (some i) j z hz

theorem haar_supported_complex_smul {f : HaarLp 2} {S : Set ℝ} (hf : SupportedOn f S)
    (c : ℂ) : SupportedOn (c • f) S := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx hsmul
  intro hout
  rw [hsmul, Pi.smul_apply, hx hout, smul_zero]

/-- The multiplier of the mean-zero bad part is supported on the union
of its bad cells. Coarser Haar terms, including the constant, vanish. -/
theorem haar_bad_multiplier_supported (f : ℝ → ℂ) (hf : MemLp f 2 haarMeasure)
    (hfi : Integrable f haarMeasure) (s : Finset DyadicCell) (t : Finset HaarIndex)
    (a : HaarIndex → ℂ) :
    SupportedOn (haarL2Multiplier t a (dyadicBadPartLp f hf s)) (⋃ j ∈ s, dyadicCellSet j) := by
  classical
  rw [haarL2Multiplier_apply]
  apply SupportedOn.finset_sum
  intro i _
  rcases i with _ | k
  · rw [dyadicBadPartLp_inner_constant_zero f hf hfi, mul_zero, zero_smul]
    exact Eventually.of_forall fun _ _ => by simp
  · by_cases hcontain : ∃ j ∈ s, dyadicCellSet k ⊆ dyadicCellSet j
    · obtain ⟨j, hj, hsub⟩ := hcontain
      apply haar_supported_complex_smul
      apply (haarFunction_supported 2 k.1 k.2).mono
      exact fun _ hx => Set.mem_iUnion₂.mpr ⟨j, hj, hsub hx⟩
    · have hnot : ∀ j ∈ s, ¬dyadicCellSet k ⊆ dyadicCellSet j := by
        intro j hj hs
        exact hcontain ⟨j, hj, hs⟩
      rw [dyadicBadPartLp_inner_zero_of_not_contained f hf hfi s k hnot, mul_zero, zero_smul]
      exact Eventually.of_forall fun _ _ => by simp

end SchauderTranslates.LpConstruction
