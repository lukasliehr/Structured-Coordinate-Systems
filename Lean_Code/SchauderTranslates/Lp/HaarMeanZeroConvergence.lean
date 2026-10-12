import Lean_Code.SchauderTranslates.Lp.HaarMeanZeroModel

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Adding the constant to finite mean-zero index sets is cofinal in
the finite full Haar index sets. -/
theorem haar_meanZero_finsets_cofinal :
    Tendsto (fun s : Finset HaarMeanZeroIndex => insert none (s.image some)) atTop atTop := by
  classical
  refine (show Monotone (fun s : Finset HaarMeanZeroIndex => insert none (s.image some)) from
    fun _ _ h => Finset.insert_subset_insert none (Finset.image_mono some h)).tendsto_atTop_finset ?_
  intro i
  cases i with
  | none => exact ⟨∅, by simp⟩
  | some i => exact ⟨{i}, by simp⟩

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haar_meanZero_finset_tendsto (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : haarMeanZero p q) :
    Tendsto (fun s : Finset HaarMeanZeroIndex =>
      ∑ i ∈ s, haarMeanZeroCoordinate p q i f • haarMeanZeroAtom p q i) atTop (𝓝 f) := by
  classical
  have ht := (haar_normalized_finset_tendsto p q hp2 hpfin (f : HaarLp p)).comp
    haar_meanZero_finsets_cofinal
  have he (s : Finset HaarMeanZeroIndex) :
      (∑ i ∈ insert none (s.image some),
        haarNormalizedCoordinate p q i (f : HaarLp p) • haarNormalizedAtom p i) =
        ((∑ i ∈ s, haarMeanZeroCoordinate p q i f • haarMeanZeroAtom p q i : haarMeanZero p q) :
          HaarLp p) := by
    rw [Finset.sum_insert (by simp), haarNormalizedCoordinate_none_meanZero, zero_smul, zero_add,
      Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp [haarMeanZeroCoordinate, haarMeanZeroAtom, Submodule.coe_sum]
  apply tendsto_subtype_rng.mpr
  exact ht.congr (fun s => he s)

theorem haar_meanZero_finite_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (s : Finset HaarMeanZeroIndex) (w : HaarMeanZeroIndex → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) (f : haarMeanZero p q) :
    ‖∑ i ∈ s, (w i * haarMeanZeroCoordinate p q i f) • haarMeanZeroAtom p q i‖ ≤
      haarStrongConstant q.toReal * ‖f‖ := by
  classical
  let w' : HaarIndex → ℂ := fun i => match i with
    | none => 0
    | some i => w i
  have hw' : ∀ i ∈ s.image some, ‖w' i‖ ≤ 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hw j hj
  have hb := haar_normalized_finite_bound p q hp2 hpfin (s.image some) w' hw' (f : HaarLp p)
  rw [Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)] at hb
  change ‖((∑ i ∈ s, (w i * haarMeanZeroCoordinate p q i f) • haarMeanZeroAtom p q i :
    haarMeanZero p q) : HaarLp p)‖ ≤ haarStrongConstant q.toReal * ‖f‖
  simpa only [w', haarMeanZeroCoordinate, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_sum, Submodule.coe_smul, haarMeanZeroAtom,
    Submodule.norm_coe] using hb

end SchauderTranslates.LpConstruction
