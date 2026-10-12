import Lean_Code.SchauderTranslates.HilbertBlocks
import Lean_Code.SchauderTranslates.SkewDecomposition
import Lean_Code.SchauderTranslates.SplitRowModel
import Lean_Code.SchauderTranslates.RealComplexNorm
import Lean_Code.SchauderTranslates.SplitRowMetric

noncomputable section
open scoped InnerProductSpace InnerProduct MatrixOrder

namespace SchauderTranslates

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- An idempotent is a block row in its range/orthogonal-range decomposition. -/
theorem projection_block_representation (P : E →L[𝕜] E)
    (hP : ∀ x, P (P x) = P x) :
    ∃ Z : P.rangeᗮ →L[𝕜] P.range,
      P.range.orthogonalDecomposition.conjStarAlgEquiv P = hilbertBlockProjection Z := by
  let S := P.range
  let Z : Sᗮ →L[𝕜] S := (P.comp Sᗮ.subtypeL).codRestrict S
    (fun x => ⟨x, rfl⟩)
  refine ⟨Z, ?_⟩
  have hfix (x : S) : P (x : E) = x := by
    obtain ⟨y, hy⟩ := x.property
    change P y = (x : E) at hy
    rw [← hy]
    exact hP y
  ext x
  apply S.orthogonalDecomposition.symm.injective
  change S.orthogonalDecomposition.symm
    (S.orthogonalDecomposition (P (S.orthogonalDecomposition.symm x))) =
    S.orthogonalDecomposition.symm (hilbertBlockProjection Z x)
  simp only [LinearIsometryEquiv.symm_apply_apply, hilbertBlockProjection_apply,
    Submodule.orthogonalDecomposition_symm_apply]
  change P ((x.fst : E) + (x.snd : E)) = ((x.fst : E) + P (x.snd : E)) + 0
  rw [map_add, hfix, add_zero]

/-- The norm of a nonzero oblique projection is determined by its skew part. -/
theorem projection_norm_skew (P : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x)
    (hne : P ≠ 0) : ‖P‖ ^ 2 = 1 + ‖P - P†‖ ^ 2 := by
  have : Nontrivial P.range := by
    apply Submodule.nontrivial_iff_ne_bot.mpr
    intro h
    apply hne
    ext x
    have hx : P x ∈ P.range := ⟨x, rfl⟩
    simpa [h] using hx
  obtain ⟨Z, hZ⟩ := projection_block_representation P hP
  let e := P.range.orthogonalDecomposition
  have hn : ‖hilbertBlockProjection Z‖ = ‖P‖ := by
    rw [← hZ]
    exact hilbertConjugate_norm e P
  have hs : ‖hilbertBlockProjection Z - (hilbertBlockProjection Z)†‖ = ‖P - P†‖ := by
    rw [← hZ, ← hilbertConjugate_adjoint, ← map_sub]
    exact hilbertConjugate_norm e _
  rw [← hn, hilbertBlockProjection_norm_sq, ← hs, hilbertBlockProjection_skew_norm]

/-- Complementary nonzero projections have the same norm. The endpoints are excluded. -/
theorem complementary_projection_norm (P : E →L[𝕜] E)
    (hP : ∀ x, P (P x) = P x) (hne : P ≠ 0) (hid : P ≠ 1) :
    ‖1 - P‖ = ‖P‖ := by
  have hQ : ∀ x, (1 - P : E →L[𝕜] E) ((1 - P : E →L[𝕜] E) x) =
      (1 - P : E →L[𝕜] E) x := by
    intro x
    simp [map_sub, hP]
  have hQne : (1 - P : E →L[𝕜] E) ≠ 0 := sub_ne_zero.mpr (Ne.symm hid)
  have hp := projection_norm_skew P hP hne
  have hq := projection_norm_skew (1 - P) hQ hQne
  have hs : (1 - P : E →L[𝕜] E) - (1 - P)† = -(P - P†) := by
    simp only [map_sub, ContinuousLinearMap.adjoint_one]
    abel
  rw [hs, norm_neg] at hq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hq.trans hp.symm)

/-- The zero endpoint can be absorbed by taking the maximum with one. -/
theorem projection_max_norm_skew (P : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x) :
    max 1 (‖P‖ ^ 2) = 1 + ‖P - P†‖ ^ 2 := by
  by_cases h : P = 0
  · simp [h]
  · rw [projection_norm_skew P hP h, max_eq_right (by nlinarith [sq_nonneg ‖P - P†‖])]

theorem complementary_projection_norm_sq_le (P : E →L[𝕜] E)
    (hP : ∀ x, P (P x) = P x) : ‖1 - P‖ ^ 2 ≤ max 1 (‖P‖ ^ 2) := by
  by_cases hzero : P = 0
  · simp only [hzero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, max_eq_left zero_le_one]
    have h : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg (1 : E →L[𝕜] E)]
  by_cases hone : P = 1
  · simp [hone]
  rw [complementary_projection_norm P hP hzero hone]
  exact le_max_right _ _

section Real
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

/-- The split-row norm is bounded by the larger endpoint plus the exact row cost. -/
theorem real_row_split (P : H →L[ℝ] H) (x y : H)
    (hP : ∀ z, P (P z) = P z) (hPx : P x = 0)
    (hyP : ∀ z, inner ℝ y (P z) = 0) (hxy : inner ℝ x y = 1)
    (hm : ‖x‖ ^ 2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖splitRowOperator P x y t (Real.sqrt (t * (1 - t)))‖ ^ 2 ≤
      max (‖splitRowOperator P x y 0 0‖ ^ 2) (‖splitRowOperator P x y 1 0‖ ^ 2) +
        t * (1 - t) * (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  have hyx : inner ℝ y x = 1 := by rw [real_inner_comm, hxy]
  have hproj (r s : ℝ) (hs : s ^ 2 = r * (1 - r)) :=
    projection_norm_skew (splitRowOperator P x y r s)
      (splitRowOperator_idempotent P x y r s hP hPx hyP hyx hs)
      (splitRowOperator_ne_zero P x y r s hPx hyx)
  have hpt := hproj t (Real.sqrt (t * (1 - t)))
    (Real.sq_sqrt (mul_nonneg ht (sub_nonneg.mpr ht1)))
  have hp0 := hproj 0 0 (by norm_num)
  have hp1 := hproj 1 0 (by norm_num)
  have hJ1 : P - P† + rankTwoSkew x y =
      (P + InnerProductSpace.rankOne ℝ x y) - (P + InnerProductSpace.rankOne ℝ x y)† := by
    rw [map_add, rankOne_real_adjoint]
    unfold rankTwoSkew
    abel
  simp only [splitRowOperator_skew, zero_smul, add_zero, skewArrowhead_zero_norm] at hp0
  simp only [splitRowOperator_skew, one_smul, hJ1, skewArrowhead_zero_norm] at hp1
  have hc := split_row_skew_compression P x y hxy hm ht ht1
  rw [hpt, hp0, hp1]
  have he : max (1 + ‖P - P†‖ ^ 2)
      (1 + ‖(P + InnerProductSpace.rankOne ℝ x y) -
        (P + InnerProductSpace.rankOne ℝ x y)†‖ ^ 2) =
      1 + max (‖P - P†‖ ^ 2)
        (‖(P + InnerProductSpace.rankOne ℝ x y) -
          (P + InnerProductSpace.rankOne ℝ x y)†‖ ^ 2) := by
    exact max_add_add_left _ _ _
  rw [he]
  linarith

end Real
section Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The paper's selected-Gram quantity `F(t)`, using the Euclidean operator norm. -/
def splitRowQuantity (B : Matrix ι ι ℝ) (e : κ → ι) (j : ι) (t : ℝ) : ℝ :=
  ‖(gramRoot (metricSplitGram B e j t)).comp
    (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := κ ⊕ Unit)) (metricSplitGram B⁻¹ e j t)).comp
      (gramRoot (metricSplitGram B e j t)))‖

theorem splitRowQuantity_eq_norm {B : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (e : κ → ι) (j : ι) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    splitRowQuantity B e j t = ‖metricSplitRow B e j t‖ ^ 2 :=
  (metricSplitRow_norm_sq hB e j ht ht1).symm

/-- Real row splitting in the precise selected-Gram form used in the construction. -/
theorem real_matrix_row_split {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    splitRowQuantity B e j t ≤
      max (splitRowQuantity B e j 0) (splitRowQuantity B e j 1) +
        t * (1 - t) * (1 - B j j) * (B⁻¹ j j - 1) := by
  have hxy : inner ℝ (metricColumn B j) (metricDual B j) = 1 := by
    rw [real_inner_comm]
    simpa using metricDual_inner_column hB j j
  have h := real_row_split (metricPrefix B e) (metricColumn B j) (metricDual B j)
    (metricPrefix_idempotent hB e he) (metricPrefix_column_zero hB e j hj)
    (metricDual_prefix_zero hB e j hj) hxy (metricColumn_norm_sq_le_one hB.posSemidef hBI j)
    ht ht1
  rw [splitRowQuantity_eq_norm hB.posSemidef e j ht ht1,
    splitRowQuantity_eq_norm hB.posSemidef e j (t := 0) le_rfl zero_le_one,
    splitRowQuantity_eq_norm hB.posSemidef e j (t := 1) zero_le_one le_rfl]
  simpa only [metricSplitRow, metricColumn_norm_sq hB.posSemidef,
    metricDual_norm_sq hB.posSemidef, zero_mul, mul_zero, sub_self, Real.sqrt_zero] using h

end Matrix
end SchauderTranslates
