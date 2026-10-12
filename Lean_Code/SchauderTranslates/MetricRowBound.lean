import Lean_Code.SchauderTranslates.ExtendedRowSplit
import Lean_Code.SchauderTranslates.SplitRowMetric

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The precise endpoint bound and diagonal penalty for a cut in row `j`. -/
def metricRowBound (B : Matrix ι ι ℝ) (e : κ → ι) (j : ι) : ℝ :=
  max (‖metricPrefix B e‖ ^ 2)
    (‖metricPrefix B e + rankOne ℝ (metricColumn B j) (metricDual B j)‖ ^ 2) +
      (1 / 4) * (1 - B j j) * (B⁻¹ j j - 1)

theorem metricRowBound_ge_one {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j) : 1 ≤ metricRowBound B e j := by
  have hxy : inner ℝ (metricColumn B j) (metricDual B j) = 1 := by
    rw [real_inner_comm, metricDual_inner_column hB]; simp
  have hn := nextPrefix_norm_sq_ge_one _ _ _ (metricPrefix_column_zero hB e j hj) hxy
  have hc := rowSplit_cost_nonneg _ _ hxy (metricColumn_norm_sq_le_one hB.posSemidef hBI j)
  rw [metricColumn_norm_sq hB.posSemidef, metricDual_norm_sq hB.posSemidef] at hc
  unfold metricRowBound
  have hm := le_max_right (‖metricPrefix B e‖ ^ 2)
    (‖metricPrefix B e + rankOne ℝ (metricColumn B j) (metricDual B j)‖ ^ 2)
  nlinarith

/-- The two-dimensional projection parameter disappears from the uniform bound. -/
theorem metricSplitRow_quarter {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖metricSplitRow B e j t‖ ^ 2 ≤ metricRowBound B e j := by
  have h := real_row_split_quarter (metricPrefix B e) (metricColumn B j) (metricDual B j)
    (metricPrefix_idempotent hB e he) (metricPrefix_column_zero hB e j hj)
    (metricDual_prefix_zero hB e j hj)
    (by rw [real_inner_comm, metricDual_inner_column hB]; simp)
    (metricColumn_norm_sq_le_one hB.posSemidef hBI j) ht ht1
  simpa only [metricColumn_norm_sq hB.posSemidef, metricDual_norm_sq hB.posSemidef,
    metricRowBound, metricSplitRow] using h

/-- A complete active/inactive plane satisfies the same bound as its small split-row core. -/
theorem metricExtendedRow_quarter {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    (R : K →L[ℝ] K) (u : K) (hu : ‖u‖ = 1) (hRu : R u = 0)
    (huR : ∀ w, inner ℝ u (R w) = 0) (hR : ‖R‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖extendedSplitRowOperator (metricPrefix B e) (metricColumn B j) (metricDual B j)
      R u t (Real.sqrt (t * (1 - t)))‖ ^ 2 ≤ metricRowBound B e j :=
  extendedSplitRow_norm_sq_le _ _ _ _ _ _ _ hu hRu huR hR
    (metricRowBound_ge_one hB hBI e j hj) (metricSplitRow_quarter hB hBI e he j hj ht ht1)

end SchauderTranslates
