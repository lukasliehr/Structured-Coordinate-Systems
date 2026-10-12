import Lean_Code.SchauderTranslates.MetricRowBound
import Lean_Code.SchauderTranslates.CoordinateSelection

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A row cut on an active/inactive two-projection plane, in original coefficients. -/
def coefficientPlaneCut (e : κ → ι) (j : ι) (t s : ℝ)
    (a b : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  (coordinateSelection e a + (t * a j + s * b j) • EuclideanSpace.single j 1,
    coordinateSelection e b + (s * a j + (1 - t) * b j) • EuclideanSpace.single j 1)

/-- The metric square root turns the coefficient cut into the already bounded split operator. -/
theorem coefficientPlaneCut_conjugacy {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (j : ι) (t s : ℝ) (a b : EuclideanSpace ℝ ι) :
    extendedSplitRowOperator (metricPrefix B e) (metricColumn B j) (metricDual B j)
      (coordinateSelection e) (EuclideanSpace.single j 1) t s
        (WithLp.toLp 2 (gramRoot B a, b)) =
      WithLp.toLp 2 (gramRoot B (coefficientPlaneCut e j t s a b).1,
        (coefficientPlaneCut e j t s a b).2) := by
  rw [extendedSplitRowOperator_apply]
  simp only [coefficientPlaneCut, metricColumn, map_add, map_smul]
  change WithLp.toLp 2
    (metricPrefix B e (gramRoot B a) +
      (t * inner ℝ (metricDual B j) (gramRoot B a) +
        s * inner ℝ (EuclideanSpace.single j 1) b) • gramRoot B (EuclideanSpace.single j 1),
      coordinateSelection e b +
        (s * inner ℝ (metricDual B j) (gramRoot B a) +
          (1 - t) * inner ℝ (EuclideanSpace.single j 1) b) • EuclideanSpace.single j 1) = _
  simp [metricPrefix_root_apply hB, metricDual_inner_root hB, EuclideanSpace.inner_single_left]

/-- Each complete plane satisfies precisely the diagonal-penalty bound in the paper. -/
theorem coefficientPlaneCut_energy_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : EuclideanSpace ℝ ι) :
    coefficientQuadratic B (coefficientPlaneCut e j t (Real.sqrt (t * (1 - t))) a b).1 +
      ‖(coefficientPlaneCut e j t (Real.sqrt (t * (1 - t))) a b).2‖ ^ 2 ≤
        metricRowBound B e j * (coefficientQuadratic B a + ‖b‖ ^ 2) := by
  let T := extendedSplitRowOperator (metricPrefix B e) (metricColumn B j) (metricDual B j)
    (coordinateSelection e) (EuclideanSpace.single j 1) t (Real.sqrt (t * (1 - t)))
  have hT : ‖T‖ ^ 2 ≤ metricRowBound B e j :=
    metricExtendedRow_quarter hB hBI e he j hj _ _ (by simp)
      (coordinateSelection_single_zero e j hj) (coordinateSelection_inner_zero e j hj)
      (coordinateSelection_norm_le_one e he) ht ht1
  have hpoint := pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (WithLp.toLp 2 (gramRoot B a, b))) 2
  rw [mul_pow] at hpoint
  have hbound := hpoint.trans (mul_le_mul_of_nonneg_right hT (sq_nonneg _))
  change ‖extendedSplitRowOperator _ _ _ _ _ _ _ (WithLp.toLp 2 (gramRoot B a, b))‖ ^ 2 ≤ _ at hbound
  rw [coefficientPlaneCut_conjugacy hB, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2] at hbound
  change ‖gramRoot B (coefficientPlaneCut e j t (Real.sqrt (t * (1 - t))) a b).1‖ ^ 2 +
    ‖(coefficientPlaneCut e j t (Real.sqrt (t * (1 - t))) a b).2‖ ^ 2 ≤
      metricRowBound B e j * (‖gramRoot B a‖ ^ 2 + ‖b‖ ^ 2) at hbound
  simpa only [gramRoot_norm_sq hB.posSemidef, coefficientQuadratic] using hbound

end SchauderTranslates
