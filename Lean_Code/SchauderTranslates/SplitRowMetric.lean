import Lean_Code.SchauderTranslates.MetricColumns
import Lean_Code.SchauderTranslates.SplitRowGram

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The old coordinate projection in the positive metric. -/
def metricPrefix (B : Matrix ι ι ℝ) (e : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  gramConjugate B (selectionColumns (𝕜 := ℝ) e * (selectionColumns (𝕜 := ℝ) e).conjTranspose)

/-- The paper's split-row operator in its original coefficient metric. -/
def metricSplitRow (B : Matrix ι ι ℝ) (e : κ → ι) (j : ι) (t : ℝ) :
    WithLp 2 (EuclideanSpace ℝ ι × ℝ) →L[ℝ] WithLp 2 (EuclideanSpace ℝ ι × ℝ) :=
  splitRowOperator (metricPrefix B e) (metricColumn B j) (metricDual B j)
    t (Real.sqrt (t * (1 - t)))

/-- The matrix `C_t`; substituting the inverse metric gives `D_t`. -/
def metricSplitGram (B : Matrix ι ι ℝ) (e : κ → ι) (j : ι) (t : ℝ) :
    Matrix (κ ⊕ Unit) (κ ⊕ Unit) ℝ :=
  splitGram (B.submatrix e e) (fun i => B (e i) j) (B j j) t

theorem metricPrefix_as_sum {B : Matrix ι ι ℝ} (hB : B.PosSemidef) (e : κ → ι) :
    metricPrefix B e = ∑ i, rankOne ℝ (metricColumn B (e i)) (metricDual B (e i)) :=
  (metric_prefix_sum hB e).symm

theorem metricPrefix_idempotent {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (he : Function.Injective e) :
    ∀ z, metricPrefix B e (metricPrefix B e z) = metricPrefix B e z := by
  rw [metricPrefix_as_sum hB.posSemidef]
  apply biorthogonal_rankOne_idempotent
  intro i j
  rw [metricDual_inner_column hB]
  simp only [he.eq_iff]

theorem metricPrefix_column_zero {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j) :
    metricPrefix B e (metricColumn B j) = 0 := by
  rw [metricPrefix_as_sum hB.posSemidef]
  simp [sum_apply, rankOne_apply, metricDual_inner_column hB, hj]

theorem metricDual_prefix_zero {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j) (z : EuclideanSpace ℝ ι) :
    inner ℝ (metricDual B j) (metricPrefix B e z) = 0 := by
  rw [metricPrefix_as_sum hB.posSemidef]
  have hj' (i : κ) : j ≠ e i := (hj i).symm
  simp [sum_apply, rankOne_apply, inner_sum, real_inner_smul_right,
    metricDual_inner_column hB, hj']

theorem metricSplitRow_idempotent {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ z, metricSplitRow B e j t (metricSplitRow B e j t z) = metricSplitRow B e j t z := by
  apply splitRowOperator_idempotent
  · exact metricPrefix_idempotent hB e he
  · exact metricPrefix_column_zero hB e j hj
  · exact metricDual_prefix_zero hB e j hj
  · simpa using metricDual_inner_column hB j j
  · exact Real.sq_sqrt (mul_nonneg ht (sub_nonneg.mpr ht1))

theorem metricSplitRow_ne_zero {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j) (t : ℝ) :
    metricSplitRow B e j t ≠ 0 :=
  splitRowOperator_ne_zero _ _ _ _ _ (metricPrefix_column_zero hB e j hj)
    (by simpa using metricDual_inner_column hB j j)

/-- Exact equality with the two displayed Gram compressions of the paper. -/
theorem metricSplitRow_norm_sq {B : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (e : κ → ι) (j : ι) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖metricSplitRow B e j t‖ ^ 2 =
      ‖(gramRoot (metricSplitGram B e j t)).comp
        (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := κ ⊕ Unit)) (metricSplitGram B⁻¹ e j t)).comp
          (gramRoot (metricSplitGram B e j t)))‖ := by
  have h := splitRow_norm_gram (fun i => metricColumn B (e i))
    (fun i => metricDual B (e i)) (metricColumn B j) (metricDual B j) ht ht1
  rw [metric_prefix_sum hB, metricColumn_gram hB, metricDual_gram hB,
    metricColumn_norm_sq hB, metricDual_norm_sq hB] at h
  simp only [metricColumn_inner hB, metricDual_inner hB] at h
  exact h

/-- The split-row formula, with every coordinate and endpoint condition explicit. -/
theorem split_row_projection {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ z, metricSplitRow B e j t (metricSplitRow B e j t z) = metricSplitRow B e j t z) ∧
    metricSplitRow B e j t ≠ 0 ∧
    ‖metricSplitRow B e j t‖ ^ 2 =
      ‖(gramRoot (metricSplitGram B e j t)).comp
        (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := κ ⊕ Unit)) (metricSplitGram B⁻¹ e j t)).comp
          (gramRoot (metricSplitGram B e j t)))‖ :=
  ⟨metricSplitRow_idempotent hB e he j hj ht ht1, metricSplitRow_ne_zero hB e j hj t,
    metricSplitRow_norm_sq hB.posSemidef e j ht ht1⟩

end SchauderTranslates
