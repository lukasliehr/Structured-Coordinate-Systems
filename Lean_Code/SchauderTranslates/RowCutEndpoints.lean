import Lean_Code.SchauderTranslates.HilbertRowCut

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Scalar coordinate cut when the spatial projection acts by zero or one. -/
def endpointCoefficientCut (e : κ → ι) (j : ι) (δ : ℝ) (a : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := coordinateSelection e a + (δ * a j) • EuclideanSpace.single j 1

theorem familyRowCut_eigenvector (e : κ → ι) (j : ι) (F : K →L[ℝ] K)
    (v : K) (δ : ℝ) (hFv : F v = δ • v) (a : EuclideanSpace ℝ ι) :
    familyRowCut e j F (fun i => a i • v) =
      (fun i => endpointCoefficientCut e j δ a i • v) := by
  have hc (i) : familyCoordinateSelection e (fun i => a i • v) i =
      (coordinateSelection e a) i • v := by
    simpa using familyCoordinateSelection_plane e a 0 v 0 i
  ext i
  simp only [familyRowCut, Pi.add_apply, hc, map_smul, hFv, endpointCoefficientCut,
    PiLp.add_apply, PiLp.smul_apply]
  by_cases hij : i = j
  · subst i
    simp only [Pi.single_eq_same, PiLp.single_apply, Pi.single_eq_same, ite_true]
    module
  · simp [hij]

theorem activationEnergy_active_vector (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K)
    (v : K) (hQv : Q v = v) (a : EuclideanSpace ℝ ι) :
    activationEnergy B Q (fun i => a i • v) = coefficientQuadratic B a * ‖v‖ ^ 2 := by
  simp only [activationEnergy, map_smul, hQv, sub_self]
  rw [matrixEnergy_smul_vector]
  simp [matrixEnergy]

theorem activationEnergy_inactive_vector (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K)
    (v : K) (hQv : Q v = 0) (a : EuclideanSpace ℝ ι) :
    activationEnergy B Q (fun i => a i • v) = ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [activationEnergy, map_smul, hQv, smul_zero, sub_zero]
  rw [matrixEnergy_one]
  simp [matrixEnergy, norm_smul, EuclideanSpace.norm_sq_eq, mul_pow, Finset.sum_mul]

/-- Both active endpoint cuts inherit the same uniform row bound. -/
theorem endpointCoefficientCut_active_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {δ : ℝ} (hδ : δ = 0 ∨ δ = 1) (a : EuclideanSpace ℝ ι) :
    coefficientQuadratic B (endpointCoefficientCut e j δ a) ≤
      metricRowBound B e j * coefficientQuadratic B a := by
  have hz : coefficientQuadratic B (0 : EuclideanSpace ℝ ι) = 0 := by simp [coefficientQuadratic]
  rcases hδ with rfl | rfl
  · simpa [coefficientPlaneCut, endpointCoefficientCut, hz] using
      coefficientPlaneCut_energy_bound hB hBI e he j hj (t := 0) (by norm_num) (by norm_num) a 0
  · simpa [coefficientPlaneCut, endpointCoefficientCut, hz] using
      coefficientPlaneCut_energy_bound hB hBI e he j hj (t := 1) (by norm_num) (by norm_num) a 0

/-- Both inactive endpoint cuts also satisfy the same bound. -/
theorem endpointCoefficientCut_inactive_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    {δ : ℝ} (hδ : δ = 0 ∨ δ = 1) (a : EuclideanSpace ℝ ι) :
    ‖endpointCoefficientCut e j δ a‖ ^ 2 ≤ metricRowBound B e j * ‖a‖ ^ 2 := by
  have hz : coefficientQuadratic B (0 : EuclideanSpace ℝ ι) = 0 := by simp [coefficientQuadratic]
  rcases hδ with rfl | rfl
  · simpa [coefficientPlaneCut, endpointCoefficientCut, hz] using
      coefficientPlaneCut_energy_bound hB hBI e he j hj (t := 1) (by norm_num) (by norm_num) 0 a
  · simpa [coefficientPlaneCut, endpointCoefficientCut, hz] using
      coefficientPlaneCut_energy_bound hB hBI e he j hj (t := 0) (by norm_num) (by norm_num) 0 a

/-- Common eigenspaces, including zero-dimensional and zero-vector cases, satisfy the row bound. -/
theorem familyRowCut_common_eigenvector_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    (F Q : K →L[ℝ] K) (v : K) {δ : ℝ} (hδ : δ = 0 ∨ δ = 1)
    (hFv : F v = δ • v) (hQv : Q v = 0 ∨ Q v = v) (a : EuclideanSpace ℝ ι) :
    activationEnergy B Q (familyRowCut e j F (fun i => a i • v)) ≤
      metricRowBound B e j * activationEnergy B Q (fun i => a i • v) := by
  rw [familyRowCut_eigenvector e j F v δ hFv a]
  rcases hQv with hQv | hQv
  · rw [activationEnergy_inactive_vector B Q v hQv,
      activationEnergy_inactive_vector B Q v hQv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (endpointCoefficientCut_inactive_bound hB hBI e he j hj hδ a) (sq_nonneg _)
  · rw [activationEnergy_active_vector B Q v hQv,
      activationEnergy_active_vector B Q v hQv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (endpointCoefficientCut_active_bound hB hBI e he j hj hδ a) (sq_nonneg _)

end SchauderTranslates
