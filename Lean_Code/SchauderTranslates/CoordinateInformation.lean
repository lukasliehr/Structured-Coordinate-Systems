import Lean_Code.SchauderTranslates.ProjectionInformation
import Lean_Code.SchauderTranslates.EuclideanMatrixOperators

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coordinateMask (i₀ : ι) : Matrix ι ι ℂ := Matrix.diagonal (fun i => if i = i₀ then 1 else 0)
def coordinateComplementMask (i₀ : ι) : Matrix ι ι ℂ := Matrix.diagonal (fun i => if i = i₀ then 0 else 1)

theorem coordinateMasks_products (i₀ : ι) :
    coordinateComplementMask i₀ * coordinateComplementMask i₀ = coordinateComplementMask i₀ ∧
      coordinateMask i₀ * coordinateMask i₀ = coordinateMask i₀ ∧
      coordinateComplementMask i₀ * coordinateMask i₀ = 0 ∧
      coordinateMask i₀ * coordinateComplementMask i₀ = 0 := by
  constructor
  · simp only [coordinateComplementMask, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  constructor
  · simp only [coordinateMask, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  constructor <;>
    simp [coordinateComplementMask, coordinateMask, Matrix.diagonal_mul_diagonal, mul_ite, ite_mul] <;>
    funext i <;> split_ifs <;> rfl

theorem informationSandwich_zero (φ : ι → H) : informationSandwich φ (0 : Matrix ι ι ℂ) = 0 := by
  simp [informationSandwich]

theorem informationSandwich_smul (φ : ι → H) (c : ℂ) (A : Matrix ι ι ℂ) :
    informationSandwich φ (c • A) = c • informationSandwich φ A := by
  simp [informationSandwich, smul_comp, comp_smul]

/-- The two coordinate projections, on the whole ambient Hilbert space. -/
def familyCoordinateProjection (φ : ι → H) (i₀ : ι) : H →L[ℂ] H :=
  informationSandwich φ (coordinateMask i₀)

def familyCoordinateComplement (φ : ι → H) (i₀ : ι) : H →L[ℂ] H :=
  informationSandwich φ (coordinateComplementMask i₀)

theorem familyCoordinate_products (φ : ι → H) (hφ : Matrix.gram ℂ φ = 1) (i₀ : ι) :
    familyCoordinateComplement φ i₀ * familyCoordinateComplement φ i₀ = familyCoordinateComplement φ i₀ ∧
      familyCoordinateProjection φ i₀ * familyCoordinateProjection φ i₀ = familyCoordinateProjection φ i₀ ∧
      familyCoordinateComplement φ i₀ * familyCoordinateProjection φ i₀ = 0 ∧
      familyCoordinateProjection φ i₀ * familyCoordinateComplement φ i₀ = 0 := by
  obtain ⟨hpp, hqq, hpq, hqp⟩ := coordinateMasks_products i₀
  simp only [familyCoordinateProjection, familyCoordinateComplement, informationSandwich_mul,
    hφ, Matrix.mul_one, hpp, hqq, hpq, hqp, informationSandwich_zero, and_self]

theorem informationSandwich_two_values (φ : ι → H) (i₀ : ι) (a b : ℂ) :
    informationSandwich φ (Matrix.diagonal (fun i => if i = i₀ then b else a)) =
      a • familyCoordinateComplement φ i₀ + b • familyCoordinateProjection φ i₀ := by
  have he : Matrix.diagonal (fun i => if i = i₀ then b else a) =
      a • coordinateComplementMask i₀ + b • coordinateMask i₀ := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> by_cases hi : i = i₀ <;>
      simp_all [coordinateMask, coordinateComplementMask, Matrix.diagonal_apply,
        Matrix.smul_apply]
  rw [he, informationSandwich_add, informationSandwich_smul, informationSandwich_smul]
  rfl

theorem familyCoordinateProjection_apply (φ : ι → H) (i₀ : ι) (h : H) :
    familyCoordinateProjection φ i₀ h = inner ℂ (φ i₀) h • φ i₀ := by
  simp [familyCoordinateProjection, informationSandwich, coordinateMask,
    hilbertSynthesis_apply, hilbertSynthesis_adjoint_apply, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct, Matrix.diagonal_apply, mul_ite, ite_mul]

/-- Information coefficients on an orthonormal carrier, recovered from the actual
capture equation on the whole ambient Hilbert space. -/
theorem coordinate_information_from_capture {τ : Type*} [Fintype τ] [DecidableEq τ]
    (v : τ → H) {C : Matrix τ τ ℂ} (hC : C.PosDef)
    (φ : ι → H) (hφ : Matrix.gram ℂ φ = 1) (i₀ : ι) (M x y : ℝ)
    (hM : 0 < M) (hx : x < M) (hy : y < M)
    (hc : captureOperator v C = (M : ℂ)⁻¹ •
      informationSandwich φ (Matrix.diagonal (fun i => if i = i₀ then (y : ℂ) else (x : ℂ)))) :
    informationOperator v C =
      ((x / (M - x) : ℝ) : ℂ) • familyCoordinateComplement φ i₀ +
      ((y / (M - y) : ℝ) : ℂ) • familyCoordinateProjection φ i₀ := by
  obtain ⟨hp, hq, hpq, hqp⟩ := familyCoordinate_products φ hφ i₀
  have he : captureOperator v C = ((x : ℂ) / (M : ℂ)) • familyCoordinateComplement φ i₀ +
      ((y : ℂ) / (M : ℂ)) • familyCoordinateProjection φ i₀ := by
    rw [hc, informationSandwich_two_values, smul_add, smul_smul, smul_smul]
    simp only [div_eq_mul_inv, mul_comm]
  apply information_of_normalized_capture hp hq hpq hqp M x y hM hx hy
  have h := (information_capture_equations v hC).1
  rwa [he] at h

end SchauderTranslates
