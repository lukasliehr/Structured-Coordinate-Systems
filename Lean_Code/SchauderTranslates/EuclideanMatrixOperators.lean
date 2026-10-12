import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- Rectangular matrices act on Euclidean coefficient spaces with their Hilbert norms. -/
def euclideanMatrixOperator (A : Matrix ι κ ℂ) : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
  A.toEuclideanLin.toContinuousLinearMap

@[simp] theorem euclideanMatrixOperator_apply (A : Matrix ι κ ℂ) (x : EuclideanSpace ℂ κ) :
    euclideanMatrixOperator A x = WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl

theorem euclideanMatrixOperator_square (A : Matrix ι ι ℂ) :
    euclideanMatrixOperator A = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A := rfl

theorem euclideanMatrixOperator_mul (A : Matrix ι κ ℂ) (B : Matrix κ ν ℂ) :
    euclideanMatrixOperator (A * B) = (euclideanMatrixOperator A).comp (euclideanMatrixOperator B) := by
  ext x i
  change ((A * B) *ᵥ x.ofLp) i = (A *ᵥ (B *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

theorem euclideanMatrixOperator_adjoint (A : Matrix ι κ ℂ) :
    (euclideanMatrixOperator A)† = euclideanMatrixOperator Aᴴ := by
  unfold euclideanMatrixOperator
  rw [← LinearMap.adjoint_toContinuousLinearMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem euclideanMatrixOperator_smul (c : ℂ) (A : Matrix ι κ ℂ) :
    euclideanMatrixOperator (c • A) = c • euclideanMatrixOperator A := by
  ext x i
  change ((c • A) *ᵥ x.ofLp) i = c * (A *ᵥ x.ofLp) i
  rw [Matrix.smul_mulVec]
  rfl

/-- A rectangular source sandwich is transported with both adjoints in the correct order. -/
theorem euclideanMatrixOperator_sandwich (S : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) :
    ((euclideanMatrixOperator S)†).comp ((euclideanMatrixOperator A).comp (euclideanMatrixOperator S)) =
      euclideanMatrixOperator (Sᴴ * A * S) := by
  rw [euclideanMatrixOperator_adjoint, euclideanMatrixOperator_mul,
    euclideanMatrixOperator_mul, comp_assoc]

end SchauderTranslates
