import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open ContinuousLinearMap Matrix
open scoped InnerProductSpace InnerProduct BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- A real coefficient metric acting on a finite family of Hilbert-space vectors. -/
def matrixEnergy (B : Matrix ι ι ℝ) (f : ι → K) : ℝ :=
  ∑ i, ∑ j, B i j * inner ℝ (f i) (f j)

/-- Apply a finite real matrix to a family of vectors. -/
def matrixVectorAction (D : Matrix ι ι ℝ) (f : ι → K) : ι → K :=
  fun i => ∑ j, D i j • f j

/-- The scalar quadratic form expanded as a double sum. -/
theorem coefficientQuadratic_real_sum (B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    coefficientQuadratic B x = ∑ i, ∑ j, B i j * x i * x j := by
  simp only [coefficientQuadratic_eq_dot, Matrix.mulVec, dotProduct,
    RCLike.re_to_real, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Parseval decomposes the vector-valued energy into scalar coefficient energies. -/
theorem matrixEnergy_orthonormalBasis (b : OrthonormalBasis κ ℝ K)
    (B : Matrix ι ι ℝ) (f : ι → K) :
    matrixEnergy B f = ∑ a, coefficientQuadratic B
      (WithLp.toLp 2 (fun i => inner ℝ (b a) (f i))) := by
  have hp (i j : ι) : inner ℝ (f i) (f j) =
      ∑ a, inner ℝ (b a) (f i) * inner ℝ (b a) (f j) := by
    rw [← b.sum_inner_mul_inner (f i) (f j)]
    apply Finset.sum_congr rfl
    intro a _
    rw [real_inner_comm (b a) (f i)]
  simp only [matrixEnergy, hp, Finset.mul_sum, coefficientQuadratic_real_sum]
  calc
    (∑ i, ∑ j, ∑ a, B i j * (inner ℝ (b a) (f i) * inner ℝ (b a) (f j))) =
        ∑ i, ∑ a, ∑ j, B i j * (inner ℝ (b a) (f i) * inner ℝ (b a) (f j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, B i j * (inner ℝ (b a) (f i) * inner ℝ (b a) (f j)) :=
      Finset.sum_comm
    _ = _ := by simp only [mul_assoc]

/-- Coordinates commute with the matrix action. -/
theorem matrixVectorAction_coordinate (b : OrthonormalBasis κ ℝ K)
    (D : Matrix ι ι ℝ) (f : ι → K) (a : κ) :
    WithLp.toLp 2 (fun i => inner ℝ (b a) (matrixVectorAction D f i)) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D
        (WithLp.toLp 2 (fun i => inner ℝ (b a) (f i))) := by
  ext i
  simp [matrixVectorAction, Matrix.mulVec, dotProduct,
    inner_sum, real_inner_smul_right]

/-- A scalar quadratic bound holds with the same constant for vector-valued coefficients. -/
theorem matrixEnergy_bound_of_scalar (b : OrthonormalBasis κ ℝ K)
    (B D : Matrix ι ι ℝ) (C : ℝ)
    (h : ∀ x : EuclideanSpace ℝ ι,
      coefficientQuadratic B ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D x) ≤
        C * coefficientQuadratic B x) (f : ι → K) :
    matrixEnergy B (matrixVectorAction D f) ≤ C * matrixEnergy B f := by
  rw [matrixEnergy_orthonormalBasis b, matrixEnergy_orthonormalBasis b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [matrixVectorAction_coordinate]
  exact h _

/-- The metric operator norm bounds its amplification to finitely many Hilbert coordinates. -/
theorem matrixEnergy_bound_of_gramConjugate (b : OrthonormalBasis κ ℝ K)
    {B : Matrix ι ι ℝ} (hB : B.PosDef) (D : Matrix ι ι ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ‖gramConjugate B D‖ ^ 2 ≤ C) (f : ι → K) :
    matrixEnergy B (matrixVectorAction D f) ≤ C * matrixEnergy B f := by
  apply matrixEnergy_bound_of_scalar b B D C _ f
  intro x
  have hx := (gramConjugate_bound_iff hB D hC).mp h x
  simpa only [gramRoot_norm_sq hB.posSemidef, coefficientQuadratic] using hx

end SchauderTranslates
