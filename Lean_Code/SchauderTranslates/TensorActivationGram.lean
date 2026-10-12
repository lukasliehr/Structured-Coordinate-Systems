import Lean_Code.SchauderTranslates.ProjectionRowBound

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι ν K : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Synthesize one spatial function for each row from a rectangular coefficient array. -/
def rowSynthesis (u : ν → K) (c : EuclideanSpace ℝ (ι × ν)) : ι → K :=
  fun i => ∑ a, c (i, a) • u a

/-- The finite Gram for the active metric and the inactive identity metric. -/
def tensorActivationGram (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K) (u : ν → K) :
    Matrix (ι × ν) (ι × ν) ℝ := fun a b =>
  B a.1 b.1 * inner ℝ (Q (u a.2)) (Q (u b.2)) +
    (if a.1 = b.1 then 1 else 0) * inner ℝ (u a.2 - Q (u a.2)) (u b.2 - Q (u b.2))

/-- A vector-family Gram is precisely the quadratic energy of its row synthesis. -/
theorem matrixEnergy_rowSynthesis (B : Matrix ι ι ℝ) (u : ν → K)
    (c : EuclideanSpace ℝ (ι × ν)) :
    matrixEnergy B (rowSynthesis u c) = coefficientQuadratic
      (fun a b : ι × ν => B a.1 b.1 * inner ℝ (u a.2) (u b.2)) c := by
  have hi (i j : ι) : inner ℝ (rowSynthesis u c i) (rowSynthesis u c j) =
      ∑ a, ∑ b, c (i,a) * c (j,b) * inner ℝ (u a) (u b) := by
    change inner ℝ (∑ a, c (i,a) • u a) (∑ b, c (j,b) • u b) = _
    rw [sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [matrixEnergy, hi, Finset.mul_sum, coefficientQuadratic_real_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The two-projection energy equals the actual finite tensor coefficient quadratic form. -/
theorem activationEnergy_rowSynthesis (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K)
    (u : ν → K) (c : EuclideanSpace ℝ (ι × ν)) :
    activationEnergy B Q (rowSynthesis u c) = coefficientQuadratic (tensorActivationGram B Q u) c := by
  have hq : (fun i => Q (rowSynthesis u c i)) = rowSynthesis (fun a => Q (u a)) c := by
    ext i
    simp [rowSynthesis]
  have hi : (fun i => rowSynthesis u c i - Q (rowSynthesis u c i)) =
      rowSynthesis (fun a => u a - Q (u a)) c := by
    ext i
    simp [rowSynthesis, Finset.sum_sub_distrib, smul_sub]
  rw [activationEnergy, hq, hi, matrixEnergy_rowSynthesis, matrixEnergy_rowSynthesis]
  simp only [coefficientQuadratic_real_sum, tensorActivationGram, Matrix.one_apply,
    add_mul, Finset.sum_add_distrib]

end SchauderTranslates
