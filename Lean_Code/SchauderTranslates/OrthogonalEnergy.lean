import Lean_Code.SchauderTranslates.MatrixEnergy

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι η K : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

omit [DecidableEq ι] in
@[simp] theorem matrixEnergy_zero (B : Matrix ι ι ℝ) : matrixEnergy B (0 : ι → K) = 0 := by
  simp [matrixEnergy]

theorem matrixEnergy_one (f : ι → K) : matrixEnergy (1 : Matrix ι ι ℝ) f = ∑ i, ‖f i‖ ^ 2 := by
  simp [matrixEnergy, Matrix.one_apply]

omit [DecidableEq ι] in
/-- Orthogonal families add without cross terms for every real matrix metric. -/
theorem matrixEnergy_add_orthogonal (B : Matrix ι ι ℝ) (f g : ι → K)
    (h : ∀ i j, inner ℝ (f i) (g j) = 0) :
    matrixEnergy B (f + g) = matrixEnergy B f + matrixEnergy B g := by
  have h' (i j) : inner ℝ (g i) (f j) = 0 := by rw [real_inner_comm, h]
  simp [matrixEnergy, inner_add_left, inner_add_right, h, h', mul_add, Finset.sum_add_distrib]

/-- Pythagorean decomposition for a finite collection of mutually orthogonal vector families. -/
theorem matrixEnergy_sum_orthogonal [DecidableEq η] (B : Matrix ι ι ℝ)
    (f : η → ι → K) (s : Finset η)
    (h : ∀ a b, a ≠ b → ∀ i j, inner ℝ (f a i) (f b j) = 0) :
    matrixEnergy B (∑ a ∈ s, f a) = ∑ a ∈ s, matrixEnergy B (f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, matrixEnergy_add_orthogonal, ih, Finset.sum_insert ha]
    intro i j
    simp only [Finset.sum_apply, inner_sum]
    apply Finset.sum_eq_zero
    intro b hb
    exact h a b (fun hab => ha (hab ▸ hb)) i j

/-- Energy of a coefficient vector carried by one spatial direction. -/
theorem matrixEnergy_smul_vector (B : Matrix ι ι ℝ) (a : EuclideanSpace ℝ ι) (v : K) :
    matrixEnergy B (fun i => a i • v) = coefficientQuadratic B a * ‖v‖ ^ 2 := by
  simp only [matrixEnergy, coefficientQuadratic_real_sum, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An activation projection uses `B` on its range and the identity on its kernel. -/
def activationEnergy (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K) (f : ι → K) : ℝ :=
  matrixEnergy B (fun i => Q (f i)) + matrixEnergy 1 (fun i => f i - Q (f i))

theorem activationEnergy_add_orthogonal (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K)
    (f g : ι → K)
    (hQ : ∀ i j, inner ℝ (Q (f i)) (Q (g j)) = 0)
    (hI : ∀ i j, inner ℝ (f i - Q (f i)) (g j - Q (g j)) = 0) :
    activationEnergy B Q (f + g) = activationEnergy B Q f + activationEnergy B Q g := by
  have he : (fun i => (f + g) i - Q ((f + g) i)) =
      (fun i => f i - Q (f i)) + (fun i => g i - Q (g i)) := by
    ext i
    simp only [Pi.add_apply, map_add]
    abel
  have hq : (fun i => Q ((f + g) i)) = (fun i => Q (f i)) + (fun i => Q (g i)) := by
    ext i
    simp
  simp only [activationEnergy, he, hq, matrixEnergy_add_orthogonal _ _ _ hQ,
    matrixEnergy_add_orthogonal _ _ _ hI]
  ring

/-- The energy on an active/inactive orthonormal pair has the coefficient form used above. -/
theorem activationEnergy_plane (B : Matrix ι ι ℝ) (Q : K →L[ℝ] K)
    (v w : K) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hQv : Q v = v) (hQw : Q w = 0) (a b : EuclideanSpace ℝ ι) :
    activationEnergy B Q (fun i => a i • v + b i • w) =
      coefficientQuadratic B a + ‖b‖ ^ 2 := by
  have hq : (fun i => Q (a i • v + b i • w)) = (fun i => a i • v) := by
    ext i
    simp [hQv, hQw]
  have hi : (fun i => a i • v + b i • w - Q (a i • v + b i • w)) =
      (fun i => b i • w) := by
    ext i
    simp [hQv, hQw]
  rw [activationEnergy, hq, hi, matrixEnergy_smul_vector, matrixEnergy_one, hv]
  simp [norm_smul, hw, EuclideanSpace.norm_sq_eq]

end SchauderTranslates
