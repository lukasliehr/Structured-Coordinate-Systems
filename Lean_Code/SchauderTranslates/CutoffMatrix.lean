import Lean_Code.SchauderTranslates.CutoffBasis
import Lean_Code.SchauderTranslates.ActivationExhaustion
import Lean_Code.SchauderTranslates.OperatorMatrixPositive

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Finite raw Gram, retaining every old row over a symmetric circle window. -/
def cutoffGram (s : ScalarData d n) (p : ℝ) (N : ℕ) :
    Matrix ((Unit ⊕ Fin n) × CircleWindow N) ((Unit ⊕ Fin n) × CircleWindow N) ℂ :=
  basisOperatorMatrix (circleCutoffBasis (Unit ⊕ Fin n) N)
    (compressedOperator (s.activatedGram p) (circleCutoffSpace (Unit ⊕ Fin n) N))

/-- The finite matrix is exactly the product-weight Fourier Gram. -/
theorem cutoffGram_entry (s : ScalarData d n) (p : ℝ) (N : ℕ)
    (a c : (Unit ⊕ Fin n) × CircleWindow N) :
    s.cutoffGram p N a c = s.activatedMoment p a.1 c.1 a.2.1 c.2.1 := by
  unfold cutoffGram basisOperatorMatrix compressedOperator
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simp only [circleCutoffBasis_coe]
  exact s.activatedGram_fourier_entry p a.1 c.1 a.2.1 c.2.1

/-- The finite raw Gram is positive definite for the actual retained Fourier family. -/
theorem cutoffGram_posDef (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) : (s.cutoffGram p N).PosDef := by
  apply basisOperatorMatrix_posDef _ _ hb
  · intro x y
    rw [compressedOperator_inner]
    change inner ℂ (s.activatedGram p (x : ActivationSpace n)) (y : ActivationSpace n) =
      inner ℂ x ((circleCutoffSpace (Unit ⊕ Fin n) N).orthogonalProjectionOnto
        (s.activatedGram p (y : ActivationSpace n)))
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, s.activatedGram_symmetric]
  · exact compressedOperator_coercive (s.activatedGram p)
      (fun x => (s.activatedGram_bounds hb.le hfloor p x).1) _

/-- Each finite raw diagonal equals the unnormalized product-weight mass. -/
theorem cutoffGram_diagonal (s : ScalarData d n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (a : (Unit ⊕ Fin n) × CircleWindow N) :
    s.cutoffGram p N a a = ((1 - p * (1 - s.mass) : ℝ) : ℂ) := by
  rw [s.cutoffGram_entry, ← s.activatedGram_fourier_entry]
  change inner ℂ (circleRow (EuclideanSpace.single a.1 1) a.2.1)
    (activationOperator (activationSet p) (activationSet_measurable p)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram)
      (circleRow (EuclideanSpace.single a.1 1) a.2.1)) = _
  rw [circleRow_activation_diagonal _ hp0 hp1, s.rawGram_diagonal]
  push_cast
  ring

/-- Matrix inversion agrees exactly with inversion of the coercive compressed operator. -/
theorem cutoffGram_inverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) :
    (s.cutoffGram p N)⁻¹ = basisOperatorMatrix (circleCutoffBasis (Unit ⊕ Fin n) N)
      (s.cutoffInverse hb hfloor p N : circleCutoffSpace (Unit ⊕ Fin n) N →L[ℂ]
        circleCutoffSpace (Unit ⊕ Fin n) N) := by
  apply basisOperatorMatrix_inverse
  ext1 x
  exact (coerciveEquiv (compressedOperator (s.activatedGram p) (circleCutoffSpace (Unit ⊕ Fin n) N)) hb
    (compressedOperator_coercive (s.activatedGram p)
      (fun y => (s.activatedGram_bounds hb.le hfloor p y).1) _)).apply_symm_apply x

/-- The inverse bound is now a statement about the actual finite Fourier Gram entries. -/
theorem cutoffGram_inverse_diagonal_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (a : (Unit ⊕ Fin n) × CircleWindow N) :
    ((s.cutoffGram p N)⁻¹ a a).re ≤ 1 + p * ((s.rawGram⁻¹ a.1 a.1).re - 1) := by
  rw [s.cutoffGram_inverse hb hfloor]
  have ha : circleCutoffBasis (Unit ⊕ Fin n) N a =
      ⟨circleRow (EuclideanSpace.single a.1 1) a.2.1,
        circleRow_mem_cutoff _ _ N (Finset.mem_Icc.mp a.2.property)⟩ :=
    Subtype.ext (circleCutoffBasis_coe N a)
  change (inner ℂ (circleCutoffBasis (Unit ⊕ Fin n) N a)
    (s.cutoffInverse hb hfloor p N (circleCutoffBasis (Unit ⊕ Fin n) N a))).re ≤ _
  rw [ha]
  exact s.cutoffInverse_diagonal_le hb hfloor hp0 hp1 N a.1 a.2.1
    (Finset.mem_Icc.mp a.2.property)

/-- The finite Gram inverse uses the Euclidean operator norm. -/
theorem cutoffGram_inverse_norm_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := (Unit ⊕ Fin n) × CircleWindow N))
      (s.cutoffGram p N)⁻¹‖ ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹‖ := by
  rw [s.cutoffGram_inverse hb hfloor, basisOperatorMatrix_norm]
  exact s.cutoffInverse_norm_le hb hfloor p N

/-- The initial constant character's coordinate in every symmetric cutoff. -/
def cutoffConstantIndex (n N : ℕ) : (Unit ⊕ Fin n) × CircleWindow N :=
  (Sum.inl (), ⟨0, Finset.mem_Icc.mpr (by constructor <;> omega)⟩)

theorem cutoffGram_constant_inverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) :
    ((s.cutoffGram p N)⁻¹ (cutoffConstantIndex n N) (cutoffConstantIndex n N)).re =
      s.cutoffConstantInverse hb hfloor p N := by
  rw [s.cutoffGram_inverse hb hfloor]
  have ha : circleCutoffBasis (Unit ⊕ Fin n) N (cutoffConstantIndex n N) =
      ⟨circleRow (EuclideanSpace.single (Sum.inl ()) 1) 0,
        circleRow_mem_cutoff _ 0 N (by constructor <;> omega)⟩ :=
    Subtype.ext (circleCutoffBasis_coe N _)
  change (inner ℂ (circleCutoffBasis (Unit ⊕ Fin n) N (cutoffConstantIndex n N))
    (s.cutoffInverse hb hfloor p N (circleCutoffBasis (Unit ⊕ Fin n) N (cutoffConstantIndex n N)))).re = _
  rw [ha]
  rfl

end ScalarData
end SchauderTranslates
