import Lean_Code.SchauderTranslates.ActivationWeight
import Lean_Code.SchauderTranslates.ActivationNorms

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The real part of a Hermitian complex matrix is a symmetric real matrix. -/
theorem hermitian_realPart {ι : Type*} [Fintype ι] {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    (B.map Complex.re).IsHermitian := by
  ext i j
  have he := congrArg Complex.re (hB.apply i j)
  change (B j i).re = (B i j).re
  simpa only [Complex.star_def, Complex.conj_re] using he

/-- Restricting a positive complex quadratic form to real coefficients preserves positivity. -/
theorem posDef_realPart {ι : Type*} [Fintype ι] {B : Matrix ι ι ℂ} (hB : B.PosDef) :
    (B.map Complex.re).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hermitian_realPart hB.isHermitian)
  intro x hx
  have hz : (fun i => (x i : ℂ)) ≠ 0 := by
    intro hz
    apply hx
    funext i
    have hi := congrArg Complex.re (congrFun hz i)
    simpa using hi
  have h := hB.re_dotProduct_pos hz
  change 0 < (star (fun i => (x i : ℂ)) ⬝ᵥ B *ᵥ (fun i => (x i : ℂ))).re at h
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.mul_re] using h

theorem posSemidef_realPart {ι : Type*} [Fintype ι] {B : Matrix ι ι ℂ} (hB : B.PosSemidef) :
    (B.map Complex.re).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hermitian_realPart hB.isHermitian)
  intro x
  have h := hB.re_dotProduct_nonneg (fun i => (x i : ℂ))
  change 0 ≤ (star (fun i => (x i : ℂ)) ⬝ᵥ B *ᵥ (fun i => (x i : ℂ))).re at h
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.mul_re] using h

namespace ScalarData
variable {d n : ℕ}

/-- Evenness makes every raw scalar Fourier Gram entry real. -/
theorem rawGram_real (s : ScalarData d n) (hs : s.IsEven) (i j : Unit ⊕ Fin n) :
    (s.rawGram i j).im = 0 := by
  change (inner ℂ (s.vector (s.augmentedFrequency i)) (s.vector (s.augmentedFrequency j))).im = 0
  rw [s.toTorusWeight.vector_inner]
  apply integral_real_of_neg_conj
  intro x
  rw [hs x, torus_character_neg_apply, torus_character_neg_apply]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

def realRawGram (s : ScalarData d n) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  s.rawGram.map Complex.re

theorem realRawGram_posDef (s : ScalarData d n) : s.realRawGram.PosDef :=
  posDef_realPart s.rawGram_posDef

theorem realRawGram_map (s : ScalarData d n) (hs : s.IsEven) :
    s.realRawGram.map Complex.ofReal = s.rawGram := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (s.rawGram_real hs i j).symm

/-- The raw coefficient Gram is a positive contraction before taking its real part. -/
theorem rawGram_le_one (s : ScalarData d n) : s.rawGram ≤ 1 := by
  let Φ := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)
  have h : Φ s.rawGram ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap (Φ s.rawGram) zero_le_one
      (matrixHilbert_nonneg s.rawGram_posDef.posSemidef)).mp s.rawGram_norm_le_one
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr h)
  rw [Matrix.le_iff]
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  change (Φ (1 - s.rawGram)).IsPositive
  simpa only [map_sub, map_one] using hp

theorem realRawGram_le_one (s : ScalarData d n) : s.realRawGram ≤ 1 := by
  have hp := posSemidef_realPart (Matrix.le_iff.mp s.rawGram_le_one)
  rw [Matrix.le_iff]
  convert! hp using 1
  ext i j
  simp [realRawGram, Matrix.one_apply, apply_ite Complex.re]

/-- Inversion commutes with the real coefficient representation when the Gram is real. -/
theorem realRawGram_inverse_map (s : ScalarData d n) (hs : s.IsEven) :
    s.rawGram⁻¹ = (s.realRawGram⁻¹).map Complex.ofReal := by
  apply Matrix.inv_eq_right_inv
  rw [← s.realRawGram_map hs]
  change s.realRawGram.map (Complex.ofRealHom : ℝ → ℂ) *
    s.realRawGram⁻¹.map (Complex.ofRealHom : ℝ → ℂ) = 1
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp s.realRawGram_posDef.isUnit)]
  simp


end ScalarData
end SchauderTranslates
