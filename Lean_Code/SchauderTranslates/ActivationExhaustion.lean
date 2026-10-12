import Lean_Code.SchauderTranslates.ActivationInverse
import Lean_Code.SchauderTranslates.CircleCutoffs
import Lean_Code.SchauderTranslates.ActivationNorms
import Lean_Code.SchauderTranslates.CompressedInverseNorm

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- The inverse of the actual compression to a finite symmetric Fourier window. -/
def cutoffInverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) :
    circleCutoffSpace (Unit ⊕ Fin n) N ≃L[ℂ] circleCutoffSpace (Unit ⊕ Fin n) N :=
  (coerciveEquiv (compressedOperator (s.activatedGram p) (circleCutoffSpace (Unit ⊕ Fin n) N)) hb
    (compressedOperator_coercive (s.activatedGram p)
      (fun x => (s.activatedGram_bounds hb.le hfloor p x).1) _)).symm

/-- Individual inverse diagonals are bounded uniformly in the retained Fourier window. -/
theorem cutoffInverse_diagonal_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (i : Unit ⊕ Fin n) (k : ℤ) (hk : -(N : ℤ) ≤ k ∧ k ≤ N) :
    let v : circleCutoffSpace (Unit ⊕ Fin n) N :=
      ⟨circleRow (EuclideanSpace.single i 1) k, circleRow_mem_cutoff i k N hk⟩
    (inner ℂ v (s.cutoffInverse hb hfloor p N v)).re ≤
      1 + p * ((s.rawGram⁻¹ i i).re - 1) := by
  dsimp only
  have h := inverse_compression (s.activatedGram p) hb
    (fun x => (s.activatedGram_bounds hb.le hfloor p x).1) (s.activatedGram_symmetric p)
    (circleCutoffSpace (Unit ⊕ Fin n) N)
    ⟨circleRow (EuclideanSpace.single i 1) k, circleRow_mem_cutoff i k N hk⟩
  rw [s.activated_coercive_inverse hb hfloor, s.activatedInverse_diagonal hp0 hp1] at h
  simpa only [cutoffInverse, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero] using! h

/-- The norm of every finite augmented inverse is bounded by the old inverse norm. -/
theorem cutoffInverse_norm_le (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) :
    ‖(s.cutoffInverse hb hfloor p N : circleCutoffSpace (Unit ⊕ Fin n) N →L[ℂ]
      circleCutoffSpace (Unit ⊕ Fin n) N)‖ ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹‖ := by
  have hBC (x : ActivationSpace n) : s.activatedGram p (s.activatedInverse p x) = x :=
    congrArg (fun T : ActivationSpace n →L[ℂ] ActivationSpace n => T x)
      (s.activatedGram_inverse p).1
  exact (compressed_inverse_norm_le (s.activatedGram p) (s.activatedInverse p) hb
    (fun x => (s.activatedGram_bounds hb.le hfloor p x).1) (s.activatedGram_symmetric p)
    hBC (circleCutoffSpace (Unit ⊕ Fin n) N)).trans (s.activatedInverse_norm_le p)

/-- Inverse constant entry in the finite raw compression. -/
def cutoffConstantInverse (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) : ℝ :=
  let v : circleCutoffSpace (Unit ⊕ Fin n) N :=
    ⟨circleRow (EuclideanSpace.single (Sum.inl ()) 1) 0,
      circleRow_mem_cutoff _ 0 N (by constructor <;> omega)⟩
  (inner ℂ v (s.cutoffInverse hb hfloor p N v)).re

/-- Concrete symmetric Fourier cutoffs exhaust the full inverse constant entry monotonically. -/
theorem cutoffConstantInverse_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (s.cutoffConstantInverse hb hfloor p) ∧
      Tendsto (s.cutoffConstantInverse hb hfloor p) atTop
        (𝓝 (1 + p * ((s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re - 1))) := by
  have hv (N : ℕ) : circleRow (EuclideanSpace.single (Sum.inl ()) 1) 0 ∈
      circleCutoffSpace (Unit ⊕ Fin n) N :=
    circleRow_mem_cutoff _ 0 N (by constructor <;> omega)
  have h := inverse_compression_exhaustion (s.activatedGram p) hb
    (fun x => (s.activatedGram_bounds hb.le hfloor p x).1) (s.activatedGram_symmetric p)
    (circleCutoffSpace (Unit ⊕ Fin n)) circleCutoffSpace_mono circleCutoffSpace_dense
    (circleRow (EuclideanSpace.single (Sum.inl ()) 1) 0) hv
  dsimp only at h
  rw [s.activated_coercive_inverse hb hfloor, s.activatedInverse_diagonal hp0 hp1] at h
  simpa only [cutoffConstantInverse, cutoffInverse, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero] using! h

/-- Gain read from the finite augmented inverse before changing to centered coordinates. -/
def cutoffGain (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (N : ℕ) : ℝ :=
  (1 - p * (1 - s.mass)) * s.cutoffConstantInverse hb hfloor p N - 1

theorem activationMass_pos (s : ScalarData d n) {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 - p * (1 - s.mass) := by
  have h := mul_le_mul_of_nonneg_right hp1 (sub_nonneg.mpr s.mass_le_one)
  linarith [s.mass_pos]

/-- The cutoff gains are increasing and converge to the exact value in (S1). -/
theorem cutoffGain_tendsto (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (s.cutoffGain hb hfloor p) ∧
      Tendsto (s.cutoffGain hb hfloor p) atTop (𝓝 (s.activationLimitGain p)) := by
  obtain ⟨hm, ht⟩ := s.cutoffConstantInverse_tendsto hb hfloor hp0 hp1
  constructor
  · intro a b hab
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hm hab) (s.activationMass_pos hp0 hp1).le) 1
  · exact (tendsto_const_nhds.mul ht).sub tendsto_const_nhds

/-- Every strict gain target below the full limit already holds at a finite symmetric cutoff. -/
theorem exists_cutoffGain_gt (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {z : ℝ} (hz : z < s.activationLimitGain p) :
    ∃ N : ℕ, z < s.cutoffGain hb hfloor p N := by
  have he : ∀ᶠ N in atTop, z < s.cutoffGain hb hfloor p N :=
    (s.cutoffGain_tendsto hb hfloor hp0 hp1).2 (Ioi_mem_nhds hz)
  exact he.exists

end ScalarData
end SchauderTranslates
