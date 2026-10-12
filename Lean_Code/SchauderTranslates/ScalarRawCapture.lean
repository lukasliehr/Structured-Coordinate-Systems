import Lean_Code.SchauderTranslates.ScalarCaptureData

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- Capture by the nonconstant uncentered characters is the mass times `Z/(1+Z)`.
The proof solves the finite normal equations and reads the actual constant inverse entry. -/
theorem raw_capture_gain (s : ScalarData d n) :
    gramCapture s.nonconstantGram s.moment = s.mass * s.gain / (1 + s.gain) := by
  let c := s.nonconstantGram⁻¹ *ᵥ s.moment
  have hGc : s.nonconstantGram *ᵥ c = s.moment := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp s.nonconstantGram_posDef.isUnit), Matrix.one_mulVec]
  let v : Unit ⊕ Fin n → ℂ := Sum.elim (fun _ => 1) (-c)
  have hv : s.rawGram *ᵥ v = Sum.elim
      (fun _ : Unit => (s.mass : ℂ) - star s.moment ⬝ᵥ c) (fun _ : Fin n => 0) := by
    rw [s.rawGram_fromBlocks, Matrix.fromBlocks_mulVec]
    have hneg : s.nonconstantGram *ᵥ (-c) = -s.moment := by
      rw [Matrix.mulVec_neg, hGc]
    ext (i | i)
    · cases i
      simp [v, Matrix.mulVec, dotProduct, momentRow, Pi.star_apply, Finset.sum_neg_distrib, sub_eq_add_neg]
    · change (momentColumn s.moment *ᵥ (fun _ : Unit => (1 : ℂ))) i +
        (s.nonconstantGram *ᵥ (-c)) i = 0
      rw [hneg]
      simp [momentColumn, Matrix.mulVec, dotProduct]
  have hi : s.rawGram⁻¹ *ᵥ (s.rawGram *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp s.rawGram_posDef.isUnit), Matrix.one_mulVec]
  rw [hv] at hi
  have h0 := congrFun hi (Sum.inl ())
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, mul_zero, Finset.sum_const_zero, add_zero, v] at h0
  rw [s.rawGram_inverse_constant_gain] at h0
  have hr := congrArg Complex.re h0
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.one_re] at hr
  change ((1 + s.gain) / s.mass) * (s.mass - gramCapture s.nonconstantGram s.moment) = 1 at hr
  have hm := s.toTorusWeight.mass_pos
  have hz : 0 < 1 + s.gain := by linarith [s.gain_nonneg]
  field_simp [hm.ne'] at hr
  apply (eq_div_iff hz.ne').mpr
  nlinarith

end ScalarData
end SchauderTranslates
