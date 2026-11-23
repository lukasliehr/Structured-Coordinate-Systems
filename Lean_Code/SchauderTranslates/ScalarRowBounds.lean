module

public import Lean_Code.SchauderTranslates.AugmentedScalarPrefixes
public import Lean_Code.SchauderTranslates.OrderedActivation

@[expose] public section

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

@[simp] theorem precedingScalarRows_constant (n : ℕ) :
    precedingScalarRows n (Sum.inl ()) = ∅ := by
  ext i
  simp [mem_precedingScalarRows]

namespace ScalarData
variable {d n : ℕ}

@[simp] theorem realRawGram_diagonal (s : ScalarData d n) (j : Unit ⊕ Fin n) :
    s.realRawGram j j = s.mass := by
  change (s.rawGram j j).re = s.mass
  rw [s.rawGram_diagonal, Complex.ofReal_re]

theorem realRawGram_inverse_diagonal (s : ScalarData d n) (hs : s.IsEven)
    (j : Unit ⊕ Fin n) : s.realRawGram⁻¹ j j = (s.rawGram⁻¹ j j).re := by
  rw [s.realRawGram_inverse_map hs]
  rfl

theorem realRawGram_inverse_constant (s : ScalarData d n) (hs : s.IsEven) :
    s.realRawGram⁻¹ (Sum.inl ()) (Sum.inl ()) = (1 + s.gain) / s.mass := by
  rw [s.realRawGram_inverse_diagonal hs, s.rawGram_inverse_constant_gain, Complex.ofReal_re]

/-- The penalty of a nonconstant row is bounded by half the squared mass deficit. -/
theorem nonconstant_row_bound (s : ScalarData d n) (hs : s.IsEven)
    {ε q : ℝ} (hε : 0 ≤ ε) (hm : s.mass = 1 - ε) (hq : 0 ≤ q)
    (hp : s.AugmentedPrefixSqBound q) (j : Fin n)
    (hdiag : (s.rawGram⁻¹ (Sum.inr j) (Sum.inr j)).re - 1 ≤ 2 * ε) :
    metricRowBound s.realRawGram
      (fun i : precedingScalarRows n (Sum.inr j) => (i : Unit ⊕ Fin n)) (Sum.inr j) ≤
        q + ε ^ 2 / 2 := by
  have hb := s.precedingRows_prefix_sq_le hs hq hp (Sum.inr j)
  have ht := s.throughRow_prefix_sq_le hs hq hp (Sum.inr j)
  rw [metricPrefix_finset_insert s.realRawGram_posDef.posSemidef _ _
    (not_mem_precedingScalarRows _)] at ht
  unfold metricRowBound
  have hm' : max _ _ ≤ q := max_le hb ht
  rw [s.realRawGram_diagonal, hm, s.realRawGram_inverse_diagonal hs]
  have hc := mul_le_mul_of_nonneg_left hdiag hε
  nlinarith

/-- The initial constant row has an exact scalar cost, without the nonconstant diagonal estimate. -/
theorem constant_row_bound_eq (s : ScalarData d n) (hs : s.IsEven) :
    metricRowBound s.realRawGram
      (fun i : precedingScalarRows n (Sum.inl ()) => (i : Unit ⊕ Fin n)) (Sum.inl ()) =
      1 + s.gain + (1 - s.mass) * (1 + s.gain - s.mass) / (4 * s.mass) := by
  unfold metricRowBound
  rw [precedingScalarRows_constant, metricPrefix_finset_empty s.realRawGram_posDef.posSemidef]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, norm_rankOne, mul_pow,
    metricColumn_norm_sq s.realRawGram_posDef.posSemidef,
    metricDual_norm_sq s.realRawGram_posDef.posSemidef, s.realRawGram_diagonal,
    s.realRawGram_inverse_constant hs]
  have hm := s.toTorusWeight.mass_pos
  have hg := s.gain_nonneg
  rw [max_eq_right (by positivity)]
  field_simp
  <;> ring

end ScalarData
end SchauderTranslates
