import Lean_Code.SchauderTranslates.ScalarSupply
import Lean_Code.SchauderTranslates.ScalarAffinePrefixes
import Lean_Code.SchauderTranslates.ScalarAffineGain

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- An even polynomial scalar block of prescribed positive small gain and arbitrarily
small loss. The affine path preserves the ordered augmented bound; orthogonal removal
of the initial constant gives the same centered bound. -/
theorem scalar_gain_tuning {z δ : ℝ} (hz : 0 < z) (hz1 : z < 1 / 646) (hδ : 0 < δ) :
    ∃ (d n : ℕ) (s : ScalarData d n) (ε K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧ s.gain = z ∧
      0 ≤ K ∧ K < 2 ∧ s.CenteredPrefixSqBound (K ^ 2) ∧ s.AugmentedPrefixSqBound (K ^ 2) := by
  obtain ⟨d, n, s, ε, q, K, hpoly, heven, hfloor, _, hε0, hεδ, hε1, hmass,
    hgain, _, _, _, hK0, hK2, haug, _, _, _⟩ := scalar_blocks hδ
  obtain ⟨θ, hθ0, hθ1, hθpos, hθgain⟩ := s.exists_affine_gain hz (hz1.le.trans hgain)
  let t := s.affine θ hθ0 hθ1
  let J := max 1 K
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJK : K ≤ J := le_max_right _ _
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ1
  have hJ2 : J < 2 := max_lt (by norm_num) hK2
  have hqJ : K ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hK0 hJK 2
  have hJq : 1 ≤ J ^ 2 := by nlinarith
  have hpJ : s.AugmentedPrefixSqBound (J ^ 2) := FinitePrefixSqBound.mono haug hqJ
  have htEven : t.IsEven := s.affine_even heven θ hθ0 hθ1
  obtain ⟨b, hb, hf⟩ := hfloor
  refine ⟨d, n, t, θ * ε, J, s.affine_polynomial hpoly θ hθ0 hθ1, htEven,
    ⟨b, hb, s.affine_floor hb hf θ hθ0 hθ1⟩, t.rawGram_real htEven,
    mul_pos hθpos hε0, ?_, ?_, ?_, hθgain, hJ0, hJ2,
    s.affine_centered_prefix θ hθ0 hθ1 hJq hpJ,
    s.affine_augmented_prefix θ hθ0 hθ1 hJq hpJ⟩
  · exact (mul_le_of_le_one_left hε0.le hθ1).trans_lt hεδ
  · exact (mul_le_of_le_one_left hε0.le hθ1).trans hε1
  · change (s.affine θ hθ0 hθ1).mass = _
    rw [s.affine_mass, hmass]
    ring

end SchauderTranslates
