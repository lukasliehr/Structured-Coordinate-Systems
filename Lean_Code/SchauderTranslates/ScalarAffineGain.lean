import Lean_Code.SchauderTranslates.ScalarAffine

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

/-- A real formula for gain along the affine path, suitable for the intermediate value theorem. -/
def affineGain (s : ScalarData d n) (θ : ℝ) : ℝ :=
  (1 - θ + θ * s.mass) * ((s.affineGram θ)⁻¹ (Sum.inl ()) (Sum.inl ())).re - 1

theorem affine_gain (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (s.affine θ h0 h1).gain = s.affineGain θ := by
  rw [gain_eq_mass_inverse_constant, affine_mass, affine_rawGram]
  rfl

@[simp] theorem affineGain_zero (s : ScalarData d n) : s.affineGain 0 = 0 := by
  simp [affineGain, affineGram]

@[simp] theorem affineGain_one (s : ScalarData d n) : s.affineGain 1 = s.gain := by
  simp only [affineGain, affineGram, sub_self, zero_smul, one_smul, zero_add, one_mul]
  exact s.gain_eq_mass_inverse_constant.symm

theorem affineGain_continuousOn (s : ScalarData d n) : ContinuousOn s.affineGain (Set.Icc 0 1) := by
  intro θ hθ
  have hpd : (s.affineGram θ).PosDef := by
    rw [← s.affine_rawGram θ hθ.1 hθ.2]
    exact (s.affine θ hθ.1 hθ.2).rawGram_posDef
  have hC : Continuous s.affineGram := by unfold affineGram; fun_prop
  have hi : ContinuousAt (fun t => (s.affineGram t)⁻¹) θ :=
    (gram_inverse_continuousAt hpd).comp hC.continuousAt
  have he : ContinuousAt (fun t => ((s.affineGram t)⁻¹ (Sum.inl ()) (Sum.inl ())).re) θ :=
    Complex.continuous_re.continuousAt.comp ((continuous_apply _).continuousAt.comp
      ((continuous_apply _).continuousAt.comp hi))
  exact ((show ContinuousAt (fun t : ℝ => 1 - t + t * s.mass) θ by fun_prop).mul he |>.sub
    continuousAt_const).continuousWithinAt

/-- Every gain between zero and the block's gain is attained by an actual affine density. -/
theorem exists_affine_gain (s : ScalarData d n) {z : ℝ} (hz : 0 < z) (hs : z ≤ s.gain) :
    ∃ θ : ℝ, ∃ h0 : 0 ≤ θ, ∃ h1 : θ ≤ 1,
      0 < θ ∧ (s.affine θ h0 h1).gain = z := by
  have hz' : z ∈ Set.Icc (s.affineGain 0) (s.affineGain 1) := by simpa using And.intro hz.le hs
  obtain ⟨θ, hθ, hgain⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    s.affineGain_continuousOn hz'
  have hθ0 : 0 < θ := by
    by_contra hnot
    have he : θ = 0 := le_antisymm (not_lt.mp hnot) hθ.1
    rw [he, s.affineGain_zero] at hgain
    linarith
  exact ⟨θ, hθ.1, hθ.2, hθ0, (s.affine_gain θ hθ.1 hθ.2).trans hgain⟩

end ScalarData
end SchauderTranslates
