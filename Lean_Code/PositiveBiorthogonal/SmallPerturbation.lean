import Lean_Code.PositiveBiorthogonal.Definitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

/-! Explicit Neumann-series equivalences and bounds for a perturbation of the identity. -/
noncomputable section
set_option autoImplicit false
namespace PositiveBiorthogonal
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

def smallPerturbation (T : E →L[𝕜] E) (ρ : ℝ) (hT : ‖T‖ ≤ ρ) (hρ : ρ < 1) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub (-T) (by simpa using hT.trans_lt hρ))

@[simp] theorem smallPerturbation_apply (T : E →L[𝕜] E) (ρ : ℝ)
    (hT : ‖T‖ ≤ ρ) (hρ : ρ < 1) (f : E) : smallPerturbation T ρ hT hρ f = f + T f := by
  change (1 - -T) f = _
  simp

theorem smallPerturbation_norm (T : E →L[𝕜] E) (ρ : ℝ) (hT : ‖T‖ ≤ ρ) (hρ : ρ < 1) :
    ‖(smallPerturbation T ρ hT hρ).toContinuousLinearMap‖ ≤ 1 + ρ := by
  change ‖1 - -T‖ ≤ _
  rw [sub_neg_eq_add]
  exact (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hT)

theorem smallPerturbation_inverse_norm (T : E →L[𝕜] E) (ρ : ℝ)
    (hT : ‖T‖ ≤ ρ) (hρ : ρ < 1) :
    ‖(smallPerturbation T ρ hT hρ).symm.toContinuousLinearMap‖ ≤ (1 - ρ)⁻¹ := by
  change ‖∑' n : ℕ, (-T) ^ n‖ ≤ _
  have hb := tsum_geometric_le_of_norm_lt_one (-T) (by simpa using hT.trans_lt hρ)
  have hi : (1 - ‖T‖)⁻¹ ≤ (1 - ρ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hρ) (sub_le_sub_left hT 1)
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rw [norm_neg] at hb
  linarith

end PositiveBiorthogonal
