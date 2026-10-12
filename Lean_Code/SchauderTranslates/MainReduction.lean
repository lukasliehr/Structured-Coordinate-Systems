import Lean_Code.SchauderTranslates.FourierCovariance
import Lean_Code.SchauderTranslates.FourierTransport

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace SchauderTranslates
open Construction

theorem weightedCharacter_image_eq_modulate (w : Weight) (μ : ℝ) :
    weightedL2_isometryEquiv w (weightedCharacter w μ) =
      modulateL2 μ (weightedL2_isometryEquiv w (weightedCharacter w 0)) := by
  apply Lp.ext
  filter_upwards [weightedL2_isometryEquiv_character w μ,
    modulateL2_ae μ (weightedL2_isometryEquiv w (weightedCharacter w 0)),
    weightedL2_isometryEquiv_constant w] with t ht hm hc
  rw [ht, hm, hc]

/-- This is a reduction, not an unconditional existence proof. Its remaining hypothesis
is the weighted exponential-basis construction specified in the blueprint. -/
theorem translates_of_weighted_exponential_basis (hb : WeightedExponentialBasisExists) :
    ∃ (g : LebesgueL2) (Λ : ℕ → ℝ),
      g ≠ 0 ∧ Function.Injective Λ ∧
      OrderedSchauderBasis (fun n => translateL2 (Λ n) g) := by
  obtain ⟨w, μ, u, hμ, hu, hb⟩ := hb
  have hueq : u = fun n => weightedCharacter w (μ n) := by
    funext n
    exact Lp.ext ((hu n).trans (weightedCharacter_ae w (μ n)).symm)
  subst u
  let U : WeightedL2 w ≃L[ℂ] LebesgueL2 :=
    (weightedL2_isometryEquiv w).toContinuousLinearEquiv.trans
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv
  let g := U (weightedCharacter w 0)
  have hzero : weightedCharacter w 0 ≠ 0 :=
    LinearIndependent.ne_zero 0 (characters_linearIndependent w id Function.injective_id)
  have hg : g ≠ 0 := by
    intro h
    apply hzero
    apply U.injective
    simpa only [map_zero] using h
  have hU (n : ℕ) : U (weightedCharacter w (μ n)) = translateL2 (-μ n) g := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ).symm
      (weightedL2_isometryEquiv w (weightedCharacter w (μ n))) = _
    rw [weightedCharacter_image_eq_modulate, inverseFourier_modulate_L2]
    rfl
  refine ⟨g, fun n => -μ n, hg, neg_injective.comp hμ, ?_⟩
  simpa only [hU] using schauder_transport U hb

end SchauderTranslates
