import Lean_Code.SchauderTranslates.FourierCovariance

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

end SchauderTranslates
