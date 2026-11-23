module

public import Lean_Code.SchauderTranslates.SoftLossScale
public import Lean_Code.SchauderTranslates.SoftCaptureBounds

@[expose] public section

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Only the already proved soft-capture estimates are needed for selection. -/
structure SoftWindowCaptureBounds (g : ℝ → ℝ) (ε : ℝ) : Prop where
  antitone : AntitoneOn g (Set.Icc 0 1)
  nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t
  initial : (1 / 4000 : ℝ) ≤ g (ε ^ 2)
  final : g (Real.sqrt ε) ≤ Real.sqrt ε
  step : ∀ R t : ℝ, 1 ≤ R → 0 ≤ t → R * t ≤ 1 / 2 → g t / (4 * R) ≤ g (R * t)

/-- The chosen mass and the two ratios, with nonnegative bounds exposing their limits. -/
structure SoftWindowResult (g : ℝ → ℝ) (κ ε m : ℝ) : Prop where
  mass_pos : 0 < m
  mass_le : m ≤ (1 / 2 : ℝ) ^ softLossLength ε
  capture_lower : Real.sqrt ε < g (m * seedGamma κ (softLossLength ε))
  capture_upper : g (m * seedGamma κ (softLossLength ε)) ≤ ε ^ (1 / 4 : ℝ)
  ratio_nonneg : 0 ≤ g m / g (m * seedGamma κ (softLossLength ε))
  ratio_upper : g m / g (m * seedGamma κ (softLossLength ε)) ≤ softLossRatio κ ε ^ (-(1 / 16 : ℝ))
  error_nonneg : 0 ≤ ε / g (m * seedGamma κ (softLossLength ε))
  error_upper : ε / g (m * seedGamma κ (softLossLength ε)) ≤ Real.sqrt ε

/-- Any choices meeting the window bounds have both ratios tending to zero.
The capture function and selected mass may vary with the scalar loss. -/
theorem soft_spectral_window_limits {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (g : ℝ → ℝ → ℝ) (m : ℝ → ℝ)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), SoftWindowResult (g ε) κ ε (m ε)) :
    Tendsto (fun ε => g ε (m ε) / g ε (m ε * seedGamma κ (softLossLength ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun ε => ε / g ε (m ε * seedGamma κ (softLossLength ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact ⟨squeeze_zero' (h.mono fun _ h => h.ratio_nonneg) (h.mono fun _ h => h.ratio_upper)
      (softLossRatio_drop_tendsto hκ0 hκ1),
    squeeze_zero' (h.mono fun _ h => h.error_nonneg) (h.mono fun _ h => h.error_upper) softLoss_sqrt_tendsto⟩

end SchauderTranslates
