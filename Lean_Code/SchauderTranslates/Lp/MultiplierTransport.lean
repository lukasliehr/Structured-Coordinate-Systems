import Lean_Code.SchauderTranslates.Lp.RootCoefficients
import Lean_Code.SchauderTranslates.FourierTransport

noncomputable section
open scoped BigOperators

namespace SchauderTranslates.LpConstruction

theorem finite_multiplier_bound_transport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (u : ℕ → E) {H : ℝ} (hu : FiniteMultiplierBound u H) :
    FiniteMultiplierBound (fun n => U (u n)) H := by
  intro n c a ha
  have he (d : ℕ → ℂ) :
      (∑ j ∈ Finset.range n, d j • U (u j)) = U (∑ j ∈ Finset.range n, d j • u j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun _ _ => (U.map_smul _ _).symm)
  rw [he, he, U.norm_map, U.norm_map]
  exact hu n c a ha

end SchauderTranslates.LpConstruction
