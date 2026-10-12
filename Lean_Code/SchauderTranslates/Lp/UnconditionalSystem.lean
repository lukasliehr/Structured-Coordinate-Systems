import Lean_Code.SchauderTranslates.Lp.MultiplierTransport

noncomputable section
open Filter
open scoped BigOperators Topology

namespace SchauderTranslates.LpConstruction

/-- An indexed normalized system has unique ordered expansions for every
enumeration, a common finite multiplier bound, and convergence of the
finite-subset coordinate net. -/
def NormalizedUnconditionalSystem {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ι → E) (coord : ι → E →L[ℂ] ℂ) (H : ℝ) : Prop :=
  Nonempty (ℕ ≃ ι) ∧ (∀ i, ‖u i‖ = 1) ∧
    (∀ e : ℕ ≃ ι, Construction.OrderedSchauderBasis (fun n => u (e n)) ∧
      FiniteMultiplierBound (fun n => u (e n)) H) ∧
    (∀ x : E, Tendsto (fun s : Finset ι => ∑ i ∈ s, coord i x • u i) atTop (𝓝 x))

theorem normalized_unconditional_system_transport {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (u : ι → E) (coord : ι → E →L[ℂ] ℂ) {H : ℝ}
    (hu : NormalizedUnconditionalSystem u coord H) :
    NormalizedUnconditionalSystem (fun i => U (u i))
      (fun i => (coord i).comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) H := by
  obtain ⟨he, hn, ho, hc⟩ := hu
  refine ⟨he, fun i => (U.norm_map (u i)).trans (hn i), ?_, ?_⟩
  · intro e
    exact ⟨schauder_transport U.toContinuousLinearEquiv (ho e).1,
      finite_multiplier_bound_transport U _ (ho e).2⟩
  · intro x
    have ht := U.continuous.continuousAt.tendsto.comp (hc (U.symm x))
    simpa only [Function.comp_def, map_sum, map_smul, U.apply_symm_apply,
      ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe] using ht

end SchauderTranslates.LpConstruction
