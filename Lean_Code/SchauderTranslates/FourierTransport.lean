import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open Filter
open scoped BigOperators Topology

namespace SchauderTranslates

open Construction

/-- Ordered Schauder expansions are preserved by a continuous linear equivalence.
This is the full generic statement of blueprint node `fourier:transport`. -/
theorem schauder_transport
    {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup H'] [NormedSpace ℂ H']
    (U : H ≃L[ℂ] H') {u : ℕ → H} (hu : OrderedSchauderBasis u) :
    OrderedSchauderBasis (fun n => U (u n)) := by
  intro f
  obtain ⟨c, hc, huniq⟩ := hu (U.symm f)
  refine ⟨c, ?_, ?_⟩
  · simpa only [Function.comp_def, map_sum, map_smul, U.apply_symm_apply] using
      U.continuous.continuousAt.tendsto.comp hc
  · intro d hd
    apply huniq d
    simpa only [Function.comp_def, map_sum, map_smul, U.symm_apply_apply] using
      U.symm.continuous.continuousAt.tendsto.comp hd

theorem schauder_transport_iff
    {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup H'] [NormedSpace ℂ H']
    (U : H ≃L[ℂ] H') (u : ℕ → H) :
    OrderedSchauderBasis (fun n => U (u n)) ↔ OrderedSchauderBasis u := by
  refine ⟨fun h => ?_, schauder_transport U⟩
  simpa only [U.symm_apply_apply] using schauder_transport U.symm h

end SchauderTranslates
