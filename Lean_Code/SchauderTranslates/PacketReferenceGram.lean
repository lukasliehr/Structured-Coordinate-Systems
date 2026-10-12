import Lean_Code.SchauderTranslates.SelectiveAugmentedGram
import Lean_Code.SchauderTranslates.SelectedColumnBounds

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SelectiveKernelData
open BoundedMeasurableComplex
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable (ρ : Measure S) [IsProbabilityMeasure ρ]

theorem packetRows_reference_cross {L : ℕ} (φ : ι → BoundedMeasurableComplex S)
    (i : ι) (j : Fin L) :
    inner ℂ ((packetRows φ (Sum.inl i)).toL2 (ρ.prod (torusMeasure L)))
      ((packetRows φ (Sum.inr j)).toL2 (ρ.prod (torusMeasure L))) = 0 := by
  rw [inner_toL2]
  change (∫ p, star (φ i p.1) * seedPhaseRepresentative j p.2 ∂ρ.prod (torusMeasure L)) = 0
  have h := (φ i).conjugate.integral_tensor (seedPhaseRepresentative j) ρ (torusMeasure L)
  dsimp only [conjugate] at h
  rw [h, seedPhase_integral, mul_zero]

/-- The original carrier Gram and the identity seed Gram form a genuine
orthogonal direct sum under the reference product law. -/
theorem packetRows_reference_gram (L : ℕ) (φ : ι → BoundedMeasurableComplex S) :
    referenceRowGram ρ (packetRows (L := L) φ) =
      Matrix.fromBlocks (Matrix.gram ℂ (fun i => (φ i).toL2 ρ)) 0 0 1 := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact inner_pullbackFst ρ (torusMeasure L) (φ i) (φ j)
    | inr j => exact packetRows_reference_cross ρ φ i j
  | inr i => cases j with
    | inl j =>
      change inner ℂ ((packetRows φ (Sum.inr i)).toL2 (ρ.prod (torusMeasure L)))
        ((packetRows φ (Sum.inl j)).toL2 (ρ.prod (torusMeasure L))) = 0
      rw [← inner_conj_symm, packetRows_reference_cross ρ φ j i, map_zero]
    | inr j =>
      exact (inner_pullbackSnd ρ (torusMeasure L) _ _).trans (seedPhase_inner i j)

end SchauderTranslates.SelectiveKernelData
