import Lean_Code.SchauderTranslates.CarrierKernelInformation
import Lean_Code.SchauderTranslates.SeedCaptureBounds

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ]

/-- The exact geometric result in the original carrier and actual weighted law.
The projection formulas simultaneously state the two eigenvalues and vanishing
on the orthogonal complement of the whole carrier. -/
structure SelectiveCaptureData {L d n : ℕ} (a : SelectiveKernelData S L d n)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (φ : ι → BoundedMeasurableComplex S) : Prop where
  capture : captureOperator (a.kernel.marginalMeans ρ (a.packet φ))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))) =
    ((softCapture a.scalar.nonconstantGram a.scalar.moment a.m / a.mass : ℝ) : ℂ) •
      (atomSpan (fun i => (φ i).toL2 ρ) ⊓ (ℂ ∙ a.e.toL2 ρ)ᗮ).starProjection +
    ((seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L / a.mass : ℝ) : ℂ) •
      (ℂ ∙ a.e.toL2 ρ).starProjection
  information : informationOperator (a.kernel.marginalMeans ρ (a.packet φ))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))) =
    ((softCapture a.scalar.nonconstantGram a.scalar.moment a.m /
      (a.mass - softCapture a.scalar.nonconstantGram a.scalar.moment a.m) : ℝ) : ℂ) •
      (atomSpan (fun i => (φ i).toL2 ρ) ⊓ (ℂ ∙ a.e.toL2 ρ)ᗮ).starProjection +
    ((seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L /
      (a.mass - seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L) : ℝ) : ℂ) •
      (ℂ ∙ a.e.toL2 ρ).starProjection
  ordinary_margin : softCapture a.scalar.nonconstantGram a.scalar.moment a.m < a.mass
  distinguished_margin : seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L < a.mass
  lower : (3 / 4 : ℝ) * softCapture a.scalar.nonconstantGram a.scalar.moment
    (a.m * seedGamma a.κ L) ≤ seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L
  upper : seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L ≤
    softCapture a.scalar.nonconstantGram a.scalar.moment (a.m * seedGamma a.κ L)

namespace SelectiveKernelData
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)

theorem orthonormal_carrier_exists (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ)) (he1 : ‖a.e.toL2 ρ‖ = 1) :
    ∃ c : SeedCarrier (ι := ι) ρ, c.e = a.e ∧
      atomSpan (fun i => (c.representative i).toL2 ρ) = atomSpan (fun i => (φ i).toL2 ρ) := by
  classical
  have hn : Nonempty ι := by
    by_contra hn
    letI : IsEmpty ι := not_nonempty_iff.mp hn
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp he
    have hz : a.e.toL2 ρ = 0 := by simpa using hr.symm
    simp [hz] at he1
  obtain ⟨c, _, hc, hs⟩ := exists_orthonormal_carrier ρ φ hφ a.e he he1 (Classical.choice hn)
  exact ⟨c, hc, hs⟩

/-- The capture calculation is independent of orthonormal computation coordinates. -/
theorem capture_data_of_margins (φ : ι → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ)) (he1 : ‖a.e.toL2 ρ‖ = 1)
    (hL : 0 < L) (hκ0 : 0 < a.κ) (hκ1 : a.κ < 1) (hω : (3 / 4 : ℝ) ≤ seedOmega a.κ L)
    (hx : softCapture a.scalar.nonconstantGram a.scalar.moment a.m < a.mass)
    (hy : seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L < a.mass) :
    SelectiveCaptureData a ρ φ := by
  obtain ⟨c, hc, hs⟩ := a.orthonormal_carrier_exists φ hφ he he1
  have heL2 : (c.representative c.distinguished).toL2 ρ = a.e.toL2 ρ := by
    apply BoundedMeasurableComplex.toL2_congr
    exact Filter.Eventually.of_forall (fun x => congrFun hc x)
  have hp := a.packet_span_eq ρ φ c.representative hs.symm
  have hC := a.packet_centered_posDef ρ φ hφ
  have hD := a.packet_centered_posDef ρ c.representative c.representatives_independent
  have hinfo := a.kernel.marginal_information_invariant ρ (a.packet φ)
    (a.packet c.representative) hC hD hp
  have hcap : captureOperator (a.kernel.marginalMeans ρ (a.packet φ))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))) =
      captureOperator (a.kernel.marginalMeans ρ (a.packet c.representative))
        (Matrix.gram ℂ (a.kernel.centered ρ (a.packet c.representative))) := by
    rw [← a.kernel.marginal_capture_projection ρ (a.packet φ) hC,
      ← a.kernel.marginal_capture_projection ρ (a.packet c.representative) hD,
      starProjection_congr _ _ hp]
  have hP : (atomSpan (fun i => (c.representative i).toL2 ρ) ⊓
      (ℂ ∙ (c.representative c.distinguished).toL2 ρ)ᗮ).starProjection =
      (atomSpan (fun i => (φ i).toL2 ρ) ⊓ (ℂ ∙ a.e.toL2 ρ)ᗮ).starProjection := by
    apply starProjection_congr
    rw [hs, heL2]
  have hQ : (ℂ ∙ (c.representative c.distinguished).toL2 ρ).starProjection =
      (ℂ ∙ a.e.toL2 ρ).starProjection := by
    apply starProjection_congr
    rw [heL2]
  have hcapc := c.kernel_capture a hc hL hκ0 hκ1
  have hinfoc := c.kernel_information a hc hL hκ0 hκ1 hx hy
  dsimp only at hcapc hinfoc
  rw [hP, hQ] at hcapc hinfoc
  have hB := c.gram_positive_contraction L a.mass_pos a.mass_le (c.kernel_coupling_bound a hc)
  rw [c.gram_eq_seedBlock L a.mass_pos.le (c.kernel_coupling_bound a hc)] at hB
  have hb := seedCaptureValue_bounds a.scalar.nonconstantGram_posDef a.scalar.nonconstantGram_le_one
    a.scalar.moment c.distinguished hκ0 hκ1 hL a.mass_pos hB.1 hB.2.1 hω
  exact ⟨hcap.trans hcapc, hinfo.trans hinfoc, hx, hy, hb.1, hb.2⟩

end SelectiveKernelData
end SchauderTranslates
