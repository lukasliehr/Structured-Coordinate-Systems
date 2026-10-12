import Lean_Code.SchauderTranslates.CarrierCoordinatesForKernel
import Lean_Code.SchauderTranslates.SeedCarrierInformation
import Lean_Code.SchauderTranslates.OrthonormalCarrier
import Lean_Code.SchauderTranslates.WeightedCarrierSpan
import Lean_Code.SchauderTranslates.CaptureInvariance

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)
variable {L d n : ℕ} (a : SelectiveKernelData S L d n) (he : c.e = a.e)
include he

theorem kernel_capture (hL : 0 < L) (hκ0 : 0 < a.κ) (hκ1 : a.κ < 1) :
    let φ := fun i => (c.representative i).toL2 ρ
    let e := φ c.distinguished
    let x := softCapture a.scalar.nonconstantGram a.scalar.moment a.m
    let y := seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L
    captureOperator (a.kernel.marginalMeans ρ (a.packet c.representative))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet c.representative))) =
        ((x / a.mass : ℝ) : ℂ) • (atomSpan φ ⊓ (ℂ ∙ e)ᗮ).starProjection +
        ((y / a.mass : ℝ) : ℂ) • (ℂ ∙ e).starProjection := by
  let φ := fun i => (c.representative i).toL2 ρ
  let f := a.packet c.representative
  let C := Matrix.gram ℂ (a.kernel.centered ρ f)
  have hC : C.PosDef := a.packet_centered_posDef ρ c.representative c.representatives_independent
  have hproj := c.kernel_capture_projection a he hL hκ0 hκ1
  dsimp only at hproj
  rw [a.kernel.marginal_capture_projection ρ f hC] at hproj
  change captureOperator _ _ = (a.mass : ℂ)⁻¹ • informationSandwich φ _ at hproj
  rw [informationSandwich_two_values,
    familyCoordinateComplement_eq φ c.representatives_gram,
    familyCoordinateProjection_eq φ c.representatives_gram] at hproj
  simpa only [smul_add, smul_smul, Complex.ofReal_div, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_comm] using hproj

theorem kernel_information (hL : 0 < L) (hκ0 : 0 < a.κ) (hκ1 : a.κ < 1)
    (hx : softCapture a.scalar.nonconstantGram a.scalar.moment a.m < a.mass)
    (hy : seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L < a.mass) :
    let φ := fun i => (c.representative i).toL2 ρ
    let e := φ c.distinguished
    let x := softCapture a.scalar.nonconstantGram a.scalar.moment a.m
    let y := seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L
    informationOperator (a.kernel.marginalMeans ρ (a.packet c.representative))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet c.representative))) =
        ((x / (a.mass - x) : ℝ) : ℂ) • (atomSpan φ ⊓ (ℂ ∙ e)ᗮ).starProjection +
        ((y / (a.mass - y) : ℝ) : ℂ) • (ℂ ∙ e).starProjection := by
  let φ := fun i => (c.representative i).toL2 ρ
  let f := a.packet c.representative
  let C := Matrix.gram ℂ (a.kernel.centered ρ f)
  let x := softCapture a.scalar.nonconstantGram a.scalar.moment a.m
  let y := seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L
  have hC : C.PosDef := a.packet_centered_posDef ρ c.representative c.representatives_independent
  have hproj := c.kernel_capture_projection a he hL hκ0 hκ1
  have hmarg := a.kernel.marginal_capture_projection ρ f hC
  have hcapture : captureOperator (a.kernel.marginalMeans ρ f) C =
      (a.mass : ℂ)⁻¹ • informationSandwich φ
        (Matrix.diagonal (fun i => if i = c.distinguished then (y : ℂ) else (x : ℂ))) := by
    rw [← hmarg]
    simpa only [euclideanMatrixOperator_square, informationSandwich] using hproj
  have h := coordinate_information_from_capture (a.kernel.marginalMeans ρ f) hC φ
    c.representatives_gram c.distinguished a.mass x y a.mass_positive hx hy hcapture
  rw [familyCoordinateComplement_eq φ c.representatives_gram,
    familyCoordinateProjection_eq φ c.representatives_gram] at h
  exact h

end SchauderTranslates.SeedCarrier
