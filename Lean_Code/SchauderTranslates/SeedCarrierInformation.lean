import Lean_Code.SchauderTranslates.SeedCarrierCapture
import Lean_Code.SchauderTranslates.FiberMarginalCapture
import Lean_Code.SchauderTranslates.CoordinateSubspaces

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)

/-- Exact information on the full slow L² space for the actual selective kernel.
The carrier coordinates are orthonormal; the displayed operators are the genuine
orthogonal projections onto `V ∩ eᗮ` and the distinguished line. -/
theorem selective_information {d n : ℕ} (s : ScalarData d n) {L : ℕ} (hL : 0 < L) (m κ : ℝ)
    (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4)
    (hx : softCapture s.nonconstantGram s.moment m < (c.selectiveData s L m κ hm hm1 hκ).mass)
    (hy : seedCaptureValue s.nonconstantGram s.moment κ m L < (c.selectiveData s L m κ hm hm1 hκ).mass) :
    let a := c.selectiveData s L m κ hm hm1 hκ
    let φ := fun i => (c.representative i).toL2 ρ
    let e := φ c.distinguished
    let x := softCapture s.nonconstantGram s.moment m
    let y := seedCaptureValue s.nonconstantGram s.moment κ m L
    informationOperator (a.kernel.marginalMeans ρ (a.packet c.representative))
      (Matrix.gram ℂ (a.kernel.centered ρ (a.packet c.representative))) =
        ((x / (a.mass - x) : ℝ) : ℂ) • (atomSpan φ ⊓ (ℂ ∙ e)ᗮ).starProjection +
        ((y / (a.mass - y) : ℝ) : ℂ) • (ℂ ∙ e).starProjection := by
  let a := c.selectiveData s L m κ hm hm1 hκ
  let φ := fun i => (c.representative i).toL2 ρ
  let f := a.packet c.representative
  let C := Matrix.gram ℂ (a.kernel.centered ρ f)
  let x := softCapture s.nonconstantGram s.moment m
  let y := seedCaptureValue s.nonconstantGram s.moment κ m L
  have hC : C.PosDef := a.packet_centered_posDef ρ c.representative c.representatives_independent
  have hproj := c.selective_capture_projection s hL m κ hm hm1 hκ0 hκ1 hκ
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
