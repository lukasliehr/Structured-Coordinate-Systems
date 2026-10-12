import Lean_Code.SchauderTranslates.SeedCarrierCoordinates
import Lean_Code.SchauderTranslates.ScalarCaptureData

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)
variable {d n : ℕ} (s : ScalarData d n) {L : ℕ} (hL : 0 < L) (m κ : ℝ)
  (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hκ0 : 0 < κ) (hκ1 : κ < 1)
  (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4)

include hL hκ0 hκ1

/-- The spectral capture formula for the actual weighted atom-span projection in
orthonormal computation coordinates. All Gram and source hypotheses are discharged. -/
theorem selective_capture_projection :
    let a := c.selectiveData s L m κ hm hm1 hκ
    let F := (a.kernel.slowLift ρ).toContinuousLinearMap
    let T := hilbertSynthesis (𝕜 := ℂ) (fun i => (c.representative i).toL2 ρ)
    (F†).comp ((atomSpan (a.kernel.atoms ρ (a.packet c.representative))).starProjection.comp F) =
      (a.mass : ℂ)⁻¹ • T.comp
        ((euclideanMatrixOperator (Matrix.diagonal (fun i => if i = c.distinguished then
          (seedCaptureValue s.nonconstantGram s.moment κ m L : ℂ) else
          (softCapture s.nonconstantGram s.moment m : ℂ)))).comp (T†)) := by
  let a := c.selectiveData s L m κ hm hm1 hκ
  let u := a.kernel.atoms ρ (a.packet c.representative)
  let F := (a.kernel.slowLift ρ).toContinuousLinearMap
  let T := hilbertSynthesis (𝕜 := ℂ) (fun i => (c.representative i).toL2 ρ)
  let B := (m : ℂ) • seedBlock c.distinguished L κ
  have hBraw := c.gram_positive_contraction L hm hm1 hκ
  rw [c.gram_eq_seedBlock L hm.le hκ] at hBraw
  have hB : B.PosDef := hBraw.1
  have hB1 : (1 - B).PosSemidef := hBraw.2.1
  have hA := tensorGram_posDef s.nonconstantGram_posDef hB hB1
  have hgram : Matrix.gram ℂ u = (a.mass : ℂ)⁻¹ • tensorGram s.nonconstantGram B :=
    c.selective_tensorGram s L m κ hm hm1 hκ
  have hu : LinearIndependent ℂ u := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [hgram]
    apply hA.smul
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_pos.mpr a.mass_positive
  have hsource : ((hilbertSynthesis (𝕜 := ℂ) u)†).comp F =
      (a.mass : ℂ)⁻¹ • (euclideanMatrixOperator (carrierSource s.moment c.distinguished κ m L)).comp (T†) :=
    c.selective_source s L m κ hm hm1 hκ
  have h := normalized_capture_sandwich u hu F T (carrierSource s.moment c.distinguished κ m L)
    hA a.mass a.mass_positive hgram hsource
  rw [carrierSource_sandwich,
    seed_compressed_capture_diagonal s.nonconstantGram_posDef s.moment c.distinguished
      hκ0 hκ1 hL m hB hB1] at h
  exact h

end SchauderTranslates.SeedCarrier
