import Lean_Code.SchauderTranslates.SeedCarrierCapture

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

theorem kernel_coupling_bound : ∀ x, ‖(a.κ : ℂ) * c.e x‖ ≤ 1 / 4 := by
  rw [he]
  exact a.coupling_bound

theorem kernel_seedGram :
    a.rawSeedGram ρ (SelectiveKernelData.packetRows c.representative) = c.gram L a.m a.κ := by
  apply Matrix.ext
  intro i j
  change (∫ p, (seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2 : ℂ) *
      star (SelectiveKernelData.packetRows c.representative i p) *
      SelectiveKernelData.packetRows c.representative j p ∂ρ.prod (torusMeasure L)) = _
  simp_rw [c.packetRows_representative, ← he]
  rfl

theorem kernel_tensorGram :
    Matrix.gram ℂ (a.kernel.atoms ρ (a.packet c.representative)) =
      (a.mass : ℂ)⁻¹ • tensorGram a.scalar.nonconstantGram
        ((a.m : ℂ) • seedBlock c.distinguished L a.κ) := by
  change a.rowColumnGram ρ (SelectiveKernelData.packetRows c.representative) = _
  rw [a.rowColumnGram_orthonormal _ _ (c.packetRows_gram L), c.kernel_seedGram a he,
    c.gram_eq_seedBlock L a.mass_pos.le (c.kernel_coupling_bound a he)]
  rfl

theorem kernel_source :
    ((hilbertSynthesis (a.kernel.atoms ρ (a.packet c.representative)))†).comp
        (a.kernel.slowLift ρ).toContinuousLinearMap =
      (a.mass : ℂ)⁻¹ • (euclideanMatrixOperator
        (carrierSource a.scalar.moment c.distinguished a.κ a.m L)).comp
        ((hilbertSynthesis (fun i => (c.representative i).toL2 ρ))†) := by
  have heL2 : a.e.toL2 ρ = (c.representative c.distinguished).toL2 ρ := by
    apply BoundedMeasurableComplex.toL2_congr
    exact Filter.Eventually.of_forall (fun x => (congrFun he x).symm)
  ext h p
  have hs := congrArg (fun z : EuclideanSpace ℂ (Fin n × (ι ⊕ Fin L)) => z p)
    (a.packet_source_adjoint ρ c.representative h)
  change (((hilbertSynthesis (𝕜 := ℂ) (a.kernel.atoms ρ (a.packet c.representative)))†)
    (a.kernel.slowLift ρ h)) p = _
  rw [hs]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, euclideanMatrixOperator_apply,
    hilbertSynthesis_adjoint_apply, carrierSource_mulVec, PiLp.smul_apply, smul_eq_mul]
  change a.scalar.moment p.1 / (a.mass : ℂ) *
    Sum.elim (fun i => (1 - (a.m : ℂ)) * inner ℂ ((c.representative i).toL2 ρ) h)
      (fun _ => -(a.m : ℂ) * a.κ * inner ℂ (a.e.toL2 ρ) h) p.2 =
    (a.mass : ℂ)⁻¹ * (a.scalar.moment p.1 *
      Sum.elim (fun i => (1 - (a.m : ℂ)) * inner ℂ ((c.representative i).toL2 ρ) h)
        (fun _ => -(a.m : ℂ) * a.κ * inner ℂ ((c.representative c.distinguished).toL2 ρ) h) p.2)
  rw [heL2]
  ring

/-- Actual capture for an existing kernel, so no equality between dependent L²
spaces or between bundled choices of bounded representatives is assumed. -/
theorem kernel_capture_projection (hL : 0 < L) (hκ0 : 0 < a.κ) (hκ1 : a.κ < 1) :
    let F := (a.kernel.slowLift ρ).toContinuousLinearMap
    let T := hilbertSynthesis (𝕜 := ℂ) (fun i => (c.representative i).toL2 ρ)
    (F†).comp ((atomSpan (a.kernel.atoms ρ (a.packet c.representative))).starProjection.comp F) =
      (a.mass : ℂ)⁻¹ • T.comp
        ((euclideanMatrixOperator (Matrix.diagonal (fun i => if i = c.distinguished then
          (seedCaptureValue a.scalar.nonconstantGram a.scalar.moment a.κ a.m L : ℂ) else
          (softCapture a.scalar.nonconstantGram a.scalar.moment a.m : ℂ)))).comp (T†)) := by
  let u := a.kernel.atoms ρ (a.packet c.representative)
  let F := (a.kernel.slowLift ρ).toContinuousLinearMap
  let T := hilbertSynthesis (𝕜 := ℂ) (fun i => (c.representative i).toL2 ρ)
  let B := (a.m : ℂ) • seedBlock c.distinguished L a.κ
  have hBraw := c.gram_positive_contraction L a.mass_pos a.mass_le (c.kernel_coupling_bound a he)
  rw [c.gram_eq_seedBlock L a.mass_pos.le (c.kernel_coupling_bound a he)] at hBraw
  have hB : B.PosDef := hBraw.1
  have hB1 : (1 - B).PosSemidef := hBraw.2.1
  have hA := tensorGram_posDef a.scalar.nonconstantGram_posDef hB hB1
  have hgram : Matrix.gram ℂ u = (a.mass : ℂ)⁻¹ • tensorGram a.scalar.nonconstantGram B :=
    c.kernel_tensorGram a he
  have hu : LinearIndependent ℂ u := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [hgram]
    apply hA.smul
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_pos.mpr a.mass_positive
  have hsource : ((hilbertSynthesis (𝕜 := ℂ) u)†).comp F =
      (a.mass : ℂ)⁻¹ • (euclideanMatrixOperator
        (carrierSource a.scalar.moment c.distinguished a.κ a.m L)).comp (T†) :=
    c.kernel_source a he
  have h := normalized_capture_sandwich u hu F T
    (carrierSource a.scalar.moment c.distinguished a.κ a.m L)
    hA a.mass a.mass_positive hgram hsource
  rw [carrierSource_sandwich,
    seed_compressed_capture_diagonal a.scalar.nonconstantGram_posDef a.scalar.moment c.distinguished
      hκ0 hκ1 hL a.m hB hB1] at h
  exact h

end SchauderTranslates.SeedCarrier
