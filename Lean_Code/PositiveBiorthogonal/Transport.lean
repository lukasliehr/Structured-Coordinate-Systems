import Lean_Code.PositiveBiorthogonal.GlobalAction

/-! Transport of a represented basis through paired continuous linear equivalences. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def SchauderBasis.transport (B : SchauderBasis 𝕜 p) (e : L 𝕜 p ≃L[𝕜] L 𝕜 p) : SchauderBasis 𝕜 p where
  b n := e.symm (B.b n)
  coeff n := (B.coeff n).comp e.toContinuousLinearMap
  biorthogonal i j := by simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, B.biorthogonal]
  expansion f := by
    have h := e.symm.continuous.tendsto (e f) |>.comp (B.expansion (e f))
    simpa only [Function.comp_def, map_sum, map_smul, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h

theorem SchauderBasis.transport_projection (B : SchauderBasis 𝕜 p)
    (e : L 𝕜 p ≃L[𝕜] L 𝕜 p) (n : ℕ) :
    P (B.transport e) n = e.symm.toContinuousLinearMap.comp ((P B n).comp e.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro f
  simp [StatementAudit.P_apply, transport, map_sum, map_smul]

theorem dense_span_equiv_image (v : ℕ → L 𝕜 p) (e : L 𝕜 p ≃L[𝕜] L 𝕜 p)
    (hv : Dense (Submodule.span 𝕜 (Set.range v) : Set (L 𝕜 p))) :
    Dense (Submodule.span 𝕜 (Set.range (fun n => e (v n))) : Set (L 𝕜 p)) := by
  apply (e.surjective.denseRange.dense_image e.continuous hv).mono
  rintro f ⟨g, hg, rfl⟩
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, rfl⟩ := hf
    exact Submodule.subset_span ⟨n, rfl⟩
  | zero => simp
  | add f g hf hg hfm hgm =>
    change e (f + g) ∈ Submodule.span 𝕜 (Set.range (fun n => e (v n)))
    rw [map_add]
    exact Submodule.add_mem _ hfm hgm
  | smul c f hf hfm =>
    change e (c • f) ∈ Submodule.span 𝕜 (Set.range (fun n => e (v n)))
    rw [map_smul]
    exact Submodule.smul_mem _ c hfm

namespace ConstructionData
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

def transportedBasis : SchauderBasis 𝕜 p := C.rawBasis.transport C.U

def positiveCoefficient (n : ℕ) : L 𝕜 q := C.V (C.rawCoefficient n)

theorem transportedBasis_represents : Represents C.transportedBasis C.positiveCoefficient := by
  intro n f
  change representedFunctional (C.rawCoefficient n) (C.U f) = pairing f (C.V (C.rawCoefficient n))
  rw [representedFunctional_apply, C.UV_paired]

theorem transported_projection_bound (n : ℕ) :
    ‖P C.transportedBasis n‖ ≤ ((1 + C.ρ) / (1 - C.ρ)) * (1 + C.δ + C.η) := by
  rw [transportedBasis, SchauderBasis.transport_projection, C.rawBasis_projection]
  have hK : 0 ≤ 1 + C.δ + C.η := by linarith [C.δ_pos, C.η_pos]
  calc
    ‖C.U.symm.toContinuousLinearMap.comp ((C.rawProjection n).comp C.U.toContinuousLinearMap)‖
        ≤ ‖C.U.symm.toContinuousLinearMap‖ * (‖C.rawProjection n‖ * ‖C.U.toContinuousLinearMap‖) :=
      (C.U.symm.toContinuousLinearMap.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left ((C.rawProjection n).opNorm_comp_le _) (norm_nonneg _))
    _ ≤ (1 - C.ρ)⁻¹ * ((1 + C.δ + C.η) * (1 + C.ρ)) := by
      gcongr
      · exact inv_nonneg.mpr (sub_nonneg.mpr C.ρ_lt_one.le)
      · exact C.U_inverse_norm
      · exact C.rawProjection_bound n
      · exact C.U_norm
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem transported_K_bound :
    K C.transportedBasis ≤ ((1 + C.ρ) / (1 - C.ρ)) * (1 + C.δ + C.η) :=
  K_le_of_projection_bound C.transportedBasis _ C.transported_projection_bound

theorem positiveCoefficient_biorthogonal (i j : ℕ) :
    pairing (C.transportedBasis.b i) (C.positiveCoefficient j) = if i = j then 1 else 0 :=
  represented_pairing_biorthogonal C.transportedBasis C.positiveCoefficient C.transportedBasis_represents i j

theorem positiveCoefficient_ne_zero (n : ℕ) : C.positiveCoefficient n ≠ 0 := by
  intro h
  have hb := C.positiveCoefficient_biorthogonal n n
  rw [h, if_pos rfl] at hb
  simp only [← pairingCLM_apply, map_zero] at hb
  exact zero_ne_one hb

theorem positiveCoefficient_nonnegative (n : ℕ) : Nonnegative (C.positiveCoefficient n) :=
  C.V_rawCoefficient_nonnegative n

theorem positiveCoefficient_step (n : ℕ) : CompactlySupportedStep (C.positiveCoefficient n) :=
  C.V_rawCoefficient_step n

theorem positiveCoefficient_dense (hq : q ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range C.positiveCoefficient) : Set (L 𝕜 q)) :=
  dense_span_equiv_image C.rawCoefficient C.V (C.rawCoefficient_dense hq)

end ConstructionData
end PositiveBiorthogonal
