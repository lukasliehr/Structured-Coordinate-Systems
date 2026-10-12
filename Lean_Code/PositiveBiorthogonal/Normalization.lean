import Lean_Code.PositiveBiorthogonal.Transport
import Lean_Code.PositiveBiorthogonal.StepNormalization

/-! Diagonal normalization preserves projections, basis constants, and coefficient spans. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem inverse_rescale_term (c a : 𝕜) (hc : c ≠ 0) (v : L 𝕜 p) :
    (c⁻¹ * a) • (c • v) = a • v := by
  rw [smul_smul]
  congr 1
  field_simp

def SchauderBasis.rescale (B : SchauderBasis 𝕜 p) (c : ℕ → 𝕜) (hc : ∀ n, c n ≠ 0) : SchauderBasis 𝕜 p where
  b n := c n • B.b n
  coeff n := (c n)⁻¹ • B.coeff n
  biorthogonal i j := by
    simp only [smul_apply, map_smul, smul_eq_mul, B.biorthogonal]
    by_cases h : i = j
    · subst j
      simp [hc i]
    · simp [h]
  expansion f := by
    simpa only [smul_apply, smul_eq_mul, inverse_rescale_term _ _ (hc _)] using B.expansion f

theorem SchauderBasis.rescale_projection (B : SchauderBasis 𝕜 p) (c : ℕ → 𝕜)
    (hc : ∀ n, c n ≠ 0) (n : ℕ) : P (B.rescale c hc) n = P B n := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [StatementAudit.P_apply, rescale, smul_apply, smul_eq_mul,
    inverse_rescale_term _ _ (hc _)]

theorem SchauderBasis.rescale_K (B : SchauderBasis 𝕜 p) (c : ℕ → 𝕜) (hc : ∀ n, c n ≠ 0) :
    K (B.rescale c hc) = K B := by
  simp only [K, B.rescale_projection]

theorem span_range_nonzero_smul_eq (v : ℕ → L 𝕜 p) (c : ℕ → 𝕜) (hc : ∀ n, c n ≠ 0) :
    Submodule.span 𝕜 (Set.range (fun n => c n • v n)) = Submodule.span 𝕜 (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    have h := Submodule.smul_mem (Submodule.span 𝕜 (Set.range (fun n => c n • v n))) (c n)⁻¹
      (Submodule.subset_span ⟨n, rfl⟩)
    simp only [smul_smul, inv_mul_cancel₀ (hc n), one_smul] at h
    exact h

namespace ConstructionData
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

def normalizationScale (n : ℕ) : 𝕜 := stepSup (C.positiveCoefficient n)

theorem normalizationScale_ne_zero (n : ℕ) : C.normalizationScale n ≠ 0 := by
  have h := (stepSup_pos (C.positiveCoefficient_step n) (C.positiveCoefficient_ne_zero n)).ne'
  change (stepSup (C.positiveCoefficient n) : 𝕜) ≠ 0
  exact_mod_cast h

def normalizedBasis : SchauderBasis 𝕜 p :=
  C.transportedBasis.rescale C.normalizationScale C.normalizationScale_ne_zero

def normalizedCoefficient (n : ℕ) : L 𝕜 q := normalizeStep (C.positiveCoefficient n)

theorem normalized_represents : Represents C.normalizedBasis C.normalizedCoefficient := by
  intro n f
  change ((C.normalizationScale n)⁻¹ • C.transportedBasis.coeff n) f =
    pairing f ((C.normalizationScale n)⁻¹ • C.positiveCoefficient n)
  rw [smul_apply, C.transportedBasis_represents n f, pairing_smul_right, smul_eq_mul]

theorem normalized_step (n : ℕ) : CompactlySupportedStep (C.normalizedCoefficient n) :=
  normalizeStep_step (C.positiveCoefficient_step n)

theorem normalized_bounds (n : ℕ) :
    ∀ᵐ x : ℝ, 0 ≤ C.normalizedCoefficient n x ∧ C.normalizedCoefficient n x ≤ 1 :=
  normalizeStep_bounds (C.positiveCoefficient_step n) (C.positiveCoefficient_ne_zero n)
    (C.positiveCoefficient_nonnegative n)

theorem normalized_sup (n : ℕ) : eLpNorm (C.normalizedCoefficient n) ∞ volume = 1 :=
  normalizeStep_sup (C.positiveCoefficient_step n) (C.positiveCoefficient_ne_zero n)

theorem normalized_projection (n : ℕ) : P C.normalizedBasis n = P C.transportedBasis n :=
  C.transportedBasis.rescale_projection C.normalizationScale C.normalizationScale_ne_zero n

theorem normalized_K : K C.normalizedBasis = K C.transportedBasis :=
  C.transportedBasis.rescale_K C.normalizationScale C.normalizationScale_ne_zero

theorem normalized_K_bound :
    K C.normalizedBasis ≤ ((1 + C.ρ) / (1 - C.ρ)) * (1 + C.δ + C.η) := by
  rw [C.normalized_K]
  exact C.transported_K_bound

theorem normalized_dual_term (n : ℕ) (g : L 𝕜 q) :
    pairing (C.normalizedBasis.b n) g • C.normalizedCoefficient n =
      pairing (C.transportedBasis.b n) g • C.positiveCoefficient n := by
  change pairing (C.normalizationScale n • C.transportedBasis.b n) g •
    ((C.normalizationScale n)⁻¹ • C.positiveCoefficient n) = _
  rw [pairing_smul_left, smul_smul]
  congr 1
  field_simp [C.normalizationScale_ne_zero n]

theorem normalized_dual_sum (N : ℕ) (g : L 𝕜 q) :
    (∑ n ∈ Finset.range N, pairing (C.normalizedBasis.b n) g • C.normalizedCoefficient n) =
      ∑ n ∈ Finset.range N, pairing (C.transportedBasis.b n) g • C.positiveCoefficient n := by
  exact Finset.sum_congr rfl (fun n _ => C.normalized_dual_term n g)

theorem normalized_span :
    Submodule.span 𝕜 (Set.range C.normalizedCoefficient) =
      Submodule.span 𝕜 (Set.range C.positiveCoefficient) :=
  span_range_nonzero_smul_eq C.positiveCoefficient (fun n => (C.normalizationScale n)⁻¹)
    (fun n => inv_ne_zero (C.normalizationScale_ne_zero n))

theorem normalized_dense (hq : q ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range C.normalizedCoefficient) : Set (L 𝕜 q)) := by
  rw [C.normalized_span]
  exact C.positiveCoefficient_dense hq

end ConstructionData
end PositiveBiorthogonal
