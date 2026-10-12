import Lean_Code.PositiveBiorthogonal.Statements

/-!
# The first vector of the constructed non-negative basis

The non-negative basis of `Lᵖ(ℝ)`, `1 < p < ∞`, built in `Lean_Code/PositiveBiorthogonal` is the
sequence of normalized coefficient functions `C.normalizedCoefficient n` of a basis of `Lᑫ(ℝ)`.
The correction operator `C.V` fixes the root vector `(gridUnit 0).indicator`, the indicator of
the unit interval `(0, 1]`, and the normalization (in the supremum norm) does not change it.
This file exports that fact:

* `PositiveBiorthogonal.ConstructionData.normalizedCoefficient_zero`;
* `PositiveBiorthogonal.exists_almost_monotone_positive_basis_with_root`: the statement
  `exists_almost_monotone_positive_basis` together with `B.b 0 = (gridUnit 0).indicator`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

/-- The essential supremum of the indicator of the unit interval `(0, 1]` is one. -/
theorem stepSup_gridUnit_zero : stepSup ((gridUnit 0).indicator : L 𝕜 q) = 1 := by
  have h : eLpNorm ((gridUnit 0).indicator : L 𝕜 q) ∞ volume = 1 := by
    rw [eLpNorm_congr_ae ((gridUnit 0).coe_indicator (𝕜 := 𝕜) (p := q)), eLpNorm_exponent_top,
      eLpNormEssSup_indicator_const_eq _ _ (gridUnit 0).volume_pos.ne']
    simp
  simp [stepSup, h]

/-- Normalizing the root indicator in the supremum norm does nothing. -/
theorem normalizeStep_gridUnit_zero :
    normalizeStep ((gridUnit 0).indicator : L 𝕜 q) = (gridUnit 0).indicator := by
  rw [normalizeStep, stepSup_gridUnit_zero]
  simp

namespace ConstructionData

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

/-- The correction operator fixes the root vector. -/
theorem positiveCoefficient_zero : C.positiveCoefficient 0 = (gridUnit 0).indicator := by
  rw [positiveCoefficient, C.rawCoefficient_zero, C.V_apply, C.sumR_root, add_zero]

/-- The first normalized coefficient function is the indicator of `(0, 1]`. -/
theorem normalizedCoefficient_zero : C.normalizedCoefficient 0 = (gridUnit 0).indicator := by
  rw [normalizedCoefficient, C.positiveCoefficient_zero, normalizeStep_gridUnit_zero]

end ConstructionData

/-- The dual basis of `almost_monotone_existence`, with its first vector identified.
Here `p` is the exponent of the auxiliary basis and `q` the exponent of the non-negative basis. -/
theorem almost_monotone_dual_basis_with_root [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞) (hp1 : 1 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ Γ : SchauderBasis 𝕜 q,
      Γ.b 0 = (gridUnit 0).indicator ∧ PositiveBasis Γ ∧
      (∀ n, CompactlySupportedStep (Γ.b n)) ∧ K Γ < 1 + ε := by
  let t := min ε 1 / 8
  have ht := error_parameters ε hε
  change 0 < t / 2 ∧ 0 < t ∧ t < 1 ∧
    ((1 + t) / (1 - t)) * (1 + t / 2 + t / 2) < 1 + ε at ht
  let C : ConstructionData 𝕜 p q :=
    { hpfin := hp
      δ := t / 2
      δ_pos := ht.1
      η := t / 2
      η_pos := ht.1
      ρ := t
      ρ_pos := ht.2.1
      ρ_lt_one := ht.2.2.1
      aux := auxiliaryFamily hp (t / 2) ht.1 }
  have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  let Γ := dualBasisOfDense C.normalizedBasis C.normalizedCoefficient C.normalized_represents
    (C.normalized_dense hq)
  refine ⟨Γ, C.normalizedCoefficient_zero, ?_, C.normalized_step, ?_⟩
  · exact dualBasisOfDense_positive _ _ _ _
      (fun n => (C.normalized_bounds n).mono (fun x hx => hx.1))
  · have hK : K Γ = K C.normalizedBasis := dualBasisOfDense_constant _ _ _ _
    rw [hK]
    exact C.normalized_K_bound.trans_lt ht.2.2.2

/-- For `1 < p < ∞` there are non-negative Schauder bases of `Lᵖ(ℝ)` consisting of compactly
supported step functions, with basis constant below `1 + ε`, whose first vector is the
indicator of the unit interval `(0, 1]`. -/
theorem exists_almost_monotone_positive_basis_with_root
    (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : SchauderBasis 𝕜 p,
      B.b 0 = (gridUnit 0).indicator ∧ PositiveBasis B ∧
      (∀ n, CompactlySupportedStep (B.b n)) ∧ K B < 1 + ε := by
  obtain ⟨q, hpq⟩ := StatementAudit.conjugate_exists hp₁.le
  let := StatementAudit.conjugate_instance hpq
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp₁
  have hq₁ : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp
  have hqp : 1 / q + 1 / p = 1 := by simpa only [add_comm] using hpq
  let := StatementAudit.conjugate_instance hqp
  exact almost_monotone_dual_basis_with_root (𝕜 := 𝕜) (p := q) (q := p) hq.ne hq₁ ε hε

end PositiveBiorthogonal
