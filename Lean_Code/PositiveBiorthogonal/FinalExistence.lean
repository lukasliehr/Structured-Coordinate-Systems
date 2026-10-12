import Lean_Code.PositiveBiorthogonal.Normalization
import Lean_Code.PositiveBiorthogonal.AuxiliaryExistence
import Lean_Code.PositiveBiorthogonal.Existence
import Lean_Code.PositiveBiorthogonal.DualExpansion

/-! The normalized construction and the same coefficient sequence in the dual expansion. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem almost_monotone_existence (hp : p ≠ ∞) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q),
      (∀ n, CompactlySupportedStep (γ n)) ∧
      (∀ n, ∀ᵐ x : ℝ, 0 ≤ γ n x ∧ γ n x ≤ 1) ∧
      (∀ n, eLpNorm (γ n) ∞ volume = 1) ∧
      Represents B γ ∧
      (∀ n l, pairing (B.b n) (γ l) = if n = l then 1 else 0) ∧
      (∀ f : L 𝕜 p,
        Tendsto (fun N => ∑ n ∈ Finset.range N, pairing f (γ n) • B.b n) atTop (𝓝 f)) ∧
      K B < 1 + ε ∧
      (∀ (g : L 𝕜 q) (f : L 𝕜 p),
        Tendsto (fun N => ∑ n ∈ Finset.range N, pairing (B.b n) g * pairing f (γ n))
          atTop (𝓝 (pairing f g))) ∧
      (1 < p → ∃ Γ : SchauderBasis 𝕜 q,
        (∀ n, Γ.b n = γ n) ∧
        (∀ n (g : L 𝕜 q), Γ.coeff n g = pairing (B.b n) g) ∧
        PositiveBasis Γ ∧ K Γ = K B) := by
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
  refine ⟨C.normalizedBasis, C.normalizedCoefficient, C.normalized_step, C.normalized_bounds,
    C.normalized_sup, C.normalized_represents, ?_, ?_, ?_, ?_, ?_⟩
  · exact represented_pairing_biorthogonal _ _ C.normalized_represents
  · intro f
    have hrep (n : ℕ) : C.normalizedBasis.coeff n f = pairing f (C.normalizedCoefficient n) :=
      C.normalized_represents n f
    simpa only [hrep] using C.normalizedBasis.expansion f
  · exact C.normalized_K_bound.trans_lt ht.2.2.2
  · exact dual_weak _ _ C.normalized_represents
  · intro hp1
    have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
    let Γ := dualBasisOfDense C.normalizedBasis C.normalizedCoefficient C.normalized_represents
      (C.normalized_dense hq)
    refine ⟨Γ, fun n => rfl, ?_, ?_, ?_⟩
    · exact dualBasisOfDense_coeff _ _ _ _
    · exact dualBasisOfDense_positive _ _ _ _ (fun n => (C.normalized_bounds n).mono (fun x hx => hx.1))
    · exact dualBasisOfDense_constant _ _ _ _

end PositiveBiorthogonal
