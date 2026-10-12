import Lean_Code.PositiveBiorthogonal.EndpointAuxiliary
import Lean_Code.PositiveBiorthogonal.InteriorAuxiliary

/-! Existence of the auxiliary family for every finite primal exponent. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem auxiliary_exists (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (AuxiliaryFamily 𝕜 p q δ) := by
  by_cases hp : p = 1
  · subst p
    have hq : q = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q 1).mpr rfl
    subst q
    exact ⟨endpointAuxiliary δ hδ⟩
  · have hp1 : 1 < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp)
    obtain ⟨A, _⟩ := aux_interior (𝕜 := 𝕜) (q := q) hp1 hpfin δ hδ
    exact ⟨A⟩

/-- A chosen family is obtained only after its existence has been proved. -/
def auxiliaryFamily (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) : AuxiliaryFamily 𝕜 p q δ :=
  (auxiliary_exists hpfin δ hδ).some

end PositiveBiorthogonal
