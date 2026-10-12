import Lean_Code.PositiveBiorthogonal.BatchOrder
import Lean_Code.PositiveBiorthogonal.UnitExtraction

/-! The exact ordered batch and the algebra behind its biorthogonality. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem pairing_add_left (f h : L 𝕜 p) (g : L 𝕜 q) :
    pairing (f + h) g = pairing f g + pairing h g := by
  simp only [← representedFunctional_apply, map_add]

theorem pairing_sub_left (f h : L 𝕜 p) (g : L 𝕜 q) :
    pairing (f - h) g = pairing f g - pairing h g := by
  simp only [← representedFunctional_apply, map_sub]

theorem pairing_smul_left (c : 𝕜) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing (c • f) g = c * pairing f g := by
  simp only [← representedFunctional_apply, map_smul, smul_eq_mul]

theorem pairing_add_right (f : L 𝕜 p) (g h : L 𝕜 q) :
    pairing f (g + h) = pairing f g + pairing f h := by
  simp only [← pairingCLM_apply, map_add]

theorem pairing_sub_right (f : L 𝕜 p) (g h : L 𝕜 q) :
    pairing f (g - h) = pairing f g - pairing f h := by
  simp only [← pairingCLM_apply, map_sub]

theorem pairing_smul_right (c : 𝕜) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing f (c • g) = c * pairing f g := by
  simp only [← pairingCLM_apply, map_smul, smul_eq_mul]

def batchVector {N : ℕ} (d : Fin (2 * N) → L 𝕜 p) (H : Fin N → L 𝕜 p)
    (a : 𝕜) : BatchIndex N → L 𝕜 p
  | Sum.inl (i, b) => if b = 0 then d (batchFirst i) - a⁻¹ • H i else H i
  | Sum.inr i => d (batchLast i)

def batchCoefficient {N : ℕ} (s : Fin (2 * N) → L 𝕜 q) (φ : Fin N → L 𝕜 q)
    (a : 𝕜) : BatchIndex N → L 𝕜 q
  | Sum.inl (i, b) => if b = 0 then s (batchFirst i) else a⁻¹ • s (batchFirst i) + φ i
  | Sum.inr i => s (batchLast i)

theorem batch_biorthogonal {N : ℕ}
    (d : Fin (2 * N) → L 𝕜 p) (s : Fin (2 * N) → L 𝕜 q)
    (H : Fin N → L 𝕜 p) (φ : Fin N → L 𝕜 q) (a : 𝕜)
    (hds : ∀ i j, pairing (d i) (s j) = if i = j then 1 else 0)
    (hHφ : ∀ i j, pairing (H i) (φ j) = if i = j then 1 else 0)
    (hdφ : ∀ i j, pairing (d i) (φ j) = 0)
    (hHs : ∀ i j, pairing (H i) (s j) = 0) (x y : BatchIndex N) :
    pairing (batchVector d H a x) (batchCoefficient s φ a y) = if x = y then 1 else 0 := by
  classical
  rcases x with ⟨i, b⟩ | i <;> rcases y with ⟨j, c⟩ | j
  · fin_cases b <;> fin_cases c <;>
      simp [batchVector, batchCoefficient, pairing_sub_left, pairing_smul_left,
        pairing_add_right, pairing_smul_right, hds, hHφ, hdφ, hHs]
  · fin_cases b <;>
      simp [batchVector, batchCoefficient, pairing_sub_left, pairing_smul_left,
        hds, hHs]
  · fin_cases c <;>
      simp [batchVector, batchCoefficient, pairing_add_right, pairing_smul_right,
        hds, hdφ]
  · simp [batchVector, batchCoefficient, hds]

theorem batchVector_step {N : ℕ} (d : Fin (2 * N) → L 𝕜 p) (H : Fin N → L 𝕜 p)
    (a : 𝕜) (hd : ∀ i, CompactlySupportedStep (d i)) (hH : ∀ i, CompactlySupportedStep (H i))
    (x : BatchIndex N) : CompactlySupportedStep (batchVector d H a x) := by
  rcases x with ⟨i, b⟩ | i
  · dsimp [batchVector]
    split_ifs
    · exact step_sub (hd _) (step_smul (hH _) _)
    · exact hH _
  · exact hd _

theorem batchCoefficient_step {N : ℕ} (s : Fin (2 * N) → L 𝕜 q) (φ : Fin N → L 𝕜 q)
    (a : 𝕜) (hs : ∀ i, CompactlySupportedStep (s i)) (hφ : ∀ i, CompactlySupportedStep (φ i))
    (x : BatchIndex N) : CompactlySupportedStep (batchCoefficient s φ a x) := by
  rcases x with ⟨i, b⟩ | i
  · dsimp [batchCoefficient]
    split_ifs
    · exact hs _
    · exact step_add (step_smul (hs _) _) (hφ _)
  · exact hs _

def orderedBatchVector {N : ℕ} (d : Fin (2 * N) → L 𝕜 p) (H : Fin N → L 𝕜 p)
    (a : 𝕜) (j : Fin (3 * N)) : L 𝕜 p := batchVector d H a ((batchOrder N).symm j)

def orderedBatchCoefficient {N : ℕ} (s : Fin (2 * N) → L 𝕜 q) (φ : Fin N → L 𝕜 q)
    (a : 𝕜) (j : Fin (3 * N)) : L 𝕜 q := batchCoefficient s φ a ((batchOrder N).symm j)

theorem orderedBatch_biorthogonal {N : ℕ}
    (d : Fin (2 * N) → L 𝕜 p) (s : Fin (2 * N) → L 𝕜 q)
    (H : Fin N → L 𝕜 p) (φ : Fin N → L 𝕜 q) (a : 𝕜)
    (hds : ∀ i j, pairing (d i) (s j) = if i = j then 1 else 0)
    (hHφ : ∀ i j, pairing (H i) (φ j) = if i = j then 1 else 0)
    (hdφ : ∀ i j, pairing (d i) (φ j) = 0)
    (hHs : ∀ i j, pairing (H i) (s j) = 0) (i j : Fin (3 * N)) :
    pairing (orderedBatchVector d H a i) (orderedBatchCoefficient s φ a j) =
      if i = j then 1 else 0 := by
  simp only [orderedBatchVector, orderedBatchCoefficient,
    batch_biorthogonal d s H φ a hds hHφ hdφ hHs, Equiv.apply_eq_iff_eq]

theorem complete_pair_operator (d H : L 𝕜 p) (s φ : L 𝕜 q) (a : 𝕜) :
    (representedFunctional (p := p) s).smulRight (d - a⁻¹ • H) +
      (representedFunctional (p := p) (a⁻¹ • s + φ)).smulRight H =
    (representedFunctional (p := p) s).smulRight d + (representedFunctional (p := p) φ).smulRight H := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, representedFunctional_apply,
    pairing_add_right, pairing_smul_right]
  module

end PositiveBiorthogonal
