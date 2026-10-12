import Lean_Code.PositiveBiorthogonal.ActiveIndicator

/-! Explicit paired rank-one corrections on the primal and conjugate spaces. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def localS (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  (c : 𝕜) • rankPair z (P.indicator : L 𝕜 q)

def localR (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) : L 𝕜 q →L[𝕜] L 𝕜 q :=
  (c : 𝕜) • rankPair (P.indicator : L 𝕜 q) z

theorem localS_apply (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (f : L 𝕜 p) :
    localS (q := q) P z c f = ((c : 𝕜) * ∫ x in P.active, f x) • z := by
  simp only [localS, smul_apply, rankPair_apply, P.pairing_indicator, smul_smul]

theorem localR_apply (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (g : L 𝕜 q) :
    localR P z c g = ((c : 𝕜) * pairing z g) • P.indicator := by
  simp only [localR, smul_apply, rankPair_apply, smul_smul, pairing_comm g z]

theorem local_corrections_paired (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing (localS (q := q) P z c f) g = pairing f (localR P z c g) := by
  rw [localS_apply, localR_apply, pairing_smul_left, pairing_smul_right, P.pairing_indicator]
  ring

theorem localS_norm (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (hc : 0 ≤ c) :
    ‖localS (q := q) P z c‖ = c * (volume.real P.active) ^ (1 / q.toReal) * ‖z‖ := by
  rw [localS, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc, rankPair,
    represented_rank_one_norm, P.indicator_norm]
  ring

theorem localR_norm (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (hc : 0 ≤ c) :
    ‖localR (q := q) P z c‖ = c * (volume.real P.active) ^ (1 / q.toReal) * ‖z‖ := by
  rw [localR, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc, rankPair,
    represented_rank_one_norm, P.indicator_norm]
  ring

theorem localR_step (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (g : L 𝕜 q) :
    CompactlySupportedStep (localR P z c g) := by
  rw [localR_apply]
  exact step_smul P.indicator_step _

theorem localS_step (P : ActivePartition) (z : L 𝕜 p) (c : ℝ)
    (hz : CompactlySupportedStep z) (f : L 𝕜 p) : CompactlySupportedStep (localS (q := q) P z c f) := by
  rw [localS_apply]
  exact step_smul hz _

theorem localR_supported (P : ActivePartition) (z : L 𝕜 p) (c : ℝ) (g : L 𝕜 q) :
    ∀ᵐ x : ℝ, x ∉ P.active → localR P z c g x = 0 := by
  rw [localR_apply]
  filter_upwards [Lp.coeFn_smul ((c : 𝕜) * pairing z g) (P.indicator : L 𝕜 q),
    P.indicator_supported (𝕜 := 𝕜) (p := q)] with x hx hi
  intro ha
  simp [hx, hi ha]

theorem localR_zero_of_pairing_zero (P : ActivePartition) (z : L 𝕜 p) (c : ℝ)
    (g : L 𝕜 q) (hg : pairing z g = 0) : localR P z c g = 0 := by
  rw [localR_apply, hg, mul_zero, zero_smul]

end PositiveBiorthogonal
