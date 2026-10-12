import Lean_Code.PositiveBiorthogonal.LocalSmall

/-! The explicit correction formulas make every batch coefficient nonnegative. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

theorem nonnegative_add {f g : L 𝕜 p} (hf : Nonnegative f) (hg : Nonnegative g) :
    Nonnegative (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy ha
  rw [ha, Pi.add_apply]
  exact add_nonneg hx hy

theorem nonnegative_smul {f : L 𝕜 p} (hf : Nonnegative f) {c : 𝕜} (hc : 0 ≤ c) :
    Nonnegative (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx hs
  rw [hs, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg hc hx

theorem ActivePartition.indicator_sub_cell_nonnegative (P : ActivePartition) (D : IntervalCell)
    (hD : D.carrier ⊆ P.active) : Nonnegative ((P.indicator : L 𝕜 p) - D.indicator) := by
  filter_upwards [P.coe_indicator (𝕜 := 𝕜) (p := p), D.coe_indicator (𝕜 := 𝕜) (p := p),
    Lp.coeFn_sub (P.indicator : L 𝕜 p) D.indicator] with x hP hD' hs
  rw [hs, Pi.sub_apply, hP, hD']
  by_cases hxD : x ∈ D.carrier
  · simp [hxD, hD hxD]
  · by_cases hxP : x ∈ P.active <;> simp [hxD, hxP]

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem corrected_positive_coefficient (P : ActivePartition) (z : L 𝕜 p) (s : L 𝕜 q)
    (c : ℝ) (hc : 0 ≤ c) (hs : Nonnegative s) (hβ : 0 ≤ pairing z s) :
    Nonnegative (s + localR P z c s) := by
  rw [localR_apply]
  exact nonnegative_add hs (nonnegative_smul P.indicator_nonnegative
    (mul_nonneg (RCLike.ofReal_nonneg.mpr hc) hβ))

theorem corrected_haar_formula (P : ActivePartition) (z : L 𝕜 p) (s : L 𝕜 q)
    (S : IntervalSplit) (a θ : ℝ) (ha : 0 < a) (hθ : S.ratio = θ)
    (hφ : pairing z (S.haarPhi : L 𝕜 q) = 0) :
    ((a : 𝕜)⁻¹ • s + S.haarPhi) + localR P z (a * θ) ((a : 𝕜)⁻¹ • s + S.haarPhi) =
      (a : 𝕜)⁻¹ • s + S.leftChild.indicator +
        (θ : 𝕜) • ((P.indicator : L 𝕜 q) - S.parent.indicator) +
        ((θ : 𝕜) * (pairing z s - 1)) • P.indicator := by
  rw [localR_apply, pairing_add_right, pairing_smul_right, hφ, add_zero]
  have haK : (a : 𝕜) ≠ 0 := by exact_mod_cast ha.ne'
  have hc : ((a * θ : ℝ) : 𝕜) * ((a : 𝕜)⁻¹ * pairing z s) = (θ : 𝕜) * pairing z s := by
    rw [RCLike.ofReal_mul]
    field_simp
  rw [hc, IntervalSplit.haarPhi, hθ]
  module

theorem corrected_haar_nonnegative (P : ActivePartition) (z : L 𝕜 p) (s : L 𝕜 q)
    (S : IntervalSplit) (a θ : ℝ) (ha : 0 < a) (hθ : S.ratio = θ) (hθ0 : 0 ≤ θ)
    (hD : S.parent.carrier ⊆ P.active) (hs : Nonnegative s)
    (hβ : 1 ≤ pairing z s) (hφ : pairing z (S.haarPhi : L 𝕜 q) = 0) :
    Nonnegative (((a : 𝕜)⁻¹ • s + S.haarPhi) +
      localR P z (a * θ) ((a : 𝕜)⁻¹ • s + S.haarPhi)) := by
  rw [corrected_haar_formula P z s S a θ ha hθ hφ]
  have ha0 : 0 ≤ (a : 𝕜)⁻¹ := by
    rw [← RCLike.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr ha.le)
  have hθK : 0 ≤ (θ : 𝕜) := RCLike.ofReal_nonneg.mpr hθ0
  exact nonnegative_add
    (nonnegative_add (nonnegative_add (nonnegative_smul hs ha0) S.leftChild.indicator_nonnegative)
      (nonnegative_smul (P.indicator_sub_cell_nonnegative S.parent hD) hθK))
    (nonnegative_smul P.indicator_nonnegative (mul_nonneg hθK (sub_nonneg.mpr hβ)))

namespace AuxiliaryFamily
variable {δ : ℝ} (A : AuxiliaryFamily 𝕜 p q δ) {N : ℕ}

theorem transferred_beta_nonnegative (hN : 0 < N) (F : UnitBlock (2 * N)) (j : Fin (2 * N)) :
    0 ≤ pairing (F.transfer (A.z N)) (F.transfer (A.s N j)) := by
  rw [F.transfer_pairing]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (A.z_nonneg N hN i) (A.s_nonneg N hN j i))

theorem transferred_beta_ge_one (hN : 0 < N) (F : UnitBlock (2 * N)) (j : Fin N) :
    1 ≤ pairing (F.transfer (A.z N)) (F.transfer (A.s N (batchFirst j))) := by
  rw [F.transfer_pairing]
  exact A.z_pairing N hN (batchFirst j) j.isLt

theorem corrected_batch_nonnegative (hN : 0 < N) (T : RefinementTrace N) (F : UnitBlock (2 * N))
    (hF : Disjoint F.carrier (T.state 0).active) (a θ : ℝ) (ha : 0 < a) (hθ : 0 ≤ θ)
    (hratio : ∀ j, (T.split j).ratio = θ) (i : Fin (3 * N)) :
    Nonnegative (A.batchCoefficients T F (a : 𝕜) i +
      localR (T.state 0) (F.transfer (A.z N)) (a * θ) (A.batchCoefficients T F (a : 𝕜) i)) := by
  change Nonnegative (batchCoefficient (fun j => F.transfer (A.s N j))
    (fun j => (T.split j).haarPhi) (a : 𝕜) ((batchOrder N).symm i) +
    localR (T.state 0) (F.transfer (A.z N)) (a * θ)
      (batchCoefficient (fun j => F.transfer (A.s N j))
        (fun j => (T.split j).haarPhi) (a : 𝕜) ((batchOrder N).symm i)))
  generalize (batchOrder N).symm i = x
  rcases x with ⟨j, b⟩ | j
  · by_cases hb : b = 0
    · simp only [batchCoefficient, if_pos hb]
      exact corrected_positive_coefficient _ _ _ _ (mul_nonneg ha.le hθ)
        (F.transfer_nonnegative _ (A.s_nonneg N hN _)) (A.transferred_beta_nonnegative hN F _)
    · simp only [batchCoefficient, if_neg hb]
      exact corrected_haar_nonnegative _ _ _ _ a θ ha (hratio j) hθ (T.parent_subset_initial j)
        (F.transfer_nonnegative _ (A.s_nonneg N hN _)) (A.transferred_beta_ge_one hN F j)
        (T.transfer_pairing_haarPhi F hF (A.z N) j)
  · exact corrected_positive_coefficient _ _ _ _ (mul_nonneg ha.le hθ)
      (F.transfer_nonnegative _ (A.s_nonneg N hN _)) (A.transferred_beta_nonnegative hN F _)

theorem corrected_batch_step (T : RefinementTrace N) (F : UnitBlock (2 * N))
    (a c : ℝ) (i : Fin (3 * N)) :
    CompactlySupportedStep (A.batchCoefficients T F (a : 𝕜) i +
      localR (T.state 0) (F.transfer (A.z N)) c (A.batchCoefficients T F (a : 𝕜) i)) :=
  step_add (A.batchCoefficients_step T F _ i) (localR_step _ _ _ _)

end AuxiliaryFamily
end PositiveBiorthogonal
