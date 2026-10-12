import Lean_Code.PositiveBiorthogonal.DisjointSums
import Lean_Code.PositiveBiorthogonal.HaarSupport
import Lean_Code.PositiveBiorthogonal.FiniteCoordinates

/-! Isometric realization of finite coordinates on distinct grid units. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal

structure UnitBlock (m : ℕ) where
  unit : Fin m → ℤ
  injective : Function.Injective unit

namespace UnitBlock
variable {m : ℕ} (B : UnitBlock m)

def cell (i : Fin m) : IntervalCell := gridUnit (B.unit i)
def carrier : Set ℝ := ⋃ i : Fin m, (B.cell i).carrier

theorem measurable : MeasurableSet B.carrier := MeasurableSet.iUnion (fun i => (B.cell i).measurable)

@[simp] theorem cell_length (i : Fin m) : (B.cell i).length = 1 := by
  simp [cell, gridUnit, IntervalCell.length]

theorem disjoint : Pairwise (fun i j => Disjoint (B.cell i).carrier (B.cell j).carrier) := by
  intro i j hij
  exact gridUnit_disjoint (fun he => hij (B.injective he))

theorem cell_subset (i : Fin m) : (B.cell i).carrier ⊆ B.carrier :=
  subset_iUnion (fun j : Fin m => (B.cell j).carrier) i

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

def transfer (x : FiniteLp 𝕜 p m) : L 𝕜 p := ∑ i : Fin m, x i • (B.cell i).indicator

theorem transfer_step (x : FiniteLp 𝕜 p m) : CompactlySupportedStep (B.transfer x) :=
  step_finset_sum _ _ (fun i _ => step_smul (B.cell i).indicator_step (x i))

theorem term_supported (x : FiniteLp 𝕜 p m) (i : Fin m) :
    ∀ᵐ t : ℝ, t ∉ (B.cell i).carrier → (x i • (B.cell i).indicator : L 𝕜 p) t = 0 := by
  filter_upwards [Lp.coeFn_smul (x i) ((B.cell i).indicator : L 𝕜 p),
    (B.cell i).coe_indicator (𝕜 := 𝕜) (p := p)] with t hs hi
  intro ht
  simp [hs, hi, ht]

theorem transfer_supported (x : FiniteLp 𝕜 p m) :
    ∀ᵐ t : ℝ, t ∉ B.carrier → B.transfer x t = 0 := by
  filter_upwards [ae_all_iff.mpr (B.term_supported x),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin m => x i • ((B.cell i).indicator : L 𝕜 p))] with t ht hs
  intro htc
  change (∑ i : Fin m, x i • (B.cell i).indicator : L 𝕜 p) t = 0
  rw [hs]
  exact Finset.sum_eq_zero (fun i _ => ht i (fun hti => htc (B.cell_subset i hti)))

theorem transfer_nonnegative (x : FiniteLp 𝕜 p m) (hx : ∀ i, 0 ≤ x i) :
    Nonnegative (B.transfer x) := by
  have hterm : ∀ i : Fin m, ∀ᵐ t : ℝ, 0 ≤ (x i • (B.cell i).indicator : L 𝕜 p) t := by
    intro i
    filter_upwards [Lp.coeFn_smul (x i) ((B.cell i).indicator : L 𝕜 p),
      (B.cell i).indicator_nonnegative (𝕜 := 𝕜) (p := p)] with t hs hi
    simpa only [hs, Pi.smul_apply, smul_eq_mul] using mul_nonneg (hx i) hi
  filter_upwards [ae_all_iff.mpr hterm,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin m => x i • ((B.cell i).indicator : L 𝕜 p))] with t ht hs
  change 0 ≤ (∑ i : Fin m, x i • (B.cell i).indicator : L 𝕜 p) t
  rw [hs]
  exact Finset.sum_nonneg (fun i _ => ht i)

theorem cell_indicator_pairing (i j : Fin m) :
    pairing ((B.cell i).indicator : L 𝕜 p) ((B.cell j).indicator : L 𝕜 q) =
      if i = j then 1 else 0 := by
  classical
  rw [IntervalCell.pairing_indicators]
  by_cases hij : i = j
  · subst j
    simp [Set.inter_self, IntervalCell.volume_real]
  · rw [Set.disjoint_iff_inter_eq_empty.mp (B.disjoint hij)]
    simp [hij]

variable [Fact (1 ≤ p)]

@[simp] theorem cell_indicator_norm (i : Fin m) : ‖((B.cell i).indicator : L 𝕜 p)‖ = 1 := by
  by_cases hp : p = ∞
  · subst p
    exact (B.cell i).indicator_norm_top
  · rw [(B.cell i).indicator_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp,
      B.cell_length, Real.one_rpow]

theorem transfer_norm_rpow (hpfin : p ≠ ∞) (x : FiniteLp 𝕜 p m) :
    ‖B.transfer x‖ ^ p.toReal = ‖x‖ ^ p.toReal := by
  rw [transfer, norm_rpow_sum_of_disjoint hpfin Finset.univ (fun i => (B.cell i).carrier)
    B.disjoint _ (B.term_supported x), finiteLp_norm_rpow hpfin]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_smul, B.cell_indicator_norm, mul_one]

theorem transfer_pairing_indicator [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (x : FiniteLp 𝕜 p m) (j : Fin m) :
    pairing (B.transfer x) ((B.cell j).indicator : L 𝕜 q) = x j := by
  classical
  rw [← representedFunctional_apply]
  change representedFunctional (p := p) ((B.cell j).indicator : L 𝕜 q)
    (∑ i : Fin m, x i • (B.cell i).indicator) = x j
  rw [map_sum]
  simp [map_smul, B.cell_indicator_pairing]

theorem transfer_norm_top (x : FiniteLp 𝕜 ∞ m) : ‖B.transfer x‖ = ‖x‖ := by
  apply le_antisymm
  · exact norm_top_sum_of_disjoint_le Finset.univ (fun i => (B.cell i).carrier) B.disjoint
      (fun i => x i • (B.cell i).indicator) (B.term_supported x) ‖x‖ (norm_nonneg x)
      (fun i => by simpa only [norm_smul, B.cell_indicator_norm, mul_one] using PiLp.norm_apply_le x i)
  · rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (B.transfer x))).mpr
    intro i
    have h := norm_pairing_le (B.transfer x) ((B.cell i).indicator : L 𝕜 1)
    simpa only [B.transfer_pairing_indicator, B.cell_indicator_norm, mul_one] using h

theorem transfer_norm (x : FiniteLp 𝕜 p m) : ‖B.transfer x‖ = ‖x‖ := by
  by_cases hp : p = ∞
  · subst p
    exact B.transfer_norm_top x
  · exact (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _)
      (p.toReal_pos_iff_ne_top.mpr hp).ne').mp (B.transfer_norm_rpow hp x)

def transferLinear : FiniteLp 𝕜 p m →ₗ[𝕜] L 𝕜 p where
  toFun := B.transfer
  map_add' x y := by simp [transfer, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [transfer, PiLp.smul_apply, smul_smul, Finset.smul_sum]

def transferIsometry : FiniteLp 𝕜 p m →ₗᵢ[𝕜] L 𝕜 p where
  toLinearMap := B.transferLinear
  norm_map' := B.transfer_norm

@[simp] theorem transferIsometry_apply (x : FiniteLp 𝕜 p m) : B.transferIsometry x = B.transfer x := rfl

theorem transfer_pairing [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    pairing (B.transfer x) (B.transfer y) = finitePairing x y := by
  rw [← pairingCLM_apply]
  change pairingCLM (q := q) (B.transfer x) (∑ i : Fin m, y i • (B.cell i).indicator) = _
  rw [map_sum]
  simp only [map_smul, pairingCLM_apply, B.transfer_pairing_indicator, smul_eq_mul,
    finitePairing, mul_comm]

end UnitBlock
end PositiveBiorthogonal
