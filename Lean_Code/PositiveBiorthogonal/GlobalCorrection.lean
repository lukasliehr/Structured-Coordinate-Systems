import Lean_Code.PositiveBiorthogonal.RawBasis
import Lean_Code.PositiveBiorthogonal.SmallPerturbation

/-! The operator-norm sums of the paired local corrections and their invertible perturbations. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace PositiveBiorthogonal
namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

set_option backward.isDefEq.respectTransparency false in
theorem tolerance_hasSum : HasSum C.tolerance C.ρ := by
  have h : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) 1 := by
    convert! (hasSum_nat_add_iff' 1).mpr
      (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)) using 1 <;> norm_num
  simpa only [tolerance, mul_one] using! h.mul_left C.ρ

theorem localS_summable : Summable C.localS :=
  C.tolerance_hasSum.summable.of_norm_bounded (fun k => (C.local_norms_lt k).1.le)

theorem localR_summable : Summable C.localR :=
  C.tolerance_hasSum.summable.of_norm_bounded (fun k => (C.local_norms_lt k).2.le)

def sumS : L 𝕜 p →L[𝕜] L 𝕜 p := ∑' k, C.localS k

def sumR : L 𝕜 q →L[𝕜] L 𝕜 q := ∑' k, C.localR k

theorem sumS_norm : ‖C.sumS‖ ≤ C.ρ :=
  tsum_of_norm_bounded C.tolerance_hasSum (fun k => (C.local_norms_lt k).1.le)

theorem sumR_norm : ‖C.sumR‖ ≤ C.ρ :=
  tsum_of_norm_bounded C.tolerance_hasSum (fun k => (C.local_norms_lt k).2.le)

theorem sumS_apply (f : L 𝕜 p) : C.sumS f = ∑' k, C.localS k f :=
  (ContinuousLinearMap.apply 𝕜 (L 𝕜 p) f).map_tsum C.localS_summable

theorem sumR_apply (g : L 𝕜 q) : C.sumR g = ∑' k, C.localR k g :=
  (ContinuousLinearMap.apply 𝕜 (L 𝕜 q) g).map_tsum C.localR_summable

theorem sum_paired (f : L 𝕜 p) (g : L 𝕜 q) : pairing (C.sumS f) g = pairing f (C.sumR g) := by
  have hs := ((representedFunctional g).comp (ContinuousLinearMap.apply 𝕜 (L 𝕜 p) f)).hasSum
    C.localS_summable.hasSum
  have hr := ((pairingCLM f).comp (ContinuousLinearMap.apply 𝕜 (L 𝕜 q) g)).hasSum
    C.localR_summable.hasSum
  change HasSum (fun k => representedFunctional g (C.localS k f)) (representedFunctional g (C.sumS f)) at hs
  change HasSum (fun k => pairingCLM f (C.localR k g)) (pairingCLM f (C.sumR g)) at hr
  simp only [representedFunctional_apply, pairingCLM_apply, C.local_paired] at hs hr
  exact hs.unique hr

def U : L 𝕜 p ≃L[𝕜] L 𝕜 p := smallPerturbation C.sumS C.ρ C.sumS_norm C.ρ_lt_one

def V : L 𝕜 q ≃L[𝕜] L 𝕜 q := smallPerturbation C.sumR C.ρ C.sumR_norm C.ρ_lt_one

@[simp] theorem U_apply (f : L 𝕜 p) : C.U f = f + C.sumS f := smallPerturbation_apply _ _ _ _ f

@[simp] theorem V_apply (g : L 𝕜 q) : C.V g = g + C.sumR g := smallPerturbation_apply _ _ _ _ g

theorem U_norm : ‖C.U.toContinuousLinearMap‖ ≤ 1 + C.ρ := smallPerturbation_norm _ _ _ _

theorem V_norm : ‖C.V.toContinuousLinearMap‖ ≤ 1 + C.ρ := smallPerturbation_norm _ _ _ _

theorem U_inverse_norm : ‖C.U.symm.toContinuousLinearMap‖ ≤ (1 - C.ρ)⁻¹ :=
  smallPerturbation_inverse_norm _ _ _ _

theorem V_inverse_norm : ‖C.V.symm.toContinuousLinearMap‖ ≤ (1 - C.ρ)⁻¹ :=
  smallPerturbation_inverse_norm _ _ _ _

theorem UV_paired (f : L 𝕜 p) (g : L 𝕜 q) : pairing (C.U f) g = pairing f (C.V g) := by
  rw [C.U_apply, C.V_apply, pairing_add_left, pairing_add_right, C.sum_paired]

end ConstructionData
end PositiveBiorthogonal
