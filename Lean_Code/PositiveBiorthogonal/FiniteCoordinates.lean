import Lean_Code.PositiveBiorthogonal.Definitions
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Finite coordinates always carry their stated ℓᵖ norm. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

abbrev FiniteLp (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (m : ℕ) :=
  PiLp p (fun _ : Fin m => 𝕜)

theorem finiteLp_norm_rpow {m : ℕ} (hpfin : p ≠ ∞) (x : FiniteLp 𝕜 p m) :
    ‖x‖ ^ p.toReal = ∑ i : Fin m, ‖x i‖ ^ p.toReal := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hpfin
  rw [PiLp.norm_eq_sum hr,
    ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hr.ne', Real.rpow_one]

/-- The right shift deletes the last coordinate and inserts zero at the start. -/
def finiteRightShift (m : ℕ) (x : FiniteLp 𝕜 p m) : FiniteLp 𝕜 p m :=
  WithLp.toLp p fun i => if h : 0 < i.val then x ⟨i.val - 1, by omega⟩ else 0

omit [Fact (1 ≤ p)] in
@[simp] theorem finiteRightShift_zero (m : ℕ) (x : FiniteLp 𝕜 p (m + 1)) :
    finiteRightShift (m + 1) x 0 = 0 := by simp [finiteRightShift]

omit [Fact (1 ≤ p)] in
@[simp] theorem finiteRightShift_succ (m : ℕ) (x : FiniteLp 𝕜 p (m + 1)) (i : Fin m) :
    finiteRightShift (m + 1) x i.succ = x i.castSucc := by
  simp [finiteRightShift]
  rfl

theorem finiteRightShift_norm_le (m : ℕ) (x : FiniteLp 𝕜 p m) :
    ‖finiteRightShift m x‖ ≤ ‖x‖ := by
  by_cases hp : p = ∞
  · subst p
    rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    change ‖if h : 0 < i.val then x ⟨i.val - 1, by omega⟩ else 0‖ ≤ ‖x‖
    split_ifs
    · exact PiLp.norm_apply_le x _
    · exact (norm_zero : ‖(0 : 𝕜)‖ = 0).le.trans (norm_nonneg x)
  · have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    rw [PiLp.norm_eq_sum hr, PiLp.norm_eq_sum hr]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    cases m with
    | zero => simp
    | succ m =>
      rw [Fin.sum_univ_succ]
      simp only [finiteRightShift_zero, norm_zero, Real.zero_rpow hr.ne', zero_add,
        finiteRightShift_succ]
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)

def rightShift (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  LinearMap.mkContinuous
    { toFun := finiteRightShift m
      map_add' := by
        intro x y
        ext i
        simp only [finiteRightShift, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro c x
        ext i
        simp only [finiteRightShift, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
    1 (fun x => by simpa using finiteRightShift_norm_le m x)

@[simp] theorem rightShift_apply (m : ℕ) (x : FiniteLp 𝕜 p m) :
    rightShift m x = finiteRightShift m x := rfl

theorem rightShift_norm_le (m : ℕ) : ‖rightShift (𝕜 := 𝕜) (p := p) m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using finiteRightShift_norm_le m x

theorem rightShift_pow_apply (m k : ℕ) (x : FiniteLp 𝕜 p m) (i : Fin m) :
    ((rightShift m) ^ k) x i =
      if h : k ≤ i.val then x ⟨i.val - k, by omega⟩ else 0 := by
  induction k generalizing x i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, rightShift_apply]
    change (if h : 0 < i.val then ((rightShift m) ^ k) x ⟨i.val - 1, by omega⟩ else 0) = _
    by_cases hi : 0 < i.val
    · rw [dif_pos hi, ih]
      by_cases hk : k + 1 ≤ i.val
      · rw [dif_pos (show k ≤ i.val - 1 by omega), dif_pos hk]
        exact congrArg (fun j : Fin m => x j) (Fin.ext (by dsimp; omega))
      · rw [dif_neg (show ¬ k ≤ i.val - 1 by omega), dif_neg hk]
    · rw [dif_neg hi, dif_neg (show ¬ k + 1 ≤ i.val by omega)]

theorem rightShift_nilpotent (m : ℕ) : (rightShift (𝕜 := 𝕜) (p := p) m) ^ m = 0 := by
  ext x i
  rw [rightShift_pow_apply, dif_neg (Nat.not_le.mpr i.isLt)]
  simp

theorem rightShift_pow_norm_le (m k : ℕ) : ‖(rightShift (𝕜 := 𝕜) (p := p) m) ^ k‖ ≤ 1 := by
  induction k with
  | zero =>
    change ‖ContinuousLinearMap.id 𝕜 (FiniteLp 𝕜 p m)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ]
    apply (norm_mul_le _ _).trans
    simpa using mul_le_mul ih (rightShift_norm_le (𝕜 := 𝕜) (p := p) m) (norm_nonneg _) zero_le_one

/-- Reversing coordinates is an isometry for every stated exponent. -/
def coordinateReverse (m : ℕ) : FiniteLp 𝕜 p m ≃ₗᵢ[𝕜] FiniteLp 𝕜 p m :=
  LinearIsometryEquiv.piLpCongrLeft p 𝕜 𝕜 Fin.revPerm

@[simp] theorem coordinateReverse_apply (m : ℕ) (x : FiniteLp 𝕜 p m) (i : Fin m) :
    coordinateReverse m x i = x i.rev := rfl

@[simp] theorem coordinateReverse_reverse (m : ℕ) (x : FiniteLp 𝕜 p m) :
    coordinateReverse m (coordinateReverse m x) = x := by
  ext i
  simp

def leftShift (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  (coordinateReverse m).toContinuousLinearEquiv.toContinuousLinearMap ∘L rightShift m ∘L
    (coordinateReverse m).toContinuousLinearEquiv.toContinuousLinearMap

theorem leftShift_norm_le (m : ℕ) : ‖leftShift (𝕜 := 𝕜) (p := p) m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖coordinateReverse m (rightShift m (coordinateReverse m x))‖ ≤ 1 * ‖x‖
  rw [(coordinateReverse m).norm_map, one_mul]
  exact (finiteRightShift_norm_le m (coordinateReverse m x)).trans_eq
    ((coordinateReverse m).norm_map x)

theorem leftShift_pow_apply (m k : ℕ) (x : FiniteLp 𝕜 p m) :
    ((leftShift m) ^ k) x = coordinateReverse m (((rightShift m) ^ k) (coordinateReverse m x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    change coordinateReverse m (rightShift m
      (coordinateReverse m (coordinateReverse m (((rightShift m) ^ k) (coordinateReverse m x))))) = _
    rw [coordinateReverse_reverse, pow_succ', mul_apply_eq_comp]

theorem leftShift_nilpotent (m : ℕ) : (leftShift (𝕜 := 𝕜) (p := p) m) ^ m = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [leftShift_pow_apply, rightShift_nilpotent]
  simp

theorem leftShift_pow_norm_le (m k : ℕ) : ‖(leftShift (𝕜 := 𝕜) (p := p) m) ^ k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [leftShift_pow_apply, (coordinateReverse m).norm_map, one_mul]
  apply (((rightShift (𝕜 := 𝕜) (p := p) m) ^ k).le_opNorm (coordinateReverse m x)).trans
  simpa only [(coordinateReverse m).norm_map, one_mul] using
    mul_le_mul_of_nonneg_right (rightShift_pow_norm_le (𝕜 := 𝕜) (p := p) m k)
      (norm_nonneg (coordinateReverse m x))

@[simp] theorem leftShift_last (m : ℕ) (x : FiniteLp 𝕜 p (m + 1)) :
    leftShift (m + 1) x (Fin.last m) = 0 := by
  change rightShift (m + 1) (coordinateReverse (m + 1) x) (Fin.last m).rev = 0
  rw [Fin.rev_last, rightShift_apply, finiteRightShift_zero]

@[simp] theorem leftShift_castSucc (m : ℕ) (x : FiniteLp 𝕜 p (m + 1)) (i : Fin m) :
    leftShift (m + 1) x i.castSucc = x i.succ := by
  change rightShift (m + 1) (coordinateReverse (m + 1) x) i.castSucc.rev = _
  rw [Fin.rev_castSucc, rightShift_apply, finiteRightShift_succ, coordinateReverse_apply,
    Fin.rev_castSucc, Fin.rev_rev]

def finitePairing {q : ℝ≥0∞} {m : ℕ} (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) : 𝕜 :=
  ∑ i : Fin m, x i * y i

omit [Fact (1 ≤ p)] in
theorem finitePairing_comm {q : ℝ≥0∞} {m : ℕ} (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing x y = finitePairing y x := by simp only [finitePairing, mul_comm]

omit [Fact (1 ≤ p)] in
theorem finitePairing_add_left {q : ℝ≥0∞} {m : ℕ}
    (x z : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (x + z) y = finitePairing x y + finitePairing z y := by
  simp only [finitePairing, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

omit [Fact (1 ≤ p)] in
theorem finitePairing_sum_left {q : ℝ≥0∞} {m : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (∑ k ∈ s, f k) y = ∑ k ∈ s, finitePairing (f k) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [finitePairing]
  | @insert a s ha ih => simp [Finset.sum_insert ha, finitePairing_add_left, ih]

omit [Fact (1 ≤ p)] in
theorem finitePairing_sum_right {q : ℝ≥0∞} {m : ℕ} {ι : Type*}
    (x : FiniteLp 𝕜 p m) (s : Finset ι) (f : ι → FiniteLp 𝕜 q m) :
    finitePairing x (∑ k ∈ s, f k) = ∑ k ∈ s, finitePairing x (f k) := by
  rw [finitePairing_comm, finitePairing_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  exact finitePairing_comm _ _

omit [Fact (1 ≤ p)] in
theorem finitePairing_real_smul_left {q : ℝ≥0∞} {m : ℕ}
    (r : ℝ) (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (r • x) y = r • finitePairing x y := by
  simp only [finitePairing, PiLp.smul_apply, smul_mul_assoc, Finset.smul_sum]

omit [Fact (1 ≤ p)] in
theorem finitePairing_real_smul_right {q : ℝ≥0∞} {m : ℕ}
    (r : ℝ) (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing x (r • y) = r • finitePairing x y := by
  rw [finitePairing_comm, finitePairing_real_smul_left, finitePairing_comm y x]

theorem finite_shift_pairing {q : ℝ≥0∞} [Fact (1 ≤ q)] (m : ℕ)
    (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (rightShift m x) y = finitePairing x (leftShift m y) := by
  cases m with
  | zero => simp [finitePairing]
  | succ m =>
    unfold finitePairing
    conv_lhs => rw [Fin.sum_univ_succ]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp

theorem finite_shift_power_pairing {q : ℝ≥0∞} [Fact (1 ≤ q)] (m k : ℕ)
    (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (((rightShift m) ^ k) x) y = finitePairing x (((leftShift m) ^ k) y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, finite_shift_pairing, ih, pow_succ, mul_apply_eq_comp]

theorem finitePairing_norm_bound {q : ℝ≥0∞} {m : ℕ}
    (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    ‖finitePairing x y‖ ≤ (∑ i : Fin m, ‖y i‖) * ‖x‖ := by
  unfold finitePairing
  calc
    ‖∑ i : Fin m, x i * y i‖ ≤ ∑ i : Fin m, ‖x i * y i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ‖x‖ * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i : Fin m, ‖y i‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

def finitePairingFunctional {q : ℝ≥0∞} {m : ℕ} (y : FiniteLp 𝕜 q m) :
    FiniteLp 𝕜 p m →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => finitePairing x y
      map_add' := fun x z => finitePairing_add_left x z y
      map_smul' := by
        intro c x
        simp only [finitePairing, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_assoc, Finset.mul_sum] }
    (∑ i : Fin m, ‖y i‖) (fun x => finitePairing_norm_bound x y)

@[simp] theorem finitePairingFunctional_apply {q : ℝ≥0∞} {m : ℕ}
    (y : FiniteLp 𝕜 q m) (x : FiniteLp 𝕜 p m) :
    finitePairingFunctional y x = finitePairing x y := rfl

def finiteRankProjection {q : ℝ≥0∞} {m : ℕ}
    (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m) (h : ℕ) :
    FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h), (finitePairingFunctional (s j)).smulRight (d j)

@[simp] theorem finiteRankProjection_apply {q : ℝ≥0∞} {m : ℕ}
    (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m) (h : ℕ) (x : FiniteLp 𝕜 p m) :
    finiteRankProjection d s h x =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h), finitePairing x (s j) • d j := by
  simp [finiteRankProjection]

omit [Fact (1 ≤ p)] in
@[simp] theorem finitePairing_single_left {q : ℝ≥0∞} {m : ℕ} (i : Fin m) (y : FiniteLp 𝕜 q m) :
    finitePairing (PiLp.single p i (1 : 𝕜)) y = y i := by
  simp [finitePairing, PiLp.single_apply]

omit [Fact (1 ≤ p)] in
@[simp] theorem finitePairing_single_right {q : ℝ≥0∞} {m : ℕ} (i : Fin m) (x : FiniteLp 𝕜 p m) :
    finitePairing x (PiLp.single q i (1 : 𝕜)) = x i := by
  rw [finitePairing_comm, finitePairing_single_left]

theorem finiteBiorthogonal_span {q : ℝ≥0∞} {m : ℕ}
    (d : Fin m → FiniteLp 𝕜 p m) (s : Fin m → FiniteLp 𝕜 q m)
    (hbi : ∀ i j, finitePairing (d i) (s j) = if i = j then 1 else 0) :
    Submodule.span 𝕜 (Set.range d) = ⊤ := by
  have hlin : LinearIndependent 𝕜 d :=
    LinearIndependent.of_pairwise_dual_eq_zero_one d
      (fun j => (finitePairingFunctional (s j)).toLinearMap)
      (by
        intro i j hij
        change finitePairing (d j) (s i) = 0
        simp [hbi, Ne.symm hij])
      (by intro i; change finitePairing (d i) (s i) = 1; simp [hbi])
  apply hlin.span_eq_top_of_card_eq_finrank'
  exact (Module.finrank_eq_card_basis (PiLp.basisFun p 𝕜 (Fin m))).symm

end PositiveBiorthogonal
