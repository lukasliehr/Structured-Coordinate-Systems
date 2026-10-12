import Lean_Code.PositiveBiorthogonal.Auxiliary
import Lean_Code.PositiveBiorthogonal.FiniteCuts
import Lean_Code.PositiveBiorthogonal.HilbertCorner

/-! The finite Toeplitz biorthogonal family and its uniform partial-projection bound. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators Polynomial ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def leftToeplitz (α : ℝ) (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  Polynomial.aeval (leftShift m) (truncatedPolynomial (toeplitzCoefficient α) m)

def leftToeplitzInverse (α : ℝ) (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  Polynomial.aeval (leftShift m) (truncatedPolynomial (inverseSequence (toeplitzCoefficient α)) m)

theorem leftToeplitz_inverse_left (α : ℝ) (m : ℕ) :
    leftToeplitzInverse (𝕜 := 𝕜) (p := p) α m * leftToeplitz α m = 1 :=
  truncatedPolynomial_inverse_eval _ rfl m _ (leftShift_nilpotent m)

theorem leftToeplitz_inverse_right (α : ℝ) (m : ℕ) :
    leftToeplitz (𝕜 := 𝕜) (p := p) α m * leftToeplitzInverse α m = 1 :=
  truncatedPolynomial_inverse_eval_right _ rfl m _ (leftShift_nilpotent m)

def toeplitzD (α : ℝ) (m : ℕ) (j : Fin m) : FiniteLp 𝕜 p m :=
  leftToeplitzInverse α m (PiLp.single p j 1)

def toeplitzS (α : ℝ) (m : ℕ) (j : Fin m) : FiniteLp 𝕜 p m :=
  finiteToeplitz α m (PiLp.single p j 1)

theorem toeplitz_biorthogonal {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (α : ℝ) (m : ℕ) (i j : Fin m) :
    finitePairing (toeplitzD (𝕜 := 𝕜) (p := p) α m i) (toeplitzS (p := q) α m j) =
      if i = j then 1 else 0 := by
  rw [toeplitzD, toeplitzS, finiteToeplitz, finitePairing_comm,
    finitePolynomial_transpose_pairing]
  change finitePairing (PiLp.single q j (1 : 𝕜))
    (leftToeplitz (𝕜 := 𝕜) (p := p) α m (leftToeplitzInverse α m (PiLp.single p i 1))) = _
  have he := congrArg (fun T : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m => T (PiLp.single p i 1))
    (leftToeplitz_inverse_right (𝕜 := 𝕜) (p := p) α m)
  simp only [mul_apply_eq_comp] at he
  rw [he]
  simp [PiLp.single_apply]

theorem toeplitz_primal_span (α : ℝ) (m : ℕ) : Submodule.span 𝕜 (Set.range (toeplitzD (𝕜 := 𝕜) (p := p) α m)) = ⊤ :=
  finiteBiorthogonal_span _ (toeplitzS (p := p) α m) (toeplitz_biorthogonal α m)

theorem toeplitz_dual_span (α : ℝ) (m : ℕ) :
    Submodule.span 𝕜 (Set.range (toeplitzS (𝕜 := 𝕜) (p := p) α m)) = ⊤ := by
  apply finiteBiorthogonal_span _ (toeplitzD (p := p) α m)
  intro i j
  rw [finitePairing_comm]
  simpa only [eq_comm] using toeplitz_biorthogonal (p := p) (q := p) α m j i

theorem finitePolynomial_right_single (a : ℕ → ℝ) (m : ℕ) (i j : Fin m) :
    Polynomial.aeval (rightShift (𝕜 := 𝕜) (p := p) m) (truncatedPolynomial a m)
        (PiLp.single p j 1) i = if j.val ≤ i.val then (a (i.val - j.val) : 𝕜) else 0 := by
  classical
  rw [aeval_truncatedPolynomial]
  simp only [sum_apply, smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  by_cases hji : j.val ≤ i.val
  · rw [if_pos hji, Finset.sum_eq_single (i.val - j.val)]
    · rw [rightShift_pow_apply, dif_pos (by omega)]
      have he : (⟨i.val - (i.val - j.val), by omega⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
      simp [he, RCLike.real_smul_eq_coe_mul]
    · intro k hk hne
      rw [rightShift_pow_apply]
      split_ifs with hki
      · have he : (⟨i.val - k, by omega⟩ : Fin m) ≠ j := by
          intro he
          have := congrArg Fin.val he
          dsimp at this
          omega
        simp [he]
      · simp
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr (by have := i.isLt; omega)))
  · rw [if_neg hji]
    apply Finset.sum_eq_zero
    intro k _
    rw [rightShift_pow_apply]
    split_ifs with hki
    · have he : (⟨i.val - k, by omega⟩ : Fin m) ≠ j := by
        intro he
        have := congrArg Fin.val he
        dsimp at this
        omega
      simp [he]
    · simp

theorem finitePolynomial_left_apply (a : ℕ → ℝ) (m : ℕ) (x : FiniteLp 𝕜 p m) (i : Fin m) :
    Polynomial.aeval (leftShift m) (truncatedPolynomial a m) x i =
      ∑ j : Fin m, if i.val ≤ j.val then (a (j.val - i.val) : 𝕜) * x j else 0 := by
  rw [← finitePairing_single_left (p := p) i,
    ← finitePolynomial_transpose_pairing, finitePairing]
  apply Finset.sum_congr rfl
  intro j _
  rw [finitePolynomial_right_single]
  split_ifs <;> simp

theorem toeplitz_projection_formula {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (α : ℝ) (m h : ℕ) :
    finiteRankProjection (toeplitzD (𝕜 := 𝕜) (p := p) α m) (toeplitzS (p := q) α m) h =
      leftToeplitzInverse α m * coordinateCut m h * leftToeplitz α m := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp, mul_apply_eq_comp, coordinateCut_eq_sum, map_sum]
  rw [finiteRankProjection_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  congr 1
  rw [toeplitzS, finitePairing_comm, finiteToeplitz, finitePolynomial_transpose_pairing,
    finitePairing_single_left]
  rfl

theorem leftToeplitz_single (α : ℝ) (m : ℕ) (i j : Fin m) :
    leftToeplitz (𝕜 := 𝕜) (p := p) α m (PiLp.single p j 1) i =
      if i.val ≤ j.val then (toeplitzCoefficient α (j.val - i.val) : 𝕜) else 0 := by
  rw [leftToeplitz, ← finitePairing_single_left (p := p) i,
    ← finitePolynomial_transpose_pairing, finitePairing_single_right,
    finitePolynomial_right_single]

theorem toeplitz_corner_coefficient (α : ℝ) (h i j : ℕ) (hi : i < h) (hj : h ≤ j) :
    toeplitzCoefficient α (j - i) = α * hilbertKernel (h - 1 - i) (j - h) := by
  have hd : j - i = (j - i - 1) + 1 := by omega
  rw [hd, toeplitzCoefficient, hilbertKernel]
  have he : ((j - i - 1 : ℕ) : ℝ) + 2 =
      ((h - 1 - i : ℕ) : ℝ) + 1 + ((j - h : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show j - i - 1 + 2 = h - 1 - i + 1 + (j - h) + 1 by omega)
  rw [he]
  ring

theorem toeplitz_commutator {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (α : ℝ) (m h : ℕ) (hh : h ≤ m) :
    coordinateCut (𝕜 := 𝕜) (p := p) m h * leftToeplitz α m -
      leftToeplitz α m * coordinateCut m h = α • hilbertCorner (q := q) hp1 hpfin m h hh := by
  apply finiteMap_ext_on_single
  intro j
  ext i
  simp only [sub_apply, mul_apply_eq_comp, PiLp.sub_apply, smul_apply,
    WithLp.ofLp_smul, Pi.smul_apply]
  rw [coordinateCut_apply, coordinateCut_single, hilbertCorner_single]
  by_cases hj : j.val < h
  · rw [if_pos hj]
    by_cases hi : i.val < h
    · simp [hi, Nat.not_le.mpr hj]
    · have hij : ¬ i.val ≤ j.val := by omega
      simp [hi, Nat.not_le.mpr hj, leftToeplitz_single, hij]
  · rw [if_neg hj, map_zero]
    by_cases hi : i.val < h
    · have hij : i.val ≤ j.val := by omega
      have hj' : h ≤ j.val := by omega
      simp only [hi, hj', and_self, if_true, PiLp.zero_apply, sub_zero,
        leftToeplitz_single, hij]
      rw [toeplitz_corner_coefficient α h i.val j.val hi hj', RCLike.ofReal_mul,
        RCLike.real_smul_eq_coe_mul]
    · simp [hi]

theorem toeplitz_commutator_norm_le {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 ≤ α) (m h : ℕ) (hh : h ≤ m) :
    ‖coordinateCut (𝕜 := 𝕜) (p := p) m h * leftToeplitz α m -
      leftToeplitz α m * coordinateCut m h‖ ≤ α * (p.toReal + q.toReal) := by
  rw [toeplitz_commutator (q := q) hp1 hpfin α m h hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  exact mul_le_mul_of_nonneg_left (hilbertCorner_norm_le (q := q) hp1 hpfin m h hh) hα

theorem toeplitz_projection_decomposition {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (α : ℝ) (m h : ℕ) :
    finiteRankProjection (toeplitzD (𝕜 := 𝕜) (p := p) α m) (toeplitzS (p := q) α m) h =
      coordinateCut m h + leftToeplitzInverse α m *
        (coordinateCut m h * leftToeplitz α m - leftToeplitz α m * coordinateCut m h) := by
  rw [toeplitz_projection_formula, mul_sub,
    ← mul_assoc (leftToeplitzInverse (𝕜 := 𝕜) (p := p) α m) (leftToeplitz α m) (coordinateCut m h),
    leftToeplitz_inverse_left, one_mul, ← mul_assoc]
  abel

theorem toeplitz_projection_norm_le {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (m h : ℕ) (hh : h ≤ m) :
    ‖finiteRankProjection (toeplitzD (𝕜 := 𝕜) (p := p) α m) (toeplitzS (p := q) α m) h‖ ≤
      1 + 2 * α * (p.toReal + q.toReal) := by
  rw [toeplitz_projection_decomposition]
  apply (norm_add_le _ _).trans
  have hInv : ‖leftToeplitzInverse (𝕜 := 𝕜) (p := p) α m‖ ≤ 2 :=
    finiteToeplitzInverse_opposite_norm_le α hα hα1 m
  calc
    _ ≤ 1 + ‖leftToeplitzInverse (𝕜 := 𝕜) (p := p) α m‖ *
        ‖coordinateCut m h * leftToeplitz α m - leftToeplitz α m * coordinateCut m h‖ :=
      add_le_add (coordinateCut_norm_le m h) (norm_mul_le _ _)
    _ ≤ 1 + 2 * (α * (p.toReal + q.toReal)) := by
      gcongr
      exact toeplitz_commutator_norm_le (q := q) hp1 hpfin α hα.le m h hh
    _ = _ := by ring

end PositiveBiorthogonal
