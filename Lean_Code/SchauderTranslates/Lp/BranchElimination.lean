import Lean_Code.SchauderTranslates.Lp.BranchNorm

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : 0 < p.toReal) (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n)

theorem branchScalar_unit_future {k n : ℕ} (hnk : n ≤ k) (i : Fin (N k)) :
    branchScalar p N n (branchUnit p N k i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [branchScalar_succ, ih (by omega), branchMean_unit_other p N (by omega)]
    simp

theorem branchScalar_meanVector_future {k n : ℕ} (hnk : n ≤ k) :
    branchScalar p N n (branchMeanVector p N k) = 0 := by
  simp [branchMeanVector, map_smul, map_sum, branchScalar_unit_future N hnk]

theorem branchMean_meanVector_other {k n : ℕ} (hnk : n ≠ k) :
    branchMean p N n (branchMeanVector p N k) = 0 := by
  simp [branchMeanVector, map_smul, map_sum, branchMean_unit_other p N hnk]

include hp hN in
theorem branchScalar_residual_self (n : ℕ) :
    branchScalar p N n (branchResidual p N n) = 1 := by
  induction n with
  | zero => simp [branchResidual]
  | succ n ih =>
    have hb : (branchBeta p.toReal : ℂ) * (branchRatio p.toReal : ℂ) = 1 / 2 := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) (branch_beta_ratio hp)
    simp only [branchScalar_succ, branchResidual, ContinuousLinearMap.map_smul_of_tower, map_sub, ih,
      branchScalar_meanVector_future N le_rfl, branchMean_residual_future p N le_rfl,
      branchMean_meanVector hp N hN, smul_eq_mul, Complex.real_smul]
    linear_combination 2 * hb

theorem branchCoordinate_unit_future {k n : ℕ} (hnk : n < k) (i : Fin (N k))
    (j : Fin (N n)) : branchCoordinate p N n j (branchUnit p N k i) = 0 := by
  simp [branchScalar_unit_future N hnk.le, branchMean_unit_other p N (by omega : n ≠ k),
    branchUnit_other p N (by omega : n ≠ k)]

theorem branchCoordinate_meanVector_future {k n : ℕ} (hnk : n < k) (j : Fin (N n)) :
    branchCoordinate p N n j (branchMeanVector p N k) = 0 := by
  simp [branchMeanVector, map_smul, map_sum, branchCoordinate_unit_future N hnk]

include hp hN in
theorem branchCoordinate_residual_self (n : ℕ) (j : Fin (N n)) :
    branchCoordinate p N n j (branchResidual p N n) =
      (layerPrimalScale p.toReal (N n) / 2 : ℂ) := by
  simp [branchResidual_private_future p N le_rfl, branchScalar_residual_self hp N hN,
    branchMean_residual_future p N le_rfl]

include hp hN in
theorem branchCoordinate_meanVector_self (n : ℕ) (j : Fin (N n)) :
    branchCoordinate p N n j (branchMeanVector p N n) =
      (layerPrimalScale p.toReal (N n) / 2 : ℂ) := by
  simp only [branchCoordinate_apply, branchMeanVector_same,
    branchScalar_meanVector_future N le_rfl, branchMean_meanVector hp N hN]
  ring

include hp hN in
theorem branchCoordinate_residual_future {k n : ℕ} (hnk : n < k) (j : Fin (N n)) :
    branchCoordinate p N n j (branchResidual p N k) = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [branchResidual, ContinuousLinearMap.map_smul_of_tower, map_sub]
    rcases Nat.eq_or_lt_of_le (by omega : n ≤ k) with he | he
    · subst k
      rw [branchCoordinate_residual_self hp N hN, branchCoordinate_meanVector_self hp N hN]
      simp
    · rw [ih he, branchCoordinate_meanVector_future N he]
      simp

theorem branchAtom_private_future {k n : ℕ} (hkn : k < n)
    (i : Fin (N k)) (j : Fin (N n)) : branchAtom p N k i (some ⟨n, j⟩) = 0 := by
  simp [branchAtom, lp.coeFn_smul, branchUnit_other p N (by omega : n ≠ k),
    branchResidual_private_future p N hkn.le]

theorem branchMean_atom_future {k n : ℕ} (hkn : k < n) (i : Fin (N k)) :
    branchMean p N n (branchAtom p N k i) = 0 := by
  simp [branchAtom_private_future N hkn]

include hp hN in
theorem branchScalar_atom_next (k : ℕ) (i : Fin (N k)) :
    branchScalar p N (k + 1) (branchAtom p N k i) = 0 := by
  simp [branchAtom, map_add, map_smul, branchScalar_unit_future N le_rfl,
    branchScalar_residual_self hp N hN, branchMean_residual_future p N le_rfl, mul_comm]

include hp hN in
theorem branchScalar_atom_future {k n : ℕ} (hkn : k < n) (i : Fin (N k)) :
    branchScalar p N n (branchAtom p N k i) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (by omega : k ≤ n) with he | he
    · subst n; exact branchScalar_atom_next hp N hN k i
    · rw [branchScalar_succ, ih he, branchMean_atom_future N he]
      simp

include hp hN in
/-- Continuous coordinate maps are biorthogonal in every pair of layers. -/
theorem branchCoordinate_biorthogonal (n k : ℕ) (i : Fin (N n)) (j : Fin (N k)) :
    branchCoordinate p N n i (branchAtom p N k j) =
      if (⟨n, i⟩ : Σ n, Fin (N n)) = ⟨k, j⟩ then 1 else 0 := by
  rcases lt_trichotomy n k with hlt | he | hgt
  · have hneq : (⟨n, i⟩ : Σ n, Fin (N n)) ≠ ⟨k, j⟩ := by
      intro he; have := congrArg Sigma.fst he; dsimp at this; omega
    rw [branchAtom, map_add, ContinuousLinearMap.map_smul_of_tower,
      branchCoordinate_unit_future N hlt, branchCoordinate_residual_future hp N hN hlt]
    simp [hneq]
  · subst k
    rw [branchAtom, map_add, ContinuousLinearMap.map_smul_of_tower,
      branchCoordinate_residual_self hp N hN]
    simp only [branchCoordinate_apply,
      branchUnit_same, branchScalar_unit_future N le_rfl, branchMean_unit_same,
      Complex.real_smul,
      Sigma.mk.inj_iff, heq_eq_eq, true_and]
    by_cases he : i = j
    · simp [he]; ring
    · simp [he]; ring
  · have hneq : (⟨n, i⟩ : Σ n, Fin (N n)) ≠ ⟨k, j⟩ := by
      intro he; have := congrArg Sigma.fst he; dsimp at this; omega
    simp [branchAtom_private_future N hgt, branchScalar_atom_future hp N hN hgt,
      branchMean_atom_future N hgt, hneq]

theorem branch_synthesis (n : ℕ) (c : Fin (N n) → ℂ) :
    (∑ i, c i • branchAtom p N n i) = branchLayer p N n c +
      ((layerDualScale p.toReal (N n) : ℂ) * ∑ i, c i) • branchResidual p N n := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum, Finset.sum_apply, branchAtom, branchLayer,
    lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  congr 1
  ring

theorem branch_layer_coefficients (n : ℕ) (y : Fin (N n) → ℂ) (b : ℂ) :
    branchLayer p N n (fun i => y i + (layerPrimalScale p.toReal (N n) / 2 : ℂ) * b) =
      branchLayer p N n y + (b / 2) • branchMeanVector p N n := by
  apply lp.ext
  funext k
  simp only [branchLayer, branchMeanVector, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sum,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Complex.real_smul]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  congr 1
  ring

include hp hN in
theorem branch_coefficient_mean (n : ℕ) (y : Fin (N n) → ℂ) (b : ℂ) :
    (layerDualScale p.toReal (N n) : ℂ) *
      (∑ i, (y i + (layerPrimalScale p.toReal (N n) / 2 : ℂ) * b)) =
      (layerDualScale p.toReal (N n) : ℂ) * (∑ i, y i) + b / 2 := by
  have hc : (N n : ℂ) * (layerPrimalScale p.toReal (N n) : ℂ) *
      (layerDualScale p.toReal (N n) : ℂ) = 1 := by
    exact_mod_cast layer_scale_product hp (hN n)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  linear_combination b / 2 * hc

include hp hN in
/-- Exact finite elimination in the actual ℓᵖ branch. -/
theorem branch_elimination_identity (n : ℕ) (z : BranchSpace p N) :
    branchScalar p N n z • branchResidual p N n +
      branchLayer p N n (fun i => z (some ⟨n, i⟩)) =
      (∑ i, branchCoordinate p N n i z • branchAtom p N n i) +
        branchScalar p N (n + 1) z • branchResidual p N (n + 1) := by
  have hb : (branchBeta p.toReal : ℂ) * (branchRatio p.toReal : ℂ) = 1 / 2 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) (branch_beta_ratio hp)
  rw [branch_synthesis]
  simp only [branchCoordinate_apply]
  rw [branch_layer_coefficients, branch_coefficient_mean hp N hN]
  apply lp.ext
  funext k
  simp only [branchScalar_succ, branchResidual, lp.coeFn_add, lp.coeFn_smul,
    lp.coeFn_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Complex.real_smul, branchMean_apply]
  linear_combination
    -(branchScalar p N n z - (layerDualScale p.toReal (N n) : ℂ) *
      ∑ i, z (some ⟨n, i⟩)) *
      (branchResidual p N n k - branchMeanVector p N n k) * hb

include hp hN in
/-- Blueprint `lp:elimination`: unit residuals, continuous biorthogonal
coordinates, and the exact layer-elimination identity. -/
theorem branch_elimination :
    (∀ n, ‖branchResidual p N n‖ = 1) ∧
    (∀ n (i : Fin (N n)), Continuous (branchCoordinate p N n i)) ∧
    (∀ n k (i : Fin (N n)) (j : Fin (N k)),
      branchCoordinate p N n i (branchAtom p N k j) =
        if (⟨n, i⟩ : Σ n, Fin (N n)) = ⟨k, j⟩ then 1 else 0) ∧
    (∀ n (z : BranchSpace p N),
      branchScalar p N n z • branchResidual p N n +
        branchLayer p N n (fun i => z (some ⟨n, i⟩)) =
        (∑ i, branchCoordinate p N n i z • branchAtom p N n i) +
          branchScalar p N (n + 1) z • branchResidual p N (n + 1)) :=
  ⟨branchResidual_norm hp N hN, fun _ _ => (branchCoordinate p N _ _).continuous,
    branchCoordinate_biorthogonal hp N hN, branch_elimination_identity hp N hN⟩

end SchauderTranslates.LpConstruction
