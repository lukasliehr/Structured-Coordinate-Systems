import Lean_Code.PositiveBiorthogonal.ToeplitzProjections
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Column bounds and correction vectors for the interior auxiliary family. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped ENNReal BigOperators Topology ComplexOrder
namespace PositiveBiorthogonal

theorem toeplitzCoefficient_power_sum (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (r : ℝ) (hr : 1 < r) (m : ℕ) :
    (∑ i : Fin m, toeplitzCoefficient α i.val ^ r) ≤ 1 + 1 / (r - 1) := by
  cases m with
  | zero => simp; positivity
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, toeplitzCoefficient, Real.one_rpow, Fin.val_succ]
    have he : -(r - 1) - 1 = -r := by ring
    have ht : (∑ k : Fin n, ((k.val : ℝ) + 2) ^ (-r)) ≤ 1 / (r - 1) := by
      have hb := power_tail_bound (r - 1) (by linarith) 1 (n + 1) (by norm_num)
      simpa [Finset.sum_Ico_eq_sum_range, Finset.sum_range, he, Nat.cast_add,
        Nat.cast_one, add_comm, add_left_comm, add_assoc, one_add_one_eq_two] using hb
    apply add_le_add_right _ 1
    apply (Finset.sum_le_sum (fun k _ => ?_)).trans ht
    have hk : 0 < (k.val : ℝ) + 2 := by positivity
    calc
      (α / ((k.val : ℝ) + 2)) ^ r ≤ (1 / ((k.val : ℝ) + 2)) ^ r :=
        Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hα1 hk.le) (by linarith)
      _ = ((k.val : ℝ) + 2) ^ (-r) := by rw [one_div, Real.inv_rpow hk.le, Real.rpow_neg hk.le]

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem toeplitzS_coordinate (α : ℝ) (m : ℕ) (j i : Fin m) :
    toeplitzS (𝕜 := 𝕜) (p := p) α m j i =
      if j.val ≤ i.val then (toeplitzCoefficient α (i.val - j.val) : 𝕜) else 0 :=
  finitePolynomial_right_single _ m i j

theorem toeplitzS_nonnegative (α : ℝ) (hα : 0 < α) (m : ℕ) (j i : Fin m) :
    0 ≤ toeplitzS (𝕜 := 𝕜) (p := p) α m j i := by
  rw [toeplitzS_coordinate]
  split_ifs
  · exact_mod_cast (toeplitzCoefficient_pos α hα _).le
  · exact le_rfl

theorem toeplitzS_eq_shift (α : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    toeplitzS (𝕜 := 𝕜) (p := p) α (n + 1) j =
      ((rightShift (n + 1)) ^ j.val) (toeplitzS α (n + 1) 0) := by
  ext i
  rw [toeplitzS_coordinate, rightShift_pow_apply]
  by_cases hji : j.val ≤ i.val
  · rw [if_pos hji, dif_pos hji, toeplitzS_coordinate]
    simp
  · rw [if_neg hji, dif_neg hji]

theorem toeplitzS_norm_le_first (α : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ‖toeplitzS (𝕜 := 𝕜) (p := p) α (n + 1) j‖ ≤ ‖toeplitzS (𝕜 := 𝕜) (p := p) α (n + 1) 0‖ := by
  rw [toeplitzS_eq_shift]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (rightShift_pow_norm_le (𝕜 := 𝕜) (p := p) (n + 1) j.val) (norm_nonneg (toeplitzS (𝕜 := 𝕜) (p := p) α (n + 1) 0))

theorem toeplitzS_norm_power_le (hp1 : 1 < p) (hpfin : p ≠ ∞)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (j : Fin m) :
    ‖toeplitzS (𝕜 := 𝕜) (p := p) α m j‖ ^ p.toReal ≤ 1 + 1 / (p.toReal - 1) := by
  have hr : 1 < p.toReal := by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpfin).mpr hp1
  cases m with
  | zero => exact Fin.elim0 j
  | succ n =>
    apply (Real.rpow_le_rpow (norm_nonneg _) (toeplitzS_norm_le_first α n j) (by linarith)).trans
    rw [finiteLp_norm_rpow hpfin]
    have he : (∑ i : Fin (n + 1), ‖toeplitzS (𝕜 := 𝕜) (p := p) α (n + 1) 0 i‖ ^ p.toReal) =
        ∑ i : Fin (n + 1), toeplitzCoefficient α i.val ^ p.toReal := by
      apply Finset.sum_congr rfl
      intro i _
      simp [toeplitzS_coordinate, abs_of_pos (toeplitzCoefficient_pos α hα _)]
    rw [he]
    exact toeplitzCoefficient_power_sum α hα hα1 _ hr _

omit [Fact (1 ≤ p)] in
theorem toeplitzS_norm_le_conjugate {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (m : ℕ) (j : Fin m) :
    ‖toeplitzS (𝕜 := 𝕜) (p := q) α m j‖ ≤ p.toReal ^ (1 / q.toReal) := by
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp (lt_top_iff_ne_top.mpr hpfin)
  have hrs := ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _) hrs.symm.pos).mp
  rw [← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hrs.symm.pos.ne', Real.rpow_one]
  have hb := toeplitzS_norm_power_le (𝕜 := 𝕜) hq1 hqfin α hα hα1 m j
  have he : 1 + 1 / (q.toReal - 1) = p.toReal := by
    have hq : q.toReal - 1 ≠ 0 := by linarith [hrs.symm.lt]
    field_simp [hq]
    nlinarith [hrs.mul_eq_add]
  simpa only [he] using hb

def interiorLambda (α : ℝ) (N : ℕ) : ℝ :=
  1 + α * ∑ k : Fin N, 1 / ((k.val : ℝ) + 2)

theorem interiorLambda_ge_one (α : ℝ) (hα : 0 ≤ α) (N : ℕ) : 1 ≤ interiorLambda α N := by
  unfold interiorLambda
  have hs : 0 ≤ ∑ k : Fin N, 1 / ((k.val : ℝ) + 2) := Finset.sum_nonneg fun k _ => by positivity
  linarith [mul_nonneg hα hs]

theorem interiorLambda_pos (α : ℝ) (hα : 0 ≤ α) (N : ℕ) : 0 < interiorLambda α N :=
  zero_lt_one.trans_le (interiorLambda_ge_one α hα N)

theorem interiorLambda_eq_harmonic (α : ℝ) (N : ℕ) :
    interiorLambda α N = α * (harmonic (N + 1) : ℝ) + (1 - α) := by
  simp only [interiorLambda, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.sum_range_succ']
  simp only [zero_add, Nat.cast_one, inv_one, Nat.cast_add,
    Finset.sum_range, show (1 : ℝ) + 1 = 2 by norm_num, add_assoc, one_div]
  ring

theorem interiorLambda_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (interiorLambda α) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hH : Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun N => ?_) hlog
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using
      log_add_one_le_harmonic (N + 1)
  have hlim := tendsto_atTop_add_const_right atTop (1 - α) (hH.const_mul_atTop hα)
  simpa only [← interiorLambda_eq_harmonic] using hlim

def interiorZ (α : ℝ) (N : ℕ) : FiniteLp 𝕜 p (2 * N) :=
  WithLp.toLp p fun _ => ((interiorLambda α N)⁻¹ : 𝕜)

omit [Fact (1 ≤ p)] in
theorem interiorZ_nonnegative (α : ℝ) (hα : 0 ≤ α) (N : ℕ) (i : Fin (2 * N)) :
    0 ≤ interiorZ (𝕜 := 𝕜) (p := p) α N i := by
  change 0 ≤ ((interiorLambda α N)⁻¹ : 𝕜)
  exact_mod_cast (inv_pos.mpr (interiorLambda_pos α hα N)).le

theorem interiorZ_norm (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 ≤ α) (N : ℕ) :
    ‖interiorZ (𝕜 := 𝕜) (p := p) α N‖ =
      ((2 * N : ℕ) : ℝ) ^ (1 / p.toReal) * (interiorLambda α N)⁻¹ := by
  change ‖WithLp.toLp p (Function.const (Fin (2 * N)) ((interiorLambda α N)⁻¹ : 𝕜))‖ = _
  rw [PiLp.norm_toLp_const hpfin]
  simp [abs_of_pos (interiorLambda_pos α hα N)]

theorem interior_correction_formula (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 ≤ α)
    (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / p.toReal)) * ‖interiorZ (𝕜 := 𝕜) (p := p) α N‖ =
      (2 : ℝ) ^ (1 / p.toReal) * (interiorLambda α N)⁻¹ := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [interiorZ_norm hpfin α hα, Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num) hNr.le]
  calc
    _ = (2 : ℝ) ^ (1 / p.toReal) *
        ((N : ℝ) ^ (-(1 / p.toReal)) * (N : ℝ) ^ (1 / p.toReal)) * (interiorLambda α N)⁻¹ := by ring
    _ = _ := by rw [← Real.rpow_add hNr, neg_add_cancel, Real.rpow_zero, mul_one]

theorem interior_small_correction (hpfin : p ≠ ∞) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / p.toReal)) * ‖interiorZ (𝕜 := 𝕜) (p := p) α N‖)
      atTop (𝓝 0) := by
  have hlim := (tendsto_inv_atTop_zero.comp (interiorLambda_tendsto α hα)).const_mul
    ((2 : ℝ) ^ (1 / p.toReal))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (interior_correction_formula hpfin α hα.le N hN).symm

theorem interiorLambda_eq_coefficient_sum (α : ℝ) (N : ℕ) :
    interiorLambda α N = ∑ k : Fin (N + 1), toeplitzCoefficient α k.val := by
  rw [Fin.sum_univ_succ]
  simp [interiorLambda, toeplitzCoefficient, div_eq_mul_inv, Finset.mul_sum]

def toeplitzColumnMass (α : ℝ) (m : ℕ) (j : Fin m) : ℝ :=
  ∑ i : Fin m, if j.val ≤ i.val then toeplitzCoefficient α (i.val - j.val) else 0

theorem toeplitzColumnMass_initial (α : ℝ) (hα : 0 < α) (m : ℕ) (j : Fin m)
    (N : ℕ) (hjN : j.val + N < m) :
    (∑ k : Fin (N + 1), toeplitzCoefficient α k.val) ≤ toeplitzColumnMass α m j := by
  classical
  let f : Fin (N + 1) → Fin m := fun k => ⟨j.val + k.val, by have := k.isLt; omega⟩
  have hf : Function.Injective f := by
    intro k l he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  let F (i : Fin m) : ℝ := if j.val ≤ i.val then toeplitzCoefficient α (i.val - j.val) else 0
  have he : (∑ k : Fin (N + 1), toeplitzCoefficient α k.val) =
      ∑ i ∈ Finset.univ.image f, F i := by
    rw [Finset.sum_image (fun k _ l _ h => hf h)]
    apply Finset.sum_congr rfl
    intro k _
    simp [F, f, -Fin.val_fin_le, -Fin.val_fin_lt]
  rw [he]
  change ∑ i ∈ Finset.univ.image f, F i ≤ ∑ i : Fin m, F i
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  dsimp [F]
  split_ifs
  · exact (toeplitzCoefficient_pos α hα _).le
  · exact le_rfl

theorem toeplitzColumnMass_ge_lambda (α : ℝ) (hα : 0 < α) (N : ℕ)
    (j : Fin (2 * N)) (hj : j.val < N) :
    interiorLambda α N ≤ toeplitzColumnMass α (2 * N) j := by
  rw [interiorLambda_eq_coefficient_sum]
  exact toeplitzColumnMass_initial α hα (2 * N) j N (by omega)

omit [Fact (1 ≤ p)] in
theorem interiorZ_pairing {q : ℝ≥0∞} [Fact (1 ≤ q)] (α : ℝ) (N : ℕ) (j : Fin (2 * N)) :
    finitePairing (interiorZ (𝕜 := 𝕜) (p := p) α N) (toeplitzS (p := q) α (2 * N) j) =
      ((interiorLambda α N)⁻¹ * toeplitzColumnMass α (2 * N) j : ℝ) := by
  change (∑ i : Fin (2 * N), ((interiorLambda α N)⁻¹ : 𝕜) * toeplitzS α (2 * N) j i) = _
  rw [← Finset.mul_sum, RCLike.ofReal_mul, RCLike.ofReal_inv]
  congr 1
  simp only [toeplitzColumnMass, RCLike.ofReal_sum, toeplitzS_coordinate]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [Fact (1 ≤ p)] in
theorem interiorZ_pairing_ge_one {q : ℝ≥0∞} [Fact (1 ≤ q)] (α : ℝ) (hα : 0 < α)
    (N : ℕ) (j : Fin (2 * N)) (hj : j.val < N) :
    1 ≤ finitePairing (interiorZ (𝕜 := 𝕜) (p := p) α N) (toeplitzS (p := q) α (2 * N) j) := by
  rw [interiorZ_pairing]
  have hL := interiorLambda_pos α hα.le N
  have hm := toeplitzColumnMass_ge_lambda α hα N j hj
  have hb : (1 : ℝ) ≤ (interiorLambda α N)⁻¹ * toeplitzColumnMass α (2 * N) j := by
    calc
      1 = (interiorLambda α N)⁻¹ * interiorLambda α N := (inv_mul_cancel₀ hL.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (inv_pos.mpr hL).le
  exact_mod_cast hb

/-- The source's interior auxiliary family, with the uniform bound M = p^(1/q). -/
def interiorAuxiliary {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (δ α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 2 * α * (p.toReal + q.toReal) ≤ δ) : AuxiliaryFamily 𝕜 p q δ where
  M := p.toReal ^ (1 / q.toReal)
  M_ge_one := by
    have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
    have hrs := ENNReal.HolderConjugate.toReal_of_ne_top hpfin hqfin
    exact Real.one_le_rpow hrs.lt.le (by positivity)
  d N := toeplitzD α (2 * N)
  s N := toeplitzS α (2 * N)
  z N := interiorZ α N
  biorthogonal N _ := toeplitz_biorthogonal α (2 * N)
  primal_span N _ := toeplitz_primal_span α (2 * N)
  dual_span N _ := toeplitz_dual_span α (2 * N)
  s_nonneg N _ := toeplitzS_nonnegative α hα (2 * N)
  s_norm_le N _ := toeplitzS_norm_le_conjugate hp1 hpfin α hα hα1 (2 * N)
  projection_bound N _ h hh :=
    (toeplitz_projection_norm_le hp1 hpfin α hα hα1 (2 * N) h hh).trans (by linarith)
  z_nonneg N _ := interiorZ_nonnegative α hα.le N
  z_pairing N _ := interiorZ_pairing_ge_one α hα N
  small_correction := interior_small_correction hpfin α hα

theorem aux_interior {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : AuxiliaryFamily 𝕜 p q δ, A.M = p.toReal ^ (1 / q.toReal) := by
  have hpR : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hpfin
  have hC : 0 < p.toReal + q.toReal := add_pos_of_pos_of_nonneg hpR ENNReal.toReal_nonneg
  let α : ℝ := min 1 (δ / (2 * (p.toReal + q.toReal)))
  have hα : 0 < α := lt_min zero_lt_one (div_pos hδ (mul_pos (by norm_num) hC))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hbound : 2 * α * (p.toReal + q.toReal) ≤ δ := by
    have hb : α ≤ δ / (2 * (p.toReal + q.toReal)) := min_le_right _ _
    have hc := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hC)).mp hb
    nlinarith
  exact ⟨interiorAuxiliary hp1 hpfin δ α hα hα1 hbound, rfl⟩

end PositiveBiorthogonal
