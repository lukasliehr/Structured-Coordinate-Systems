import Lean_Code.SchauderTranslates.TorusFejerKernel

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

theorem fejerMultiplier_nonneg (N : ℕ) (k : ℤ) : 0 ≤ fejerMultiplier N k := by
  unfold fejerMultiplier
  positivity

theorem fejerMultiplier_le_one (N : ℕ) (k : ℤ) : fejerMultiplier N k ≤ 1 := by
  unfold fejerMultiplier
  apply (div_le_one (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).mpr
  exact_mod_cast Nat.sub_le (N + 1) k.natAbs

@[simp] theorem fejerMultiplier_zero (N : ℕ) : fejerMultiplier N 0 = 1 := by
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [fejerMultiplier, Int.natAbs_zero, Nat.sub_zero, div_self hN]

@[simp] theorem fejerMultiplier_neg (N : ℕ) (k : ℤ) : fejerMultiplier N (-k) = fejerMultiplier N k := by
  simp [fejerMultiplier]

theorem fejerMultiplier_outside (N : ℕ) (k : ℤ) (hk : N < k.natAbs) : fejerMultiplier N k = 0 := by
  simp [fejerMultiplier, Nat.sub_eq_zero_of_le hk]

/-- On each fixed mode the exact Fourier multiplier tends to one. -/
theorem fejerMultiplier_tendsto (k : ℤ) : Tendsto (fun N => fejerMultiplier N k) atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h : Tendsto (fun N : ℕ => 1 - (k.natAbs : ℝ) * (((N + 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  apply h.congr'
  filter_upwards [eventually_ge_atTop k.natAbs] with N hN
  have hNk : k.natAbs ≤ N + 1 := by omega
  have hpos : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fejerMultiplier, Nat.cast_sub hNk]
  field_simp

theorem torusFejerMultiplier_nonneg {d : ℕ} (N : ℕ) (k : Fin d → ℤ) :
    0 ≤ torusFejerMultiplier N k := Finset.prod_nonneg (fun i _ => fejerMultiplier_nonneg N (k i))

theorem torusFejerMultiplier_le_one {d : ℕ} (N : ℕ) (k : Fin d → ℤ) :
    torusFejerMultiplier N k ≤ 1 :=
  Finset.prod_le_one (fun i _ => fejerMultiplier_nonneg N (k i)) (fun i _ => fejerMultiplier_le_one N (k i))

@[simp] theorem torusFejerMultiplier_zero (d N : ℕ) : torusFejerMultiplier N (0 : Fin d → ℤ) = 1 := by
  simp [torusFejerMultiplier]

@[simp] theorem torusFejerMultiplier_neg {d : ℕ} (N : ℕ) (k : Fin d → ℤ) :
    torusFejerMultiplier N (-k) = torusFejerMultiplier N k := by
  simp [torusFejerMultiplier]

theorem torusFejerMultiplier_tendsto {d : ℕ} (k : Fin d → ℤ) :
    Tendsto (fun N => torusFejerMultiplier N k) atTop (𝓝 1) := by
  have h := tendsto_finset_prod Finset.univ (fun i _ => fejerMultiplier_tendsto (k i))
  simpa only [torusFejerMultiplier, Finset.prod_const_one] using h

end SchauderTranslates
