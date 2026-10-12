import Lean_Code.PositiveBiorthogonal.Auxiliary

/-! The finite summing/difference family at p = 1. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜]

def endpointD (m : ℕ) (j : Fin m) : FiniteLp 𝕜 1 m :=
  PiLp.single 1 j 1 - leftShift m (PiLp.single 1 j 1)

def endpointS (m : ℕ) (j : Fin m) : FiniteLp 𝕜 ∞ m :=
  WithLp.toLp ∞ fun i => if j.val ≤ i.val then 1 else 0

theorem endpointS_difference (m : ℕ) (j : Fin m) :
    endpointS (𝕜 := 𝕜) m j - rightShift m (endpointS m j) = PiLp.single ∞ j 1 := by
  ext i
  change endpointS (𝕜 := 𝕜) m j i - finiteRightShift m (endpointS m j) i = _
  by_cases hji : j = i
  · subst j
    by_cases hi : 0 < i.val
    · have hn : ¬ i.val ≤ i.val - 1 := by omega
      simp [endpointS, finiteRightShift, hi, -Fin.val_fin_le, -Fin.val_fin_lt, hn]
    · simp [endpointS, finiteRightShift, hi, -Fin.val_fin_le, -Fin.val_fin_lt]
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hi : 0 < i.val
    · have heq : (j.val ≤ i.val) ↔ (j.val ≤ i.val - 1) := by omega
      simp [endpointS, finiteRightShift, hi, -Fin.val_fin_le, -Fin.val_fin_lt, heq, hji]
    · have hn : ¬ j.val ≤ i.val := by omega
      simp [endpointS, finiteRightShift, hi, -Fin.val_fin_le, -Fin.val_fin_lt, hn, hji]

theorem endpoint_biorthogonal (m : ℕ) (i j : Fin m) :
    finitePairing (endpointD (𝕜 := 𝕜) m i) (endpointS m j) = if i = j then 1 else 0 := by
  rw [endpointD, ← finitePairingFunctional_apply]
  rw [map_sub]
  simp only [finitePairingFunctional_apply]
  rw [finitePairing_comm (leftShift m (PiLp.single 1 i 1)) (endpointS m j),
    ← finite_shift_pairing, finitePairing_single_right, finitePairing_single_left]
  have he := congrArg (fun x : FiniteLp 𝕜 ∞ m => x i) (endpointS_difference m j)
  change endpointS (𝕜 := 𝕜) m j i - rightShift m (endpointS m j) i = _ at he
  simpa [PiLp.single_apply, eq_comm] using he

theorem endpoint_primal_span (m : ℕ) :
    Submodule.span 𝕜 (Set.range (endpointD (𝕜 := 𝕜) m)) = ⊤ :=
  finiteBiorthogonal_span _ (endpointS m) (endpoint_biorthogonal m)

theorem endpoint_dual_span (m : ℕ) :
    Submodule.span 𝕜 (Set.range (endpointS (𝕜 := 𝕜) m)) = ⊤ := by
  apply finiteBiorthogonal_span _ (endpointD m)
  intro i j
  rw [finitePairing_comm]
  simpa only [eq_comm] using endpoint_biorthogonal m j i

theorem endpointS_nonnegative (m : ℕ) (j i : Fin m) : 0 ≤ endpointS (𝕜 := 𝕜) m j i := by
  change 0 ≤ if j.val ≤ i.val then (1 : 𝕜) else 0
  split_ifs <;> simp

theorem endpointS_norm (m : ℕ) (j : Fin m) : ‖endpointS (𝕜 := 𝕜) m j‖ = 1 := by
  apply le_antisymm
  · rw [← PiLp.norm_ofLp]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖if j.val ≤ i.val then (1 : 𝕜) else 0‖ ≤ 1
    split_ifs <;> simp
  · have h := PiLp.norm_apply_le (endpointS (𝕜 := 𝕜) m j) j
    simpa [endpointS] using h

/-- Summing coordinate units below a cutoff gives its indicator vector. -/
theorem endpoint_unit_sum (m h : ℕ) (i : Fin m) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h),
      PiLp.single 1 j (1 : 𝕜)) i = if i.val < h then 1 else 0 := by
  classical
  simp

theorem endpoint_prefix (m h : ℕ) (hh : h ≤ m) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h), endpointD (𝕜 := 𝕜) m j =
      if hz : h = 0 then 0 else PiLp.single 1 ⟨h - 1, by omega⟩ 1 := by
  classical
  simp only [endpointD, Finset.sum_sub_distrib, ← map_sum]
  by_cases hz : h = 0
  · subst h
    simp
  · rw [dif_neg hz]
    cases m with
    | zero => omega
    | succ m =>
      ext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rw [PiLp.sub_apply, leftShift_last, sub_zero, endpoint_unit_sum]
        simp only [PiLp.single_apply, Fin.val_last]
        by_cases hm : h = m + 1
        · subst h
          simp [show (Fin.last m : Fin (m + 1)) = ⟨m, by omega⟩ from rfl]
        · have hle : h ≤ m := by omega
          have hne : (Fin.last m : Fin (m + 1)) ≠ ⟨h - 1, by omega⟩ := by
            intro he
            have := congrArg Fin.val he
            simp only [Fin.val_last] at this
            omega
          simp [Nat.not_lt.mpr hle, hne]
      · rw [PiLp.sub_apply, leftShift_castSucc, endpoint_unit_sum, endpoint_unit_sum]
        simp only [PiLp.single_apply, Fin.val_castSucc, Fin.val_succ]
        by_cases hk : k.val + 1 < h
        · have hk' : k.val < h := by omega
          have hne : k.castSucc ≠ (⟨h - 1, by omega⟩ : Fin (m + 1)) := by
            intro he
            have := congrArg Fin.val he
            dsimp at this
            omega
          simp [hk, hk', hne]
        · by_cases hk' : k.val < h
          · have heq : k.castSucc = (⟨h - 1, by omega⟩ : Fin (m + 1)) := by
              apply Fin.ext
              dsimp
              omega
            simp [hk, hk', heq]
          · have hne : k.castSucc ≠ (⟨h - 1, by omega⟩ : Fin (m + 1)) := by
              intro he
              have := congrArg Fin.val he
              dsimp at this
              omega
            simp [hk, hk', hne]

theorem endpoint_prefix_norm (m h : ℕ) (hh : h ≤ m) :
    ‖∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < h), endpointD (𝕜 := 𝕜) m j‖ ≤ 1 := by
  rw [endpoint_prefix m h hh]
  split_ifs <;> simp

theorem endpoint_projection_single (m h : ℕ) (i : Fin m) :
    finiteRankProjection (endpointD (𝕜 := 𝕜) m) (endpointS m) h (PiLp.single 1 i 1) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < min h (i.val + 1)), endpointD m j := by
  classical
  rw [finiteRankProjection_apply]
  simp only [finitePairing_single_left, endpointS, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < h <;> by_cases hji : j.val ≤ i.val
  all_goals
    have hm : (j.val < min h (i.val + 1)) ↔ (j.val < h ∧ j.val ≤ i.val) := by omega
    simp only [hm, hj, hji, and_true, and_false, if_true, if_false, one_smul, zero_smul]

theorem endpoint_projection_norm (m h : ℕ) (hh : h ≤ m) :
    ‖finiteRankProjection (endpointD (𝕜 := 𝕜) m) (endpointS m) h‖ ≤ 1 := by
  classical
  let Q := finiteRankProjection (endpointD (𝕜 := 𝕜) m) (endpointS m) h
  have hu (i : Fin m) : ‖Q (PiLp.single 1 i 1)‖ ≤ 1 := by
    rw [show Q = finiteRankProjection (endpointD m) (endpointS m) h from rfl,
      endpoint_projection_single]
    exact endpoint_prefix_norm _ _ ((min_le_left _ _).trans hh)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hx : (∑ i : Fin m, x i • PiLp.single 1 i (1 : 𝕜)) = x := by
    simpa using (PiLp.basisFun 1 𝕜 (Fin m)).sum_repr x
  change ‖Q x‖ ≤ 1 * ‖x‖
  calc
    ‖Q x‖ = ‖∑ i : Fin m, x i • Q (PiLp.single 1 i 1)‖ := by
      conv_lhs => rw [← hx]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin m, ‖x i • Q (PiLp.single 1 i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ‖x i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, mul_one] using mul_le_mul_of_nonneg_left (hu i) (norm_nonneg (x i))
    _ = 1 * ‖x‖ := by rw [one_mul, PiLp.norm_eq_of_L1]

def endpointZ (m : ℕ) : FiniteLp 𝕜 1 m :=
  if hm : 0 < m then PiLp.single 1 ⟨m - 1, by omega⟩ 1 else 0

theorem endpointZ_norm (m : ℕ) (hm : 0 < m) : ‖endpointZ (𝕜 := 𝕜) m‖ = 1 := by
  simp [endpointZ, hm]

theorem endpointZ_nonnegative (m : ℕ) (i : Fin m) : 0 ≤ endpointZ (𝕜 := 𝕜) m i := by
  have hm : 0 < m := by have := i.isLt; omega
  simp only [endpointZ, dif_pos hm, PiLp.single_apply]
  split_ifs <;> simp

theorem endpointZ_pairing (m : ℕ) (j : Fin m) :
    finitePairing (endpointZ (𝕜 := 𝕜) m) (endpointS m j) = 1 := by
  have hm : 0 < m := by have := j.isLt; omega
  have hj : j.val ≤ m - 1 := by have := j.isLt; omega
  simp [endpointZ, hm, endpointS, hj, -Fin.val_fin_le]

theorem endpoint_small_correction :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / (1 : ℝ≥0∞).toReal)) *
      ‖endpointZ (𝕜 := 𝕜) (2 * N)‖) atTop (𝓝 0) := by
  apply (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [endpointZ_norm (2 * N) (by omega)]
  simp [Real.rpow_neg_one]

/-- The endpoint auxiliary family, including the vanishing correction estimate. -/
def endpointAuxiliary (δ : ℝ) (hδ : 0 < δ) : AuxiliaryFamily 𝕜 1 ∞ δ where
  M := 1
  M_ge_one := le_rfl
  d N := endpointD (2 * N)
  s N := endpointS (2 * N)
  z N := endpointZ (2 * N)
  biorthogonal N _ := endpoint_biorthogonal (2 * N)
  primal_span N _ := endpoint_primal_span (2 * N)
  dual_span N _ := endpoint_dual_span (2 * N)
  s_nonneg N _ := endpointS_nonnegative (2 * N)
  s_norm_le N _ j := (endpointS_norm (2 * N) j).le
  projection_bound N _ h hh := (endpoint_projection_norm (2 * N) h hh).trans (by linarith)
  z_nonneg N _ := endpointZ_nonnegative (2 * N)
  z_pairing N _ j _ := (endpointZ_pairing (2 * N) j).ge
  small_correction := endpoint_small_correction

theorem aux_endpoint (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : AuxiliaryFamily 𝕜 1 ∞ δ, A.M = 1 := ⟨endpointAuxiliary δ hδ, rfl⟩

end PositiveBiorthogonal
