import Lean_Code.PositiveTranslates.Forest.Synthesis

/-!
# The estimates of the positive forest

Let `v` be a coefficient family living on the stages `< T`, and `cut s⋆ k v` the family
retained by a partial sum. Write `F = c₀ e0 + F.synth T v = y + x` with

* `y = c₀ e0 + F.lin T (synthCoord r F.N v)` (the component in `Y = range PY`),
* `x = ∑_{j < T} rootCoef r F.N v j • root j` (the component in `X = ker PY`).

This file proves

* `norm_coord_part_cut_le`: the `Y`-component of the partial sum has norm
  `≤ 9 ‖y‖ + 3 D ‖x‖`;
* `norm_root_part_cut_le`: the `X`-component of the partial sum has norm
  `≤ D ‖x‖ + 4 ‖y‖`;
* `norm_e0_add_synth_cut_le`: hence the partial sum has norm
  `≤ (4 D (1 + B) + 13 B) ‖F‖`.

The constant `9 = 3 · 3` comes from `norm_lin_synthCoord_le` (synthesis has norm `≤ 3`)
and `norm_lin_coordPart_le` (the coordinate-driven part of the coefficients has norm
`≤ 3 ‖y‖`); the constant `3 D` comes from the weight estimate `sum_stage_weight_le` of the
schedule and the coefficient bound `|t_j| ≤ 2 D ‖x‖` of the roots (triangle inequality — no
lower `ℓ^r` estimate for the roots is used).
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.PositiveForest

open Forest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ} (F : PositiveForest Z r)

/-! ### The coordinate-driven part: constant `9` -/

/-- Synthesis has norm at most `3` on the coordinates:
`‖(v_s + 2 m(v_{succ s}) u_s)_s‖ ≤ ‖v‖ + 2 ‖(m(v_s))_s‖ ≤ 3 ‖v‖`. -/
theorem norm_lin_synthCoord_le (hr : 1 ≤ r) {T : ℕ} {w : Coef F.N}
    (hw : ∀ s, T ≤ s → w s = 0) :
    ‖F.lin T (synthCoord r F.N w)‖ ≤ 3 * ‖F.lin T w‖ := by
  have hr0 : 0 < r := by linarith
  have h1 : F.lin T (synthCoord r F.N w) = F.lin T w +
      (2 : ℂ) • ∑ s ∈ Finset.range T, blockMean r (w (succStage s)) • F.avg s := by
    rw [lin_apply, lin_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [synthCoord_apply, map_add, map_smul, avg_eq_blk, smul_smul]
  have h2 : ‖∑ s ∈ Finset.range T, blockMean r (w (succStage s)) • F.avg s‖ ≤ ‖F.lin T w‖ := by
    rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr0,
      F.norm_sum_smul_avg_rpow hr0, F.norm_lin_rpow' hr0]
    calc ∑ s ∈ Finset.range T, ‖blockMean r (w (succStage s))‖ ^ r
        ≤ ∑ s ∈ Finset.range T, ‖blockMean r (w s)‖ ^ r :=
          sum_range_succStage_le T (fun s => ‖blockMean r (w s)‖ ^ r)
            (fun s => Real.rpow_nonneg (norm_nonneg _) _)
            (fun s hs => by rw [hw s hs, map_zero, norm_zero, Real.zero_rpow hr0.ne'])
      _ ≤ ∑ s ∈ Finset.range T, ‖F.blk s (w s)‖ ^ r :=
          Finset.sum_le_sum fun s _ =>
            Real.rpow_le_rpow (norm_nonneg _) (F.norm_blockMean_le_norm_blk hr s (w s)) hr0.le
  calc ‖F.lin T (synthCoord r F.N w)‖
      ≤ ‖F.lin T w‖ +
          ‖(2 : ℂ) • ∑ s ∈ Finset.range T, blockMean r (w (succStage s)) • F.avg s‖ := by
        rw [h1]
        exact norm_add_le _ _
    _ = ‖F.lin T w‖ +
          2 * ‖∑ s ∈ Finset.range T, blockMean r (w (succStage s)) • F.avg s‖ := by
        rw [norm_smul]
        norm_num
    _ ≤ 3 * ‖F.lin T w‖ := by linarith

/-- The coordinate-driven part of the coefficients is bounded by the coordinates:
`‖(y⁰_s + a^y_s u_s)_s‖ ≤ ‖y‖ + ‖(b_s)_s‖ + ‖(a^y_s)_s‖ ≤ 3 ‖y‖`. The bound
`‖(a^y_s)_s‖ ≤ ‖(b_s)_s‖` is the statement that `2 + R` (`R` the right shift along the
families of each target) is bounded below by `1`. -/
theorem norm_lin_coordPart_le (hr : 1 ≤ r) (T : ℕ) (v : Coef F.N) :
    ‖F.lin T (coordPart r F.N v)‖ ≤ 3 * ‖F.lin T (synthCoord r F.N v)‖ := by
  have hr0 : 0 < r := by linarith
  have hN := F.N_pos'
  have h1 : F.lin T (coordPart r F.N v) =
      F.lin T (synthCoord r F.N v) -
        ∑ s ∈ Finset.range T, blockMean r (synthCoord r F.N v s) • F.avg s +
        ∑ s ∈ Finset.range T, coordMean r F.N v s • F.avg s := by
    rw [lin_apply, lin_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [coordPart_eq hr0 hN, map_add, map_sub, map_smul, map_smul, avg_eq_blk]
  have hB : ‖∑ s ∈ Finset.range T, blockMean r (synthCoord r F.N v s) • F.avg s‖ ≤
      ‖F.lin T (synthCoord r F.N v)‖ := by
    rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr0,
      F.norm_sum_smul_avg_rpow hr0, F.norm_lin_rpow' hr0]
    exact Finset.sum_le_sum fun s _ =>
      Real.rpow_le_rpow (norm_nonneg _) (F.norm_blockMean_le_norm_blk hr s _) hr0.le
  have hAA' : ‖∑ s ∈ Finset.range T, coordMean r F.N v s • F.avg s‖ ≤
      ‖∑ s ∈ Finset.range T, coordMean r F.N v (succStage s) • F.avg s‖ := by
    rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr0,
      F.norm_sum_smul_avg_rpow hr0, F.norm_sum_smul_avg_rpow hr0]
    exact sum_range_le_sum_succStage T (fun s => ‖coordMean r F.N v s‖ ^ r)
      (fun s => Real.rpow_nonneg (norm_nonneg _) _)
      (fun j => by rw [coordMean_first, norm_zero, Real.zero_rpow hr0.ne'])
  have hrec : ∑ s ∈ Finset.range T, coordMean r F.N v (succStage s) • F.avg s =
      (1 / 2 : ℂ) • (∑ s ∈ Finset.range T, blockMean r (synthCoord r F.N v s) • F.avg s -
        ∑ s ∈ Finset.range T, coordMean r F.N v s • F.avg s) := by
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [coordMean_succStage hr0 hN, ← sub_smul, smul_smul]
  have hA' : ‖∑ s ∈ Finset.range T, coordMean r F.N v (succStage s) • F.avg s‖ ≤
      1 / 2 * (‖∑ s ∈ Finset.range T, blockMean r (synthCoord r F.N v s) • F.avg s‖ +
        ‖∑ s ∈ Finset.range T, coordMean r F.N v s • F.avg s‖) := by
    rw [hrec, norm_smul]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
  calc ‖F.lin T (coordPart r F.N v)‖
      ≤ ‖F.lin T (synthCoord r F.N v)‖ +
          ‖∑ s ∈ Finset.range T, blockMean r (synthCoord r F.N v s) • F.avg s‖ +
          ‖∑ s ∈ Finset.range T, coordMean r F.N v s • F.avg s‖ := by
        rw [h1]
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 3 * ‖F.lin T (synthCoord r F.N v)‖ := by linarith

/-- Cutting a coefficient family does not increase the norm of its combination. -/
theorem norm_lin_cut_le (hr : 0 < r) (T sStar k : ℕ) (w : Coef F.N) :
    ‖F.lin T (cut sStar k w)‖ ≤ ‖F.lin T w‖ := by
  have h := F.norm_lin_le_of_blk_le hr (T := T) (c := cut sStar k w) (c' := w) zero_le_one
    (fun s _ => by
      rw [one_mul, cut_apply]
      split_ifs
      · exact le_rfl
      · exact F.norm_blk_trunc_le hr s k (w s)
      · rw [map_zero, norm_zero]
        exact norm_nonneg _)
  rwa [one_mul] at h

/-- The coordinates of the cut coordinate-driven part: constant `9 = 3 · 3`. -/
theorem norm_lin_synthCoord_cut_coordPart_le (hr : 1 ≤ r) {T sStar : ℕ} (hs : sStar < T)
    (k : ℕ) (v : Coef F.N) :
    ‖F.lin T (synthCoord r F.N (cut sStar k (coordPart r F.N v)))‖ ≤
      9 * ‖F.lin T (synthCoord r F.N v)‖ := by
  have hr0 : 0 < r := by linarith
  have h1 := F.norm_lin_synthCoord_le hr (T := T) (w := cut sStar k (coordPart r F.N v))
    (fun s hs' => cut_apply_of_gt k _ (by omega))
  have h2 := F.norm_lin_cut_le hr0 T sStar k (coordPart r F.N v)
  have h3 := F.norm_lin_coordPart_le hr T v
  linarith

/-! ### The root-driven part: constant `3 D` -/

/-- The block of stage `s` of the coordinates of the cut root-driven part vanishes unless
`s ≤ s⋆ ≤ succStage s`, and then it is bounded by `|a^x_s|`. -/
theorem norm_blk_synthCoord_cut_rootPart_le (hr : 1 ≤ r) (v : Coef F.N) (sStar k s : ℕ) :
    ‖F.blk s (synthCoord r F.N (cut sStar k (rootPart r F.N v)) s)‖ ≤
      (if s ≤ sStar ∧ sStar ≤ succStage s then 1 else 0) * ‖rootMean r F.N v s‖ := by
  have hr0 : 0 < r := by linarith
  have hlt := lt_succStage s
  have hnn : (0 : ℝ) ≤ (if s ≤ sStar ∧ sStar ≤ succStage s then 1 else 0) *
      ‖rootMean r F.N v s‖ :=
    mul_nonneg (by split_ifs <;> norm_num) (norm_nonneg _)
  rw [synthCoord_cut_rootPart hr0 F.N_pos']
  by_cases h1 : s < sStar
  · rw [if_pos h1]
    by_cases h2 : succStage s < sStar
    · rw [if_pos h2, map_zero, norm_zero]
      exact hnn
    · rw [if_neg h2]
      by_cases h3 : succStage s = sStar
      · rw [if_pos h3, if_pos ⟨h1.le, h3.ge⟩, one_mul, F.norm_blk_smul_blockUnit hr0, norm_mul]
        have hθ0 := truncFrac_nonneg r (F.N_pos' (succStage s)) k
        have hθ1 := truncFrac_le_one hr0 (F.N_pos' (succStage s)) k
        have hle : ‖(1 - (truncFrac r (F.N (succStage s)) k : ℂ))‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_le]
          constructor <;> linarith
        exact mul_le_of_le_one_left (norm_nonneg _) hle
      · rw [if_neg h3, if_pos ⟨h1.le, by omega⟩, one_mul, F.norm_blk_smul_blockUnit hr0]
  · rw [if_neg h1]
    by_cases h2 : s = sStar
    · subst h2
      rw [if_pos rfl, if_pos ⟨le_rfl, hlt.le⟩, one_mul, map_smul, norm_smul]
      have h := F.norm_blk_trunc_le hr0 s k (blockUnit r (F.N s))
      rw [← avg_eq_blk, F.norm_avg hr0] at h
      exact mul_le_of_le_one_right (norm_nonneg _) h
    · rw [if_neg h2, map_zero, norm_zero]
      exact hnn

/-- The mean coefficients of the first families are controlled by the root component. -/
theorem norm_blockMean_firstStage_le {T : ℕ} {v : Coef F.N} (hv : ∀ s, T ≤ s → v s = 0)
    (s : ℕ) :
    ‖blockMean r (v (firstStage s))‖ ≤
      F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ := by
  have h2 : 2 * ‖blockMean r (v (firstStage s))‖ = ‖rootCoef r F.N v (stagePair s).1‖ := by
    rw [rootCoef, norm_mul]
    norm_num
    rfl
  by_cases hj : (stagePair s).1 < T
  · have h := F.norm_coeff_root_le (rootCoef r F.N v) hj
    linarith
  · have h := rootCoef_eq_zero (r := r) v hv (not_lt.mp hj)
    rw [h, norm_zero] at h2
    have h0 : 0 ≤ F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ :=
      mul_nonneg F.D_nonneg (norm_nonneg _)
    linarith

/-- The coordinates of the cut root-driven part: by the triangle inequality over the
stages, the coefficient bound of the roots and the weight estimate of the schedule,
their norm is at most `3 D ‖x‖`. -/
theorem norm_lin_synthCoord_cut_rootPart_le (hr : 1 ≤ r) {T : ℕ} {v : Coef F.N}
    (hv : ∀ s, T ≤ s → v s = 0) (sStar k : ℕ) :
    ‖F.lin T (synthCoord r F.N (cut sStar k (rootPart r F.N v)))‖ ≤
      3 * F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ := by
  have hX : 0 ≤ F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ :=
    mul_nonneg F.D_nonneg (norm_nonneg _)
  calc ‖F.lin T (synthCoord r F.N (cut sStar k (rootPart r F.N v)))‖
      ≤ ∑ s ∈ Finset.range T,
          ‖F.blk s (synthCoord r F.N (cut sStar k (rootPart r F.N v)) s)‖ := by
        rw [lin_apply]
        exact norm_sum_le _ _
    _ ≤ ∑ s ∈ Finset.range T,
          (if s ≤ sStar ∧ sStar ≤ succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0) *
            (F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖) := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine (F.norm_blk_synthCoord_cut_rootPart_le hr v sStar k s).trans ?_
        rw [norm_rootMean]
        split_ifs
        · rw [one_mul]
          exact mul_le_mul_of_nonneg_left (F.norm_blockMean_firstStage_le hv s) (by positivity)
        · simp
    _ = (∑ s ∈ Finset.range T,
          (if s ≤ sStar ∧ sStar ≤ succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0)) *
            (F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖) := by
        rw [Finset.sum_mul]
    _ ≤ 3 * (F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖) :=
        mul_le_mul_of_nonneg_right (sum_stage_weight_le sStar T) hX
    _ = 3 * F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ := by ring

/-! ### The `Y`-component of a partial sum -/

/-- **The `Y`-component of a partial sum** is bounded by `9 ‖y‖ + 3 D ‖x‖`. -/
theorem norm_coord_part_cut_le (hr : 1 ≤ r) (c0 : ℂ) {T : ℕ} {v : Coef F.N}
    (hv : ∀ s, T ≤ s → v s = 0) {sStar : ℕ} (hs : sStar < T) (k : ℕ) :
    ‖c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k v))‖ ≤
      9 * ‖c0 • F.e0 + F.lin T (synthCoord r F.N v)‖ +
        3 * F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ := by
  have hr0 : 0 < r := by linarith
  have hsplit : synthCoord r F.N (cut sStar k v) =
      synthCoord r F.N (cut sStar k (coordPart r F.N v)) +
        synthCoord r F.N (cut sStar k (rootPart r F.N v)) := by
    rw [← map_add, ← map_add, add_comm, rootPart_add_coordPart]
  have h9 := F.norm_e0_add_lin_le hr0 c0 (by norm_num : (1 : ℝ) ≤ 9)
    (F.norm_lin_synthCoord_cut_coordPart_le hr hs k v)
  calc ‖c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k v))‖
      = ‖(c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k (coordPart r F.N v)))) +
          F.lin T (synthCoord r F.N (cut sStar k (rootPart r F.N v)))‖ := by
        rw [hsplit, map_add, add_assoc]
    _ ≤ ‖c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k (coordPart r F.N v)))‖ +
          ‖F.lin T (synthCoord r F.N (cut sStar k (rootPart r F.N v)))‖ := norm_add_le _ _
    _ ≤ 9 * ‖c0 • F.e0 + F.lin T (synthCoord r F.N v)‖ +
          3 * F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ :=
        add_le_add h9 (F.norm_lin_synthCoord_cut_rootPart_le hr hv sStar k)

/-! ### The `X`-component of a partial sum -/

private theorem sum_range_ite_lt {M : Type*} [AddCommMonoid M] {q T : ℕ} (h : q ≤ T)
    (f : ℕ → M) :
    ∑ j ∈ Finset.range T, (if j < q then f j else 0) = ∑ j ∈ Finset.range q, f j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A convex combination of two consecutive initial projections of the roots. -/
theorem norm_convex_prefix_le (t : ℕ → ℂ) {q T : ℕ} (hq : q < T) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    ‖∑ j ∈ Finset.range q, t j • F.root j + ((θ : ℂ) * t q) • F.root q‖ ≤
      F.D * ‖∑ j ∈ Finset.range T, t j • F.root j‖ := by
  have e : ∑ j ∈ Finset.range q, t j • F.root j + ((θ : ℂ) * t q) • F.root q =
      ((1 - θ : ℝ) : ℂ) • ∑ j ∈ Finset.range q, t j • F.root j +
        (θ : ℂ) • ∑ j ∈ Finset.range (q + 1), t j • F.root j := by
    rw [Finset.sum_range_succ]
    push_cast
    module
  have ha := F.root_prefix t q T hq.le
  have hb := F.root_prefix t (q + 1) T hq
  rw [e]
  calc ‖((1 - θ : ℝ) : ℂ) • ∑ j ∈ Finset.range q, t j • F.root j +
        (θ : ℂ) • ∑ j ∈ Finset.range (q + 1), t j • F.root j‖
      ≤ (1 - θ) * ‖∑ j ∈ Finset.range q, t j • F.root j‖ +
          θ * ‖∑ j ∈ Finset.range (q + 1), t j • F.root j‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0]
    _ ≤ (1 - θ) * (F.D * ‖∑ j ∈ Finset.range T, t j • F.root j‖) +
          θ * (F.D * ‖∑ j ∈ Finset.range T, t j • F.root j‖) :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
          (mul_le_mul_of_nonneg_left hb h0)
    _ = F.D * ‖∑ j ∈ Finset.range T, t j • F.root j‖ := by ring

/-- **The `X`-component of a partial sum** is bounded by `D ‖x‖ + 4 ‖y‖`: it is a convex
combination of two consecutive initial projections of the roots, plus a multiple of the
root whose first family is being introduced. -/
theorem norm_root_part_cut_le (hr : 1 ≤ r) {T : ℕ} (v : Coef F.N) {sStar : ℕ} (hs : sStar < T)
    (k : ℕ) :
    ‖∑ j ∈ Finset.range T, rootCoef r F.N (cut sStar k v) j • F.root j‖ ≤
      F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ +
        4 * ‖F.lin T (synthCoord r F.N v)‖ := by
  classical
  have hr0 : 0 < r := by linarith
  have hN := F.N_pos'
  by_cases hn : (stagePair sStar).2 = 0
  · -- the cut lies in the first family of the target `q`
    obtain ⟨q, hq⟩ : ∃ q, stageOf (q, 0) = sStar :=
      ⟨(stagePair sStar).1, by rw [← hn, Prod.mk.eta, stageOf_stagePair]⟩
    subst hq
    have hqT : q < T := lt_of_le_of_lt (le_stageOf_first q) hs
    have hcoef : ∀ j, rootCoef r F.N (cut (stageOf (q, 0)) k v) j =
        if j < q then rootCoef r F.N v j
        else if j = q then 2 * blockMean r (trunc k (v (stageOf (q, 0)))) else 0 := by
      intro j
      rw [rootCoef_cut]
      by_cases h1 : j < q
      · rw [if_pos (stageOf_first_lt_iff.mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 (stageOf_first_lt_iff.mp h)), if_neg h1]
        by_cases h2 : j = q
        · subst h2
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h2, if_neg]
          intro h
          exact h2 (by simpa using stageOf_injective h)
    have hsum : ∑ j ∈ Finset.range T, rootCoef r F.N (cut (stageOf (q, 0)) k v) j • F.root j =
        ∑ j ∈ Finset.range q, rootCoef r F.N v j • F.root j +
          (2 * blockMean r (trunc k (v (stageOf (q, 0))))) • F.root q := by
      have hterm : ∀ j, rootCoef r F.N (cut (stageOf (q, 0)) k v) j • F.root j =
          (if j < q then rootCoef r F.N v j • F.root j else 0) +
            (if j = q then (2 * blockMean r (trunc k (v (stageOf (q, 0))))) • F.root q
              else 0) := by
        intro j
        rw [hcoef]
        by_cases h1 : j < q
        · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
        · rw [if_neg h1, if_neg h1, zero_add]
          by_cases h2 : j = q
          · subst h2
            rw [if_pos rfl, if_pos rfl]
          · rw [if_neg h2, if_neg h2, zero_smul]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
        sum_range_ite_lt hqT.le, Finset.sum_ite_eq' (Finset.range T) q,
        if_pos (Finset.mem_range.mpr hqT)]
    -- the mean-free part of the block of the stage which is being introduced
    have hY0 : v (stageOf (q, 0)) -
        blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0))) =
        synthCoord r F.N v (stageOf (q, 0)) -
          blockMean r (synthCoord r F.N v (stageOf (q, 0))) •
            blockUnit r (F.N (stageOf (q, 0))) :=
      sub_blockMean_smul_eq hr0 hN v _
    have hmean : blockMean r (trunc k (v (stageOf (q, 0)))) =
        blockMean r (trunc k (v (stageOf (q, 0)) -
          blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0))))) +
        blockMean r (v (stageOf (q, 0))) * (truncFrac r (F.N (stageOf (q, 0))) k : ℂ) := by
      rw [map_sub, map_sub, map_smul, map_smul, blockMean_trunc_blockUnit, smul_eq_mul]
      ring
    have hθ0 := truncFrac_nonneg r (hN (stageOf (q, 0))) k
    have hθ1 := truncFrac_le_one hr0 (hN (stageOf (q, 0))) k
    have hsplit : ∑ j ∈ Finset.range q, rootCoef r F.N v j • F.root j +
        (2 * blockMean r (trunc k (v (stageOf (q, 0))))) • F.root q =
        (∑ j ∈ Finset.range q, rootCoef r F.N v j • F.root j +
          ((truncFrac r (F.N (stageOf (q, 0))) k : ℂ) * rootCoef r F.N v q) • F.root q) +
        (2 * blockMean r (trunc k (v (stageOf (q, 0)) -
          blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0)))))) •
            F.root q := by
      rw [hmean, rootCoef]
      module
    have hsmall : ‖(2 * blockMean r (trunc k (v (stageOf (q, 0)) -
        blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0)))))) •
          F.root q‖ ≤ 4 * ‖F.lin T (synthCoord r F.N v)‖ := by
      rw [norm_smul, F.norm_root, mul_one, norm_mul]
      have e1 := F.norm_blockMean_le_norm_blk hr (stageOf (q, 0)) (trunc k (v (stageOf (q, 0)) -
        blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0)))))
      have e2 := F.norm_blk_trunc_le hr0 (stageOf (q, 0)) k (v (stageOf (q, 0)) -
        blockMean r (v (stageOf (q, 0))) • blockUnit r (F.N (stageOf (q, 0))))
      have e3 := F.norm_blk_sub_blockMean_le hr (stageOf (q, 0))
        (synthCoord r F.N v (stageOf (q, 0)))
      rw [← hY0] at e3
      have e4 := F.norm_blk_le_norm_lin hr0 hs (synthCoord r F.N v)
      have e5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [e5]
      linarith
    rw [hsum, hsplit]
    exact (norm_add_le _ _).trans
      (add_le_add (F.norm_convex_prefix_le (rootCoef r F.N v) hqT hθ0 hθ1) hsmall)
  · -- the cut lies in a later family: the root part is an initial projection
    obtain ⟨q, hq, hiff⟩ := exists_stageOf_first_lt_iff sStar
    have hcoef : ∀ j, rootCoef r F.N (cut sStar k v) j =
        if j < q then rootCoef r F.N v j else 0 := by
      intro j
      rw [rootCoef_cut]
      by_cases h1 : j < q
      · rw [if_pos ((hiff j).mpr h1), if_pos h1]
      · rw [if_neg (fun h => h1 ((hiff j).mp h)), if_neg h1, if_neg]
        intro h
        apply hn
        rw [← h, stagePair_stageOf]
    have hsum : ∑ j ∈ Finset.range T, rootCoef r F.N (cut sStar k v) j • F.root j =
        ∑ j ∈ Finset.range q, rootCoef r F.N v j • F.root j := by
      rw [← sum_range_ite_lt (hq.trans hs.le)]
      exact Finset.sum_congr rfl fun j _ => by
        rw [hcoef]
        split_ifs
        · rfl
        · rw [zero_smul]
    rw [hsum]
    exact (F.root_prefix (rootCoef r F.N v) q T (hq.trans hs.le)).trans
      (le_add_of_nonneg_right (by positivity))

/-! ### The partial sums -/

/-- **Main inequality.** Cutting the coefficient family of a combination of `e0` and the
atoms increases the norm at most by the factor `4 D (1 + B) + 13 B`. -/
theorem norm_e0_add_synth_cut_le (hr : 1 ≤ r) (c0 : ℂ) {T : ℕ} {v : Coef F.N}
    (hv : ∀ s, T ≤ s → v s = 0) {sStar : ℕ} (hs : sStar < T) (k : ℕ) :
    ‖c0 • F.e0 + F.synth T (cut sStar k v)‖ ≤
      (4 * F.D * (1 + F.B) + 13 * F.B) * ‖c0 • F.e0 + F.synth T v‖ := by
  have hr0 : 0 < r := by linarith
  have hD := F.D_nonneg
  have hv' : ∀ s, T ≤ s → cut sStar k v s = 0 := fun s hs' => cut_apply_of_gt k v (by omega)
  have hy : ‖c0 • F.e0 + F.lin T (synthCoord r F.N v)‖ ≤ F.B * ‖c0 • F.e0 + F.synth T v‖ := by
    rw [← F.PY_e0_add_synth c0 hv]
    exact F.norm_PY_apply_le _
  have hx : ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ ≤
      (1 + F.B) * ‖c0 • F.e0 + F.synth T v‖ := by
    rw [← F.e0_add_synth_sub_PY c0 hv]
    exact F.norm_sub_PY_apply_le _
  have h1 := F.norm_coord_part_cut_le hr c0 hv hs k
  have h2 := F.norm_root_part_cut_le hr v hs k
  have h3 := F.norm_lin_le_norm_e0_add_lin hr0 c0 T (synthCoord r F.N v)
  calc ‖c0 • F.e0 + F.synth T (cut sStar k v)‖
      = ‖(c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k v))) +
          ∑ j ∈ Finset.range T, rootCoef r F.N (cut sStar k v) j • F.root j‖ := by
        rw [F.synth_eq hv', add_assoc]
    _ ≤ ‖c0 • F.e0 + F.lin T (synthCoord r F.N (cut sStar k v))‖ +
          ‖∑ j ∈ Finset.range T, rootCoef r F.N (cut sStar k v) j • F.root j‖ :=
        norm_add_le _ _
    _ ≤ 4 * F.D * ‖∑ j ∈ Finset.range T, rootCoef r F.N v j • F.root j‖ +
          13 * ‖c0 • F.e0 + F.lin T (synthCoord r F.N v)‖ := by linarith
    _ ≤ 4 * F.D * ((1 + F.B) * ‖c0 • F.e0 + F.synth T v‖) +
          13 * (F.B * ‖c0 • F.e0 + F.synth T v‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hx (by positivity))
          (mul_le_mul_of_nonneg_left hy (by norm_num))
    _ = (4 * F.D * (1 + F.B) + 13 * F.B) * ‖c0 • F.e0 + F.synth T v‖ := by ring

end StructuredBases.PositiveTranslates.PositiveForest
