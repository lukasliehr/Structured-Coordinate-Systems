import Lean_Code.PositiveTranslates.Forest.Schedule

/-!
# Scalar bookkeeping for the positive forest

This file contains everything about the positive forest which only concerns coefficient
vectors: no Banach space appears.

A *block* is a vector `y : Fin n → ℂ` (the coefficients with respect to the `n` coordinate
vectors of one stage).

* `primalScale r n = n^{-1/r}`, `dualScale r n = n^{-(r-1)/r}`.
* `blockUnit r n`: the constant block `n^{-1/r}` (coefficients of the normalized average `u`).
* `blockMean r y = n^{-(r-1)/r} ∑ᵢ yᵢ`: the functional `m` of the paper; `m(u) = 1` and
  `|m(y)|^r ≤ ∑ᵢ |yᵢ|^r` (Hölder, `norm_blockMean_rpow_le`).
* `trunc k`: restriction to the first `k` coordinates (`E_k`), `truncFrac r n k = m(E_k u)`,
  a number in `[0, 1]`.

A *coefficient family* `v : Coef N` assigns a block `v s : Fin (N s) → ℂ` to every stage.

* `cut s⋆ k v`: the coefficients retained by the partial sum which contains the stages
  `< s⋆` and the first `k` atoms of stage `s⋆`.
* `synthCoord r N v`: the coordinates of the `Y`-part of `∑ v s i • atom s i`, namely
  `v s + 2 m(v (succStage s)) • u_s`.
* `rootCoef r N v j = 2 m(v (stageOf (j, 0)))`: the coefficient of `root j`.
* `rootMean`, `coordMean`, `rootPart`, `coordPart`: the splitting of the mean coefficients
  `a_s = m(v s)` and of `v` itself into the part driven by the root coefficients
  (`a^x_{(j,n)} = (-1/2)^n t_j / 2`) and the remainder, which is controlled by the
  coordinates (`a^y_{(j,0)} = 0`, `a^y_{(j,n+1)} = (b_{(j,n)} - a^y_{(j,n)}) / 2`).
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.Forest

/-! ### The two scales -/

/-- `n^{-1/r}`: the coefficient of the normalized average of `n` coordinate vectors. -/
def primalScale (r : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-1 / r)

/-- `n^{-(r-1)/r}`: the scale of the mean functional and of the coupling in the atoms. -/
def dualScale (r : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(r - 1) / r)

theorem primalScale_pos (r : ℝ) {n : ℕ} (hn : 0 < n) : 0 < primalScale r n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem dualScale_pos (r : ℝ) {n : ℕ} (hn : 0 < n) : 0 < dualScale r n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem card_mul_primalScale_mul_dualScale {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * primalScale r n * dualScale r n = 1 := by
  have h : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [primalScale, dualScale, mul_assoc, ← Real.rpow_add h]
  have he : -1 / r + -(r - 1) / r = -1 := by field_simp; ring
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ h.ne']

theorem card_mul_primalScale_rpow {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * primalScale r n ^ r = 1 := by
  have h : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [primalScale, ← Real.rpow_mul h.le, div_mul_cancel₀ _ hr.ne', Real.rpow_neg_one,
    mul_inv_cancel₀ h.ne']

theorem dualScale_rpow_mul {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    dualScale r n ^ r * (n : ℝ) ^ (r - 1) = 1 := by
  have h : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [dualScale, ← Real.rpow_mul h.le, ← Real.rpow_add h]
  have he : -(r - 1) / r * r + (r - 1) = 0 := by field_simp; ring
  rw [he, Real.rpow_zero]

/-! ### Blocks -/

/-- Restriction of a block to its first `k` coordinates (`E_k` in the paper). -/
def trunc {n : ℕ} (k : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun y i := if (i : ℕ) < k then y i else 0
  map_add' y z := by
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]
  map_smul' c y := by
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]

theorem trunc_apply {n : ℕ} (k : ℕ) (y : Fin n → ℂ) (i : Fin n) :
    trunc k y i = if (i : ℕ) < k then y i else 0 := rfl

theorem norm_trunc_apply_le {n : ℕ} (k : ℕ) (y : Fin n → ℂ) (i : Fin n) :
    ‖trunc k y i‖ ≤ ‖y i‖ := by
  rw [trunc_apply]
  split_ifs
  · exact le_rfl
  · simp

/-- The mean functional `m(y) = n^{-(r-1)/r} ∑ᵢ yᵢ` of a block. -/
def blockMean (r : ℝ) {n : ℕ} : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun y := (dualScale r n : ℂ) * ∑ i, y i
  map_add' y z := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem blockMean_apply (r : ℝ) {n : ℕ} (y : Fin n → ℂ) :
    blockMean r y = (dualScale r n : ℂ) * ∑ i, y i := rfl

/-- The constant block `n^{-1/r}`: the coefficients of the normalized average. -/
def blockUnit (r : ℝ) (n : ℕ) : Fin n → ℂ := fun _ => (primalScale r n : ℂ)

@[simp] theorem blockUnit_apply (r : ℝ) (n : ℕ) (i : Fin n) :
    blockUnit r n i = (primalScale r n : ℂ) := rfl

theorem blockMean_blockUnit {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    blockMean r (blockUnit r n) = 1 := by
  rw [blockMean_apply]
  simp only [blockUnit_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have h := card_mul_primalScale_mul_dualScale hr hn
  have h' : ((dualScale r n : ℝ) : ℂ) * ((n : ℂ) * (primalScale r n : ℂ)) =
      (((n : ℝ) * primalScale r n * dualScale r n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h', h]
  simp

theorem sum_norm_blockUnit_rpow {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, ‖blockUnit r n i‖ ^ r = 1 := by
  simp only [blockUnit_apply, Complex.norm_real, Real.norm_of_nonneg (primalScale_pos r hn).le,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact card_mul_primalScale_rpow hr hn

/-- **Hölder's inequality** for the mean functional: `|m(y)|^r ≤ ∑ᵢ |yᵢ|^r`. -/
theorem norm_blockMean_rpow_le {r : ℝ} (hr : 1 ≤ r) {n : ℕ} (hn : 0 < n) (y : Fin n → ℂ) :
    ‖blockMean r y‖ ^ r ≤ ∑ i, ‖y i‖ ^ r := by
  have hr0 : 0 < r := by linarith
  have hd := dualScale_pos r hn
  rw [blockMean_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le,
    Real.mul_rpow hd.le (norm_nonneg _)]
  have h1 : ‖∑ i, y i‖ ^ r ≤ (∑ i, ‖y i‖) ^ r :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) hr0.le
  have h2 := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ (fun i => ‖y i‖) hr
  simp only [abs_norm, Finset.card_univ, Fintype.card_fin] at h2
  calc dualScale r n ^ r * ‖∑ i, y i‖ ^ r
      ≤ dualScale r n ^ r * ((n : ℝ) ^ (r - 1) * ∑ i, ‖y i‖ ^ r) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hd.le _)
    _ = (dualScale r n ^ r * (n : ℝ) ^ (r - 1)) * ∑ i, ‖y i‖ ^ r := by ring
    _ = ∑ i, ‖y i‖ ^ r := by rw [dualScale_rpow_mul hr0 hn, one_mul]

/-- `m(E_k u)`: the proportion `min(k, n) / n` of a family which has been introduced. -/
def truncFrac (r : ℝ) (n k : ℕ) : ℝ :=
  dualScale r n * primalScale r n * ((Finset.univ.filter fun i : Fin n => (i : ℕ) < k).card : ℝ)

theorem blockMean_trunc_blockUnit (r : ℝ) (n k : ℕ) :
    blockMean r (trunc k (blockUnit r n)) = (truncFrac r n k : ℂ) := by
  rw [blockMean_apply]
  simp only [trunc_apply, blockUnit_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    truncFrac]
  push_cast
  ring

theorem truncFrac_nonneg (r : ℝ) {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 ≤ truncFrac r n k :=
  mul_nonneg (mul_nonneg (dualScale_pos r hn).le (primalScale_pos r hn).le) (Nat.cast_nonneg _)

theorem truncFrac_le_one {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    truncFrac r n k ≤ 1 := by
  have hc : ((Finset.univ.filter fun i : Fin n => (i : ℕ) < k).card : ℝ) ≤ n := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => (i : ℕ) < k)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hpos : 0 ≤ dualScale r n * primalScale r n :=
    mul_nonneg (dualScale_pos r hn).le (primalScale_pos r hn).le
  calc truncFrac r n k ≤ dualScale r n * primalScale r n * n :=
        mul_le_mul_of_nonneg_left hc hpos
    _ = (n : ℝ) * primalScale r n * dualScale r n := by ring
    _ = 1 := card_mul_primalScale_mul_dualScale hr hn

/-! ### Coefficient families -/

/-- A coefficient family: one block for every stage. -/
abbrev Coef (N : ℕ → ℕ) : Type := (s : ℕ) → Fin (N s) → ℂ

variable (r : ℝ) (N : ℕ → ℕ)

variable {N} in
/-- The coefficients retained by the partial sum consisting of all stages `< s⋆` and of the
first `k` atoms of stage `s⋆`. -/
def cut (sStar k : ℕ) : Coef N →ₗ[ℂ] Coef N where
  toFun v s := if s < sStar then v s else if s = sStar then trunc k (v s) else 0
  map_add' v w := by
    funext s
    by_cases h1 : s < sStar
    · simp [h1]
    · by_cases h2 : s = sStar <;> simp [h1, h2]
  map_smul' c v := by
    funext s
    by_cases h1 : s < sStar
    · simp [h1]
    · by_cases h2 : s = sStar <;> simp [h1, h2]

variable {N}

theorem cut_apply (sStar k : ℕ) (v : Coef N) (s : ℕ) :
    cut sStar k v s = if s < sStar then v s else if s = sStar then trunc k (v s) else 0 := rfl

theorem cut_apply_of_lt {sStar s : ℕ} (k : ℕ) (v : Coef N) (h : s < sStar) :
    cut sStar k v s = v s := by
  rw [cut_apply, if_pos h]

theorem cut_apply_self (sStar k : ℕ) (v : Coef N) :
    cut sStar k v sStar = trunc k (v sStar) := by
  rw [cut_apply, if_neg (lt_irrefl _), if_pos rfl]

theorem cut_apply_of_gt {sStar s : ℕ} (k : ℕ) (v : Coef N) (h : sStar < s) :
    cut sStar k v s = 0 := by
  rw [cut_apply, if_neg (by omega), if_neg (by omega)]

variable (N)

/-- The coordinates of the `Y`-part of the combination `∑ v s i • atom s i`: the block of
stage `s` is `v s + 2 m(v (succStage s)) • u_s`. -/
def synthCoord : Coef N →ₗ[ℂ] Coef N where
  toFun v s := v s + (2 * blockMean r (v (succStage s))) • blockUnit r (N s)
  map_add' v w := by
    funext s
    simp only [Pi.add_apply, map_add, mul_add, add_smul]
    abel
  map_smul' c v := by
    funext s
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
    congr 2
    ring

/-- The coefficient of `root j` in the combination `∑ v s i • atom s i`. -/
def rootCoef (v : Coef N) (j : ℕ) : ℂ := 2 * blockMean r (v (stageOf (j, 0)))

/-- The part `a^x_s = (-1/2)^n · m(v (j, 0))` of the mean coefficient `m(v s)`,
`stagePair s = (j, n)`, which is determined by the root coefficient of the target. -/
def rootMean (v : Coef N) (s : ℕ) : ℂ :=
  (-1 / 2 : ℂ) ^ (stagePair s).2 * blockMean r (v (firstStage s))

/-- The part `a^y_s = m(v s) - a^x_s` of the mean coefficient which is controlled by the
coordinates. -/
def coordMean (v : Coef N) (s : ℕ) : ℂ := blockMean r (v s) - rootMean r N v s

/-- The part `a^x_s • u_s` of a coefficient family which is driven by the root coefficients. -/
def rootPart (v : Coef N) : Coef N := fun s => rootMean r N v s • blockUnit r (N s)

/-- The part of a coefficient family which is driven by the coordinates. -/
def coordPart (v : Coef N) : Coef N := fun s => v s - rootMean r N v s • blockUnit r (N s)

variable {r N}

theorem synthCoord_apply (v : Coef N) (s : ℕ) :
    synthCoord r N v s = v s + (2 * blockMean r (v (succStage s))) • blockUnit r (N s) := rfl

theorem rootPart_add_coordPart (v : Coef N) : rootPart r N v + coordPart r N v = v := by
  funext s
  simp [rootPart, coordPart]

theorem blockMean_synthCoord (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N) (s : ℕ) :
    blockMean r (synthCoord r N v s) =
      blockMean r (v s) + 2 * blockMean r (v (succStage s)) := by
  rw [synthCoord_apply, map_add, map_smul, blockMean_blockUnit hr (hN s), smul_eq_mul, mul_one]

theorem rootCoef_eq_zero (v : Coef N) {T j : ℕ} (hv : ∀ s, T ≤ s → v s = 0) (hj : T ≤ j) :
    rootCoef r N v j = 0 := by
  rw [rootCoef, hv _ (hj.trans (le_stageOf_first j)), map_zero, mul_zero]

/-- Rewriting the stage inside a mean coefficient (the blocks have dependent types). -/
theorem blockMean_congr (v : Coef N) {s t : ℕ} (h : s = t) :
    blockMean r (v s) = blockMean r (v t) := by
  subst h
  rfl

theorem rootMean_first (v : Coef N) (j : ℕ) :
    rootMean r N v (stageOf (j, 0)) = blockMean r (v (stageOf (j, 0))) := by
  rw [rootMean, stagePair_stageOf, blockMean_congr v (firstStage_stageOf j 0)]
  simp

theorem rootMean_succStage (v : Coef N) (s : ℕ) :
    rootMean r N v (succStage s) = -(1 / 2) * rootMean r N v s := by
  rw [rootMean, rootMean, stagePair_succStage, blockMean_congr v (firstStage_succStage s),
    pow_succ]
  ring

theorem norm_rootMean (v : Coef N) (s : ℕ) :
    ‖rootMean r N v s‖ = (1 / 2 : ℝ) ^ (stagePair s).2 * ‖blockMean r (v (firstStage s))‖ := by
  rw [rootMean, norm_mul, norm_pow]
  congr 2
  rw [norm_div, norm_neg, norm_one]
  simp

theorem coordMean_first (v : Coef N) (j : ℕ) : coordMean r N v (stageOf (j, 0)) = 0 := by
  rw [coordMean, rootMean_first, sub_self]

theorem coordMean_succStage (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N) (s : ℕ) :
    coordMean r N v (succStage s) =
      (1 / 2 : ℂ) * (blockMean r (synthCoord r N v s) - coordMean r N v s) := by
  rw [coordMean, coordMean, rootMean_succStage, blockMean_synthCoord hr hN]
  ring

theorem blockMean_rootPart (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N) (s : ℕ) :
    blockMean r (rootPart r N v s) = rootMean r N v s := by
  rw [rootPart, map_smul, blockMean_blockUnit hr (hN s), smul_eq_mul, mul_one]

/-- The mean-free part of `v s` equals the mean-free part of the coordinates. -/
theorem sub_blockMean_smul_eq (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N) (s : ℕ) :
    v s - blockMean r (v s) • blockUnit r (N s) =
      synthCoord r N v s - blockMean r (synthCoord r N v s) • blockUnit r (N s) := by
  rw [blockMean_synthCoord hr hN, synthCoord_apply, add_smul]
  abel

/-- The coordinate-driven part in terms of the coordinates: `y⁰_s + a^y_s u_s`. -/
theorem coordPart_eq (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N) (s : ℕ) :
    coordPart r N v s =
      synthCoord r N v s - blockMean r (synthCoord r N v s) • blockUnit r (N s) +
        coordMean r N v s • blockUnit r (N s) := by
  rw [← sub_blockMean_smul_eq hr hN, coordPart, coordMean, sub_smul]
  abel

/-- The mean coefficients of the cut root-driven part. -/
theorem blockMean_cut_rootPart (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N)
    (sStar k t : ℕ) :
    blockMean r (cut sStar k (rootPart r N v) t) =
      if t < sStar then rootMean r N v t
      else if t = sStar then rootMean r N v t * (truncFrac r (N t) k : ℂ) else 0 := by
  by_cases h1 : t < sStar
  · rw [if_pos h1, cut_apply_of_lt k _ h1, blockMean_rootPart hr hN]
  · rw [if_neg h1]
    by_cases h2 : t = sStar
    · subst h2
      rw [if_pos rfl, cut_apply_self, rootPart, map_smul, map_smul, blockMean_trunc_blockUnit,
        smul_eq_mul]
    · rw [if_neg h2, cut_apply_of_gt k _ (by omega), map_zero]

/-- The coordinates of the cut root-driven part: only the latest families of the targets
survive (the earlier ones cancel because `a^x_s + 2 a^x_{succ s} = 0`). -/
theorem synthCoord_cut_rootPart (hr : 0 < r) (hN : ∀ s, 0 < N s) (v : Coef N)
    (sStar k s : ℕ) :
    synthCoord r N (cut sStar k (rootPart r N v)) s =
      if s < sStar then
        (if succStage s < sStar then 0
        else if succStage s = sStar then
          ((1 - (truncFrac r (N (succStage s)) k : ℂ)) * rootMean r N v s) • blockUnit r (N s)
        else rootMean r N v s • blockUnit r (N s))
      else if s = sStar then rootMean r N v s • trunc k (blockUnit r (N s))
      else 0 := by
  have hlt := lt_succStage s
  rw [synthCoord_apply, blockMean_cut_rootPart hr hN]
  by_cases h1 : s < sStar
  · rw [if_pos h1, cut_apply_of_lt k _ h1]
    by_cases h2 : succStage s < sStar
    · rw [if_pos h2, if_pos h2, rootMean_succStage, rootPart, ← add_smul]
      have : rootMean r N v s + 2 * (-(1 / 2) * rootMean r N v s) = 0 := by ring
      rw [this, zero_smul]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : succStage s = sStar
      · rw [if_pos h3, if_pos h3, rootMean_succStage, rootPart, ← add_smul]
        congr 1
        ring
      · rw [if_neg h3, if_neg h3, mul_zero, zero_smul, add_zero, rootPart]
  · rw [if_neg h1, if_neg (by omega : ¬ succStage s < sStar),
      if_neg (by omega : ¬ succStage s = sStar), mul_zero, zero_smul, add_zero]
    by_cases h2 : s = sStar
    · subst h2
      rw [if_pos rfl, cut_apply_self, rootPart, map_smul]
    · rw [if_neg h2, cut_apply_of_gt k _ (by omega)]

/-- The root coefficients of a cut family. -/
theorem rootCoef_cut (v : Coef N) (sStar k j : ℕ) :
    rootCoef r N (cut sStar k v) j =
      if stageOf (j, 0) < sStar then rootCoef r N v j
      else if stageOf (j, 0) = sStar then 2 * blockMean r (trunc k (v (stageOf (j, 0))))
      else 0 := by
  rw [rootCoef, cut_apply]
  split_ifs
  · rfl
  · rfl
  · rw [map_zero, mul_zero]

end StructuredBases.PositiveTranslates.Forest
