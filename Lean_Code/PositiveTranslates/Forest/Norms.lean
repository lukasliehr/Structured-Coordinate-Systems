import Lean_Code.PositiveTranslates.Forest.Defs

/-!
# The `ℓ^r` structure of the coordinates of a positive forest

For a positive forest `F` we introduce the linear maps

* `F.blk s y = ∑ᵢ y i • coord s i` (the combination of the coordinates of stage `s`),
* `F.lin T c = ∑_{s < T} F.blk s (c s)` (the combination of the coordinates of all stages
  `< T`),

and translate the hypothesis `lr_norm` into statements about the norm of `Z`:

* `norm_lin_rpow'`: `‖F.lin T c‖^r = ∑_{s < T} ‖F.blk s (c s)‖^r`;
* `norm_lin_le_of_blk_le`: blockwise estimates pass to `F.lin T`;
* `norm_blockMean_le_norm_blk`: Hölder's inequality `|m(y)| ≤ ‖F.blk s y‖`;
* `norm_sum_smul_avg_rpow`: the averages `avg s` are again an `ℓ^r` sequence.

Because of these facts all `ℓ^r` computations of the paper can be carried out with the
norm (and the triangle inequality) of `Z` itself.
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.PositiveForest

open Forest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ} (F : PositiveForest Z r)

/-! ### Elementary consequences of the hypotheses -/

theorem B_nonneg : 0 ≤ F.B := (norm_nonneg _).trans F.norm_PY_le

/-- A normalized basis has basis constant at least one. -/
theorem one_le_D : 1 ≤ F.D := by
  have h := F.root_prefix (fun _ => 1) 1 1 le_rfl
  simp only [Finset.range_one, Finset.sum_singleton, one_smul, F.norm_root, mul_one] at h
  exact h

theorem D_nonneg : 0 ≤ F.D := zero_le_one.trans F.one_le_D

include F in
/-- The exponent of a positive forest cannot be zero. -/
theorem r_ne_zero : r ≠ 0 := by
  rintro rfl
  have h := F.lr_norm 0 1 0
  simp only [zero_smul, Pi.zero_apply, Finset.sum_const_zero, add_zero, norm_zero,
    Real.rpow_zero, Finset.range_one, Finset.sum_singleton, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h1 : (1 : ℝ) ≤ F.N 0 := by exact_mod_cast F.N_pos 0
  linarith

theorem norm_PY_apply_le (z : Z) : ‖F.PY z‖ ≤ F.B * ‖z‖ :=
  (F.PY.le_opNorm z).trans (mul_le_mul_of_nonneg_right F.norm_PY_le (norm_nonneg z))

theorem norm_sub_PY_apply_le (z : Z) : ‖z - F.PY z‖ ≤ (1 + F.B) * ‖z‖ := by
  calc ‖z - F.PY z‖ ≤ ‖z‖ + ‖F.PY z‖ := norm_sub_le _ _
    _ ≤ ‖z‖ + F.B * ‖z‖ := by linarith [F.norm_PY_apply_le z]
    _ = (1 + F.B) * ‖z‖ := by ring

theorem PY_sum_root (t : ℕ → ℂ) (S : Finset ℕ) : F.PY (∑ j ∈ S, t j • F.root j) = 0 := by
  simp [map_sum, F.PY_root]

/-- The coefficients of a combination of roots are controlled by the combination. -/
theorem norm_coeff_root_le (t : ℕ → ℂ) {T j : ℕ} (hj : j < T) :
    ‖t j‖ ≤ 2 * F.D * ‖∑ i ∈ Finset.range T, t i • F.root i‖ := by
  have h1 := F.root_prefix t (j + 1) T hj
  have h2 := F.root_prefix t j T (by omega)
  have h3 : t j • F.root j =
      ∑ i ∈ Finset.range (j + 1), t i • F.root i - ∑ i ∈ Finset.range j, t i • F.root i := by
    rw [Finset.sum_range_succ]
    abel
  calc ‖t j‖ = ‖t j • F.root j‖ := by rw [norm_smul, F.norm_root, mul_one]
    _ ≤ ‖∑ i ∈ Finset.range (j + 1), t i • F.root i‖ + ‖∑ i ∈ Finset.range j, t i • F.root i‖ := by
        rw [h3]
        exact norm_sub_le _ _
    _ ≤ 2 * F.D * ‖∑ i ∈ Finset.range T, t i • F.root i‖ := by linarith

/-! ### Combinations of the coordinates -/

/-- The combination `∑ᵢ y i • coord s i` of the coordinate vectors of stage `s`. -/
def blk (s : ℕ) : (Fin (F.N s) → ℂ) →ₗ[ℂ] Z := Fintype.linearCombination ℂ (F.coord s)

theorem blk_apply (s : ℕ) (y : Fin (F.N s) → ℂ) : F.blk s y = ∑ i, y i • F.coord s i :=
  Fintype.linearCombination_apply ℂ _ _

/-- The combination `∑_{s < T} ∑ᵢ c s i • coord s i` of the coordinates of the stages `< T`. -/
def lin (T : ℕ) : Coef F.N →ₗ[ℂ] Z :=
  ∑ s ∈ Finset.range T, (F.blk s).comp (LinearMap.proj s)

theorem lin_apply (T : ℕ) (c : Coef F.N) :
    F.lin T c = ∑ s ∈ Finset.range T, F.blk s (c s) := by
  simp [lin]

theorem PY_blk (s : ℕ) (y : Fin (F.N s) → ℂ) : F.PY (F.blk s y) = F.blk s y := by
  simp [blk_apply, map_sum, F.PY_coord]

theorem PY_lin (T : ℕ) (c : Coef F.N) : F.PY (F.lin T c) = F.lin T c := by
  simp [lin_apply, map_sum, F.PY_blk]

theorem avg_eq_blk (s : ℕ) : F.avg s = F.blk s (blockUnit r (F.N s)) := by
  rw [avg_eq, blk_apply, Finset.smul_sum]
  rfl

theorem PY_avg (s : ℕ) : F.PY (F.avg s) = F.avg s := by
  rw [avg_eq_blk, PY_blk]

/-- The sum of the atoms of a stage with coefficients `v`. -/
theorem sum_smul_atom (s : ℕ) (y : Fin (F.N s) → ℂ) :
    ∑ i, y i • F.atom s i = F.blk s y + (2 * blockMean r y) • F.target s := by
  simp only [atom_eq, smul_add, Finset.sum_add_distrib, blk_apply, smul_smul, ← Finset.sum_smul]
  congr 2
  rw [blockMean_apply, ← Finset.sum_mul]
  ring

/-! ### Norms -/

theorem norm_lin_rpow (hr : 0 < r) (T : ℕ) (c : Coef F.N) :
    ‖F.lin T c‖ ^ r = ∑ s ∈ Finset.range T, ∑ i, ‖c s i‖ ^ r := by
  have h := F.lr_norm 0 T c
  rw [zero_smul, zero_add, norm_zero, Real.zero_rpow hr.ne', zero_add] at h
  rw [lin_apply]
  simp only [blk_apply]
  exact h

theorem norm_e0_add_lin_rpow (hr : 0 < r) (c0 : ℂ) (T : ℕ) (c : Coef F.N) :
    ‖c0 • F.e0 + F.lin T c‖ ^ r = ‖c0‖ ^ r + ‖F.lin T c‖ ^ r := by
  rw [F.norm_lin_rpow hr, ← F.lr_norm c0 T c, lin_apply]
  simp only [blk_apply]

theorem norm_blk_rpow (hr : 0 < r) (s : ℕ) (y : Fin (F.N s) → ℂ) :
    ‖F.blk s y‖ ^ r = ∑ i, ‖y i‖ ^ r := by
  classical
  have h := F.norm_lin_rpow hr (s + 1) (Pi.single s y)
  have hs : s ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.lt_succ_self s)
  have h1 : F.lin (s + 1) (Pi.single s y) = F.blk s y := by
    rw [lin_apply, Finset.sum_eq_single s]
    · rw [Pi.single_eq_same]
    · intro t _ hts
      rw [Pi.single_eq_of_ne hts, map_zero]
    · exact fun h => absurd hs h
  have h2 : ∑ t ∈ Finset.range (s + 1), ∑ i, ‖(Pi.single s y : Coef F.N) t i‖ ^ r =
      ∑ i, ‖y i‖ ^ r := by
    rw [Finset.sum_eq_single s]
    · rw [Pi.single_eq_same]
    · intro t _ hts
      rw [Pi.single_eq_of_ne hts]
      simp [Real.zero_rpow hr.ne']
    · exact fun h => absurd hs h
  rw [← h1, h, h2]

/-- The `ℓ^r` identity over the stages `< T`. -/
theorem norm_lin_rpow' (hr : 0 < r) (T : ℕ) (c : Coef F.N) :
    ‖F.lin T c‖ ^ r = ∑ s ∈ Finset.range T, ‖F.blk s (c s)‖ ^ r := by
  rw [F.norm_lin_rpow hr]
  exact Finset.sum_congr rfl fun s _ => (F.norm_blk_rpow hr s (c s)).symm

theorem norm_blk_le_norm_lin (hr : 0 < r) {T s : ℕ} (hs : s < T) (c : Coef F.N) :
    ‖F.blk s (c s)‖ ≤ ‖F.lin T c‖ := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr, F.norm_lin_rpow' hr]
  exact Finset.single_le_sum (f := fun s => ‖F.blk s (c s)‖ ^ r)
    (fun t _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_range.mpr hs)

/-- Blockwise estimates pass to the combination over all stages. -/
theorem norm_lin_le_of_blk_le (hr : 0 < r) {T : ℕ} {c c' : Coef F.N} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ s < T, ‖F.blk s (c s)‖ ≤ K * ‖F.blk s (c' s)‖) :
    ‖F.lin T c‖ ≤ K * ‖F.lin T c'‖ := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)) hr,
    Real.mul_rpow hK (norm_nonneg _), F.norm_lin_rpow' hr, F.norm_lin_rpow' hr, Finset.mul_sum]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [← Real.mul_rpow hK (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h s (Finset.mem_range.mp hs)) hr.le

theorem norm_lin_le_norm_e0_add_lin (hr : 0 < r) (c0 : ℂ) (T : ℕ) (c : Coef F.N) :
    ‖F.lin T c‖ ≤ ‖c0 • F.e0 + F.lin T c‖ := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr, F.norm_e0_add_lin_rpow hr]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- An estimate between combinations of coordinates survives adding the same multiple
of `e0`. -/
theorem norm_e0_add_lin_le (hr : 0 < r) (c0 : ℂ) {T : ℕ} {c c' : Coef F.N} {K : ℝ}
    (hK : 1 ≤ K) (h : ‖F.lin T c‖ ≤ K * ‖F.lin T c'‖) :
    ‖c0 • F.e0 + F.lin T c‖ ≤ K * ‖c0 • F.e0 + F.lin T c'‖ := by
  have hK0 : 0 ≤ K := by linarith
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _)) hr,
    Real.mul_rpow hK0 (norm_nonneg _), F.norm_e0_add_lin_rpow hr, F.norm_e0_add_lin_rpow hr,
    mul_add]
  have h1 : ‖F.lin T c‖ ^ r ≤ K ^ r * ‖F.lin T c'‖ ^ r := by
    rw [← Real.mul_rpow hK0 (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) h hr.le
  have h2 : ‖c0‖ ^ r ≤ K ^ r * ‖c0‖ ^ r :=
    le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg _) _) (Real.one_le_rpow hK hr.le)
  exact add_le_add h2 h1

theorem norm_e0 (hr : 0 < r) : ‖F.e0‖ = 1 := by
  have h := F.lr_norm 1 0 0
  simp only [one_smul, Finset.range_zero, Finset.sum_empty, add_zero, norm_one,
    Real.one_rpow] at h
  exact (Real.rpow_left_inj (norm_nonneg _) zero_le_one hr.ne').mp (by rw [h, Real.one_rpow])

theorem norm_coord (hr : 0 < r) (s : ℕ) (i : Fin (F.N s)) : ‖F.coord s i‖ = 1 := by
  classical
  have h := F.norm_blk_rpow hr s (Pi.single i 1)
  have h1 : F.blk s (Pi.single i 1) = F.coord s i := by
    rw [blk_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, zero_smul]
    · exact fun h => absurd (Finset.mem_univ i) h
  have h2 : ∑ j, ‖(Pi.single i 1 : Fin (F.N s) → ℂ) j‖ ^ r = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, norm_one, Real.one_rpow]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, norm_zero, Real.zero_rpow hr.ne']
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [h1, h2] at h
  exact (Real.rpow_left_inj (norm_nonneg _) zero_le_one hr.ne').mp (by rw [h, Real.one_rpow])

/-- The averages are unit vectors. -/
theorem norm_avg (hr : 0 < r) (s : ℕ) : ‖F.avg s‖ = 1 := by
  have h := F.norm_blk_rpow hr s (blockUnit r (F.N s))
  rw [sum_norm_blockUnit_rpow hr (F.N_pos s), ← avg_eq_blk] at h
  exact (Real.rpow_left_inj (norm_nonneg _) zero_le_one hr.ne').mp (by rw [h, Real.one_rpow])

/-- The targets are unit vectors. -/
theorem norm_target (hr : 0 < r) (s : ℕ) : ‖F.target s‖ = 1 := by
  rw [target]
  split_ifs
  · exact F.norm_root _
  · exact F.norm_avg hr _

/-- **Hölder's inequality**: the mean functional is dominated by the norm. -/
theorem norm_blockMean_le_norm_blk (hr : 1 ≤ r) (s : ℕ) (y : Fin (F.N s) → ℂ) :
    ‖blockMean r y‖ ≤ ‖F.blk s y‖ := by
  have hr0 : 0 < r := by linarith
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr0, F.norm_blk_rpow hr0]
  exact norm_blockMean_rpow_le hr (F.N_pos s) y

theorem norm_blk_trunc_le (hr : 0 < r) (s k : ℕ) (y : Fin (F.N s) → ℂ) :
    ‖F.blk s (trunc k y)‖ ≤ ‖F.blk s y‖ := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr, F.norm_blk_rpow hr,
    F.norm_blk_rpow hr]
  exact Finset.sum_le_sum fun i _ =>
    Real.rpow_le_rpow (norm_nonneg _) (norm_trunc_apply_le k y i) hr.le

theorem norm_blk_smul_blockUnit (hr : 0 < r) (s : ℕ) (c : ℂ) :
    ‖F.blk s (c • blockUnit r (F.N s))‖ = ‖c‖ := by
  rw [map_smul, norm_smul, ← avg_eq_blk, F.norm_avg hr, mul_one]

/-- Removing the mean of a block at most doubles the norm. -/
theorem norm_blk_sub_blockMean_le (hr : 1 ≤ r) (s : ℕ) (y : Fin (F.N s) → ℂ) :
    ‖F.blk s (y - blockMean r y • blockUnit r (F.N s))‖ ≤ 2 * ‖F.blk s y‖ := by
  have hr0 : 0 < r := by linarith
  rw [map_sub, map_smul, ← avg_eq_blk]
  calc ‖F.blk s y - blockMean r y • F.avg s‖
      ≤ ‖F.blk s y‖ + ‖blockMean r y • F.avg s‖ := norm_sub_le _ _
    _ = ‖F.blk s y‖ + ‖blockMean r y‖ := by rw [norm_smul, F.norm_avg hr0, mul_one]
    _ ≤ 2 * ‖F.blk s y‖ := by linarith [F.norm_blockMean_le_norm_blk hr s y]

theorem sum_smul_avg (T : ℕ) (c : ℕ → ℂ) :
    ∑ s ∈ Finset.range T, c s • F.avg s = F.lin T (fun s => c s • blockUnit r (F.N s)) := by
  rw [lin_apply]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, avg_eq_blk]

/-- The averages form an `ℓ^r` sequence. -/
theorem norm_sum_smul_avg_rpow (hr : 0 < r) (T : ℕ) (c : ℕ → ℂ) :
    ‖∑ s ∈ Finset.range T, c s • F.avg s‖ ^ r = ∑ s ∈ Finset.range T, ‖c s‖ ^ r := by
  rw [sum_smul_avg, F.norm_lin_rpow' hr]
  exact Finset.sum_congr rfl fun s _ => by rw [F.norm_blk_smul_blockUnit hr]

/-- The `ℓ^r` identity for an arbitrary finite set of stages. -/
theorem lr_norm_finset (c0 : ℂ) (S : Finset ℕ) (c : (s : ℕ) → Fin (F.N s) → ℂ) :
    ‖c0 • F.e0 + ∑ s ∈ S, ∑ i, c s i • F.coord s i‖ ^ r =
      ‖c0‖ ^ r + ∑ s ∈ S, ∑ i, ‖c s i‖ ^ r := by
  classical
  have hsub : S ⊆ Finset.range (S.sup id + 1) := fun s hs =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hs))
  have h := F.lr_norm c0 (S.sup id + 1) (fun s => if s ∈ S then c s else 0)
  have h1 : ∑ s ∈ Finset.range (S.sup id + 1),
      ∑ i, (if s ∈ S then c s else 0) i • F.coord s i = ∑ s ∈ S, ∑ i, c s i • F.coord s i := by
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun s hs => by rw [if_pos hs]
    · intro s _ hs
      rw [if_neg hs]
      simp
  have h2 : ∑ s ∈ Finset.range (S.sup id + 1),
      ∑ i, ‖(if s ∈ S then c s else 0) i‖ ^ r = ∑ s ∈ S, ∑ i, ‖c s i‖ ^ r := by
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun s hs => by rw [if_pos hs]
    · intro s _ hs
      rw [if_neg hs]
      simp [Real.zero_rpow F.r_ne_zero]
  rw [h1, h2] at h
  exact h

end StructuredBases.PositiveTranslates.PositiveForest
