import Lean_Code.PositiveTranslates.Forest.Tools

/-!
# A model of the positive forest

A sanity check: the hypotheses of `PositiveForest` can be satisfied. For `1 ≤ p < ∞` we
take `Z = ℓ^p × ℓ^p` (with the maximum norm), `PY (y, x) = (y, 0)`, the unit vectors of
the first factor as `e0` and as the coordinates (one coordinate per stage), and the unit
vectors of the second factor as roots; here `B = D = 1`.

The construction also illustrates how the tools of `Forest/Tools.lean` are used
(`lr_norm_of_family`). The file is independent of the proof of the main theorem; the main
theorem is applied to the model at the end of `Forest/Main.lean` (`ForestModel.exists_basis`).
-/

noncomputable section

open scoped BigOperators ENNReal

namespace StructuredBases.PositiveTranslates.ForestModel

open Forest

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The model space `ℓ^p × ℓ^p`. -/
abbrev Space : Type := lp (fun _ : ℕ => ℂ) p × lp (fun _ : ℕ => ℂ) p

/-- The unit vectors of the first factor. -/
def unitY (n : ℕ) : Space p := (lp.single p n (1 : ℂ), 0)

/-- The unit vectors of the second factor. -/
def unitX (n : ℕ) : Space p := (0, lp.single p n (1 : ℂ))

/-- The projection onto the first factor. -/
def proj : Space p →L[ℂ] Space p :=
  (ContinuousLinearMap.inl ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)

theorem proj_apply (z : Space p) : proj p z = (z.1, 0) := rfl

/-- The index map: `e0 = unitY 0`, and the single coordinate of stage `s` is
`unitY (s + 1)`. -/
def index : Option (Σ _ : ℕ, Fin 1) → ℕ := fun x => x.elim 0 fun q => q.1 + 1

theorem index_injective : Function.Injective index := by
  rintro (_ | ⟨s, i⟩) (_ | ⟨t, j⟩) h
  · rfl
  · simp [index] at h
  · simp [index] at h
  · simp only [index, Option.elim_some, add_left_inj] at h
    subst h
    have : i = j := Subsingleton.elim _ _
    subst this
    rfl

variable {p}

theorem toReal_pos (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp

omit [Fact (1 ≤ p)] in
theorem sum_smul_unitY (S : Finset ℕ) (c : ℕ → ℂ) :
    ∑ n ∈ S, c n • unitY p n = (∑ n ∈ S, lp.single p n (c n), 0) := by
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [unitY, ← lp.single_smul]
  · rw [Prod.snd_sum]
    simp [unitY]

omit [Fact (1 ≤ p)] in
theorem sum_smul_unitX (S : Finset ℕ) (c : ℕ → ℂ) :
    ∑ n ∈ S, c n • unitX p n = (0, ∑ n ∈ S, lp.single p n (c n)) := by
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp [unitX]
  · rw [Prod.snd_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [unitX, ← lp.single_smul]

theorem norm_sum_smul_unitY (hp : p ≠ ∞) (S : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ n ∈ S, c n • unitY p n‖ ^ p.toReal = ∑ n ∈ S, ‖c n‖ ^ p.toReal := by
  rw [sum_smul_unitY, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _),
    lp.norm_sum_single (toReal_pos hp)]

theorem norm_sum_smul_unitX (hp : p ≠ ∞) (S : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ n ∈ S, c n • unitX p n‖ ^ p.toReal = ∑ n ∈ S, ‖c n‖ ^ p.toReal := by
  rw [sum_smul_unitX, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
    lp.norm_sum_single (toReal_pos hp)]

/-- Vectors of the first factor are limits of combinations of the `unitY n`. -/
theorem mem_closure_span_unitY (hp : p ≠ ∞) (y : lp (fun _ : ℕ => ℂ) p) :
    ((y, 0) : Space p) ∈ closure (Submodule.span ℂ (Set.range (unitY p)) : Set (Space p)) := by
  have h := (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ => ℂ) p) (lp (fun _ : ℕ => ℂ) p)).hasSum
    (lp.hasSum_single hp y)
  refine mem_closure_of_tendsto h (Filter.Eventually.of_forall fun S => ?_)
  refine Submodule.sum_mem _ fun n _ => ?_
  have : (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ => ℂ) p) (lp (fun _ : ℕ => ℂ) p))
      (lp.single p n (y n)) = y n • unitY p n := by
    simp [unitY, ← lp.single_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- Vectors of the second factor are limits of combinations of the `unitX n`. -/
theorem mem_closure_span_unitX (hp : p ≠ ∞) (x : lp (fun _ : ℕ => ℂ) p) :
    ((0, x) : Space p) ∈ closure (Submodule.span ℂ (Set.range (unitX p)) : Set (Space p)) := by
  have h := (ContinuousLinearMap.inr ℂ (lp (fun _ : ℕ => ℂ) p) (lp (fun _ : ℕ => ℂ) p)).hasSum
    (lp.hasSum_single hp x)
  refine mem_closure_of_tendsto h (Filter.Eventually.of_forall fun S => ?_)
  refine Submodule.sum_mem _ fun n _ => ?_
  have : (ContinuousLinearMap.inr ℂ (lp (fun _ : ℕ => ℂ) p) (lp (fun _ : ℕ => ℂ) p))
      (lp.single p n (x n)) = x n • unitX p n := by
    simp [unitX, ← lp.single_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- **The model.** A positive forest in `ℓ^p × ℓ^p` with `B = D = 1` and one coordinate
per stage. -/
def forest (hp : p ≠ ∞) : PositiveForest (Space p) p.toReal where
  PY := proj p
  B := 1
  D := 1
  e0 := unitY p (index none)
  root := unitX p
  N := fun _ => 1
  coord := fun s i => unitY p (index (some ⟨s, i⟩))
  PY_idem z := rfl
  norm_PY_le := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [proj_apply, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _), one_mul]
    exact norm_fst_le z
  N_pos _ := le_rfl
  PY_e0 := by simp [proj_apply, unitY]
  PY_coord s i := by simp [proj_apply, unitY]
  lr_norm := lr_norm_of_family (unitY p) (norm_sum_smul_unitY hp) index index_injective
  coord_dense := by
    intro y hy
    have h1 : y = (y.1, 0) := by rw [← hy, proj_apply]
    rw [h1]
    refine closure_mono (SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_))
      (mem_closure_span_unitY hp y.1)
    rintro _ ⟨n, rfl⟩
    rcases n with _ | n
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, ⟨0, rfl⟩⟩)
  PY_root j := by simp [proj_apply, unitX]
  norm_root j := by
    rw [unitX, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
      lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_one]
  root_dense := by
    intro x hx
    have h1 : x = (0, x.2) := by
      rw [proj_apply] at hx
      exact Prod.ext (by simpa using congrArg Prod.fst hx) rfl
    rw [h1]
    exact mem_closure_span_unitX hp x.2
  root_prefix := by
    intro t m M hmM
    rw [one_mul, ← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (toReal_pos hp),
      norm_sum_smul_unitX hp, norm_sum_smul_unitX hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmM)
      fun _ _ _ => Real.rpow_nonneg (norm_nonneg _) _

/-! ### The first vectors of the model sequence

These computations are a test of the definitions `avg`, `target`, `atom`, `offset`, `seq`:
in the model every stage has exactly one atom, so that `seq (s + 1)` is the atom of stage
`s`, and the schedule starts with the stages `(0,0), (0,1), (1,0), (0,2), (1,1), …`. -/

theorem forest_N (hp : p ≠ ∞) (s : ℕ) : (forest hp).N s = 1 := rfl

theorem forest_coord (hp : p ≠ ∞) (s : ℕ) (i : Fin ((forest hp).N s)) :
    (forest hp).coord s i = unitY p (s + 1) := rfl

theorem forest_root (hp : p ≠ ∞) (j : ℕ) : (forest hp).root j = unitX p j := rfl

theorem forest_offset (hp : p ≠ ∞) (s : ℕ) : (forest hp).offset s = s + 1 := by
  induction s with
  | zero => simp
  | succ s ih => rw [PositiveForest.offset_succ, ih, forest_N]

theorem forest_avg (hp : p ≠ ∞) (s : ℕ) : (forest hp).avg s = unitY p (s + 1) := by
  have h1 : primalScale p.toReal ((forest hp).N s) = 1 := by
    rw [forest_N]
    simp [primalScale]
  rw [PositiveForest.avg_eq, h1, Finset.sum_congr rfl (fun i _ => forest_coord hp s i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, forest_N, one_smul]
  simp

/-- In the model, `seq (s + 1)` is the atom of stage `s`: its coordinate plus twice its
target. -/
theorem forest_seq_succ (hp : p ≠ ∞) (s : ℕ) :
    (forest hp).seq (s + 1) = unitY p (s + 1) + (2 : ℂ) • (forest hp).target s := by
  have h1 : dualScale p.toReal ((forest hp).N s) = 1 := by
    rw [forest_N]
    simp [dualScale]
  have h := (forest hp).seq_offset_add s ⟨0, by rw [forest_N]; exact Nat.one_pos⟩
  rw [forest_offset, PositiveForest.atom_eq, forest_coord, h1] at h
  simpa using h

/-- Stage `0 = (0, 0)`: the first family of target `0`. -/
example (hp : p ≠ ∞) : (forest hp).seq 1 = unitY p 1 + (2 : ℂ) • unitX p 0 := by
  have e : stageOf (0, 0) = 0 := by decide
  have ht := (forest hp).target_stageOf_zero 0
  rw [e, forest_root] at ht
  rw [forest_seq_succ hp 0, ht]

/-- Stage `1 = (0, 1)`: its target is the average of stage `0`. -/
example (hp : p ≠ ∞) : (forest hp).seq 2 = unitY p 2 + (2 : ℂ) • unitY p 1 := by
  have e : stageOf (0, 0 + 1) = 1 := by decide
  have e' : stageOf (0, 0) = 0 := by decide
  have ht := (forest hp).target_stageOf_succ 0 0
  rw [e, e', forest_avg] at ht
  rw [forest_seq_succ hp 1, ht]

/-- Stage `2 = (1, 0)`: the first family of target `1`. -/
example (hp : p ≠ ∞) : (forest hp).seq 3 = unitY p 3 + (2 : ℂ) • unitX p 1 := by
  have e : stageOf (1, 0) = 2 := by decide
  have ht := (forest hp).target_stageOf_zero 1
  rw [e, forest_root] at ht
  rw [forest_seq_succ hp 2, ht]

/-- Stage `3 = (0, 2)`: its target is the average of stage `1 = (0, 1)`. -/
example (hp : p ≠ ∞) : (forest hp).seq 4 = unitY p 4 + (2 : ℂ) • unitY p 2 := by
  have e : stageOf (0, 1 + 1) = 3 := by decide
  have e' : stageOf (0, 1) = 1 := by decide
  have ht := (forest hp).target_stageOf_succ 0 1
  rw [e, e', forest_avg] at ht
  rw [forest_seq_succ hp 3, ht]

/-- Stage `4 = (1, 1)`: its target is the average of stage `2 = (1, 0)`. -/
example (hp : p ≠ ∞) : (forest hp).seq 5 = unitY p 5 + (2 : ℂ) • unitY p 3 := by
  have e : stageOf (1, 0 + 1) = 4 := by decide
  have e' : stageOf (1, 0) = 2 := by decide
  have ht := (forest hp).target_stageOf_succ 1 0
  rw [e, e', forest_avg] at ht
  rw [forest_seq_succ hp 4, ht]

end StructuredBases.PositiveTranslates.ForestModel
