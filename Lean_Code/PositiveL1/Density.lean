import Lean_Code.PositiveL1.Intervals

/-!
# Density of the span of the interval cells

A closed subspace of `L¹(ℝ)` which contains the indicators of all interval cells is
everything (`eq_top_of_cells_mem`), provided that the unit intervals `(z j, z j + 1]` cover
the line and `θ ≤ 1 / 2`.  The reason is that the cells of a fixed unit interval which
contain a given point shrink to this point, so that the end points of the cells are dense.
Consequently the sequence built from the interval cells has a dense linear span
(`dense_span_splitSeq`).
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal

namespace StructuredBases
namespace PositiveL1

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Indicators of intervals -/

theorem indL_Ioc_eq_zero {a b : ℝ} (h : b ≤ a) : indL 𝕜 volume (Ioc a b) = 0 := by
  rw [Ioc_eq_empty_of_le h, indL_empty]

theorem indL_Ioc_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    indL 𝕜 volume (Ioc a b) + indL 𝕜 volume (Ioc b c) = indL 𝕜 volume (Ioc a c) := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, indL_union measurableSet_Ioc measurableSet_Ioc
    measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne (Ioc_disjoint_Ioc_of_le le_rfl)]

theorem norm_indL_Ioc {a b : ℝ} (hab : a ≤ b) : ‖indL 𝕜 volume (Ioc a b)‖ = b - a := by
  rw [norm_indL measurableSet_Ioc measure_Ioc_lt_top.ne, Real.volume_real_Ioc_of_le hab]

/-! ### Subspaces containing the indicators of the cells -/

section Cells

variable {z : ℕ → ℤ} {θ : ℝ} (W : Submodule 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)))

/-- The indicator of the part of the unit interval to the left of a cell. -/
theorem indL_unit_lo_mem (hθ : 0 < θ) (hθ1 : θ < 1)
    (hcell : ∀ k, indL 𝕜 volume (cellSet z θ k) ∈ W) (k : ℕ) :
    indL 𝕜 volume (Ioc (z (cell z θ k).unit : ℝ) (cell z θ k).lo) ∈ W := by
  induction k using cell_induction with
  | zero =>
    rw [unit_zero, lo_zero, indL_Ioc_eq_zero le_rfl]
    exact W.zero_mem
  | left n ih =>
    rw [unit_left, lo_left]
    exact ih
  | right n ih =>
    have h1 := hcell (3 * n + 1)
    rw [cellSet_def, lo_left, len_left] at h1
    have hl := len_pos z hθ hθ1 n
    rw [unit_right, lo_right, ← indL_Ioc_add (unit_le_lo z hθ hθ1 n) (by nlinarith)]
    exact W.add_mem ih h1
  | fresh n =>
    rw [unit_fresh, lo_fresh, indL_Ioc_eq_zero le_rfl]
    exact W.zero_mem

/-- Every point of a unit interval lies in arbitrarily short cells of this unit interval. -/
theorem exists_cell (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioc (z j : ℝ) (z j + 1)) (d : ℕ) :
    ∃ k, (cell z θ k).unit = j ∧ t ∈ cellSet z θ k ∧ (cell z θ k).len ≤ (1 - θ) ^ d := by
  have hθ1 : θ < 1 := by linarith
  induction d with
  | zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨0, unit_zero z θ, by rwa [cellSet_zero], by rw [len_zero, pow_zero]⟩
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      exact ⟨3 * n + 3, unit_fresh z θ n, by rwa [cellSet_fresh], by rw [len_fresh, pow_zero]⟩
  | succ d ih =>
    obtain ⟨k, hk1, hk2, hk3⟩ := ih
    have hl := len_pos z hθ hθ1 k
    have hstep : ∀ c : ℝ, c ≤ 1 - θ → c * (cell z θ k).len ≤ (1 - θ) ^ (d + 1) := fun c hc =>
      calc c * (cell z θ k).len ≤ (1 - θ) * (cell z θ k).len :=
            mul_le_mul_of_nonneg_right hc hl.le
        _ ≤ (1 - θ) * (1 - θ) ^ d := mul_le_mul_of_nonneg_left hk3 (by linarith)
        _ = (1 - θ) ^ (d + 1) := (pow_succ' _ _).symm
    rw [← cellSet_left_union_right z hθ hθ1 k] at hk2
    rcases hk2 with h | h
    · exact ⟨3 * k + 1, by rw [unit_left, hk1], h, by rw [len_left]; exact hstep θ (by linarith)⟩
    · exact ⟨3 * k + 2, by rw [unit_right, hk1], h, by rw [len_right]; exact hstep _ le_rfl⟩

variable (hW : IsClosed (W : Set (Lp 𝕜 1 (volume : Measure ℝ))))
include hW

/-- The indicators of the initial parts of the unit intervals. -/
theorem indL_unit_mem (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hcell : ∀ k, indL 𝕜 volume (cellSet z θ k) ∈ W) (j : ℕ) {t : ℝ} (h1 : (z j : ℝ) ≤ t)
    (h2 : t ≤ z j + 1) : indL 𝕜 volume (Ioc (z j : ℝ) t) ∈ W := by
  have hθ1 : θ < 1 := by linarith
  rcases h1.eq_or_lt with rfl | h1'
  · rw [indL_Ioc_eq_zero le_rfl]
    exact W.zero_mem
  · rw [← SetLike.mem_coe, ← hW.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - θ < 1)
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_cell (z := z) hθ hθ' j ⟨h1', h2⟩ d
    have hmem := indL_unit_lo_mem W hθ hθ1 hcell k
    have hlo := unit_le_lo z hθ hθ1 k
    rw [hk1] at hmem hlo
    rw [cellSet_def] at hk2
    refine ⟨_, hmem, ?_⟩
    rw [dist_eq_norm, ← indL_Ioc_add hlo hk2.1.le, add_sub_cancel_left, norm_indL_Ioc hk2.1.le]
    linarith [hk2.2]

/-- The indicators of all intervals which lie in a unit interval. -/
theorem indL_Ioc_mem_of_unit (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hcell : ∀ k, indL 𝕜 volume (cellSet z θ k) ∈ W) (j : ℕ) {a b : ℝ} (h1 : (z j : ℝ) ≤ a)
    (h2 : a ≤ b) (h3 : b ≤ z j + 1) : indL 𝕜 volume (Ioc a b) ∈ W := by
  have ha := indL_unit_mem W hW hθ hθ' hcell j h1 (h2.trans h3)
  have hb := indL_unit_mem W hW hθ hθ' hcell j (h1.trans h2) h3
  have hsub : indL 𝕜 volume (Ioc a b) =
      indL 𝕜 volume (Ioc (z j : ℝ) b) - indL 𝕜 volume (Ioc (z j : ℝ) a) := by
    rw [← indL_Ioc_add h1 h2, add_sub_cancel_left]
  rw [hsub]
  exact W.sub_mem hb ha

/-- A closed subspace of `L¹(ℝ)` containing the indicators of all cells is everything. -/
theorem eq_top_of_cells_mem (hz : Function.Bijective z) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2)
    (hcell : ∀ k, indL 𝕜 volume (cellSet z θ k) ∈ W) : W = ⊤ := by
  refine eq_top_of_indL_Ioc_inter_mem W hW (U := fun n => Ioc (z n : ℝ) (z n + 1))
    (fun n => measurableSet_Ioc) (fun n => measure_Ioc_lt_top.ne)
    (fun i j hij => disjoint_unit hz.injective hij) ?_ ?_ ?_
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := hz.surjective (⌈x⌉ - 1)
    refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
    · rw [hn]
      push_cast
      linarith [Int.ceil_lt_add_one x]
    · rw [hn]
      push_cast
      linarith [Int.le_ceil x]
  · intro n
    exact indL_Ioc_mem_of_unit W hW hθ hθ' hcell n le_rfl (by linarith) le_rfl
  · intro n a b
    rw [Ioc_inter_Ioc]
    rcases le_total (min b ((z n : ℝ) + 1)) (max a (z n)) with h | h
    · rw [indL_Ioc_eq_zero h]
      exact W.zero_mem
    · exact indL_Ioc_mem_of_unit W hW hθ hθ' hcell n (le_max_right _ _) h (min_le_right _ _)

end Cells

/-- The sequence built from the interval cells has a dense linear span in `L¹(ℝ)`. -/
theorem dense_span_splitSeq {z : ℕ → ℤ} {θ : ℝ} (hz : Function.Bijective z) (hθ' : θ ≤ 1 / 2)
    (h : SplitCells (volume : Measure ℝ) θ (cellSet z θ)) :
    Dense (Submodule.span 𝕜 (Set.range (splitSeq (h.vec 𝕜))) :
      Set (Lp 𝕜 1 (volume : Measure ℝ))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine eq_top_of_cells_mem _ (Submodule.isClosed_topologicalClosure _) hz h.theta_pos hθ'
    fun k => ?_
  exact Submodule.le_topologicalClosure _ (h.indL_mem_span k)

end PositiveL1
end StructuredBases
