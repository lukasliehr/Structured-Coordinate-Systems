import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# An abstract splitting scheme and its prefix bounds

This file contains the purely normed-space part of the construction of a Schauder basis
of `L¹(ℝ)` consisting of non-negative functions.

The cells of the construction are indexed by `ℕ` in the order of their creation.  At time
`n` the cells with index in `Finset.Icc n (3 * n)` are alive.  In step `n` the cell `n` is
split into the cells `3 * n + 1` (the part of proportion `θ`) and `3 * n + 2`, and
`3 * n + 3` is a fresh cell.  For a cell `k` we are given a normalised vector `e k` and a
functional `φ k`; the hypotheses are collected in `SplitSystem`.  The sequence

`b 0 = e 0`, `b (2 * n + 1) = e (3 * n + 2) + e (3 * n + 3)`,
`b (2 * n + 2) = e (3 * n + 1) + e (3 * n + 3)`

(`splitSeq e`) then satisfies the prefix bound
`‖∑_{k < N} a k • b k‖ ≤ (1 + 2 θ) ‖∑_{k < M} a k • b k‖` for `N ≤ M`
(`SplitSystem.prefix_bound`), it consists of nonzero vectors, and it has the same linear
span as `e`.
-/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace StructuredBases
namespace PositiveL1

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The sequence -/

/-- The sequence `e 0, e 2 + e 3, e 1 + e 3, e 5 + e 6, e 4 + e 6, …`. -/
def splitSeq (e : ℕ → X) : ℕ → X
  | 0 => e 0
  | k + 1 =>
    if k % 2 = 0 then e (3 * (k / 2) + 2) + e (3 * (k / 2) + 3)
    else e (3 * (k / 2) + 1) + e (3 * (k / 2) + 3)

@[simp] theorem splitSeq_zero (e : ℕ → X) : splitSeq e 0 = e 0 := rfl

theorem splitSeq_odd (e : ℕ → X) (n : ℕ) :
    splitSeq e (2 * n + 1) = e (3 * n + 2) + e (3 * n + 3) := by
  simp [splitSeq]

theorem splitSeq_even (e : ℕ → X) (n : ℕ) :
    splitSeq e (2 * n + 2) = e (3 * n + 1) + e (3 * n + 3) := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [splitSeq, h1, h2]

/-- Every term of `splitSeq e` is a term of `e` or a sum of two terms of `e`. -/
theorem splitSeq_induction (e : ℕ → X) {P : X → Prop} (h0 : ∀ i, P (e i))
    (h1 : ∀ i j, P (e i + e j)) (k : ℕ) : P (splitSeq e k) := by
  cases k with
  | zero => exact h0 0
  | succ k =>
    simp only [splitSeq]
    split_ifs
    · exact h1 _ _
    · exact h1 _ _

/-- Case analysis for the indices of `splitSeq`. -/
theorem index_cases {P : ℕ → Prop} (zero : P 0) (odd : ∀ n, P (2 * n + 1))
    (even : ∀ n, P (2 * n + 2)) (k : ℕ) : P k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact zero
  · obtain ⟨n, hn⟩ : ∃ n, k = 2 * n + 1 ∨ k = 2 * n + 2 := ⟨(k - 1) / 2, by omega⟩
    rcases hn with rfl | rfl
    · exact odd n
    · exact even n

/-! ### The hypotheses -/

/-- Hypotheses on the normalised cell vectors `e k` and the cell functionals `φ k`.
The cells alive at time `n` are those with index in `Finset.Icc n (3 * n)`. -/
structure SplitSystem (θ : ℝ) (e : ℕ → X) (φ : ℕ → X →L[𝕜] 𝕜) : Prop where
  theta_nonneg : 0 ≤ θ
  theta_le_one : θ ≤ 1
  /-- The cell vectors have norm at most one. -/
  norm_le : ∀ k, ‖e k‖ ≤ 1
  /-- The functionals of the cells alive at a given time have total size at most one. -/
  sum_le : ∀ n f, ∑ k ∈ Finset.Icc n (3 * n), ‖φ k f‖ ≤ ‖f‖
  /-- The vectors and the functionals of the cells alive at a given time are biorthogonal. -/
  dual : ∀ n, ∀ i ∈ Finset.Icc n (3 * n), ∀ j ∈ Finset.Icc n (3 * n),
    φ i (e j) = if i = j then 1 else 0
  /-- The vector of a cell is a convex combination of the vectors of its two parts. -/
  split : ∀ n, e n = (θ : 𝕜) • e (3 * n + 1) + (1 - (θ : 𝕜)) • e (3 * n + 2)

/-! ### Operators built from the cells alive at a given time -/

/-- The operator `f ↦ ∑ k, φ k f • t k`, the sum running over the cells alive at time `m`. -/
def cellOp (φ : ℕ → X →L[𝕜] 𝕜) (t : ℕ → X) (m : ℕ) : X →L[𝕜] X :=
  ∑ k ∈ Finset.Icc m (3 * m), (φ k).smulRight (t k)

theorem cellOp_apply (φ : ℕ → X →L[𝕜] 𝕜) (t : ℕ → X) (m : ℕ) (f : X) :
    cellOp φ t m f = ∑ k ∈ Finset.Icc m (3 * m), φ k f • t k := by
  simp [cellOp]

/-- The images under the operator `R` of step `n` of the vectors of the cells alive at time
`n + 1`: old cells are fixed, the two parts of the cell `n` are mapped to `e n`, and the
fresh cell is mapped to `-e n`. -/
def rVec (e : ℕ → X) (n k : ℕ) : X :=
  if k ≤ 3 * n then e k else if k = 3 * n + 3 then -e n else e n

variable (𝕜) in
/-- The images under the operator `S` of step `n` of the vectors of the cells alive at time
`n + 1`. -/
def sVec (θ : ℝ) (e : ℕ → X) (n k : ℕ) : X :=
  if k ≤ 3 * n then e k
  else if k = 3 * n + 1 then (θ : 𝕜) • e (3 * n + 1) - (1 - (θ : 𝕜)) • e (3 * n + 3)
  else if k = 3 * n + 2 then (θ : 𝕜) • e (3 * n + 1) + e (3 * n + 2) + (θ : 𝕜) • e (3 * n + 3)
  else (1 - (θ : 𝕜)) • e (3 * n + 3) - (θ : 𝕜) • e (3 * n + 1)

variable (𝕜) in
/-- The span of the cells alive at time `n`. -/
def cellSpan (e : ℕ → X) (n : ℕ) : Submodule 𝕜 X :=
  Submodule.span 𝕜 (e '' Set.Icc n (3 * n))

namespace SplitSystem

variable {θ : ℝ} {e : ℕ → X} {φ : ℕ → X →L[𝕜] 𝕜}

theorem norm_theta (h : SplitSystem θ e φ) : ‖(θ : 𝕜)‖ = θ := by
  rw [RCLike.norm_ofReal, abs_of_nonneg h.theta_nonneg]

theorem norm_one_sub_theta (h : SplitSystem θ e φ) : ‖1 - (θ : 𝕜)‖ = 1 - θ := by
  have : (1 - (θ : 𝕜)) = ((1 - θ : ℝ) : 𝕜) := by push_cast; ring
  rw [this, RCLike.norm_ofReal, abs_of_nonneg (by linarith [h.theta_le_one])]

theorem cellOp_cell (h : SplitSystem θ e φ) (t : ℕ → X) {m j : ℕ}
    (hj : j ∈ Finset.Icc m (3 * m)) : cellOp φ t m (e j) = t j := by
  rw [cellOp_apply, Finset.sum_congr rfl fun k hk => by rw [h.dual m k hk j hj]]
  simp [hj]

theorem norm_cellOp_le (h : SplitSystem θ e φ) (t : ℕ → X) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ k ∈ Finset.Icc m (3 * m), ‖t k‖ ≤ C) (f : X) : ‖cellOp φ t m f‖ ≤ C * ‖f‖ := by
  rw [cellOp_apply]
  calc ‖∑ k ∈ Finset.Icc m (3 * m), φ k f • t k‖
      ≤ ∑ k ∈ Finset.Icc m (3 * m), ‖φ k f • t k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc m (3 * m), ‖φ k f‖ * C := Finset.sum_le_sum fun k hk => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_left (ht k hk) (norm_nonneg _)
    _ = (∑ k ∈ Finset.Icc m (3 * m), ‖φ k f‖) * C := by rw [Finset.sum_mul]
    _ ≤ ‖f‖ * C := mul_le_mul_of_nonneg_right (h.sum_le m f) hC
    _ = C * ‖f‖ := mul_comm _ _

theorem norm_rVec_le (h : SplitSystem θ e φ) (n k : ℕ) : ‖rVec e n k‖ ≤ 1 := by
  unfold rVec
  split_ifs
  · exact h.norm_le k
  · rw [norm_neg]; exact h.norm_le n
  · exact h.norm_le n

theorem norm_sVec_le (h : SplitSystem θ e φ) (n k : ℕ) : ‖sVec 𝕜 θ e n k‖ ≤ 1 + 2 * θ := by
  have h0 := h.theta_nonneg
  have h1 := h.theta_le_one
  have ha : ∀ x : X, ‖x‖ ≤ 1 → ‖(θ : 𝕜) • x‖ ≤ θ := fun x hx => by
    rw [norm_smul, h.norm_theta]
    exact mul_le_of_le_one_right h0 hx
  have hb : ∀ x : X, ‖x‖ ≤ 1 → ‖(1 - (θ : 𝕜)) • x‖ ≤ 1 - θ := fun x hx => by
    rw [norm_smul, h.norm_one_sub_theta]
    exact mul_le_of_le_one_right (by linarith) hx
  unfold sVec
  split_ifs
  · linarith [h.norm_le k]
  · linarith [norm_sub_le ((θ : 𝕜) • e (3 * n + 1)) ((1 - (θ : 𝕜)) • e (3 * n + 3)),
      ha _ (h.norm_le (3 * n + 1)), hb _ (h.norm_le (3 * n + 3))]
  · linarith [norm_add₃_le (a := (θ : 𝕜) • e (3 * n + 1)) (b := e (3 * n + 2))
        (c := (θ : 𝕜) • e (3 * n + 3)),
      ha _ (h.norm_le (3 * n + 1)), h.norm_le (3 * n + 2), ha _ (h.norm_le (3 * n + 3))]
  · linarith [norm_sub_le ((1 - (θ : 𝕜)) • e (3 * n + 3)) ((θ : 𝕜) • e (3 * n + 1)),
      ha _ (h.norm_le (3 * n + 1)), hb _ (h.norm_le (3 * n + 3))]

/-! ### The operator `R` -/

/-- The norm one operator of step `n`: it fixes the cells alive at time `n` and kills the
two new vectors of step `n`. -/
def R (_h : SplitSystem θ e φ) (n : ℕ) : X →L[𝕜] X := cellOp φ (rVec e n) (n + 1)

theorem norm_R_le (h : SplitSystem θ e φ) (n : ℕ) (f : X) : ‖h.R n f‖ ≤ ‖f‖ := by
  have := h.norm_cellOp_le (rVec e n) (n + 1) zero_le_one (fun k _ => h.norm_rVec_le n k) f
  rwa [one_mul] at this

theorem R_cell (h : SplitSystem θ e φ) {n j : ℕ} (h1 : n + 1 ≤ j) (h2 : j ≤ 3 * n) :
    h.R n (e j) = e j := by
  rw [R, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨h1, by omega⟩), rVec, if_pos h2]

theorem R_left (h : SplitSystem θ e φ) (n : ℕ) : h.R n (e (3 * n + 1)) = e n := by
  rw [R, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), rVec,
    if_neg (by omega), if_neg (by omega)]

theorem R_right (h : SplitSystem θ e φ) (n : ℕ) : h.R n (e (3 * n + 2)) = e n := by
  rw [R, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), rVec,
    if_neg (by omega), if_neg (by omega)]

theorem R_fresh (h : SplitSystem θ e φ) (n : ℕ) : h.R n (e (3 * n + 3)) = -e n := by
  rw [R, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), rVec,
    if_neg (by omega), if_pos rfl]

theorem R_parent (h : SplitSystem θ e φ) (n : ℕ) : h.R n (e n) = e n := by
  conv_lhs => rw [h.split n]
  rw [map_add, map_smul, map_smul, h.R_left, h.R_right, ← add_smul]
  simp

theorem R_odd (h : SplitSystem θ e φ) (n : ℕ) : h.R n (splitSeq e (2 * n + 1)) = 0 := by
  rw [splitSeq_odd, map_add, h.R_right, h.R_fresh, add_neg_cancel]

theorem R_even (h : SplitSystem θ e φ) (n : ℕ) : h.R n (splitSeq e (2 * n + 2)) = 0 := by
  rw [splitSeq_even, map_add, h.R_left, h.R_fresh, add_neg_cancel]

/-! ### The operator `S` -/

/-- The operator of step `n` of norm at most `1 + 2 θ`: it fixes the cells alive at time
`n` and the first new vector of step `n`, and kills the second one. -/
def S (_h : SplitSystem θ e φ) (n : ℕ) : X →L[𝕜] X := cellOp φ (sVec 𝕜 θ e n) (n + 1)

theorem norm_S_le (h : SplitSystem θ e φ) (n : ℕ) (f : X) : ‖h.S n f‖ ≤ (1 + 2 * θ) * ‖f‖ :=
  h.norm_cellOp_le (sVec 𝕜 θ e n) (n + 1) (by linarith [h.theta_nonneg])
    (fun k _ => h.norm_sVec_le n k) f

theorem S_cell (h : SplitSystem θ e φ) {n j : ℕ} (h1 : n + 1 ≤ j) (h2 : j ≤ 3 * n) :
    h.S n (e j) = e j := by
  rw [S, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨h1, by omega⟩), sVec, if_pos h2]

theorem S_left (h : SplitSystem θ e φ) (n : ℕ) :
    h.S n (e (3 * n + 1)) = (θ : 𝕜) • e (3 * n + 1) - (1 - (θ : 𝕜)) • e (3 * n + 3) := by
  rw [S, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), sVec,
    if_neg (by omega), if_pos rfl]

theorem S_right (h : SplitSystem θ e φ) (n : ℕ) :
    h.S n (e (3 * n + 2)) =
      (θ : 𝕜) • e (3 * n + 1) + e (3 * n + 2) + (θ : 𝕜) • e (3 * n + 3) := by
  rw [S, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), sVec,
    if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem S_fresh (h : SplitSystem θ e φ) (n : ℕ) :
    h.S n (e (3 * n + 3)) = (1 - (θ : 𝕜)) • e (3 * n + 3) - (θ : 𝕜) • e (3 * n + 1) := by
  rw [S, h.cellOp_cell _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), sVec,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem S_parent (h : SplitSystem θ e φ) (n : ℕ) : h.S n (e n) = e n := by
  conv_lhs => rw [h.split n]
  rw [map_add, map_smul, map_smul, h.S_left, h.S_right]
  conv_rhs => rw [h.split n]
  module

theorem S_odd (h : SplitSystem θ e φ) (n : ℕ) :
    h.S n (splitSeq e (2 * n + 1)) = splitSeq e (2 * n + 1) := by
  rw [splitSeq_odd, map_add, h.S_right, h.S_fresh]
  module

theorem S_even (h : SplitSystem θ e φ) (n : ℕ) : h.S n (splitSeq e (2 * n + 2)) = 0 := by
  rw [splitSeq_even, map_add, h.S_left, h.S_fresh]
  module

/-! ### The spans of the cells alive at a given time -/

theorem cell_mem_cellSpan (_h : SplitSystem θ e φ) {n k : ℕ} (h1 : n ≤ k) (h2 : k ≤ 3 * n) :
    e k ∈ cellSpan 𝕜 e n :=
  Submodule.subset_span ⟨k, ⟨h1, h2⟩, rfl⟩

theorem cellSpan_le_succ (h : SplitSystem θ e φ) (n : ℕ) :
    cellSpan 𝕜 e n ≤ cellSpan 𝕜 e (n + 1) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, ⟨h1, h2⟩, rfl⟩
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
  · rw [SetLike.mem_coe, h.split n]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (h.cell_mem_cellSpan (by omega) (by omega)))
      (Submodule.smul_mem _ _ (h.cell_mem_cellSpan (by omega) (by omega)))
  · exact h.cell_mem_cellSpan (by omega) (by omega)

theorem R_eq_self (h : SplitSystem θ e φ) {n : ℕ} {x : X} (hx : x ∈ cellSpan 𝕜 e n) :
    h.R n x = x := by
  have key : Set.EqOn (h.R n : X →ₗ[𝕜] X) (LinearMap.id : X →ₗ[𝕜] X) (e '' Set.Icc n (3 * n)) := by
    rintro _ ⟨k, ⟨h1, h2⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.R_parent _
    · exact h.R_cell h1' h2
  exact LinearMap.eqOn_span key hx

theorem S_eq_self (h : SplitSystem θ e φ) {n : ℕ} {x : X} (hx : x ∈ cellSpan 𝕜 e n) :
    h.S n x = x := by
  have key : Set.EqOn (h.S n : X →ₗ[𝕜] X) (LinearMap.id : X →ₗ[𝕜] X) (e '' Set.Icc n (3 * n)) := by
    rintro _ ⟨k, ⟨h1, h2⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.S_parent _
    · exact h.S_cell h1' h2
  exact LinearMap.eqOn_span key hx

theorem splitSeq_mem_cellSpan (h : SplitSystem θ e φ) (n : ℕ) :
    ∀ k < 2 * n + 1, splitSeq e k ∈ cellSpan 𝕜 e n := by
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    exact h.cell_mem_cellSpan le_rfl (by omega)
  | succ n ih =>
    intro k hk
    by_cases hk' : k < 2 * n + 1
    · exact h.cellSpan_le_succ n (ih k hk')
    · obtain rfl | rfl : k = 2 * n + 1 ∨ k = 2 * n + 2 := by omega
      · rw [splitSeq_odd]
        exact Submodule.add_mem _ (h.cell_mem_cellSpan (by omega) (by omega))
          (h.cell_mem_cellSpan (by omega) (by omega))
      · rw [splitSeq_even]
        exact Submodule.add_mem _ (h.cell_mem_cellSpan (by omega) (by omega))
          (h.cell_mem_cellSpan (by omega) (by omega))

theorem partialSum_mem_cellSpan (h : SplitSystem θ e φ) (a : ℕ → 𝕜) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), a k • splitSeq e k ∈ cellSpan 𝕜 e n :=
  Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (h.splitSeq_mem_cellSpan n k (Finset.mem_range.mp hk))

/-! ### Prefix bounds -/

theorem R_partialSum (h : SplitSystem θ e φ) (a : ℕ → 𝕜) (n : ℕ) :
    h.R n (∑ k ∈ Finset.range (2 * (n + 1) + 1), a k • splitSeq e k) =
      ∑ k ∈ Finset.range (2 * n + 1), a k • splitSeq e k := by
  have hn : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ, map_add, map_add, map_smul, map_smul,
    h.R_eq_self (h.partialSum_mem_cellSpan a n), h.R_odd, h.R_even]
  simp

theorem S_partialSum (h : SplitSystem θ e φ) (a : ℕ → 𝕜) (n : ℕ) :
    h.S n (∑ k ∈ Finset.range (2 * (n + 1) + 1), a k • splitSeq e k) =
      ∑ k ∈ Finset.range (2 * n + 2), a k • splitSeq e k := by
  have hn : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ, map_add, map_add, map_smul, map_smul,
    h.S_eq_self (h.partialSum_mem_cellSpan a n), h.S_odd, h.S_even]
  simp

theorem norm_partialSum_odd_mono (h : SplitSystem θ e φ) (a : ℕ → 𝕜) {n m : ℕ} (hnm : n ≤ m) :
    ‖∑ k ∈ Finset.range (2 * n + 1), a k • splitSeq e k‖ ≤
      ‖∑ k ∈ Finset.range (2 * m + 1), a k • splitSeq e k‖ := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    refine ih.trans ?_
    rw [← h.R_partialSum a m]
    exact h.norm_R_le m _

theorem norm_partialSum_le_odd (h : SplitSystem θ e φ) (a : ℕ → 𝕜) {N m : ℕ}
    (hN : N ≤ 2 * m + 1) :
    ‖∑ k ∈ Finset.range N, a k • splitSeq e k‖ ≤
      (1 + 2 * θ) * ‖∑ k ∈ Finset.range (2 * m + 1), a k • splitSeq e k‖ := by
  have hθ := h.theta_nonneg
  induction N using index_cases with
  | zero => simpa using mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 * θ) (norm_nonneg _)
  | odd n =>
    refine (h.norm_partialSum_odd_mono a (by omega : n ≤ m)).trans ?_
    nlinarith [norm_nonneg (∑ k ∈ Finset.range (2 * m + 1), a k • splitSeq e k)]
  | even n =>
    rw [← h.S_partialSum a n]
    exact (h.norm_S_le n _).trans
      (mul_le_mul_of_nonneg_left (h.norm_partialSum_odd_mono a (by omega)) (by linarith))

/-- **Prefix bound** for the sequence `splitSeq e`. -/
theorem prefix_bound (h : SplitSystem θ e φ) (N M : ℕ) (a : ℕ → 𝕜) (hNM : N ≤ M) :
    ‖∑ k ∈ Finset.range N, a k • splitSeq e k‖ ≤
      (1 + 2 * θ) * ‖∑ k ∈ Finset.range M, a k • splitSeq e k‖ := by
  set a' : ℕ → 𝕜 := fun k => if k < M then a k else 0 with ha'
  have h1 : ∑ k ∈ Finset.range N, a k • splitSeq e k =
      ∑ k ∈ Finset.range N, a' k • splitSeq e k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < M := lt_of_lt_of_le (Finset.mem_range.mp hk) hNM
    simp [ha', this]
  have h2 : ∑ k ∈ Finset.range M, a k • splitSeq e k =
      ∑ k ∈ Finset.range (2 * M + 1), a' k • splitSeq e k := by
    have hsub : Finset.range M ⊆ Finset.range (2 * M + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [ha', Finset.mem_range.mp hk]
    · intro k _ hk
      have : ¬ k < M := fun hlt => hk (Finset.mem_range.mpr hlt)
      simp [ha', this]
  rw [h1, h2]
  exact h.norm_partialSum_le_odd a' (by omega)

/-! ### Nonvanishing and spans -/

theorem cell_ne_zero (h : SplitSystem θ e φ) (k : ℕ) : e k ≠ 0 := by
  intro hk
  have hmem : k ∈ Finset.Icc k (3 * k) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have := h.dual k k hmem k hmem
  rw [hk, map_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem add_fresh_ne_zero (h : SplitSystem θ e φ) {n i : ℕ} (h1 : n + 1 ≤ i)
    (h2 : i < 3 * n + 3) : e i + e (3 * n + 3) ≠ 0 := by
  intro hz
  have hm : ∀ j, n + 1 ≤ j → j ≤ 3 * n + 3 → j ∈ Finset.Icc (n + 1) (3 * (n + 1)) :=
    fun j hj hj' => Finset.mem_Icc.mpr ⟨hj, by omega⟩
  have := congrArg (φ (3 * n + 3)) hz
  rw [map_add, map_zero, h.dual (n + 1) _ (hm _ (by omega) le_rfl) _ (hm _ h1 h2.le),
    h.dual (n + 1) _ (hm _ (by omega) le_rfl) _ (hm _ (by omega) le_rfl),
    if_neg (by omega), if_pos rfl, zero_add] at this
  exact one_ne_zero this

theorem splitSeq_ne_zero (h : SplitSystem θ e φ) (k : ℕ) : splitSeq e k ≠ 0 := by
  induction k using index_cases with
  | zero => simpa using h.cell_ne_zero 0
  | odd n =>
    rw [splitSeq_odd]
    exact h.add_fresh_ne_zero (by omega) (by omega)
  | even n =>
    rw [splitSeq_even]
    exact h.add_fresh_ne_zero (by omega) (by omega)

/-- Every cell vector lies in the span of the sequence `splitSeq e`. -/
theorem cell_mem_span_splitSeq (h : SplitSystem θ e φ) (n : ℕ) :
    ∀ k ≤ 3 * n, e k ∈ Submodule.span 𝕜 (Set.range (splitSeq e)) := by
  set W := Submodule.span 𝕜 (Set.range (splitSeq e)) with hW
  have hb : ∀ k, splitSeq e k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    simpa using hb 0
  | succ n ih =>
    intro k hk
    have hD : e n ∈ W := ih n (by omega)
    have hu : e (3 * n + 2) + e (3 * n + 3) ∈ W := by
      simpa [splitSeq_odd] using hb (2 * n + 1)
    have hv : e (3 * n + 1) + e (3 * n + 3) ∈ W := by
      simpa [splitSeq_even] using hb (2 * n + 2)
    have hJ : e (3 * n + 3) ∈ W := by
      have : e (3 * n + 3) = (1 - (θ : 𝕜)) • (e (3 * n + 2) + e (3 * n + 3)) +
          (θ : 𝕜) • (e (3 * n + 1) + e (3 * n + 3)) - e n := by
        rw [h.split n]; module
      rw [this]
      exact Submodule.sub_mem _
        (Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)) hD
    by_cases hk' : k ≤ 3 * n
    · exact ih k hk'
    · obtain rfl | rfl | rfl : k = 3 * n + 1 ∨ k = 3 * n + 2 ∨ k = 3 * n + 3 := by omega
      · have : e (3 * n + 1) = e (3 * n + 1) + e (3 * n + 3) - e (3 * n + 3) := by abel
        rw [this]; exact Submodule.sub_mem _ hv hJ
      · have : e (3 * n + 2) = e (3 * n + 2) + e (3 * n + 3) - e (3 * n + 3) := by abel
        rw [this]; exact Submodule.sub_mem _ hu hJ
      · exact hJ

/-- The sequence `splitSeq e` and the cell vectors have the same linear span. -/
theorem span_splitSeq (h : SplitSystem θ e φ) :
    Submodule.span 𝕜 (Set.range (splitSeq e)) = Submodule.span 𝕜 (Set.range e) := by
  have hc : ∀ i, e i ∈ Submodule.span 𝕜 (Set.range e) := fun i => Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact splitSeq_induction e (P := fun x => x ∈ Submodule.span 𝕜 (Set.range e)) hc
      (fun i j => Submodule.add_mem _ (hc i) (hc j)) k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact h.cell_mem_span_splitSeq k k (by omega)

end SplitSystem

end PositiveL1
end StructuredBases
