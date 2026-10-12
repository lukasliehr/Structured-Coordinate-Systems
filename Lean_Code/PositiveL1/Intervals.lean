import Lean_Code.PositiveL1.Cells
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The interval cells of the construction

The unit intervals `(z j, z j + 1]`, `j : ℕ`, are enumerated by a sequence `z : ℕ → ℤ`.  The
cells are half-open intervals `(lo, lo + len]`, listed in the order of their creation:

* `cell 0` is the unit interval number `0`;
* `cell (3 * n + 1)` is the left part of `cell n`, of proportion `θ`;
* `cell (3 * n + 2)` is the right part of `cell n`, of proportion `1 - θ`;
* `cell (3 * n + 3)` is the unit interval number `n + 1`.

So `cell n` is the cell which is split in step `n`, and the cells alive at time `n` are the
cells with index in `Finset.Icc n (3 * n)` (a first-in-first-out queue).  The main result is
that the sets `cellSet z θ k` form a splitting scheme (`splitCells`).
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace StructuredBases
namespace PositiveL1

/-- A cell of the construction: the half-open interval `(lo, lo + len]`, which lies in the
unit interval number `unit`. -/
structure Cell where
  /-- The number of the unit interval containing the cell. -/
  unit : ℕ
  /-- The left end point. -/
  lo : ℝ
  /-- The length. -/
  len : ℝ

namespace Cell

/-- The left part of a cell, of proportion `θ`. -/
def left (θ : ℝ) (c : Cell) : Cell := ⟨c.unit, c.lo, θ * c.len⟩

/-- The right part of a cell, of proportion `1 - θ`. -/
def right (θ : ℝ) (c : Cell) : Cell := ⟨c.unit, c.lo + θ * c.len, (1 - θ) * c.len⟩

/-- The unit interval `(z j, z j + 1]`. -/
def fresh (z : ℕ → ℤ) (j : ℕ) : Cell := ⟨j, z j, 1⟩

/-- The interval `(lo, lo + len]`. -/
def carrier (c : Cell) : Set ℝ := Ioc c.lo (c.lo + c.len)

end Cell

variable (z : ℕ → ℤ) (θ : ℝ)

/-- The cells in the order of their creation. -/
def cell : ℕ → Cell
  | 0 => Cell.fresh z 0
  | k + 1 =>
    if k % 3 = 0 then (cell (k / 3)).left θ
    else if k % 3 = 1 then (cell (k / 3)).right θ
    else Cell.fresh z (k / 3 + 1)
  decreasing_by all_goals omega

theorem cell_zero : cell z θ 0 = Cell.fresh z 0 := by
  rw [cell]

theorem cell_left (n : ℕ) : cell z θ (3 * n + 1) = (cell z θ n).left θ := by
  have h1 : 3 * n % 3 = 0 := by omega
  have h2 : 3 * n / 3 = n := by omega
  rw [cell]
  simp [h1, h2]

theorem cell_right (n : ℕ) : cell z θ (3 * n + 2) = (cell z θ n).right θ := by
  have h1 : (3 * n + 1) % 3 = 1 := by omega
  have h2 : (3 * n + 1) / 3 = n := by omega
  rw [cell]
  simp [h1, h2]

theorem cell_fresh (n : ℕ) : cell z θ (3 * n + 3) = Cell.fresh z (n + 1) := by
  have h1 : (3 * n + 2) % 3 = 2 := by omega
  have h2 : (3 * n + 2) / 3 = n := by omega
  rw [cell]
  simp [h1, h2]

/-- Induction along the creation of the cells. -/
theorem cell_induction {P : ℕ → Prop} (zero : P 0) (left : ∀ n, P n → P (3 * n + 1))
    (right : ∀ n, P n → P (3 * n + 2)) (fresh : ∀ n, P (3 * n + 3)) (k : ℕ) : P k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact zero
    · obtain ⟨n, hn⟩ : ∃ n, k = 3 * n + 1 ∨ k = 3 * n + 2 ∨ k = 3 * n + 3 :=
        ⟨(k - 1) / 3, by omega⟩
      rcases hn with rfl | rfl | rfl
      · exact left n (ih n (by omega))
      · exact right n (ih n (by omega))
      · exact fresh n

/-- The set of the `k`-th cell. -/
def cellSet (k : ℕ) : Set ℝ := (cell z θ k).carrier

theorem cellSet_def (k : ℕ) :
    cellSet z θ k = Ioc (cell z θ k).lo ((cell z θ k).lo + (cell z θ k).len) := rfl

theorem measurableSet_cellSet (k : ℕ) : MeasurableSet (cellSet z θ k) := measurableSet_Ioc

theorem volume_cellSet (k : ℕ) : volume (cellSet z θ k) = ENNReal.ofReal (cell z θ k).len := by
  rw [cellSet_def, Real.volume_Ioc, add_sub_cancel_left]

theorem volume_cellSet_ne_top (k : ℕ) : volume (cellSet z θ k) ≠ ∞ := by
  rw [volume_cellSet]
  exact ENNReal.ofReal_ne_top

/-! ### The data of the cells -/

theorem unit_zero : (cell z θ 0).unit = 0 := by rw [cell_zero]; rfl

theorem lo_zero : (cell z θ 0).lo = z 0 := by rw [cell_zero]; rfl

theorem len_zero : (cell z θ 0).len = 1 := by rw [cell_zero]; rfl

theorem unit_left (n : ℕ) : (cell z θ (3 * n + 1)).unit = (cell z θ n).unit := by
  rw [cell_left]; rfl

theorem lo_left (n : ℕ) : (cell z θ (3 * n + 1)).lo = (cell z θ n).lo := by
  rw [cell_left]; rfl

theorem len_left (n : ℕ) : (cell z θ (3 * n + 1)).len = θ * (cell z θ n).len := by
  rw [cell_left]; rfl

theorem unit_right (n : ℕ) : (cell z θ (3 * n + 2)).unit = (cell z θ n).unit := by
  rw [cell_right]; rfl

theorem lo_right (n : ℕ) :
    (cell z θ (3 * n + 2)).lo = (cell z θ n).lo + θ * (cell z θ n).len := by
  rw [cell_right]; rfl

theorem len_right (n : ℕ) : (cell z θ (3 * n + 2)).len = (1 - θ) * (cell z θ n).len := by
  rw [cell_right]; rfl

theorem unit_fresh (n : ℕ) : (cell z θ (3 * n + 3)).unit = n + 1 := by
  rw [cell_fresh]; rfl

theorem lo_fresh (n : ℕ) : (cell z θ (3 * n + 3)).lo = z (n + 1) := by
  rw [cell_fresh]; rfl

theorem len_fresh (n : ℕ) : (cell z θ (3 * n + 3)).len = 1 := by
  rw [cell_fresh]; rfl

variable {θ}

/-- The basic facts about the cells: positive length, position inside the unit interval,
and a bound for the number of the unit interval. -/
theorem cell_facts (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    0 < (cell z θ k).len ∧ (z (cell z θ k).unit : ℝ) ≤ (cell z θ k).lo ∧
      (cell z θ k).lo + (cell z θ k).len ≤ z (cell z θ k).unit + 1 ∧
      3 * (cell z θ k).unit ≤ k := by
  induction k using cell_induction with
  | zero =>
    rw [unit_zero, lo_zero, len_zero]
    exact ⟨one_pos, le_rfl, le_rfl, le_rfl⟩
  | left n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [unit_left, lo_left, len_left]
    exact ⟨mul_pos hθ h1, h2, by nlinarith, by omega⟩
  | right n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [unit_right, lo_right, len_right]
    exact ⟨mul_pos (by linarith) h1, by nlinarith [mul_pos hθ h1], by nlinarith, by omega⟩
  | fresh n =>
    rw [unit_fresh, lo_fresh, len_fresh]
    exact ⟨one_pos, le_rfl, le_rfl, by omega⟩

theorem len_pos (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) : 0 < (cell z θ k).len :=
  (cell_facts z hθ hθ1 k).1

theorem unit_le_lo (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (z (cell z θ k).unit : ℝ) ≤ (cell z θ k).lo :=
  (cell_facts z hθ hθ1 k).2.1

theorem hi_le_unit (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (cell z θ k).lo + (cell z θ k).len ≤ z (cell z θ k).unit + 1 :=
  (cell_facts z hθ hθ1 k).2.2.1

theorem three_mul_unit_le (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) : 3 * (cell z θ k).unit ≤ k :=
  (cell_facts z hθ hθ1 k).2.2.2

theorem cellSet_zero : cellSet z θ 0 = Ioc (z 0 : ℝ) (z 0 + 1) := by
  rw [cellSet_def, lo_zero, len_zero]

theorem cellSet_fresh (n : ℕ) : cellSet z θ (3 * n + 3) = Ioc (z (n + 1) : ℝ) (z (n + 1) + 1) := by
  rw [cellSet_def, lo_fresh, len_fresh]

theorem cellSet_subset_unit (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    cellSet z θ k ⊆ Ioc (z (cell z θ k).unit : ℝ) (z (cell z θ k).unit + 1) :=
  Ioc_subset_Ioc (unit_le_lo z hθ hθ1 k) (hi_le_unit z hθ hθ1 k)

theorem volume_real_cellSet (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    volume.real (cellSet z θ k) = (cell z θ k).len := by
  rw [measureReal_def, volume_cellSet, ENNReal.toReal_ofReal (len_pos z hθ hθ1 k).le]

theorem volume_cellSet_ne_zero (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    volume (cellSet z θ k) ≠ 0 := by
  rw [volume_cellSet]
  exact (ENNReal.ofReal_pos.mpr (len_pos z hθ hθ1 k)).ne'

variable {z}

/-- Different unit intervals are disjoint. -/
theorem disjoint_unit (hz : Function.Injective z) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Ioc (z i : ℝ) (z i + 1)) (Ioc (z j : ℝ) (z j + 1)) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  have h5 : (z i : ℝ) < z j + 1 := by linarith
  have h6 : (z j : ℝ) < z i + 1 := by linarith
  have h7 : z i < z j + 1 := by exact_mod_cast h5
  have h8 : z j < z i + 1 := by exact_mod_cast h6
  exact hij (hz (by omega))

variable (z)

theorem cellSet_left_union_right (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) :
    cellSet z θ (3 * n + 1) ∪ cellSet z θ (3 * n + 2) = cellSet z θ n := by
  have hl := len_pos z hθ hθ1 n
  rw [cellSet_def, cellSet_def, cellSet_def, lo_left, len_left, lo_right, len_right,
    Ioc_union_Ioc_eq_Ioc (by nlinarith) (by nlinarith)]
  congr 1
  ring

theorem disjoint_left_right (n : ℕ) :
    Disjoint (cellSet z θ (3 * n + 1)) (cellSet z θ (3 * n + 2)) := by
  rw [cellSet_def, cellSet_def, lo_left, len_left, lo_right]
  exact Ioc_disjoint_Ioc_of_le le_rfl

theorem cellSet_left_subset (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) :
    cellSet z θ (3 * n + 1) ⊆ cellSet z θ n := by
  rw [← cellSet_left_union_right z hθ hθ1 n]
  exact subset_union_left

theorem cellSet_right_subset (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) :
    cellSet z θ (3 * n + 2) ⊆ cellSet z θ n := by
  rw [← cellSet_left_union_right z hθ hθ1 n]
  exact subset_union_right

variable {z}

/-- A fresh unit interval is disjoint from all cells created before. -/
theorem disjoint_fresh (hz : Function.Injective z) (hθ : 0 < θ) (hθ1 : θ < 1) {n k : ℕ}
    (hk : k < 3 * n + 3) : Disjoint (cellSet z θ k) (cellSet z θ (3 * n + 3)) := by
  have hu := three_mul_unit_le z hθ hθ1 k
  rw [cellSet_fresh]
  exact (disjoint_unit hz (by omega)).mono_left (cellSet_subset_unit z hθ hθ1 k)

/-- The cells alive at time `n` are pairwise disjoint. -/
theorem cellSet_disjoint (hz : Function.Injective z) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) :
    ∀ i j, n ≤ i → i ≤ 3 * n → n ≤ j → j ≤ 3 * n → i ≠ j →
      Disjoint (cellSet z θ i) (cellSet z θ j) := by
  induction n with
  | zero =>
    intro i j _ hi _ hj hij
    omega
  | succ n ih =>
    have key : ∀ i j, n + 1 ≤ i → i < j → j ≤ 3 * (n + 1) →
        Disjoint (cellSet z θ i) (cellSet z θ j) := by
      intro i j hi hij hj
      by_cases hj' : j ≤ 3 * n
      · exact ih i j (by omega) (by omega) (by omega) hj' (by omega)
      · obtain rfl | rfl | rfl : j = 3 * n + 1 ∨ j = 3 * n + 2 ∨ j = 3 * n + 3 := by omega
        · exact (ih i n (by omega) (by omega) le_rfl (by omega) (by omega)).mono_right
            (cellSet_left_subset z hθ hθ1 n)
        · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with rfl | hi'
          · exact disjoint_left_right z n
          · exact (ih i n (by omega) (by omega) le_rfl (by omega) (by omega)).mono_right
              (cellSet_right_subset z hθ hθ1 n)
        · exact disjoint_fresh hz hθ hθ1 hij
    intro i j hi hi' hj hj' hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j hi h hj'
    · exact (key j i hj h hi').symm

/-- The interval cells form a splitting scheme of sets. -/
theorem splitCells (hz : Function.Injective z) (hθ : 0 < θ) (hθ1 : θ < 1) :
    SplitCells (volume : Measure ℝ) θ (cellSet z θ) where
  theta_pos := hθ
  theta_lt_one := hθ1
  measurable := measurableSet_cellSet z θ
  measure_ne_top := volume_cellSet_ne_top z θ
  measure_ne_zero := volume_cellSet_ne_zero z hθ hθ1
  disjoint := cellSet_disjoint hz hθ hθ1
  union := cellSet_left_union_right z hθ hθ1
  measure_left n := by
    rw [volume_real_cellSet z hθ hθ1, volume_real_cellSet z hθ hθ1, len_left]
  measure_right n := by
    rw [volume_real_cellSet z hθ hθ1, volume_real_cellSet z hθ hθ1, len_right]

end PositiveL1
end StructuredBases
