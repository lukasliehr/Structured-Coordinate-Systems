import Lean_Code.PositiveBiorthogonal.Averaging

/-! The scalar geometric bounds and interval splits used by the deterministic schedule. -/
noncomputable section
set_option autoImplicit false
open Set
namespace PositiveBiorthogonal

def splitTheta (L : ℕ) : ℝ := 1 / (2 * (L : ℝ))

theorem splitTheta_pos (L : ℕ) (hL : 2 ≤ L) : 0 < splitTheta L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  exact one_div_pos.mpr (mul_pos (by norm_num) hLr)

theorem splitTheta_le_quarter (L : ℕ) (hL : 2 ≤ L) : splitTheta L ≤ 1 / 4 := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  unfold splitTheta
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  linarith

theorem splitTheta_lt_one (L : ℕ) (hL : 2 ≤ L) : splitTheta L < 1 :=
  (splitTheta_le_quarter L hL).trans_lt (by norm_num)

theorem splitTheta_mul (L : ℕ) (hL : 2 ≤ L) : (L : ℝ) * splitTheta L = 1 / 2 := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  unfold splitTheta
  field_simp

theorem remainder_power_lower (L : ℕ) (hL : 2 ≤ L) (k : ℕ) (hk : k ≤ L) :
    (1 / 2 : ℝ) ≤ (1 - splitTheta L) ^ k := by
  have ht := splitTheta_pos L hL
  have ht1 := splitTheta_lt_one L hL
  have hb := one_add_mul_le_pow (a := -splitTheta L) (by linarith : -2 ≤ -splitTheta L) k
  have hkR : (k : ℝ) ≤ L := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hkR ht.le
  rw [splitTheta_mul L hL] at hm
  simp only [mul_neg, ← sub_eq_add_neg] at hb
  linarith

theorem remainder_power_upper (L : ℕ) (hL : 2 ≤ L) :
    (1 - splitTheta L) ^ L ≤ (2 / 3 : ℝ) := by
  have ht := splitTheta_pos L hL
  have ht1 := splitTheta_lt_one L hL
  have hq : 0 < 1 - splitTheta L := sub_pos.mpr ht1
  have hb := one_add_mul_le_pow (a := splitTheta L) (by linarith : -2 ≤ splitTheta L) L
  rw [splitTheta_mul L hL] at hb
  have hprod : (1 - splitTheta L) * (1 + splitTheta L) ≤ 1 := by nlinarith [sq_nonneg (splitTheta L)]
  have hp := pow_le_pow_left₀ (mul_nonneg hq.le (by linarith : 0 ≤ 1 + splitTheta L)) hprod L
  rw [mul_pow, one_pow] at hp
  have hmul := mul_le_mul_of_nonneg_left hb (pow_nonneg hq.le L)
  nlinarith

/-- A strict cut of a positive interval. -/
structure IntervalSplit where
  parent : IntervalCell
  point : ℝ
  left_lt : parent.left < point
  right_lt : point < parent.right

namespace IntervalSplit

def leftChild (S : IntervalSplit) : IntervalCell := ⟨S.parent.left, S.point, S.left_lt⟩
def rightChild (S : IntervalSplit) : IntervalCell := ⟨S.point, S.parent.right, S.right_lt⟩

theorem children_disjoint (S : IntervalSplit) : Disjoint S.leftChild.carrier S.rightChild.carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hx.2) hy.1

theorem children_union (S : IntervalSplit) : S.leftChild.carrier ∪ S.rightChild.carrier = S.parent.carrier := by
  ext x
  change (S.parent.left < x ∧ x ≤ S.point) ∨ (S.point < x ∧ x ≤ S.parent.right) ↔
    S.parent.left < x ∧ x ≤ S.parent.right
  constructor
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.trans S.right_lt.le⟩
    · exact ⟨S.left_lt.trans hx.1, hx.2⟩
  · intro hx
    by_cases hs : x ≤ S.point
    · exact Or.inl ⟨hx.1, hs⟩
    · exact Or.inr ⟨lt_of_not_ge hs, hx.2⟩

theorem left_subset (S : IntervalSplit) : S.leftChild.carrier ⊆ S.parent.carrier := by
  rw [← S.children_union]
  exact subset_union_left

theorem right_subset (S : IntervalSplit) : S.rightChild.carrier ⊆ S.parent.carrier := by
  rw [← S.children_union]
  exact subset_union_right

theorem lengths_add (S : IntervalSplit) : S.leftChild.length + S.rightChild.length = S.parent.length := by
  simp [leftChild, rightChild, IntervalCell.length]

end IntervalSplit

def geometricPoint (D : IntervalCell) (θ : ℝ) (k : ℕ) : ℝ :=
  D.left + (1 - (1 - θ) ^ k) * D.length

theorem geometricPoint_zero (D : IntervalCell) (θ : ℝ) : geometricPoint D θ 0 = D.left := by
  simp [geometricPoint]

theorem geometricPoint_lt_right (D : IntervalCell) (θ : ℝ) (hθ : θ < 1) (k : ℕ) :
    geometricPoint D θ k < D.right := by
  have hp := pow_pos (sub_pos.mpr hθ) k
  have hlen := D.length_pos
  have he : D.right = D.left + D.length := by simp [IntervalCell.length]
  rw [he]
  unfold geometricPoint
  nlinarith

theorem geometricPoint_step (D : IntervalCell) (θ : ℝ) (k : ℕ) :
    geometricPoint D θ (k + 1) - geometricPoint D θ k = θ * (1 - θ) ^ k * D.length := by
  simp only [geometricPoint, pow_succ]
  ring

theorem geometricPoint_strictMono (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    StrictMono (geometricPoint D θ) := by
  apply strictMono_nat_of_lt_succ
  intro k
  apply sub_pos.mp
  rw [geometricPoint_step]
  exact mul_pos (mul_pos hθ (pow_pos (sub_pos.mpr hθ1) k)) D.length_pos

def geometricSplit (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) : IntervalSplit where
  parent := ⟨geometricPoint D θ k, D.right, geometricPoint_lt_right D θ hθ1 k⟩
  point := geometricPoint D θ (k + 1)
  left_lt := geometricPoint_strictMono D θ hθ hθ1 (Nat.lt_succ_self k)
  right_lt := geometricPoint_lt_right D θ hθ1 (k + 1)

theorem geometricSplit_parent_length (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).parent.length = (1 - θ) ^ k * D.length := by
  simp only [geometricSplit, IntervalCell.length, geometricPoint]
  ring

theorem geometricSplit_left_length (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).leftChild.length = θ * (geometricSplit D θ hθ hθ1 k).parent.length := by
  change geometricPoint D θ (k + 1) - geometricPoint D θ k = _
  rw [geometricPoint_step, geometricSplit_parent_length]
  ring

theorem geometricSplit_right_length (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).rightChild.length =
      (1 - θ) * (geometricSplit D θ hθ hθ1 k).parent.length := by
  have he := (geometricSplit D θ hθ hθ1 k).lengths_add
  rw [geometricSplit_left_length] at he
  linarith

theorem geometricSplit_parent_subset (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).parent.carrier ⊆ D.carrier := by
  have hp := (geometricPoint_strictMono D θ hθ hθ1).monotone (Nat.zero_le k)
  rw [geometricPoint_zero] at hp
  intro x hx
  exact ⟨hp.trans_lt hx.1, hx.2⟩

theorem geometricSplit_remainder (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (k : ℕ) :
    (geometricSplit D θ hθ hθ1 k).rightChild = (geometricSplit D θ hθ hθ1 (k + 1)).parent := rfl

theorem schedule_parent_lower (D : IntervalCell) (L : ℕ) (hL : 2 ≤ L) (k : ℕ) (hk : k ≤ L) :
    D.length / 2 ≤ (geometricSplit D (splitTheta L) (splitTheta_pos L hL) (splitTheta_lt_one L hL) k).parent.length := by
  rw [geometricSplit_parent_length]
  have h := mul_le_mul_of_nonneg_right (remainder_power_lower L hL k hk) D.length_pos.le
  linarith

theorem schedule_removed_upper (D : IntervalCell) (L : ℕ) (hL : 2 ≤ L) (k : ℕ) :
    (geometricSplit D (splitTheta L) (splitTheta_pos L hL) (splitTheta_lt_one L hL) k).leftChild.length ≤
      D.length / 4 := by
  rw [geometricSplit_left_length, geometricSplit_parent_length]
  have ht := splitTheta_pos L hL
  have ht1 := splitTheta_lt_one L hL
  have hpow : (1 - splitTheta L) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  calc
    _ ≤ splitTheta L * (1 * D.length) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow D.length_pos.le) ht.le
    _ ≤ (1 / 4 : ℝ) * D.length := by
      simpa using mul_le_mul_of_nonneg_right (splitTheta_le_quarter L hL) D.length_pos.le
    _ = _ := by ring

theorem schedule_final_remainder_upper (D : IntervalCell) (L : ℕ) (hL : 2 ≤ L) :
    (geometricSplit D (splitTheta L) (splitTheta_pos L hL) (splitTheta_lt_one L hL) L).parent.length ≤
      (2 / 3 : ℝ) * D.length := by
  rw [geometricSplit_parent_length]
  exact mul_le_mul_of_nonneg_right (remainder_power_upper L hL) D.length_pos.le

end PositiveBiorthogonal
