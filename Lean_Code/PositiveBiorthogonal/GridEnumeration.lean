import Lean_Code.PositiveBiorthogonal.LocalPositive

/-! The source enumeration 0,1,-1,2,-2,..., with explicit prefix and fresh blocks. -/
noncomputable section
set_option autoImplicit false
open Set
namespace PositiveBiorthogonal

def gridEnumeration (n : ℕ) : ℤ := if n % 2 = 0 then -(n / 2 : ℕ) else (n / 2 : ℕ) + 1

@[simp] theorem gridEnumeration_even (n : ℕ) : gridEnumeration (2 * n) = -(n : ℤ) := by
  simp [gridEnumeration]

@[simp] theorem gridEnumeration_odd (n : ℕ) : gridEnumeration (2 * n + 1) = (n : ℤ) + 1 := by
  simp [gridEnumeration, Nat.add_div]

@[simp] theorem gridEnumeration_zero : gridEnumeration 0 = 0 := by simp [gridEnumeration]

theorem gridEnumeration_injective : Function.Injective gridEnumeration := by
  intro n m h
  unfold gridEnumeration at h
  split_ifs at h <;> omega

theorem gridEnumeration_surjective : Function.Surjective gridEnumeration := by
  intro z
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact ⟨0, gridEnumeration_zero⟩
    | succ n => exact ⟨2 * n + 1, by simp⟩
  | negSucc n => exact ⟨2 * (n + 1), by rw [gridEnumeration_even]; omega⟩

def gridEnumerationEquiv : ℕ ≃ ℤ :=
  Equiv.ofBijective gridEnumeration ⟨gridEnumeration_injective, gridEnumeration_surjective⟩

def enumeratedBlock (a m : ℕ) : UnitBlock m where
  unit j := gridEnumeration (a + j.val)
  injective := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel (gridEnumeration_injective hij))

def prefixUnits (a : ℕ) : Finset ℤ := (Finset.range a).image gridEnumeration

theorem prefixUnits_nonempty {a : ℕ} (ha : 0 < a) : (prefixUnits a).Nonempty :=
  (Finset.nonempty_range_iff.mpr (by omega)).image _

theorem prefix_block_carrier (a : ℕ) :
    (enumeratedBlock 0 a).carrier = ⋃ z ∈ prefixUnits a, (gridUnit z).carrier := by
  ext x
  simp [UnitBlock.carrier, UnitBlock.cell, enumeratedBlock, prefixUnits, Fin.exists_iff]

theorem prefixUnits_add (a m : ℕ) :
    prefixUnits (a + m) = prefixUnits a ∪ Finset.univ.image (enumeratedBlock a m).unit := by
  classical
  ext z
  simp only [prefixUnits, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases ha : k < a
    · exact Or.inl ⟨k, ha, rfl⟩
    · right
      refine ⟨⟨k - a, by omega⟩, ?_⟩
      change gridEnumeration (a + (k - a)) = gridEnumeration k
      congr 1
      omega
  · rintro (⟨k, hk, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨a + j.val, by omega, rfl⟩

theorem enumerated_fresh_disjoint (a m : ℕ) :
    Disjoint (enumeratedBlock a m).carrier (enumeratedBlock 0 a).carrier := by
  simp only [UnitBlock.carrier, Set.disjoint_iUnion_left, Set.disjoint_iUnion_right]
  intro j i
  apply gridUnit_disjoint
  intro h
  have he : a + i.val = 0 + j.val := gridEnumeration_injective h
  omega

theorem enumerated_blocks_disjoint {a m b n : ℕ} (hab : a + m ≤ b) :
    Disjoint (enumeratedBlock a m).carrier (enumeratedBlock b n).carrier := by
  simp only [UnitBlock.carrier, Set.disjoint_iUnion_left, Set.disjoint_iUnion_right]
  intro j i
  apply gridUnit_disjoint
  intro h
  have he : a + i.val = b + j.val := gridEnumeration_injective h
  omega

end PositiveBiorthogonal
