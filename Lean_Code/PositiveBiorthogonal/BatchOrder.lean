import Lean_Code.PositiveBiorthogonal.FiniteCoordinates

/-! Explicit positions for the two entries of each pair, followed by residual entries. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PositiveBiorthogonal

abbrev BatchIndex (N : ℕ) := (Fin N × Fin 2) ⊕ Fin N

def batchPosition {N : ℕ} : BatchIndex N → Fin (3 * N)
  | Sum.inl (j, b) => ⟨2 * j.val + b.val, by omega⟩
  | Sum.inr j => ⟨2 * N + j.val, by omega⟩

theorem batchPosition_injective (N : ℕ) : Function.Injective (batchPosition (N := N)) := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with ⟨i, b⟩ | i <;> rcases y with ⟨j, c⟩ | j
  · have hi : i = j := Fin.ext (by dsimp [batchPosition] at hv; omega)
    have hb : b = c := Fin.ext (by dsimp [batchPosition] at hv; omega)
    simp [hi, hb]
  · dsimp [batchPosition] at hv
    omega
  · dsimp [batchPosition] at hv
    omega
  · congr 1
    apply Fin.ext
    dsimp [batchPosition] at hv
    omega

theorem batchPosition_surjective (N : ℕ) : Function.Surjective (batchPosition (N := N)) := by
  intro k
  by_cases hk : k.val < 2 * N
  · refine ⟨Sum.inl (⟨k.val / 2, by omega⟩, ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩), ?_⟩
    apply Fin.ext
    dsimp [batchPosition]
    omega
  · refine ⟨Sum.inr ⟨k.val - 2 * N, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [batchPosition]
    omega

def batchOrder (N : ℕ) : BatchIndex N ≃ Fin (3 * N) :=
  Equiv.ofBijective batchPosition ⟨batchPosition_injective N, batchPosition_surjective N⟩

@[simp] theorem batchOrder_apply {N : ℕ} (i : BatchIndex N) : batchOrder N i = batchPosition i := rfl

def batchFirst {N : ℕ} (i : Fin N) : Fin (2 * N) := ⟨i.val, by omega⟩
def batchLast {N : ℕ} (i : Fin N) : Fin (2 * N) := ⟨N + i.val, by omega⟩

@[simp] theorem batchFirst_inj {N : ℕ} (i j : Fin N) : batchFirst i = batchFirst j ↔ i = j := by
  simp [batchFirst, Fin.ext_iff]

@[simp] theorem batchLast_inj {N : ℕ} (i j : Fin N) : batchLast i = batchLast j ↔ i = j := by
  simp [batchLast, Fin.ext_iff]

@[simp] theorem batchFirst_ne_last {N : ℕ} (i j : Fin N) : batchFirst i ≠ batchLast j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [batchFirst, batchLast] at hv
  omega

@[simp] theorem batchLast_ne_first {N : ℕ} (i j : Fin N) : batchLast i ≠ batchFirst j :=
  (batchFirst_ne_last j i).symm

end PositiveBiorthogonal
