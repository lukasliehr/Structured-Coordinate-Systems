import Lean_Code.PositiveBiorthogonal.StageMesh

/-! The unique batch location of each non-root index and the resulting raw sequences. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace PositiveBiorthogonal

theorem dependent_fin_apply_eq {V : Type*} {m : ℕ → ℕ} (f : ∀ k, Fin (m k) → V)
    {k l : ℕ} (h : k = l) (i : Fin (m k)) (j : Fin (m l)) (hi : i.val = j.val) :
    f k i = f l j := by
  subst l
  exact congrArg (f k) (Fin.ext hi)

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

theorem batch_end_exists (n : ℕ) : ∃ k : ℕ, n < (C.stage (k + 1)).totalCount :=
  ⟨n, by have h := C.stage_totalCount_lower (n + 1); omega⟩

def locate (n : ℕ) : ℕ := Nat.find (C.batch_end_exists n)

theorem locate_upper (n : ℕ) : n < (C.stage (C.locate n + 1)).totalCount :=
  Nat.find_spec (C.batch_end_exists n)

theorem locate_lower (n : ℕ) (hn : 0 < n) : (C.stage (C.locate n)).totalCount ≤ n := by
  cases hk : C.locate n with
  | zero => rw [C.stage_totalCount_zero]; omega
  | succ k =>
    have hmin := Nat.find_min (C.batch_end_exists n) (show k < C.locate n by rw [hk]; omega)
    exact Nat.le_of_not_gt hmin

theorem locate_unique (n k : ℕ) (hlo : (C.stage k).totalCount ≤ n)
    (hhi : n < (C.stage (k + 1)).totalCount) : C.locate n = k := by
  have hn : 0 < n := (C.stage k).totalCount_pos.trans_le hlo
  have hcu := C.locate_upper n
  have hcl := C.locate_lower n hn
  rcases lt_trichotomy (C.locate n) k with h | h | h
  · have hm : (C.stage (C.locate n + 1)).totalCount ≤ (C.stage k).totalCount :=
      C.stage_totalCount_strictMono.monotone h
    omega
  · exact h
  · have hm : (C.stage (k + 1)).totalCount ≤ (C.stage (C.locate n)).totalCount :=
      C.stage_totalCount_strictMono.monotone h
    omega

def offset (n : ℕ) : Fin (3 * C.batchSize (C.locate n)) :=
  ⟨n - (C.stage (C.locate n)).totalCount, by
    have hu := C.locate_upper n
    rw [C.stage_totalCount_succ] at hu
    have hp := C.batchSize_ge_two (C.locate n)
    omega⟩

theorem flatten_index (n : ℕ) (hn : 0 < n) :
    n = (C.stage (C.locate n)).totalCount + (C.offset n).val := by
  have hl := C.locate_lower n hn
  change n = (C.stage (C.locate n)).totalCount + (n - (C.stage (C.locate n)).totalCount)
  omega

theorem locate_batch_index (k : ℕ) (j : Fin (3 * C.batchSize k)) :
    C.locate ((C.stage k).totalCount + j.val) = k := by
  apply C.locate_unique
  · omega
  · rw [C.stage_totalCount_succ]
    omega

theorem flatten_index_unique (k l : ℕ) (i : Fin (3 * C.batchSize k)) (j : Fin (3 * C.batchSize l))
    (h : (C.stage k).totalCount + i.val = (C.stage l).totalCount + j.val) :
    k = l ∧ i.val = j.val := by
  have hk := C.locate_batch_index k i
  have hl := C.locate_batch_index l j
  rw [h] at hk
  have hkl : k = l := hk.symm.trans hl
  refine ⟨hkl, ?_⟩
  subst l
  omega

def rawVector (n : ℕ) : L 𝕜 p :=
  if n = 0 then (gridUnit 0).indicator else C.batchVectors (C.locate n) (C.offset n)

def rawCoefficient (n : ℕ) : L 𝕜 q :=
  if n = 0 then (gridUnit 0).indicator else C.batchCoefficients (C.locate n) (C.offset n)

@[simp] theorem rawVector_zero : C.rawVector 0 = (gridUnit 0).indicator := by simp [rawVector]
@[simp] theorem rawCoefficient_zero : C.rawCoefficient 0 = (gridUnit 0).indicator := by simp [rawCoefficient]

theorem rawVector_batch (k : ℕ) (j : Fin (3 * C.batchSize k)) :
    C.rawVector ((C.stage k).totalCount + j.val) = C.batchVectors k j := by
  have hn : (C.stage k).totalCount + j.val ≠ 0 := by have h := (C.stage k).totalCount_pos; omega
  have hl := C.locate_batch_index k j
  simp only [rawVector, if_neg hn, offset, hl, Nat.add_sub_cancel_left]
  exact dependent_fin_apply_eq C.batchVectors hl _ j rfl

theorem rawCoefficient_batch (k : ℕ) (j : Fin (3 * C.batchSize k)) :
    C.rawCoefficient ((C.stage k).totalCount + j.val) = C.batchCoefficients k j := by
  have hn : (C.stage k).totalCount + j.val ≠ 0 := by have h := (C.stage k).totalCount_pos; omega
  have hl := C.locate_batch_index k j
  simp only [rawCoefficient, if_neg hn, offset, hl, Nat.add_sub_cancel_left]
  exact dependent_fin_apply_eq C.batchCoefficients hl _ j rfl

theorem rawVector_step (n : ℕ) : CompactlySupportedStep (C.rawVector n) := by
  by_cases hn : n = 0
  · subst n
    exact (gridUnit 0).indicator_step
  · rw [rawVector, if_neg hn]
    exact C.aux.batchVectors_step _ _ _ _

theorem rawCoefficient_step (n : ℕ) : CompactlySupportedStep (C.rawCoefficient n) := by
  by_cases hn : n = 0
  · subst n
    exact (gridUnit 0).indicator_step
  · rw [rawCoefficient, if_neg hn]
    exact C.aux.batchCoefficients_step _ _ _ _

end ConstructionData
end PositiveBiorthogonal
