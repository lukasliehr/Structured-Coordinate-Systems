import Lean_Code.PositiveBiorthogonal.Batch

/-! Exact finite sums at each of the three kinds of cuts in the ordered batch. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal

def finitePrefix {V : Type*} [AddCommMonoid V] {m : ℕ} (f : Fin m → V) (h : ℕ) : V :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < h), f i

@[simp] theorem finitePrefix_zero {V : Type*} [AddCommMonoid V] {m : ℕ} (f : Fin m → V) :
    finitePrefix f 0 = 0 := by simp [finitePrefix]

theorem finitePrefix_succ {V : Type*} [AddCommMonoid V] {m : ℕ} (f : Fin m → V) (j : Fin m) :
    finitePrefix f (j.val + 1) = finitePrefix f j.val + f j := by
  classical
  have he : Finset.univ.filter (fun i : Fin m => i.val < j.val + 1) =
      insert j (Finset.univ.filter (fun i : Fin m => i.val < j.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  simp only [finitePrefix, he]
  rw [Finset.sum_insert (by simp)]
  exact add_comm _ _

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def rankPair (f : L 𝕜 p) (g : L 𝕜 q) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  (representedFunctional (p := p) g).smulRight f

@[simp] theorem rankPair_apply (v : L 𝕜 p) (g : L 𝕜 q) (f : L 𝕜 p) :
    rankPair v g f = pairing f g • v := by simp [rankPair]

theorem rankPair_sub_smul (d H : L 𝕜 p) (s : L 𝕜 q) (c : 𝕜) :
    rankPair (d - c • H) s = rankPair d s - c • rankPair H s := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, ContinuousLinearMap.smul_apply, rankPair_apply]
  module

theorem rankPair_smul_add (H : L 𝕜 p) (s φ : L 𝕜 q) (c : 𝕜) :
    rankPair H (c • s + φ) = c • rankPair H s + rankPair H φ := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [add_apply, ContinuousLinearMap.smul_apply, rankPair_apply,
    pairing_add_right, pairing_smul_right]
  module

def lpPrefix {m : ℕ} (v : Fin m → L 𝕜 p) (ξ : Fin m → L 𝕜 q) (h : ℕ) :
    L 𝕜 p →L[𝕜] L 𝕜 p := finitePrefix (fun i => rankPair (v i) (ξ i)) h

@[simp] theorem lpPrefix_zero {m : ℕ} (v : Fin m → L 𝕜 p) (ξ : Fin m → L 𝕜 q) :
    lpPrefix v ξ 0 = 0 := finitePrefix_zero _

theorem lpPrefix_succ {m : ℕ} (v : Fin m → L 𝕜 p) (ξ : Fin m → L 𝕜 q) (j : Fin m) :
    lpPrefix v ξ (j.val + 1) = lpPrefix v ξ j.val + rankPair (v j) (ξ j) :=
  finitePrefix_succ _ j

@[simp] theorem orderedBatchVector_position {N : ℕ} (d : Fin (2 * N) → L 𝕜 p)
    (H : Fin N → L 𝕜 p) (a : 𝕜) (i : BatchIndex N) :
    orderedBatchVector d H a (batchPosition i) = batchVector d H a i := by
  change batchVector d H a ((batchOrder N).symm (batchOrder N i)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem orderedBatchCoefficient_position {N : ℕ} (s : Fin (2 * N) → L 𝕜 q)
    (φ : Fin N → L 𝕜 q) (a : 𝕜) (i : BatchIndex N) :
    orderedBatchCoefficient s φ a (batchPosition i) = batchCoefficient s φ a i := by
  change batchCoefficient s φ a ((batchOrder N).symm (batchOrder N i)) = _
  rw [Equiv.symm_apply_apply]

variable {N : ℕ} (d : Fin (2 * N) → L 𝕜 p) (s : Fin (2 * N) → L 𝕜 q)
  (H : Fin N → L 𝕜 p) (φ : Fin N → L 𝕜 q) (a : 𝕜)

def batchPartial (h : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  lpPrefix (orderedBatchVector d H a) (orderedBatchCoefficient s φ a) h

@[simp] theorem batchPartial_zero : batchPartial d s H φ a 0 = 0 := lpPrefix_zero _ _

theorem batchPartial_first_step (j : Fin N) :
    batchPartial d s H φ a (2 * j.val + 1) = batchPartial d s H φ a (2 * j.val) +
      (rankPair (d (batchFirst j)) (s (batchFirst j)) - a⁻¹ • rankPair (H j) (s (batchFirst j))) := by
  have h := lpPrefix_succ (orderedBatchVector d H a) (orderedBatchCoefficient s φ a)
    (batchPosition (Sum.inl (j, 0)))
  rw [orderedBatchVector_position, orderedBatchCoefficient_position] at h
  simpa only [orderedBatchVector_position, orderedBatchCoefficient_position,
    batchVector, batchCoefficient, if_pos rfl, ite_true, batchPosition, Fin.val_zero, add_zero,
    rankPair_sub_smul, batchPartial] using h

theorem batchPartial_second_step (j : Fin N) :
    batchPartial d s H φ a (2 * j.val + 1 + 1) = batchPartial d s H φ a (2 * j.val + 1) +
      (a⁻¹ • rankPair (H j) (s (batchFirst j)) + rankPair (H j) (φ j)) := by
  have h := lpPrefix_succ (orderedBatchVector d H a) (orderedBatchCoefficient s φ a)
    (batchPosition (Sum.inl (j, 1)))
  rw [orderedBatchVector_position, orderedBatchCoefficient_position] at h
  simpa only [orderedBatchVector_position, orderedBatchCoefficient_position,
    batchVector, batchCoefficient, show (1 : Fin 2) ≠ 0 from by decide, if_false,
    batchPosition, Fin.val_one, rankPair_smul_add, batchPartial] using h

theorem batchPartial_pair_step (j : Fin N) :
    batchPartial d s H φ a (2 * (j.val + 1)) = batchPartial d s H φ a (2 * j.val) +
      rankPair (d (batchFirst j)) (s (batchFirst j)) + rankPair (H j) (φ j) := by
  have h1 := batchPartial_second_step d s H φ a j
  rw [batchPartial_first_step] at h1
  convert h1 using 1 <;> first | congr 1 <;> omega | abel

theorem batchPartial_residual_step (j : Fin N) :
    batchPartial d s H φ a (2 * N + j.val + 1) = batchPartial d s H φ a (2 * N + j.val) +
      rankPair (d (batchLast j)) (s (batchLast j)) := by
  have h := lpPrefix_succ (orderedBatchVector d H a) (orderedBatchCoefficient s φ a)
    (batchPosition (Sum.inr j))
  rw [orderedBatchVector_position, orderedBatchCoefficient_position] at h
  simpa only [orderedBatchVector_position, orderedBatchCoefficient_position,
    batchVector, batchCoefficient, batchPosition, batchPartial] using h

variable (E : ℕ → L 𝕜 p →L[𝕜] L 𝕜 p)
  (hE : ∀ j : Fin N, E (j.val + 1) - E j.val = rankPair (H j) (φ j))
include hE

theorem batch_cut_even (h : ℕ) (hh : h ≤ N) :
    E 0 + batchPartial d s H φ a (2 * h) = E h + lpPrefix d s h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hn : h < N := by omega
    let j : Fin N := ⟨h, hn⟩
    have hb := batchPartial_pair_step d s H φ a j
    have hc := lpPrefix_succ d s (batchFirst j)
    have he := hE j
    have hi := ih (by omega)
    change E 0 + batchPartial d s H φ a (2 * (h + 1)) = E (h + 1) + lpPrefix d s (h + 1)
    change batchPartial d s H φ a (2 * (h + 1)) = batchPartial d s H φ a (2 * h) +
      rankPair (d (batchFirst j)) (s (batchFirst j)) + rankPair (H j) (φ j) at hb
    change lpPrefix d s (h + 1) = lpPrefix d s h + rankPair (d (batchFirst j)) (s (batchFirst j)) at hc
    change E (h + 1) - E h = rankPair (H j) (φ j) at he
    rw [hb, hc, ← he]
    rw [← add_assoc, ← add_assoc, hi]
    abel

theorem batch_cut_odd (j : Fin N) :
    E 0 + batchPartial d s H φ a (2 * j.val + 1) =
      E j.val + lpPrefix d s (j.val + 1) - a⁻¹ • rankPair (H j) (s (batchFirst j)) := by
  rw [batchPartial_first_step]
  have hi := batch_cut_even d s H φ a E hE j.val j.isLt.le
  have hc := lpPrefix_succ d s (batchFirst j)
  change lpPrefix d s (j.val + 1) = lpPrefix d s j.val +
    rankPair (d (batchFirst j)) (s (batchFirst j)) at hc
  rw [hc]
  rw [← add_assoc, hi]
  abel

theorem batch_cut_residual (h : ℕ) (hh : h ≤ N) :
    E 0 + batchPartial d s H φ a (2 * N + h) = E N + lpPrefix d s (N + h) := by
  induction h with
  | zero => simpa only [add_zero] using batch_cut_even d s H φ a E hE N le_rfl
  | succ h ih =>
    have hn : h < N := by omega
    let j : Fin N := ⟨h, hn⟩
    have hb := batchPartial_residual_step d s H φ a j
    have hc := lpPrefix_succ d s (batchLast j)
    have hi := ih (by omega)
    change batchPartial d s H φ a (2 * N + h + 1) = batchPartial d s H φ a (2 * N + h) +
      rankPair (d (batchLast j)) (s (batchLast j)) at hb
    change lpPrefix d s (N + h + 1) = lpPrefix d s (N + h) +
      rankPair (d (batchLast j)) (s (batchLast j)) at hc
    change E 0 + batchPartial d s H φ a (2 * N + h + 1) = E N + lpPrefix d s (N + h + 1)
    rw [hb, hc, ← add_assoc, hi, add_assoc]

end PositiveBiorthogonal
