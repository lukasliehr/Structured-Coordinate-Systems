import Lean_Code.PositiveBiorthogonal.FiniteKernel
import Lean_Code.PositiveBiorthogonal.FiniteCuts

/-! A Hilbert rectangle, with its first block reversed, inside a finite coordinate space. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def reversedHeadIndex (m h : ℕ) (hh : h ≤ m) (i : Fin h) : Fin m :=
  ⟨h - 1 - i.val, by have := i.isLt; omega⟩

theorem reversedHeadIndex_injective (m h : ℕ) (hh : h ≤ m) :
    Function.Injective (reversedHeadIndex m h hh) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp [reversedHeadIndex] at this
  have := i.isLt
  have := j.isLt
  omega

def tailIndex (m h : ℕ) (i : Fin (m - h)) : Fin m :=
  ⟨h + i.val, by have := i.isLt; omega⟩

theorem tailIndex_injective (m h : ℕ) : Function.Injective (tailIndex m h) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp [tailIndex] at this
  omega

omit [Fact (1 ≤ p)] in
theorem hilbertAction_single (I J : ℕ) (j : Fin J) (i : Fin I) :
    hilbertAction (𝕜 := 𝕜) (p := p) I J (PiLp.single p j 1) i =
      (hilbertKernel i.val j.val : 𝕜) := by
  simp [hilbertAction, PiLp.single_apply]

def hilbertCorner {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (m h : ℕ) (hh : h ≤ m) :
    FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  coordinateScatter (reversedHeadIndex m h hh) (reversedHeadIndex_injective m h hh) ∘L
    hilbertOperator (q := q) hp1 hpfin h (m - h) ∘L
      coordinateGather (tailIndex m h) (tailIndex_injective m h)

theorem hilbertCorner_norm_le {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (m h : ℕ) (hh : h ≤ m) :
    ‖hilbertCorner (𝕜 := 𝕜) (q := q) hp1 hpfin m h hh‖ ≤ p.toReal + q.toReal := by
  have hC : 0 ≤ p.toReal + q.toReal := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖finiteScatter (reversedHeadIndex m h hh)
    (hilbertAction h (m - h) (finiteGather (tailIndex m h) x))‖ ≤ _
  apply (finiteScatter_norm_le _ (reversedHeadIndex_injective m h hh) _).trans
  apply (hilbertAction_norm_le (q := q) hp1 hpfin _ _ _).trans
  exact mul_le_mul_of_nonneg_left (finiteGather_norm_le _ (tailIndex_injective m h) x) hC

theorem hilbertCorner_single {q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
    (hp1 : 1 < p) (hpfin : p ≠ ∞) (m h : ℕ) (hh : h ≤ m) (i j : Fin m) :
    hilbertCorner (𝕜 := 𝕜) (q := q) hp1 hpfin m h hh (PiLp.single p j 1) i =
      if i.val < h ∧ h ≤ j.val then (hilbertKernel (h - 1 - i.val) (j.val - h) : 𝕜) else 0 := by
  classical
  change finiteScatter (reversedHeadIndex m h hh)
    (hilbertAction h (m - h) (finiteGather (tailIndex m h) (PiLp.single p j 1))) i = _
  by_cases hi : i.val < h
  · let k : Fin h := ⟨h - 1 - i.val, by omega⟩
    have hk : reversedHeadIndex m h hh k = i := by
      apply Fin.ext
      dsimp [reversedHeadIndex, k]
      omega
    rw [← hk, finiteScatter_image _ (reversedHeadIndex_injective m h hh), hk]
    by_cases hj : h ≤ j.val
    · let l : Fin (m - h) := ⟨j.val - h, by have := j.isLt; omega⟩
      have hl : tailIndex m h l = j := by
        apply Fin.ext
        dsimp [tailIndex, l]
        omega
      rw [← hl, finiteGather_single_image _ (tailIndex_injective m h), hilbertAction_single, hl]
      simp only [hi, hj, and_self, if_true]
      rfl
    · have hj' : j ∉ Set.range (tailIndex m h) := by
        rintro ⟨l, he⟩
        have := congrArg Fin.val he
        dsimp [tailIndex] at this
        omega
      rw [finiteGather_single_not_image _ j hj']
      simp [hilbertAction, hi, hj]
  · have hi' : i ∉ Set.range (reversedHeadIndex m h hh) := by
      rintro ⟨k, he⟩
      have := congrArg Fin.val he
      dsimp [reversedHeadIndex] at this
      have := k.isLt
      omega
    rw [finiteScatter_not_image _ _ i hi']
    simp [hi]

end PositiveBiorthogonal
