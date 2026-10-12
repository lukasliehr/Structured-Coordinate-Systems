import Lean_Code.SchauderTranslates.OrderedGramPrefixes
import Lean_Code.SchauderTranslates.FiniteRowOrder
import Lean_Code.SchauderTranslates.MetricFinitePrefixes

noncomputable section
open Matrix ContinuousLinearMap InnerProductSpace
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The constant is index zero in an augmented scalar list. -/
def ScalarData.orderedAugmentedVector {d n : ℕ} (s : ScalarData d n) (i : Fin (n + 1)) :=
  s.vector (s.augmentedFrequency ((scalarRowEquiv n).symm i))

def ScalarData.AugmentedPrefixSqBound {d n : ℕ} (s : ScalarData d n) (q : ℝ) : Prop :=
  FinitePrefixSqBound s.orderedAugmentedVector q

/-- The coefficient mask of the first `k` augmented rows. -/
def scalarRowPrefixMatrix (n k : ℕ) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ :=
  Matrix.diagonal (fun i => if (scalarRowEquiv n i).val < k then 1 else 0)

namespace ScalarData
variable {d n : ℕ}

theorem orderedAugmentedVector_linearIndependent (s : ScalarData d n) :
    LinearIndependent ℂ s.orderedAugmentedVector :=
  (s.toTorusWeight.vectors_linearIndependent s.augmentedFrequency s.augmentedFrequency_injective).comp
    (scalarRowEquiv n).symm (scalarRowEquiv n).symm.injective

theorem orderedAugmentedVector_gram (s : ScalarData d n) :
    Matrix.gram ℂ s.orderedAugmentedVector =
      s.rawGram.submatrix (scalarRowEquiv n).symm (scalarRowEquiv n).symm := rfl

/-- Ordered synthesis and the original constant-first Gram have identical prefix bounds. -/
theorem augmentedPrefixSqBound_iff_gram (s : ScalarData d n) {q : ℝ} (hq : 0 ≤ q) :
    s.AugmentedPrefixSqBound q ↔
      ∀ k, ‖gramConjugate s.rawGram (scalarRowPrefixMatrix n k)‖ ^ 2 ≤ q := by
  rw [AugmentedPrefixSqBound, finitePrefixSqBound_iff_gram _
    s.orderedAugmentedVector_linearIndependent hq, s.orderedAugmentedVector_gram]
  constructor
  · intro h k
    have hb := gramConjugate_reindex_bound
      (s.rawGram_posDef.submatrix (scalarRowEquiv n).symm.injective)
      (finitePrefixMatrix (n + 1) k) (scalarRowEquiv n) hq (h k)
    have hB : (s.rawGram.submatrix (scalarRowEquiv n).symm (scalarRowEquiv n).symm).submatrix
        (scalarRowEquiv n) (scalarRowEquiv n) = s.rawGram := by ext i j; simp
    have hD : (finitePrefixMatrix (n + 1) k).submatrix (scalarRowEquiv n) (scalarRowEquiv n) =
        scalarRowPrefixMatrix n k := by
      rw [finitePrefixMatrix, diagonal_submatrix_equiv]
      rfl
    rw [hB, hD] at hb
    exact hb
  · intro h k
    have hb := gramConjugate_reindex_bound s.rawGram_posDef (scalarRowPrefixMatrix n k)
      (scalarRowEquiv n).symm hq (h k)
    simpa only [scalarRowPrefixMatrix, diagonal_submatrix_equiv, Function.comp_def,
      Equiv.apply_symm_apply, finitePrefixMatrix] using hb

/-- Evenness identifies the real coordinate prefix with its complex Gram prefix. -/
theorem metricPrefix_finset_sq_le (s : ScalarData d n) (hs : s.IsEven)
    (S : Finset (Unit ⊕ Fin n)) {q : ℝ}
    (h : ‖gramConjugate s.rawGram
      (Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0))‖ ^ 2 ≤ q) :
    ‖metricPrefix s.realRawGram (fun i : S => (i : Unit ⊕ Fin n))‖ ^ 2 ≤ q := by
  have hBC : (s.realRawGram.map Complex.ofReal).PosDef := by
    rw [s.realRawGram_map hs]
    exact s.rawGram_posDef
  have he := gramConjugate_real_complex_norm s.realRawGram_posDef hBC
    (Matrix.diagonal (fun i => if i ∈ S then (1 : ℝ) else 0))
  rw [s.realRawGram_map hs] at he
  have hD : (Matrix.diagonal (fun i => if i ∈ S then (1 : ℝ) else 0)).map Complex.ofReal =
      Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_map (f := Complex.ofReal) Complex.ofReal_zero]
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  rw [hD] at he
  rw [metricPrefix_finset_diagonal, ← he]
  exact h

/-- The complete old rows before the active row obey the augmented prefix bound. -/
theorem precedingRows_prefix_sq_le (s : ScalarData d n) (hs : s.IsEven) {q : ℝ}
    (hq : 0 ≤ q) (h : s.AugmentedPrefixSqBound q) (j : Unit ⊕ Fin n) :
    ‖metricPrefix s.realRawGram
      (fun i : precedingScalarRows n j => (i : Unit ⊕ Fin n))‖ ^ 2 ≤ q := by
  apply s.metricPrefix_finset_sq_le hs
  simpa only [scalarRowPrefixMatrix, mem_precedingScalarRows, Fin.lt_def] using
    (s.augmentedPrefixSqBound_iff_gram hq).mp h (scalarRowEquiv n j).val

/-- Completing the active row is the next augmented prefix, including the last row. -/
theorem throughRow_prefix_sq_le (s : ScalarData d n) (hs : s.IsEven) {q : ℝ}
    (hq : 0 ≤ q) (h : s.AugmentedPrefixSqBound q) (j : Unit ⊕ Fin n) :
    ‖metricPrefix s.realRawGram
      (fun i : (insert j (precedingScalarRows n j) : Finset (Unit ⊕ Fin n)) =>
        (i : Unit ⊕ Fin n))‖ ^ 2 ≤ q := by
  apply s.metricPrefix_finset_sq_le hs
  have hm (i : Unit ⊕ Fin n) :
      i ∈ insert j (precedingScalarRows n j) ↔
        (scalarRowEquiv n i).val < (scalarRowEquiv n j).val + 1 := by
    rw [Finset.mem_insert, mem_precedingScalarRows]
    have he : i = j ↔ scalarRowEquiv n i = scalarRowEquiv n j :=
      (scalarRowEquiv n).injective.eq_iff.symm
    rw [he, Fin.ext_iff, Fin.lt_def]
    omega
  simpa only [hm, scalarRowPrefixMatrix] using
    (s.augmentedPrefixSqBound_iff_gram hq).mp h ((scalarRowEquiv n j).val + 1)

end ScalarData
end SchauderTranslates
