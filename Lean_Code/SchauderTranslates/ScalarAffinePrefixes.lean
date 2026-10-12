import Lean_Code.SchauderTranslates.ScalarAffine
import Lean_Code.SchauderTranslates.ScalarCenteredFromAugmented

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A coordinate prefix has norm at most one in the Haar metric, including empty index types. -/
theorem scalarRowPrefix_haar (n k : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    (gramDifference q (scalarRowPrefixMatrix n k) 1).PosSemidef := by
  have he : gramDifference q (scalarRowPrefixMatrix n k) 1 =
      Matrix.diagonal (fun i => ((q - if (scalarRowEquiv n i).val < k then 1 else 0 : ℝ) : ℂ)) := by
    unfold gramDifference scalarRowPrefixMatrix
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : (scalarRowEquiv n i).val < k <;>
        simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Pi.star_apply, hi, Complex.real_smul]
    · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [he, Matrix.posSemidef_diagonal_iff]
  intro i
  have h : 0 ≤ q - if (scalarRowEquiv n i).val < k then 1 else 0 := by
    split_ifs <;> linarith
  exact_mod_cast h

namespace ScalarData
variable {d n : ℕ}

theorem affine_augmented_prefix (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    {q : ℝ} (hq : 1 ≤ q) (hp : s.AugmentedPrefixSqBound q) :
    (s.affine θ h0 h1).AugmentedPrefixSqBound q := by
  have hq0 := (zero_le_one : (0 : ℝ) ≤ 1).trans hq
  apply ((s.affine θ h0 h1).augmentedPrefixSqBound_iff_gram hq0).mpr
  intro k
  have hi := gram_prefix_iff s.rawGram_posDef (scalarRowPrefixMatrix n k) (Real.sqrt q)
  rw [Real.sq_sqrt hq0] at hi
  have hs := hi.mp ((s.augmentedPrefixSqBound_iff_gram hq0).mp hp k)
  have h := gram_prefix_positive_sum q (scalarRowPrefixMatrix n k) 1 s.rawGram
    (scalarRowPrefix_haar n k hq) hs (sub_nonneg.mpr h1) h0
  have hi' := gram_prefix_iff (s.affine θ h0 h1).rawGram_posDef (scalarRowPrefixMatrix n k) (Real.sqrt q)
  rw [Real.sq_sqrt hq0] at hi'
  apply hi'.mpr
  rw [s.affine_rawGram]
  exact h

theorem affine_centered_prefix (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    {q : ℝ} (hq : 1 ≤ q) (hp : s.AugmentedPrefixSqBound q) :
    (s.affine θ h0 h1).CenteredPrefixSqBound q :=
  (s.affine θ h0 h1).centered_prefix_of_augmented (zero_le_one.trans hq)
    (s.affine_augmented_prefix θ h0 h1 hq hp)

end ScalarData
end SchauderTranslates
