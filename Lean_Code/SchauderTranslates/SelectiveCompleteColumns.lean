import Lean_Code.SchauderTranslates.SelectiveAugmentedGram

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Every zero-one coordinate mask is a contraction for the identity metric. -/
theorem diagonalMask_identity_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] {C : ℝ} (hC : 1 ≤ C) :
    (gramDifference C (Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)) 1).PosSemidef := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0)
  have hstar : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst j; by_cases hi : p i <;> simp [D, Matrix.conjTranspose_apply, hi]
    · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have hsquare : D * D = D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> norm_num
  have he : gramDifference C D 1 = Matrix.diagonal (fun i => (C : ℂ) - if p i then 1 else 0) := by
    rw [gramDifference, hstar, Matrix.mul_one, hsquare]
    ext i j
    by_cases hij : i = j
    · subst j; simp [D, Matrix.diagonal_apply, Complex.real_smul]
    · simp [D, Matrix.diagonal_apply, Matrix.one_apply, hij]
  change (gramDifference C D 1).PosSemidef
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hp : p i
  · simp only [Pi.zero_apply, if_pos hp]
    exact_mod_cast sub_nonneg.mpr hC
  · simp only [Pi.zero_apply, if_neg hp, sub_zero]
    exact_mod_cast (zero_le_one.trans hC)

namespace SelectiveKernelData
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- The complete-column prefix bound holds directly in the original row metric. -/
theorem augmented_complete_column_bound
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (hp : a.scalar.AugmentedPrefixSqBound 4) (k : ℕ) :
    ‖gramConjugate (a.augmentedRawGram ρ r)
      (scalarRowPrefixMatrix n k ⊗ₖ (1 : Matrix ι ι ℂ))‖ ≤ 2 := by
  have haux : (gramDifference (2 ^ 2) (scalarRowPrefixMatrix n k) a.scalar.rawGram).PosSemidef := by
    apply (gram_prefix_iff a.scalar.rawGram_posDef _ 2).mp
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      ((a.scalar.augmentedPrefixSqBound_iff_gram (by norm_num)).mp hp k)
  have hid : (gramDifference (2 ^ 2) (scalarRowPrefixMatrix n k) 1).PosSemidef :=
    diagonalMask_identity_difference (fun i => (scalarRowEquiv n i).val < k) (by norm_num)
  have hb := a.rawSeedGram_order ρ r
  have h := mixedTensorGram_complete_column_bound haux hid hb.1 hb.2
  have hn := (gram_prefix_iff (a.augmentedRawGram_posDef ρ r hr)
    (scalarRowPrefixMatrix n k ⊗ₖ (1 : Matrix ι ι ℂ)) 2).mpr h
  nlinarith [norm_nonneg (gramConjugate (a.augmentedRawGram ρ r)
    (scalarRowPrefixMatrix n k ⊗ₖ (1 : Matrix ι ι ℂ)))]

end SelectiveKernelData
end SchauderTranslates
