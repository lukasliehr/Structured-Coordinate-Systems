import Lean_Code.SchauderTranslates.SelectiveCompleteColumns
import Lean_Code.SchauderTranslates.SelectedColumnMask

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder MatrixOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_inverse_diagonal_le {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (k : ι) {C : ℝ} (h : (G⁻¹ k k).re ≤ C) : G⁻¹ k k ≤ (C : ℂ) := by
  apply Complex.le_def.mpr
  refine ⟨h, ?_⟩
  have hh := (Complex.le_def.mp (hG.inv.posSemidef.diag_nonneg (i := k))).2
  simpa only [Complex.zero_im, Complex.ofReal_im] using hh.symm

theorem gramConjugate_add (H D E : Matrix ι ι ℂ) :
    gramConjugate H (D + E) = gramConjugate H D + gramConjugate H E := by
  simp only [gramConjugate, map_add, add_comp, comp_add]

namespace SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] {L d n : ℕ}
variable (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsFiniteMeasure ρ]

/-- An arbitrary row-coordinate cut inside one original auxiliary column. -/
theorem augmented_partial_column_bound
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (k : Unit ⊕ Fin n) (D : Matrix ι ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hdiag : (a.scalar.rawGram⁻¹ k k).re ≤ 2)
    (hD : ‖gramConjugate (referenceRowGram ρ r) D‖ ≤ K) :
    ‖gramConjugate (a.augmentedRawGram ρ r)
      (selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i)) * D *
        (selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i))).conjTranspose)‖ ≤ Real.sqrt 2 * K := by
  have hΩ : (referenceRowGram ρ r).PosDef := Matrix.posDef_gram_iff_linearIndependent.mpr hr
  exact selected_mask_bound (a.augmentedRawGram_posDef ρ r hr).posSemidef
    hΩ (fun i : ι => (k, i)) D (by norm_num) hK
    (a.augmentedRawGram_column_upper ρ r k)
    (a.augmentedRawGram_inverse_column ρ r hr k (positive_inverse_diagonal_le a.scalar.rawGram_posDef k hdiag)) hD

/-- Complete preceding columns plus a cut inside the next one have the required
additive bound in the actual raw tensor metric. -/
theorem augmented_column_cut_bound
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (hp : a.scalar.AugmentedPrefixSqBound 4)
    (b : ℕ) (k : Unit ⊕ Fin n) (D : Matrix ι ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hdiag : (a.scalar.rawGram⁻¹ k k).re ≤ 2)
    (hD : ‖gramConjugate (referenceRowGram ρ r) D‖ ≤ K) :
    ‖gramConjugate (a.augmentedRawGram ρ r)
      (scalarRowPrefixMatrix n b ⊗ₖ (1 : Matrix ι ι ℂ) +
        selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i)) * D *
          (selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i))).conjTranspose)‖ ≤ 2 + Real.sqrt 2 * K := by
  rw [gramConjugate_add]
  exact (norm_add_le _ _).trans (add_le_add (a.augmented_complete_column_bound ρ r hr hp b)
    (a.augmented_partial_column_bound ρ r hr k D hK hdiag hD))

end SelectiveKernelData
end SchauderTranslates
