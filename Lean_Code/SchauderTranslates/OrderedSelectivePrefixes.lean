import Lean_Code.SchauderTranslates.ColumnPrefixMasks
import Lean_Code.SchauderTranslates.ScaledSynthesis

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Column-major enumeration, with the auxiliary constant column first. -/
def augmentedPacketEquiv (n r L : ℕ) :
    (Unit ⊕ Fin n) × (Fin r ⊕ Fin L) ≃ Fin ((n + 1) * (r + L)) :=
  (Equiv.prodCongr (scalarRowEquiv n) (packetRowEquiv r L)).trans finProdFinEquiv

@[simp] theorem augmentedPacketEquiv_val {n r L : ℕ}
    (p : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) :
    (augmentedPacketEquiv n r L p).val = augmentedPacketRank p := by
  rcases p with ⟨k, i | j⟩ <;>
    simp [augmentedPacketEquiv, augmentedPacketRank, packetRowEquiv, packetRowRank,
      finProdFinEquiv, finSumFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem augmentedPacketRank_lt {n r L : ℕ} (p : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) :
    augmentedPacketRank p < (n + 1) * (r + L) := by
  simpa only [augmentedPacketEquiv_val] using (augmentedPacketEquiv n r L p).isLt

theorem augmentedPacketPrefixMatrix_all {n r L t : ℕ} (ht : (n + 1) * (r + L) ≤ t) :
    augmentedPacketPrefixMatrix n r L t = 1 := by
  have h (p : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L)) : augmentedPacketRank p < t :=
    (augmentedPacketRank_lt p).trans_le ht
  simp [augmentedPacketPrefixMatrix, h]

def selectivePrefixConstant (K : ℝ) : ℝ := 2 + Real.sqrt 2 * max K 1

theorem selectivePrefixConstant_nonneg (K : ℝ) : 0 ≤ selectivePrefixConstant K := by
  have hm : 0 ≤ max K 1 := zero_le_one.trans (le_max_right _ _)
  unfold selectivePrefixConstant
  positivity

theorem selectivePrefixConstant_ge_two (K : ℝ) : 2 ≤ selectivePrefixConstant K := by
  have hm : 0 ≤ max K 1 := zero_le_one.trans (le_max_right _ _)
  exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) hm)

namespace SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] {L d n r : ℕ}
variable (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
variable (φ : Fin r → BoundedMeasurableComplex S)
variable (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
variable {K : ℝ} (hK : 0 ≤ K) (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
variable (haux : a.scalar.AugmentedPrefixSqBound 4)
variable (hdiag : ∀ k, (a.scalar.rawGram⁻¹ k k).re ≤ 2)
include hφ hK hrow haux hdiag

/-- Every augmented prefix, including endpoint and inside-column cuts, has the
paper's constant in the original carrier coordinates. -/
theorem augmented_ordered_prefix_bound (t : ℕ) :
    ‖gramConjugate (a.augmentedRawGram ρ (packetRows φ))
      (augmentedPacketPrefixMatrix n r L t)‖ ≤ selectivePrefixConstant K := by
  have hrows := packetRows_independent (L := L) ρ φ hφ
  by_cases ht : t < (n + 1) * (r + L)
  · rw [augmentedPacketPrefixMatrix_split ht]
    apply a.augmented_column_cut_bound ρ (packetRows φ) hrows haux
      (t / (r + L)) _ (packetRowPrefixMatrix r L (t % (r + L)))
      (zero_le_one.trans (le_max_right K 1)) (hdiag _)
    exact packetRows_prefix_bound ρ φ hφ hK hrow _
  · rw [augmentedPacketPrefixMatrix_all (Nat.le_of_not_gt ht)]
    have hh := gramConjugate_one_sq_le (a.augmentedRawGram_posDef ρ (packetRows φ) hrows)
      (le_refl (1 : ℝ))
    have hn : ‖gramConjugate (a.augmentedRawGram ρ (packetRows φ)) 1‖ ≤ 1 := by
      nlinarith [norm_nonneg (gramConjugate (a.augmentedRawGram ρ (packetRows φ)) 1)]
    exact hn.trans ((by norm_num : (1 : ℝ) ≤ 2).trans (selectivePrefixConstant_ge_two K))

/-- Prefix control for actual normalized weighted vectors, with the common mass
factor canceled through the proved positive Gram rescaling lemma. -/
theorem augmented_ordered_synthesis_bound (t : ℕ)
    (c : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L) → ℂ) :
    let u := a.kernel.atoms ρ (a.augmentedRowColumn (packetRows φ))
    ‖finiteSynthesis u (fun p => if augmentedPacketRank p < t then c p else 0)‖ ^ 2 ≤
      (selectivePrefixConstant K) ^ 2 * ‖finiteSynthesis u c‖ ^ 2 := by
  let u := a.kernel.atoms ρ (a.augmentedRowColumn (packetRows φ))
  let H := a.augmentedRawGram ρ (packetRows φ)
  have hH : H.PosDef := a.augmentedRawGram_posDef ρ (packetRows φ) (packetRows_independent ρ φ hφ)
  have hgram : Matrix.gram ℂ u = (a.mass : ℂ)⁻¹ • H := a.augmentedRowColumn_gram ρ (packetRows φ)
  have hb := a.augmented_ordered_prefix_bound ρ φ hφ hK hrow haux hdiag t
  have hg : Matrix.gram ℂ u = ((a.mass⁻¹ : ℝ) : ℂ) • H := by
    simpa only [Complex.ofReal_inv] using hgram
  have hz := scaled_gram_synthesis_bound u hH a.mass⁻¹ (inv_pos.mpr a.mass_positive)
    hg (augmentedPacketPrefixMatrix n r L t) (selectivePrefixConstant K) hb c

  have hm : augmentedPacketPrefixMatrix n r L t *ᵥ c =
      (fun p => if augmentedPacketRank p < t then c p else 0) := by
    ext p
    simp [augmentedPacketPrefixMatrix, Matrix.mulVec_diagonal]
  rw [hm] at hz
  exact hz

end SelectiveKernelData
end SchauderTranslates
