import Lean_Code.SchauderTranslates.PacketReferenceGram
import Lean_Code.SchauderTranslates.SelectiveCompleteColumns

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Carrier rows first in their original order, then the independent seed rows. -/
def packetRowRank {r L : ℕ} : Fin r ⊕ Fin L → ℕ :=
  Sum.elim (fun i => i.val) (fun j => r + j.val)

def packetRowPrefixMatrix (r L k : ℕ) : Matrix (Fin r ⊕ Fin L) (Fin r ⊕ Fin L) ℂ :=
  Matrix.fromBlocks (finitePrefixMatrix r k) 0 0 (finitePrefixMatrix L (k - r))

theorem packetRowPrefixMatrix_diagonal (r L k : ℕ) :
    packetRowPrefixMatrix r L k = Matrix.diagonal
      (fun i => if packetRowRank i < k then (1 : ℂ) else 0) := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => simp [packetRowPrefixMatrix, finitePrefixMatrix, packetRowRank, Matrix.diagonal_apply]
    | inr j => simp [packetRowPrefixMatrix, Matrix.diagonal_apply]
  | inr i => cases j with
    | inl j => simp [packetRowPrefixMatrix, Matrix.diagonal_apply]
    | inr j =>
      have hi : i.val < k - r ↔ r + i.val < k := by omega
      simp [packetRowPrefixMatrix, finitePrefixMatrix, packetRowRank, Matrix.diagonal_apply, hi]

theorem posSemidef_block_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  classical
  have h := (posSemidef_zero_padding (κ := κ) hA).add (posSemidef_zero_padding_right (κ := ι) hB)
  convert h using 1
  ext (i | i) (j | j) <;> simp

theorem gramDifference_block_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ℝ) (D A : Matrix ι ι ℂ) (E B : Matrix κ κ ℂ) :
    gramDifference C (Matrix.fromBlocks D 0 0 E) (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (gramDifference C D A) 0 0 (gramDifference C E B) := by
  simp only [gramDifference, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  ext (i | i) (j | j) <;> simp [Matrix.smul_apply]

namespace SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- The actual reference row prefix has constant `max K 1`: the original
carrier contributes `K` and the orthonormal seed tail contributes one. -/
theorem packetRows_prefix_bound {r L : ℕ} (φ : Fin r → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ)) {K : ℝ} (hK : 0 ≤ K)
    (hp : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2)) (k : ℕ) :
    ‖gramConjugate (referenceRowGram ρ (packetRows (L := L) φ))
      (packetRowPrefixMatrix r L k)‖ ≤ max K 1 := by
  let N := max K 1
  have hN : 1 ≤ N := le_max_right _ _
  have hNK : K ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNN : 1 ≤ N ^ 2 := by nlinarith
  have hKK : K ^ 2 ≤ N ^ 2 := by nlinarith
  have hrow := (finitePrefixSqBound_iff_gram _ hφ (sq_nonneg N)).mp (hp.mono hKK) k
  have hA := (gram_prefix_iff (Matrix.posDef_gram_iff_linearIndependent.mpr hφ)
    (finitePrefixMatrix r k) N).mp hrow
  have hB : (gramDifference (N ^ 2) (finitePrefixMatrix L (k - r)) 1).PosSemidef :=
    diagonalMask_identity_difference (fun i : Fin L => i.val < k - r) hNN
  have hblock := posSemidef_block_diagonal hA hB
  rw [← gramDifference_block_diagonal] at hblock
  have hΩ : (referenceRowGram ρ (packetRows (L := L) φ)).PosDef :=
    Matrix.posDef_gram_iff_linearIndependent.mpr (packetRows_independent ρ φ hφ)
  have hh : (gramDifference (N ^ 2) (packetRowPrefixMatrix r L k)
      (referenceRowGram ρ (packetRows (L := L) φ))).PosSemidef := by
    rw [packetRows_reference_gram]
    exact hblock
  have hn := (gram_prefix_iff hΩ (packetRowPrefixMatrix r L k) N).mpr hh
  change ‖gramConjugate (referenceRowGram ρ (packetRows (L := L) φ)) (packetRowPrefixMatrix r L k)‖ ≤ N
  nlinarith [norm_nonneg (gramConjugate (referenceRowGram ρ (packetRows (L := L) φ)) (packetRowPrefixMatrix r L k))]

end SelectiveKernelData
end SchauderTranslates
