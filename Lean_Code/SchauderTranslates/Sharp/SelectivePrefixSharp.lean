import Lean_Code.SchauderTranslates.SelectivePrefixes
import Lean_Code.SchauderTranslates.Sharp.ProjectionSum

/-!
# The sharp selective prefix estimate (paper: `h2:eq:selective-bound`)

Every centered prefix of the selective packet, in the actual column-major character order,
has squared norm at most
`1 + (√(K_s² − 1) + √(C · max(K_V, 1)² − 1))²`,
where `K_s ≥ 1` is the augmented prefix constant of the auxiliary scalar block, `C ≥ 1`
bounds its nonconstant raw inverse diagonal (`C = 1 + 2ε` in the paper) and `K_V` is the
prefix constant of the carrier rows.

A relevant prefix retains complete auxiliary columns (norm `≤ K_s`) and a row cut inside a
nonconstant column (norm `≤ √C · max(K_V, 1)`). Both, and their sum, are coordinate masks,
hence idempotents in the Gram metric; the identity `max 1 ‖Q‖² = 1 + ‖Q − Q†‖²` and the
triangle inequality for the skew parts give the bound. Cuts inside the auxiliary constant
column are never needed.
-/

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder MatrixOrder Kronecker InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates

/-- The sharp squared prefix constant `1 + (√(A − 1) + √(B − 1))²`. -/
def selectivePrefixSqSharp (A B : ℝ) : ℝ :=
  1 + (Real.sqrt (A - 1) + Real.sqrt (B - 1)) ^ 2

theorem one_le_selectivePrefixSqSharp (A B : ℝ) : 1 ≤ selectivePrefixSqSharp A B :=
  le_add_of_nonneg_right (sq_nonneg _)

/-- A diagonal matrix with idempotent entries is idempotent. -/
theorem diagonal_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι] (δ : ι → ℂ)
    (h : ∀ i, δ i * δ i = δ i) : Matrix.diagonal δ * Matrix.diagonal δ = Matrix.diagonal δ := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact h i

section Columns
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {L d n : ℕ} (a : SelectiveKernelData S L d n)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- Complete auxiliary columns: the scalar augmented prefix constant, for any `K_s ≥ 1`. -/
theorem augmented_complete_column_sq_le
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    {Ks : ℝ} (hKs : 1 ≤ Ks) (hp : a.scalar.AugmentedPrefixSqBound (Ks ^ 2)) (k : ℕ) :
    ‖gramConjugate (a.augmentedRawGram ρ r)
      (scalarRowPrefixMatrix n k ⊗ₖ (1 : Matrix ι ι ℂ))‖ ^ 2 ≤ Ks ^ 2 := by
  have haux : (gramDifference (Ks ^ 2) (scalarRowPrefixMatrix n k) a.scalar.rawGram).PosSemidef := by
    apply (gram_prefix_iff a.scalar.rawGram_posDef _ Ks).mp
    exact (a.scalar.augmentedPrefixSqBound_iff_gram (sq_nonneg Ks)).mp hp k
  have hid : (gramDifference (Ks ^ 2) (scalarRowPrefixMatrix n k) 1).PosSemidef :=
    diagonalMask_identity_difference (fun i => (scalarRowEquiv n i).val < k) (by nlinarith)
  have hb := a.rawSeedGram_order ρ r
  have h := mixedTensorGram_complete_column_bound haux hid hb.1 hb.2
  exact (gram_prefix_iff (a.augmentedRawGram_posDef ρ r hr)
    (scalarRowPrefixMatrix n k ⊗ₖ (1 : Matrix ι ι ℂ)) Ks).mpr h

/-- A row cut inside one auxiliary column, with an arbitrary inverse diagonal bound. -/
theorem augmented_partial_column_sq_le
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (k : Unit ⊕ Fin n) (D : Matrix ι ι ℂ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hdiag : (a.scalar.rawGram⁻¹ k k).re ≤ C)
    (hD : ‖gramConjugate (SelectiveKernelData.referenceRowGram ρ r) D‖ ≤ K) :
    ‖gramConjugate (a.augmentedRawGram ρ r)
      (selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i)) * D *
        (selectionColumns (𝕜 := ℂ) (fun i : ι => (k, i))).conjTranspose)‖ ^ 2 ≤ C * K ^ 2 := by
  have hΩ : (SelectiveKernelData.referenceRowGram ρ r).PosDef :=
    Matrix.posDef_gram_iff_linearIndependent.mpr hr
  have h := selected_mask_bound (a.augmentedRawGram_posDef ρ r hr).posSemidef
    hΩ (fun i : ι => (k, i)) D hC hK
    (a.augmentedRawGram_column_upper ρ r k)
    (a.augmentedRawGram_inverse_column ρ r hr k
      (positive_inverse_diagonal_le a.scalar.rawGram_posDef k hdiag)) hD
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, Real.sq_sqrt hC] at h2
  exact h2

end Columns

section Ordered
variable {S : Type*} [MeasurableSpace S] {L d n r : ℕ}
variable (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
variable (φ : Fin r → BoundedMeasurableComplex S)

theorem augmentedPacketPrefixMatrix_idempotent (t : ℕ) :
    augmentedPacketPrefixMatrix n r L t * augmentedPacketPrefixMatrix n r L t =
      augmentedPacketPrefixMatrix n r L t := by
  unfold augmentedPacketPrefixMatrix
  exact diagonal_mask_mul_self _

theorem scalarRowPrefix_kronecker_idempotent (b : ℕ) :
    (scalarRowPrefixMatrix n b ⊗ₖ (1 : Matrix (Fin r ⊕ Fin L) (Fin r ⊕ Fin L) ℂ)) *
        (scalarRowPrefixMatrix n b ⊗ₖ (1 : Matrix (Fin r ⊕ Fin L) (Fin r ⊕ Fin L) ℂ)) =
      scalarRowPrefixMatrix n b ⊗ₖ (1 : Matrix (Fin r ⊕ Fin L) (Fin r ⊕ Fin L) ℂ) := by
  rw [scalarRowPrefixMatrix, diagonal_kronecker_identity]
  apply diagonal_idempotent
  intro p
  split_ifs <;> norm_num

theorem selectedRowPrefix_idempotent (k : Unit ⊕ Fin n) (s : ℕ) :
    (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i)) *
          packetRowPrefixMatrix r L s *
          (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i))).conjTranspose) *
        (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i)) *
          packetRowPrefixMatrix r L s *
          (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i))).conjTranspose) =
      selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i)) *
          packetRowPrefixMatrix r L s *
          (selectionColumns (𝕜 := ℂ) (fun i : Fin r ⊕ Fin L => (k, i))).conjTranspose := by
  rw [packetRowPrefixMatrix_diagonal, selected_column_diagonal]
  apply diagonal_idempotent
  intro p
  split_ifs <;> norm_num

variable (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
variable {K Ks C : ℝ} (hK : 0 ≤ K)
variable (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
variable (hKs : 1 ≤ Ks) (haux : a.scalar.AugmentedPrefixSqBound (Ks ^ 2))
variable (hC : 1 ≤ C)
variable (hdiag : ∀ k : Fin n, (a.scalar.rawGram⁻¹ (Sum.inr k) (Sum.inr k)).re ≤ C)
include hφ hK hrow hKs haux hC hdiag

/-- Every augmented prefix retaining the whole auxiliary constant column has the sharp
squared norm bound, in the original carrier coordinates. -/
theorem augmented_ordered_prefix_sq_le (t : ℕ) (ht : r + L ≤ t) :
    ‖gramConjugate (a.augmentedRawGram ρ (SelectiveKernelData.packetRows φ))
      (augmentedPacketPrefixMatrix n r L t)‖ ^ 2 ≤
      selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) := by
  have hrows := SelectiveKernelData.packetRows_independent (L := L) ρ φ hφ
  have hH := a.augmentedRawGram_posDef ρ (SelectiveKernelData.packetRows φ) hrows
  have hKm : 1 ≤ max K 1 := le_max_right _ _
  have hA : 1 ≤ Ks ^ 2 := by nlinarith
  have hB : 1 ≤ C * max K 1 ^ 2 := by nlinarith
  by_cases htl : t < (n + 1) * (r + L)
  · have hw : 0 < r + L := by
      rcases Nat.eq_zero_or_pos (r + L) with h0 | h0
      · rw [h0] at htl; simp at htl
      · exact h0
    have hb1 : 1 ≤ t / (r + L) := (Nat.one_le_div_iff hw).mpr ht
    have hblt : t / (r + L) < n + 1 := (Nat.div_lt_iff_lt_mul hw).mpr htl
    -- the partially retained column is nonconstant
    obtain ⟨i, hi⟩ : ∃ i : Fin n,
        (scalarRowEquiv n).symm ⟨t / (r + L), hblt⟩ = Sum.inr i := by
      rcases hk : (scalarRowEquiv n).symm ⟨t / (r + L), hblt⟩ with u | i
      · exfalso
        have h1 := congrArg (scalarRowEquiv n) hk
        rw [Equiv.apply_symm_apply] at h1
        have h2 := congrArg Fin.val h1
        cases u
        simp only [scalarRowEquiv_constant, Fin.val_zero] at h2
        omega
      · exact ⟨i, rfl⟩
    have hsplit := augmentedPacketPrefixMatrix_split (n := n) (r := r) (L := L) htl
    dsimp only at hsplit
    rw [hi] at hsplit
    have h12 := augmentedPacketPrefixMatrix_idempotent (n := n) (r := r) (L := L) t
    rw [hsplit] at h12 ⊢
    refine gramConjugate_mask_sum_sq_le hH (scalarRowPrefix_kronecker_idempotent _)
      (selectedRowPrefix_idempotent _ _) h12 hA hB ?_ ?_
    · exact augmented_complete_column_sq_le a ρ (SelectiveKernelData.packetRows φ) hrows hKs
        haux _
    · exact augmented_partial_column_sq_le a ρ (SelectiveKernelData.packetRows φ) hrows
        (Sum.inr i) _ (zero_le_one.trans hKm) (zero_le_one.trans hC) (hdiag i)
        (SelectiveKernelData.packetRows_prefix_bound ρ φ hφ hK hrow _)
  · rw [augmentedPacketPrefixMatrix_all (Nat.le_of_not_gt htl)]
    exact (gramConjugate_one_sq_le hH (le_refl (1 : ℝ))).trans
      (one_le_selectivePrefixSqSharp _ _)

/-- Prefix control for the actual normalized weighted vectors. -/
theorem augmented_ordered_synthesis_sq_le (t : ℕ) (ht : r + L ≤ t)
    (c : (Unit ⊕ Fin n) × (Fin r ⊕ Fin L) → ℂ) :
    ‖finiteSynthesis (a.kernel.atoms ρ (a.augmentedRowColumn (SelectiveKernelData.packetRows φ)))
        (fun p => if augmentedPacketRank p < t then c p else 0)‖ ^ 2 ≤
      selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) *
        ‖finiteSynthesis (a.kernel.atoms ρ
          (a.augmentedRowColumn (SelectiveKernelData.packetRows φ))) c‖ ^ 2 := by
  set u := a.kernel.atoms ρ (a.augmentedRowColumn (SelectiveKernelData.packetRows φ)) with hu
  set H := a.augmentedRawGram ρ (SelectiveKernelData.packetRows φ) with hHdef
  set Q := selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) with hQ
  have hQ1 : 1 ≤ Q := one_le_selectivePrefixSqSharp _ _
  have hH : H.PosDef := a.augmentedRawGram_posDef ρ (SelectiveKernelData.packetRows φ)
    (SelectiveKernelData.packetRows_independent ρ φ hφ)
  have hgram : Matrix.gram ℂ u = (a.mass : ℂ)⁻¹ • H :=
    a.augmentedRowColumn_gram ρ (SelectiveKernelData.packetRows φ)
  have hb2 := augmented_ordered_prefix_sq_le a ρ φ hφ hK hrow hKs haux hC hdiag t ht
  have hb : ‖gramConjugate H (augmentedPacketPrefixMatrix n r L t)‖ ≤ Real.sqrt Q :=
    Real.le_sqrt_of_sq_le hb2
  have hg : Matrix.gram ℂ u = ((a.mass⁻¹ : ℝ) : ℂ) • H := by
    simpa only [Complex.ofReal_inv] using hgram
  have hz := scaled_gram_synthesis_bound u hH a.mass⁻¹ (inv_pos.mpr a.mass_positive)
    hg (augmentedPacketPrefixMatrix n r L t) (Real.sqrt Q) hb c
  have hm : augmentedPacketPrefixMatrix n r L t *ᵥ c =
      (fun p => if augmentedPacketRank p < t then c p else 0) := by
    ext p
    simp [augmentedPacketPrefixMatrix, Matrix.mulVec_diagonal]
  rw [hm, Real.sq_sqrt (zero_le_one.trans hQ1)] at hz
  exact hz

/-- Zero extension deletes precisely the seed entries in the auxiliary constant column;
the full initial carrier is retained by every subsequent prefix. -/
theorem extended_packet_synthesis_sq_le (t : ℕ) (b : Fin r → ℂ)
    (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    ‖finiteSynthesis (a.initialCarrier ρ φ) b +
      finiteSynthesis (a.kernel.atoms ρ (a.packet φ))
        (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) *
        ‖finiteSynthesis (a.initialCarrier ρ φ) b +
          finiteSynthesis (a.kernel.atoms ρ (a.packet φ)) c‖ ^ 2 := by
  have h := augmented_ordered_synthesis_sq_le a ρ φ hφ hK hrow hKs haux hC hdiag
    ((r + L) + t) (Nat.le_add_right _ _) (extendPacketCoefficients b c)
  rw [extendPacketCoefficients_prefix, a.synthesis_extended_packet,
    a.synthesis_extended_packet] at h
  exact h

/-- Every centered column-major prefix of the unchanged original atom list. -/
theorem centered_packet_synthesis_sq_le
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    (t : ℕ) (c : Fin n × (Fin r ⊕ Fin L) → ℂ) :
    ‖finiteSynthesis (a.kernel.centered ρ (a.packet φ))
        (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) *
        ‖finiteSynthesis (a.kernel.centered ρ (a.packet φ)) c‖ ^ 2 := by
  set Q := selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2) with hQ
  have hQ1 : 1 ≤ Q := one_le_selectivePrefixSqSharp _ _
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt (zero_le_one.trans hQ1)
  have h := centered_extension_bound (a.initialCarrier ρ φ)
    (a.kernel.atoms ρ (a.packet φ)) (a.kernel.means ρ (a.packet φ))
    (a.packet_means_mem_initial ρ φ he) (a.packet_centered_mem_initial_orthogonal ρ φ)
    (fun p => if packetRank p < t then (1 : ℂ) else 0) (Real.sqrt Q) ?_ c
  · rw [hsq] at h
    change ‖finiteSynthesis (fun i => a.kernel.atoms ρ (a.packet φ) i -
        a.kernel.means ρ (a.packet φ) i) (fun p => if packetRank p < t then c p else 0)‖ ^ 2 ≤
      Q * ‖finiteSynthesis (fun i => a.kernel.atoms ρ (a.packet φ) i -
        a.kernel.means ρ (a.packet φ) i) c‖ ^ 2
    have hm : (fun p => (if packetRank p < t then (1 : ℂ) else 0) * c p) =
        (fun p => if packetRank p < t then c p else 0) := by
      funext p
      simp only [ite_mul, one_mul, zero_mul]
    rw [hm] at h
    exact h
  · intro b c
    rw [hsq]
    simpa only [ite_mul, one_mul, zero_mul] using
      extended_packet_synthesis_sq_le a ρ φ hφ hK hrow hKs haux hC hdiag t b c

end Ordered

/-- Paper `h2:eq:selective-bound` (sharp version of blueprint `select:prefix`): every ordered
centered prefix of the selective packet has squared norm at most
`1 + (√(K_s² − 1) + √(C · max(K, 1)² − 1))²`. -/
theorem selective_centered_prefix_sharp {S : Type*} [MeasurableSpace S] {L d n r : ℕ}
    (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (φ : Fin r → BoundedMeasurableComplex S)
    (hφ : LinearIndependent ℂ (fun i => (φ i).toL2 ρ))
    (he : a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ))
    {K Ks C : ℝ} (hK : 0 ≤ K) (hrow : FinitePrefixSqBound (fun i => (φ i).toL2 ρ) (K ^ 2))
    (hKs : 1 ≤ Ks) (haux : a.scalar.AugmentedPrefixSqBound (Ks ^ 2))
    (hC : 1 ≤ C)
    (hdiag : ∀ k : Fin n, (a.scalar.rawGram⁻¹ (Sum.inr k) (Sum.inr k)).re ≤ C) :
    FinitePrefixSqBound (a.orderedCenteredPacket ρ φ)
      (selectivePrefixSqSharp (Ks ^ 2) (C * max K 1 ^ 2)) := by
  apply finitePrefixSqBound_of_rank (packetEquiv n r L)
  intro t c
  simpa only [packetEquiv_val] using
    centered_packet_synthesis_sq_le a ρ φ hφ hK hrow hKs haux hC hdiag he t c

end SchauderTranslates.Sharp
