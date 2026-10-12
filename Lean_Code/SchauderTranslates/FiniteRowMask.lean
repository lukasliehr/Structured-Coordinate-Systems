import Lean_Code.SchauderTranslates.TensorActivationGram
import Lean_Code.SchauderTranslates.ModeSelection

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι ν K : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Retain whole old rows and selected modes in the current row. -/
def rowMask {𝕜 : Type*} [Zero 𝕜] (old : Finset ι) (j : ι) (s : Finset ν)
    (c : ι × ν → 𝕜) : ι × ν → 𝕜 := fun q =>
  if q.1 ∈ old then c q else if q.1 = j ∧ q.2 ∈ s then c q else 0

/-- The same coordinate cut as a diagonal matrix over either scalar field. -/
def rowMaskMatrix {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (old : Finset ι) (j : ι) (s : Finset ν) :
    Matrix (ι × ν) (ι × ν) 𝕜 :=
  Matrix.diagonal (fun q => if q.1 ∈ old ∨ (q.1 = j ∧ q.2 ∈ s) then 1 else 0)

theorem rowMaskMatrix_apply {𝕜 : Type*} [RCLike 𝕜] (old : Finset ι) (j : ι) (s : Finset ν)
    (c : EuclideanSpace 𝕜 (ι × ν)) :
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι × ν)) (rowMaskMatrix old j s) c =
      WithLp.toLp 2 (rowMask old j s c.ofLp) := by
  ext q
  simp only [rowMaskMatrix, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, rowMask]
  by_cases h1 : q.1 ∈ old <;> by_cases h2 : q.1 = j ∧ q.2 ∈ s <;> simp [h1, h2]

theorem familyCoordinateSelection_finset (old : Finset ι) (f : ι → K) (i : ι) :
    familyCoordinateSelection (fun k : old => (k : ι)) f i = if i ∈ old then f i else 0 := by
  classical
  unfold familyCoordinateSelection
  by_cases hi : i ∈ old
  · rw [if_pos hi]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : old)]
    · simp
    · intro b _ hb
      have hbi : i ≠ (b : ι) := by intro h; exact hb (Subtype.ext h.symm)
      simp [hbi]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    have hbi : i ≠ (b : ι) := by intro h; exact hi (h ▸ b.property)
    simp [hbi]

/-- Restricting the full row cut to a finite coefficient family gives its exact coordinate mask. -/
theorem rowSynthesis_rowMask {u : ν → K} (hu : Orthonormal ℝ u)
    (old : Finset ι) (j : ι) (hj : j ∉ old) (s : Finset ν)
    (c : EuclideanSpace ℝ (ι × ν)) :
    rowSynthesis u (WithLp.toLp 2 (rowMask old j s c.ofLp)) =
      familyRowCut (fun k : old => (k : ι)) j (modeSelectionSpace u s).starProjection (rowSynthesis u c) := by
  ext i
  simp only [familyRowCut, Pi.add_apply, familyCoordinateSelection_finset]
  by_cases hi : i ∈ old
  · have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
    simp [rowSynthesis, rowMask, hi, Pi.single_apply, hij]
  · by_cases hij : i = j
    · subst i
      simp [rowSynthesis, rowMask, hj, modeSelectionSpace_apply hu, smul_ite, ite_smul]
    · simp [rowSynthesis, rowMask, hi, Pi.single_apply, hij]

/-- Every finite real coefficient cut obeys the abstract estimate uniformly in the mode set. -/
theorem finite_tensor_row_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (Q : K →L[ℝ] K) (hQ : ∀ x, Q (Q x) = Q x)
    (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    {u : ν → K} (hu : Orthonormal ℝ u) (old : Finset ι) (j : ι) (hj : j ∉ old)
    (s : Finset ν) (c : EuclideanSpace ℝ (ι × ν)) :
    coefficientQuadratic (tensorActivationGram B Q u)
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι × ν)) (rowMaskMatrix old j s) c) ≤
      metricRowBound B (fun k : old => (k : ι)) j * coefficientQuadratic (tensorActivationGram B Q u) c := by
  have h := real_projection_row_bound hB hBI (fun k : old => (k : ι)) Subtype.val_injective j
    (fun k h => hj (h ▸ k.property)) (modeSelectionSpace u s) Q hQ hQS (rowSynthesis u c)
  rw [← rowSynthesis_rowMask hu old j hj s c, activationEnergy_rowSynthesis,
    activationEnergy_rowSynthesis] at h
  simpa only [rowMaskMatrix_apply] using h

end SchauderTranslates
