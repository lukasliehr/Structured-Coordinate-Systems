import Lean_Code.SchauderTranslates.FiniteRowMask
import Lean_Code.SchauderTranslates.ScalarFourierEnergy
import Lean_Code.SchauderTranslates.RealComplexQuadratic
import Lean_Code.SchauderTranslates.CutoffMatrix

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ν : Type*} [Fintype ν] [DecidableEq ν]

@[simp] theorem rowMaskMatrix_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (old : Finset ι) (j : ι) (s : Finset ν) :
    (rowMaskMatrix (𝕜 := ℝ) old j s).map Complex.ofReal = rowMaskMatrix (𝕜 := ℂ) old j s := by
  ext a b
  simp [rowMaskMatrix, Matrix.diagonal, apply_ite Complex.ofReal]

namespace ScalarData
variable {d n : ℕ}

/-- The actual product-weight Fourier Gram for any finite frequency set. -/
def finiteActivatedGram (s : ScalarData d n) (p : ℝ) (freq : ν → ℤ) :
    Matrix ((Unit ⊕ Fin n) × ν) ((Unit ⊕ Fin n) × ν) ℂ :=
  fun a b => s.activatedMoment p a.1 b.1 (freq a.2) (freq b.2)

theorem finiteActivatedGram_tensor (s : ScalarData d n) (hs : s.IsEven) (p : ℝ) (freq : ν → ℤ) :
    s.finiteActivatedGram p freq =
      (tensorActivationGram s.realRawGram
        (lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (μ := AddCircle.haarAddCircle (T := 1))
          (activationSet p) (activationSet_measurable p))
        (fun a => fourierLp (T := 1) 2 (freq a))).map Complex.ofReal := by
  ext a b
  apply Complex.ext
  · exact s.activatedMoment_real_tensor hs p a.1 b.1 (freq a.2) (freq b.2)
  · exact s.activatedMoment_real hs p a.1 b.1 (freq a.2) (freq b.2)

/-- Every actual finite weighted Fourier row cut has the desired quadratic bound for complex coefficients. -/
theorem finiteActivatedGram_prefix (s : ScalarData d n) (hs : s.IsEven) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq)
    (old : Finset (Unit ⊕ Fin n)) (j : Unit ⊕ Fin n) (hj : j ∉ old) (cut : Finset ν)
    (c : EuclideanSpace ℂ ((Unit ⊕ Fin n) × ν)) :
    coefficientQuadratic (s.finiteActivatedGram p freq)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := (Unit ⊕ Fin n) × ν)) (rowMaskMatrix old j cut) c) ≤
      metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j *
        coefficientQuadratic (s.finiteActivatedGram p freq) c := by
  let Q := lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (μ := AddCircle.haarAddCircle (T := 1))
    (activationSet p) (activationSet_measurable p)
  let u := fun a => fourierLp (T := 1) 2 (freq a)
  have hreal := finite_tensor_row_bound s.realRawGram_posDef s.realRawGram_le_one Q
    (lpIndicatorCLM_idempotent (𝕜 := ℝ) _ _) (lpIndicatorCLM_symmetric (𝕜 := ℝ) _ _)
    (circleFourier_real_orthonormal.comp freq hfreq) old j hj cut
  have hc := coefficientQuadratic_bound_complex (tensorActivationGram s.realRawGram Q u)
    (rowMaskMatrix (𝕜 := ℝ) old j cut) _ hreal c
  rw [rowMaskMatrix_complex, ← s.finiteActivatedGram_tensor hs p freq] at hc
  exact hc

/-- Any finite frequency set embeds in a symmetric window, so its actual Gram is positive definite. -/
theorem finiteActivatedGram_posDef (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) (p : ℝ) (freq : ν → ℤ) (hfreq : Function.Injective freq) :
    (s.finiteActivatedGram p freq).PosDef := by
  let N := Finset.univ.sup (fun a => (freq a).natAbs)
  have hN (a : ν) : -(N : ℤ) ≤ freq a ∧ freq a ≤ (N : ℤ) := by
    have hn : (freq a).natAbs ≤ N := Finset.le_sup (f := fun a => (freq a).natAbs) (Finset.mem_univ a)
    have hn' : ((freq a).natAbs : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr hn
    exact ⟨(neg_le_neg hn').trans (by omega), (show freq a ≤ ((freq a).natAbs : ℤ) from Int.le_natAbs).trans hn'⟩
  let e : (Unit ⊕ Fin n) × ν → (Unit ⊕ Fin n) × CircleWindow N :=
    fun q => (q.1, ⟨freq q.2, Finset.mem_Icc.mpr (hN q.2)⟩)
  have he : Function.Injective e := by
    intro a b hab
    apply Prod.ext
    · exact congrArg (fun q : (Unit ⊕ Fin n) × CircleWindow N => q.1) hab
    apply hfreq
    exact congrArg (fun q : (Unit ⊕ Fin n) × CircleWindow N => (q.2 : ℤ)) hab
  have hg : s.finiteActivatedGram p freq = (s.cutoffGram p N).submatrix e e := by
    ext a b
    exact (s.cutoffGram_entry p N (e a) (e b)).symm
  rw [hg]
  exact (s.cutoffGram_posDef hb hfloor p N).submatrix he

/-- This is the actual finite weighted prefix operator norm, with the Hilbert coefficient metric. -/
theorem finiteActivatedGram_prefix_norm (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq)
    (old : Finset (Unit ⊕ Fin n)) (j : Unit ⊕ Fin n) (hj : j ∉ old) (cut : Finset ν) :
    ‖gramConjugate (s.finiteActivatedGram p freq) (rowMaskMatrix old j cut)‖ ^ 2 ≤
      metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j := by
  apply (gramConjugate_quadratic_bound_iff (s.finiteActivatedGram_posDef hb hfloor p freq hfreq) _
    (zero_le_one.trans (metricRowBound_ge_one s.realRawGram_posDef s.realRawGram_le_one _ j
      (fun k h => hj (h ▸ k.property))))).mpr
  exact s.finiteActivatedGram_prefix hs p freq hfreq old j hj cut

end ScalarData
end SchauderTranslates
