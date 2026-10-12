import Lean_Code.SchauderTranslates.TorusFejerKernel

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A finite complex Fourier expansion on the finite torus, with repeated modes collected. -/
def IsTorusPolynomial {d : ℕ} (f : UnitAddTorus (Fin d) → ℂ) : Prop :=
  ∃ (K : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ),
    ∀ x, f x = ∑ k ∈ K, a k * UnitAddTorus.mFourier k x

/-- Any finitely indexed character sum is a polynomial, even when its modes repeat. -/
theorem finiteCharacterSum_isPolynomial {d : ℕ} {ι : Type*} (S : Finset ι)
    (freq : ι → Fin d → ℤ) (a : ι → ℂ) :
    IsTorusPolynomial (fun x => ∑ i ∈ S, a i * UnitAddTorus.mFourier (freq i) x) := by
  classical
  refine ⟨S.image freq, fun k => ∑ i ∈ S with freq i = k, a i, ?_⟩
  intro x
  change (∑ i ∈ S, a i * UnitAddTorus.mFourier (freq i) x) = _
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image freq) (g := freq) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i => a i * UnitAddTorus.mFourier (freq i) x)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Frequencies of a square-modulus expansion, one ordered pair per torus coordinate. -/
def fejerMode {d : ℕ} (v : Fin d → ℕ × ℕ) : Fin d → ℤ :=
  fun i => ((v i).1 : ℤ) - ((v i).2 : ℤ)

def fejerModeIndices (d N : ℕ) : Finset (Fin d → ℕ × ℕ) :=
  Fintype.piFinset (fun _ : Fin d => (Finset.range (N + 1)).product (Finset.range (N + 1)))

/-- An explicit finite character expansion of the product kernel. -/
theorem torusFejerKernel_expansion (d N : ℕ) (x : UnitAddTorus (Fin d)) :
    (torusFejerKernel d N x : ℂ) = (((N + 1 : ℕ) : ℂ)⁻¹) ^ d *
      ∑ v ∈ fejerModeIndices d N, UnitAddTorus.mFourier (fejerMode v) x := by
  simp only [torusFejerKernel, Complex.ofReal_prod, circleFejerKernel_expansion]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  have he (i : Fin d) :
      (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), fourier ((r : ℤ) - s) (x i)) =
        ∑ p ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
          fourier ((p.1 : ℤ) - p.2) (x i) :=
    (Finset.sum_product (Finset.range (N + 1)) (Finset.range (N + 1))
      (fun p : ℕ × ℕ => fourier ((p.1 : ℤ) - (p.2 : ℤ)) (x i))).symm
  simp_rw [he]
  rw [Finset.prod_univ_sum]
  rfl

theorem torusFejerKernel_isPolynomial (d N : ℕ) :
    IsTorusPolynomial (fun x => (torusFejerKernel d N x : ℂ)) := by
  have h := finiteCharacterSum_isPolynomial (fejerModeIndices d N) fejerMode
    (fun _ => (((N + 1 : ℕ) : ℂ)⁻¹) ^ d)
  have he : (fun x : UnitAddTorus (Fin d) => (torusFejerKernel d N x : ℂ)) =
      (fun x => ∑ v ∈ fejerModeIndices d N,
        (((N + 1 : ℕ) : ℂ)⁻¹) ^ d * UnitAddTorus.mFourier (fejerMode v) x) := by
    funext x
    rw [torusFejerKernel_expansion, Finset.mul_sum]
  rw [he]
  exact h

theorem IsTorusPolynomial.continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℂ}
    (hf : IsTorusPolynomial f) : Continuous f := by
  obtain ⟨K, a, h⟩ := hf
  have he : f = fun x => ∑ k ∈ K, a k * UnitAddTorus.mFourier k x := funext h
  rw [he]
  fun_prop

end SchauderTranslates
