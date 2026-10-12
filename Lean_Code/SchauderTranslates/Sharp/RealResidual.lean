import Lean_Code.SchauderTranslates.ProductSetup

/-!
# Real residual coefficients for an even weight

For an even weight all inner products of line characters in the normalized law are real.
The residual of the target is determined by its orthogonality to the old characters
together with the fact that it differs from the target by an old combination. Taking real
parts of the coefficients of any such representation preserves both properties, so the
residual has real character coefficients. No injectivity of the old frequencies is needed.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction

namespace RealResidual

/-- Inversion of the line variable conjugates a character. -/
theorem character_neg_apply (a t : ℝ) : character a (-t) = star (character a t) := by
  rw [LineTransfer.star_character]
  simp only [character]
  congr 1
  push_cast
  ring

/-- For an even weight all inner products of line characters in the normalized law are
real. -/
theorem lineCharacter_inner_im (w : Weight) (hw : ∀ t, w.density (-t) = w.density t)
    (a b : ℝ) :
    (inner ℂ ((lineCharacter a).toL2 (lineLaw w)) ((lineCharacter b).toL2 (lineLaw w))).im =
      0 := by
  rw [BoundedMeasurableComplex.inner_toL2, lineLaw_integral]
  have h : (∫ t, (w.density t : ℂ) * (star (lineCharacter a t) * lineCharacter b t)).im =
      0 := by
    apply integral_real_of_neg_conj
    intro t
    simp only [lineCharacter_apply]
    rw [hw t, character_neg_apply, character_neg_apply]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, h, mul_zero]

end RealResidual

open RealResidual

/-- For an even weight the residual of the target has real character coefficients. -/
theorem residual_exists_real (w : Weight) (hw : ∀ t, w.density (-t) = w.density t)
    {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ) :
    ∃ c : Fin (d + 1) → ℂ, c 0 = 1 ∧ (∀ j, (c j).im = 0) ∧
      (∀ i, inner ℂ ((lineCharacter (μ i)).toL2 (lineLaw w))
        ((lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w)) = 0) ∧
      (lineCharacter ξ).toL2 (lineLaw w) - (lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) ∈
        Submodule.span ℂ (Set.range fun i => (lineCharacter (μ i)).toL2 (lineLaw w)) ∧
      (∫ s, w.density s) * ‖(lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w)‖ ^ 2 =
        distanceSq w μ ξ := by
  obtain ⟨c, hc0, horth, hdiff, hnorm⟩ := residual_exists w μ ξ
  -- the real parts of the coefficients
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (d + 1) → ℂ, ∀ j, c' j = ((c j).re : ℂ) :=
    ⟨fun j => ((c j).re : ℂ), fun _ => rfl⟩
  have hc0' : c' 0 = 1 := by rw [hc', hc0, Complex.one_re, Complex.ofReal_one]
  have him' : ∀ j, (c' j).im = 0 := fun j => by rw [hc', Complex.ofReal_im]
  -- the real combination is still orthogonal to the old characters: the Gram entries are real
  have horth' : ∀ i, inner ℂ ((lineCharacter (μ i)).toL2 (lineLaw w))
      ((lineSum (Fin.cons ξ μ) c').toL2 (lineLaw w)) = 0 := by
    intro i
    have h := horth i
    rw [lineSum_toL2, inner_sum] at h ⊢
    simp only [inner_smul_right] at h ⊢
    have hre := congrArg Complex.re h
    rw [Complex.re_sum, Complex.zero_re] at hre
    apply Complex.ext
    · rw [Complex.re_sum, Complex.zero_re, ← hre]
      apply Finset.sum_congr rfl
      intro j _
      rw [hc', Complex.re_ofReal_mul, Complex.mul_re, lineCharacter_inner_im w hw, mul_zero,
        sub_zero]
    · rw [Complex.im_sum, Complex.zero_im]
      apply Finset.sum_eq_zero
      intro j _
      rw [hc', Complex.im_ofReal_mul, lineCharacter_inner_im w hw, mul_zero]
  -- the target minus the real combination lies in the old span, because `c' 0 = 1`
  have hdiff' : (lineCharacter ξ).toL2 (lineLaw w) -
      (lineSum (Fin.cons ξ μ) c').toL2 (lineLaw w) ∈
        Submodule.span ℂ (Set.range fun i => (lineCharacter (μ i)).toL2 (lineLaw w)) := by
    rw [lineSum_toL2, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hc0', one_smul, sub_add_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  -- the two combinations differ by an element of the old span that is orthogonal to it
  have hmem : (lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) -
      (lineSum (Fin.cons ξ μ) c').toL2 (lineLaw w) ∈
        Submodule.span ℂ (Set.range fun i => (lineCharacter (μ i)).toL2 (lineLaw w)) := by
    have h := Submodule.sub_mem _ hdiff' hdiff
    rwa [sub_sub_sub_cancel_left] at h
  have hzero : ∀ v ∈ Submodule.span ℂ
      (Set.range fun i => (lineCharacter (μ i)).toL2 (lineLaw w)),
      inner ℂ v ((lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) -
        (lineSum (Fin.cons ξ μ) c').toL2 (lineLaw w)) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [inner_sub_right, horth i, horth' i, sub_zero]
    | zero => rw [inner_zero_left]
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have heq : (lineSum (Fin.cons ξ μ) c').toL2 (lineLaw w) =
      (lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) :=
    (sub_eq_zero.mp (inner_self_eq_zero.mp (hzero _ hmem))).symm
  refine ⟨c', hc0', him', horth', hdiff', ?_⟩
  rw [heq]
  exact hnorm

end SchauderTranslates.Sharp
