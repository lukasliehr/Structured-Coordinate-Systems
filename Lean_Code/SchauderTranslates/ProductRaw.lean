import Lean_Code.SchauderTranslates.ProductPoly
import Lean_Code.SchauderTranslates.MatrixInverseOrder

/-!
# Raw product Gram matrices of the finite extension

The raw product Gram and source of the ordered atoms on the flat torus are the total
mass `(∫ w) M` times the actual L² Gram and source in the normalized combined law. The
model conclusions therefore give the strict matrix conditions of `ProductExtension`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

theorem gramCapture_ofReal_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ}
    (hG : G.PosDef) {c : ℝ} (hc : 0 < c) (v : ι → ℂ) :
    gramCapture ((c : ℂ) • G) ((c : ℂ) • v) = c * gramCapture G v := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let : Invertible (c : ℂ) := (isUnit_iff_ne_zero.mpr hcC).invertible
  rw [gramCapture, Matrix.inv_smul G (c : ℂ) ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)]
  have h1 : (⅟(c : ℂ) • G⁻¹) *ᵥ ((c : ℂ) • v) = G⁻¹ *ᵥ v := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, invOf_mul_self, one_smul]
  have h2 : star ((c : ℂ) • v) = (c : ℂ) • star v := by
    rw [star_smul, Complex.star_def, Complex.conj_ofReal]
  rw [h1, h2, smul_dotProduct, smul_eq_mul, Complex.re_ofReal_mul]
  rfl

namespace EngineSetup
variable {T : TagSetup} {E : EngineSetup T}

theorem atomFn_measurable_pt (a : Fin (T.d + T.N * E.n * E.q)) (t : ℝ) :
    Measurable (fun y : E.Fast => E.atomFn a (E.pt t y)) :=
  (E.atomFn a).measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

/-- The raw product Gram is total mass times the actual Gram. -/
theorem productGram_eq :
    productGram T.w E.Wflat E.Λ E.κ =
      (((∫ s, T.w.density s) * E.M : ℝ) : ℂ) • Matrix.gram ℂ E.u := by
  ext a b
  simp only [productGram, Matrix.of_apply, Matrix.smul_apply, Matrix.gram_apply, smul_eq_mul]
  rw [← atomFn_toL2 a, ← atomFn_toL2 b, BoundedMeasurableComplex.inner_toL2]
  have hG := raw_integral (E := E) ((E.atomFn a).conjugate.mul (E.atomFn b))
  refine Eq.trans ?_ (hG.trans rfl)
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  have hflat := integral_fastFlat (𝕜 := ℂ) (fun y : E.Fast => (E.Wraw t y : ℂ) *
      ((E.atomFn a).conjugate.mul (E.atomFn b)) (E.pt t y))
    ((((Complex.continuous_ofReal.measurable.comp
      (Wraw_measurable.comp (measurable_const.prodMk measurable_id)))).mul
      (((E.atomFn a).conjugate.mul (E.atomFn b)).measurable.comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)
  rw [← hflat]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← atomFn_flat a t x, ← atomFn_flat b t x]
  rfl

/-- The raw product source is total mass times the actual source moments. -/
theorem productSource_eq :
    productSource T.w E.Wflat E.Λ E.κ T.ξ =
      (((∫ s, T.w.density s) * E.M : ℝ) : ℂ) • sourceMoments E.u E.tgt := by
  ext a
  simp only [productSource, Pi.smul_apply, sourceMoments, smul_eq_mul]
  rw [← atomFn_toL2 a, ← tgtFn_toL2, BoundedMeasurableComplex.inner_toL2]
  have hG := raw_integral (E := E) ((E.atomFn a).conjugate.mul E.tgtFn)
  refine Eq.trans ?_ (hG.trans rfl)
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  have hflat := integral_fastFlat (𝕜 := ℂ) (fun y : E.Fast => (E.Wraw t y : ℂ) *
      ((E.atomFn a).conjugate.mul E.tgtFn) (E.pt t y))
    ((((Complex.continuous_ofReal.measurable.comp
      (Wraw_measurable.comp (measurable_const.prodMk measurable_id)))).mul
      (((E.atomFn a).conjugate.mul E.tgtFn).measurable.comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)
  rw [← hflat]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← atomFn_flat a t x]
  rfl

/-- Strict prefix conditions for the raw Gram from a prefix bound with margin. -/
theorem prefix_posDef {Q K' : ℝ} (hind : LinearIndependent ℂ E.u)
    (hpre : FinitePrefixSqBound E.u Q) (hQ : Q < K' ^ 2) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    (prefixGramDifference K' (cutMatrix j) ((c : ℂ) • Matrix.gram ℂ E.u)).PosDef := by
  have hsmul : prefixGramDifference K' (cutMatrix j) ((c : ℂ) • Matrix.gram ℂ E.u) =
      (c : ℂ) • prefixGramDifference K' (cutMatrix j) (Matrix.gram ℂ E.u) := by
    simp only [prefixGramDifference, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [smul_comm]
  rw [hsmul]
  have hcC : (0 : ℂ) < (c : ℂ) := by exact_mod_cast hc
  apply Matrix.PosDef.smul _ hcC
  apply (prefixGramDifference_posDef_iff K' (cutMatrix j) (Matrix.isHermitian_gram ℂ E.u)).mpr
  intro x hx
  have hfull := synthesis_norm_sq E.u x
  have hcut := synthesis_norm_sq E.u ((cutMatrix j : Matrix _ _ ℂ).toEuclideanLin x)
  rw [← hfull, ← hcut]
  have hx' : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  rw [hx', LineTransfer.cutMatrix_toEuclideanLin]
  simp only [WithLp.ofLp_toLp, finiteSynthesis]
  have hp := hpre j (WithLp.ofLp x)
  have hsum : (∑ i, if i.val < j then WithLp.ofLp x i • E.u i else 0) =
      ∑ i, (if i.val < j then WithLp.ofLp x i else 0) • E.u i := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hsum] at hp
  have hpos : 0 < ‖∑ i, WithLp.ofLp x i • E.u i‖ ^ 2 := by
    have hne : ∑ i, WithLp.ofLp x i • E.u i ≠ 0 := by
      intro h0
      apply hx
      have h1 := Fintype.linearIndependent_iff.mp hind (WithLp.ofLp x) h0
      ext i
      exact h1 i
    positivity
  calc _ ≤ Q * ‖∑ i, WithLp.ofLp x i • E.u i‖ ^ 2 := hp
    _ < K' ^ 2 * ‖∑ i, WithLp.ofLp x i • E.u i‖ ^ 2 := mul_lt_mul_of_pos_right hQ hpos

/-- The raw residual error from the model's explicit approximant. -/
theorem raw_error_le (hind : LinearIndependent ℂ E.u) {b : Fin (T.d + T.N * E.n * E.q) → ℂ}
    {ε : ℝ} (hb : ‖E.tgt - ∑ k, b k • E.u k‖ ^ 2 ≤ ε) :
    E.M * (∫ s, T.w.density s) -
        gramCapture (productGram T.w E.Wflat E.Λ E.κ) (productSource T.w E.Wflat E.Λ E.κ T.ξ) ≤
      ((∫ s, T.w.density s) * E.M) * ε := by
  have hZ := weight_integral_pos T.w
  have hM := M_pos (E := E)
  have hc : 0 < (∫ s, T.w.density s) * E.M := mul_pos hZ hM
  rw [productGram_eq, productSource_eq,
    gramCapture_ofReal_smul (Matrix.posDef_gram_iff_linearIndependent.mpr hind) hc]
  have herr := gram_projection_error E.u hind E.tgt
  have hmin := gramProjection_minimal E.u hind E.tgt b
  rw [herr, tgt_norm] at hmin
  have hle : 1 - gramCapture (Matrix.gram ℂ E.u) (sourceMoments E.u E.tgt) ≤ ε := by
    have := hmin.trans hb
    simpa [finiteSynthesis] using this
  nlinarith

end EngineSetup
end SchauderTranslates
