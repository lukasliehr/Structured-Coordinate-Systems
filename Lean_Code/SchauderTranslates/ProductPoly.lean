import Lean_Code.SchauderTranslates.ProductFreq

/-!
# The raw kernel is a mixed trigonometric polynomial with constant mass

Tag densities and auxiliary densities are finite Fourier polynomials, the seed factors are
affine in the seed phases and in the lifted residual and its conjugate, and the lifted
residual is a finite sum of line characters times tag characters. Hence the raw kernel is
a finite mixed character sum after flattening. Its integral over the fresh variables is
the constant `M`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

theorem re_complex_eq (w : ℂ) : ((w.re : ℝ) : ℂ) = (w + star w) / 2 := by
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring

/-- Integrals over the flat torus are integrals over the fast space. -/
theorem integral_fastFlat {Mt dt mE L de : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (g : FastSpace Mt dt mE L de → 𝕜) (hg : AEStronglyMeasurable g (fastHaar Mt dt mE L de)) :
    (∫ x, g (fastFlat Mt dt mE L de x) ∂torusMeasure (fastDim Mt dt mE L de)) =
      ∫ y, g y ∂fastHaar Mt dt mE L de := by
  have hmp := fastFlat_measurePreserving Mt dt mE L de
  rw [← hmp.map_eq] at hg ⊢
  rw [integral_map hmp.measurable.aemeasurable hg]

theorem isFastPoly_const_fast {Mt dt mE L de : ℕ} (c : ℂ) :
    IsFastPoly (Mt := Mt) (dt := dt) (mE := mE) (L := L) (de := de) (fun _ _ => c) :=
  isMixedTrigPoly_const c

namespace EngineSetup
variable {T : TagSetup} {E : EngineSetup T}

/-- The lifted residual is a fast polynomial. -/
theorem isFastPoly_lift (i : Fin T.N) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => T.lift i (t, y.1)) := by
  have h : ∀ (t : ℝ) (y : E.Fast), T.lift i (t, y.1) = ∑ q : Fin (T.d + 1) × Fin T.nt,
      liftPacketCoeff T.st T.cn q * (character (T.lam q.1) t *
        UnitAddTorus.mFourier (T.st.frequencies q.2) (y.1 (T.blk i q.1))) := fun t y => rfl
  apply IsFastPoly.congr _ (fun t y => (h t y).symm)
  apply IsFastPoly.sum
  intro q _
  apply IsFastPoly.const_mul
  exact (isFastPoly_line _).mul (isFastPoly_tag _ _)

/-- Finite Fourier polynomials in one tag block. -/
theorem isFastPoly_tagDensity (hT : T.Valid) (b : Fin T.Mt) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun _ y => (T.st.density (y.1 b) : ℂ)) := by
  obtain ⟨K, a, ha⟩ := hT.tag_poly
  exact (isFastPoly_tag_poly b K a).congr (fun t y => (ha (y.1 b)).symm)

/-- Finite Fourier polynomials in one auxiliary block. -/
theorem isFastPoly_auxDensity (hE : E.Valid) (c : Fin (T.N * E.n)) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun _ y => ((E.a c).scalar.density (y.2 c).2 : ℂ)) := by
  obtain ⟨K, a, ha⟩ := hE.eng_poly c
  exact (isFastPoly_aux_poly c K a).congr (fun t y => (ha (y.2 c).2).symm)

/-- One seed factor of engine `c`. -/
theorem isFastPoly_seedFactor (hE : E.Valid) (c : Fin (T.N * E.n)) (j : Fin E.L) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ)) := by
  have hz : IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun _ y => fourier (1 : ℤ) ((y.2 c).1 j)) :=
    (isFastPoly_seed c (Pi.single j 1)).congr (fun t y => mFourier_single_one j _)
  have hv : IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => ((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) := by
    apply IsFastPoly.const_mul
    rw [hE.e_eq]
    exact isFastPoly_lift _
  have hexp : ∀ (t : ℝ) (y : E.Fast),
      (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ) =
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * (((E.a c).κ : ℂ) * (E.a c).e (t, y.1) *
          star (fourier (1 : ℤ) ((y.2 c).1 j))) +
        (1 / 2 : ℂ) * star (((E.a c).κ : ℂ) * (E.a c).e (t, y.1) *
          star (fourier (1 : ℤ) ((y.2 c).1 j))) := by
    intro t y
    simp only [seedFactor]
    push_cast
    rw [re_complex_eq]
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  apply IsFastPoly.add
  · apply IsFastPoly.add
    · exact isFastPoly_const_fast (1 / 2 : ℂ)
    · exact (hv.mul hz.star).const_mul _
  · exact (hv.mul hz.star).star.const_mul _

/-- The raw selective kernel of engine `c`. -/
theorem isFastPoly_raw (hE : E.Valid) (c : Fin (T.N * E.n)) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => ((E.a c).raw ((t, y.1), y.2 c) : ℂ)) := by
  have hexp : ∀ (t : ℝ) (y : E.Fast), ((E.a c).raw ((t, y.1), y.2 c) : ℂ) =
      ((E.a c).scalar.density (y.2 c).2 : ℂ) +
        (1 - ((E.a c).scalar.density (y.2 c).2 : ℂ)) *
          (((E.a c).m / (1 / 2 : ℝ) ^ E.L : ℝ) : ℂ) *
            ∏ j, (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ) := by
    intro t y
    simp only [SelectiveKernelData.raw, seedKernel, seedProduct]
    push_cast
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  apply (isFastPoly_auxDensity hE c).add
  apply IsFastPoly.mul
  · apply IsFastPoly.mul
    · exact (isFastPoly_const_fast 1).add ((isFastPoly_auxDensity hE c).const_mul (-1)) |>.congr
        (fun t y => by ring)
    · exact isFastPoly_const_fast _
  · exact IsFastPoly.prod _ (fun j _ => isFastPoly_seedFactor hE c j)

/-- The raw kernel is a fast polynomial. -/
theorem isFastPoly_Wraw (hT : T.Valid) (hE : E.Valid) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => (E.Wraw t y : ℂ)) := by
  have hexp : ∀ (t : ℝ) (y : E.Fast), (E.Wraw t y : ℂ) =
      (∏ b, (T.st.density (y.1 b) : ℂ)) * ∏ c, ((E.a c).raw ((t, y.1), y.2 c) : ℂ) := by
    intro t y
    simp only [Wraw]
    push_cast
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  exact (IsFastPoly.prod _ (fun b _ => isFastPoly_tagDensity hT b)).mul
    (IsFastPoly.prod _ (fun c _ => isFastPoly_raw hE c))

/-- The flat raw kernel. -/
def Wflat (E : EngineSetup T) (t : ℝ) (x : UnitAddTorus (Fin E.D)) : ℝ := E.Wraw t (E.flat x)

theorem isMixedTrigPoly_Wflat (hT : T.Valid) (hE : E.Valid) :
    IsMixedTrigPoly (fun t x => (E.Wflat t x : ℂ)) :=
  isFastPoly_Wraw hT hE

/-- The conditional mass of the raw kernel is `M` at every line point. -/
theorem integral_Wraw (t : ℝ) :
    (∫ y, E.Wraw t y ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de) = E.M := by
  rw [show fastHaar T.Mt T.dt (T.N * E.n) E.L E.de =
      (Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt).prod
        (Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de)) from rfl]
  have hint : Integrable (fun y : E.Fast => E.Wraw t y)
      ((Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt).prod
        (Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de))) := by
    apply Integrable.of_bound (C := 1)
    · exact (Wraw_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_of_nonneg (Wraw_pos t y).le]
      exact Wraw_le_one t y
  rw [integral_prod _ hint]
  have hin (ytag : Fin T.Mt → UnitAddTorus (Fin T.dt)) :
      (∫ yE, E.Wraw t (ytag, yE) ∂Measure.pi fun _ : Fin (T.N * E.n) =>
        (torusMeasure E.L).prod (torusMeasure E.de)) =
        (∏ b, T.st.density (ytag b)) * ∏ c, (E.a c).mass := by
    simp only [Wraw]
    rw [integral_const_mul]
    congr 1
    have h := integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun c (z : EngineFresh E.L E.de) => (E.a c).raw ((t, ytag), z))
      (μ := fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de))
    rw [h]
    exact Finset.prod_congr rfl (fun c _ => (E.a c).raw_mass _)
  simp_rw [hin]
  rw [integral_mul_const]
  have h := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun _ (z : UnitAddTorus (Fin T.dt)) => T.st.density z)
    (μ := fun _ : Fin T.Mt => torusMeasure T.dt)
  rw [h, M]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem integral_Wflat (t : ℝ) :
    (∫ x, E.Wflat t x ∂torusMeasure E.D) = E.M := by
  rw [← integral_Wraw t]
  exact integral_fastFlat (fun y => E.Wraw t y)
    (Wraw_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

end EngineSetup
end SchauderTranslates
