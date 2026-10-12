import Lean_Code.SchauderTranslates.ProductModel
import Lean_Code.SchauderTranslates.FastTorus

/-!
# The raw product kernel and the identification of the product law

The raw kernel of the finite extension is the product of all raw tag densities and all
raw selective kernels. Against the product Haar measure on the fast variables and the
old weight on the line it is the total mass `(∫ w) M` times the normalized combined law
used in `ProductModel.lean`. This identifies every raw product Gram entry with the
corresponding L² inner product.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

namespace EngineSetup
variable {T : TagSetup} (E : EngineSetup T)

/-- The fast space of all tags and engines. -/
abbrev Fast := FastSpace T.Mt T.dt (T.N * E.n) E.L E.de

/-- The combined product point of a line point and fast variables. -/
abbrev pt (t : ℝ) (y : E.Fast) : T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de) :=
  ((t, y.1), y.2)

/-- The raw kernel: all raw tag densities times all raw selective kernels. -/
def Wraw (t : ℝ) (y : E.Fast) : ℝ :=
  (∏ b, T.st.density (y.1 b)) * ∏ c, (E.a c).raw ((t, y.1), y.2 c)

/-- The conditional mass of the raw kernel. -/
def M : ℝ := T.st.mass ^ T.Mt * ∏ c, (E.a c).mass

variable {E}

theorem M_pos : 0 < E.M := by
  have h1 := T.st.toTorusWeight.mass_pos
  have h2 : 0 < ∏ c, (E.a c).mass := Finset.prod_pos (fun c _ => (E.a c).mass_positive)
  unfold M
  positivity

theorem M_le_one : E.M ≤ 1 := by
  have h1 := T.st.toTorusWeight.mass_le_one
  have h0 := T.st.toTorusWeight.mass_pos
  have hp : T.st.mass ^ T.Mt ≤ 1 := pow_le_one₀ h0.le h1
  have hq : ∏ c, (E.a c).mass ≤ 1 :=
    Finset.prod_le_one (fun c _ => (E.a c).mass_positive.le) (fun c _ => (E.a c).mass_le_one)
  unfold M
  have := pow_nonneg h0.le T.Mt
  nlinarith [Finset.prod_nonneg (fun c (_ : c ∈ Finset.univ) => (E.a c).mass_positive.le)]

theorem Wraw_pos (t : ℝ) (y : E.Fast) : 0 < E.Wraw t y := by
  unfold Wraw
  apply mul_pos
  · exact Finset.prod_pos (fun b _ => T.st.positive _)
  · exact Finset.prod_pos (fun c _ => ((E.a c).raw_bounds _).1)

theorem Wraw_le_one (t : ℝ) (y : E.Fast) : E.Wraw t y ≤ 1 := by
  unfold Wraw
  have h1 : ∏ b, T.st.density (y.1 b) ≤ 1 :=
    Finset.prod_le_one (fun b _ => (T.st.positive _).le) (fun b _ => T.st.le_one _)
  have h2 : ∏ c, (E.a c).raw ((t, y.1), y.2 c) ≤ 1 :=
    Finset.prod_le_one (fun c _ => ((E.a c).raw_bounds _).1.le) (fun c _ => ((E.a c).raw_bounds _).2)
  have h0 : 0 ≤ ∏ c, (E.a c).raw ((t, y.1), y.2 c) :=
    Finset.prod_nonneg (fun c _ => ((E.a c).raw_bounds _).1.le)
  have h0' : 0 ≤ ∏ b, T.st.density (y.1 b) :=
    Finset.prod_nonneg (fun b _ => (T.st.positive _).le)
  nlinarith

theorem Wraw_measurable : Measurable (fun p : ℝ × E.Fast => E.Wraw p.1 p.2) := by
  unfold Wraw
  apply Measurable.mul
  · exact Finset.measurable_prod _ (fun b _ =>
      T.st.measurable.comp ((measurable_pi_apply b).comp (measurable_fst.comp measurable_snd)))
  · exact Finset.measurable_prod _ (fun c _ => (E.a c).raw_measurable.comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply c).comp (measurable_snd.comp measurable_snd))))

/-- The raw kernel is the total mass times the normalized tag and engine densities. -/
theorem Wraw_eq (t : ℝ) (y : E.Fast) :
    E.Wraw t y = E.M * ((tagKernel ℝ T.st T.Mt).density (t, y.1) *
      (FiberKernel.piKernel (kernels E.a)).density ((t, y.1), y.2)) := by
  have hm := T.st.toTorusWeight.mass_pos
  have hc : ∀ c, (E.a c).mass ≠ 0 := fun c => (E.a c).mass_positive.ne'
  simp only [Wraw, M, tagKernel, FiberKernel.piKernel, scalarKernel, kernels,
    SelectiveKernelData.kernel]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hp : T.st.mass ^ T.Mt ≠ 0 := pow_ne_zero _ hm.ne'
  have hq : ∏ c, (E.a c).mass ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hc c)
  field_simp

/-- Fubini for the normalized combined law, as an iterated integral. -/
theorem integral_P (G : BoundedMeasurableComplex (T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de))) :
    (∫ p, G p ∂E.P) = ((∫ s, T.w.density s : ℝ) : ℂ)⁻¹ * ∫ t, (T.w.density t : ℂ) *
      ∫ y, (((tagKernel ℝ T.st T.Mt).density (t, y.1) *
        (FiberKernel.piKernel (kernels E.a)).density ((t, y.1), y.2) : ℝ) : ℂ) *
          G ((t, y.1), y.2) ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de := by
  set KE := FiberKernel.piKernel (kernels E.a)
  set KT := tagKernel ℝ T.st T.Mt
  -- integrate out the engine variables
  have hG : Integrable (fun p => (KE.density p : ℂ) * G p) (T.ρS.prod
      (Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de))) :=
    (KE.density_integrable T.ρS).ofReal.mul_bdd G.measurable.aestronglyMeasurable
      (Eventually.of_forall G.norm_le)
  rw [show E.P = KE.measure T.ρS from rfl, KE.integral_measure, integral_prod _ hG]
  -- integrate out the tag variables
  set H : T.Slow → ℂ := fun s => ∫ yE, (KE.density (s, yE) : ℂ) * G (s, yE)
    ∂Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de) with hH
  have hHb : ∀ s, ‖H s‖ ≤ G.bound := fun s => by
    have := KE.mean_bound G s
    simpa only [FiberKernel.mean] using this
  have hHm : AEStronglyMeasurable H T.ρS := by
    have h : StronglyMeasurable (fun p : T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de) =>
        (KE.density p : ℂ) * G p) :=
      ((Complex.continuous_ofReal.measurable.comp KE.measurable).mul G.measurable).stronglyMeasurable
    exact h.integral_prod_right'.aestronglyMeasurable
  have hKH : Integrable (fun p : T.Slow => (KT.density p : ℂ) * H p)
      (T.ρ.prod (Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt)) := by
    have hm : AEStronglyMeasurable H (T.ρ.prod (Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt)) := by
      have h : StronglyMeasurable (fun p : T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de) =>
          (KE.density p : ℂ) * G p) :=
        ((Complex.continuous_ofReal.measurable.comp KE.measurable).mul G.measurable).stronglyMeasurable
      exact h.integral_prod_right'.aestronglyMeasurable
    exact (KT.density_integrable T.ρ).ofReal.mul_bdd hm (Eventually.of_forall hHb)
  rw [show T.ρS = KT.measure T.ρ from rfl, KT.integral_measure, integral_prod _ hKH,
    lineLaw_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  -- combine the two fresh integrals into one over the fast space
  rw [show fastHaar T.Mt T.dt (T.N * E.n) E.L E.de = (Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt).prod
      (Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de)) from rfl]
  have hint : Integrable (fun y : E.Fast => (((KT.density (t, y.1) * KE.density ((t, y.1), y.2)) : ℝ) : ℂ) *
      G ((t, y.1), y.2)) ((Measure.pi fun _ : Fin T.Mt => torusMeasure T.dt).prod
        (Measure.pi fun _ : Fin (T.N * E.n) => (torusMeasure E.L).prod (torusMeasure E.de))) := by
    apply Integrable.of_bound (C := KT.bound * KE.bound * G.bound)
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · apply Complex.continuous_ofReal.measurable.comp
        exact (KT.measurable.comp (measurable_const.prodMk measurable_fst)).mul
          (KE.measurable.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
      · exact G.measurable.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    · filter_upwards [] with y
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (KT.nonneg _) (KE.nonneg _))]
      have h1 := KT.upper (t, y.1)
      have h2 := KE.upper ((t, y.1), y.2)
      have h3 := G.norm_le ((t, y.1), y.2)
      have h4 := KT.nonneg (t, y.1)
      have h5 := KE.nonneg ((t, y.1), y.2)
      have hKb : 0 ≤ KE.bound := h5.trans h2
      calc (KT.density (t, y.1) * KE.density ((t, y.1), y.2)) * ‖G ((t, y.1), y.2)‖
          ≤ (KT.bound * KE.bound) * G.bound := by
            apply mul_le_mul (mul_le_mul h1 h2 h5 (h4.trans h1)) h3 (norm_nonneg _)
            exact mul_nonneg (h4.trans h1) hKb
        _ = _ := by ring
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with ytag
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with yE
  push_cast
  ring

/-- The measure identification: raw kernel integrals are total mass times the law. -/
theorem raw_integral (G : BoundedMeasurableComplex (T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de))) :
    (∫ t, (T.w.density t : ℂ) * ∫ y, (E.Wraw t y : ℂ) * G (E.pt t y)
      ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de) =
      (((∫ s, T.w.density s) * E.M : ℝ) : ℂ) * ∫ p, G p ∂E.P := by
  have hZ := weight_integral_pos T.w
  rw [integral_P]
  have hin (t : ℝ) : (∫ y, (E.Wraw t y : ℂ) * G (E.pt t y)
      ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de) =
      (E.M : ℂ) * ∫ y, (((tagKernel ℝ T.st T.Mt).density (t, y.1) *
        (FiberKernel.piKernel (kernels E.a)).density ((t, y.1), y.2) : ℝ) : ℂ) *
          G ((t, y.1), y.2) ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Wraw_eq]
    push_cast
    ring
  simp_rw [hin]
  have hc : (∫ t, (T.w.density t : ℂ) * ((E.M : ℂ) * ∫ y, (((tagKernel ℝ T.st T.Mt).density (t, y.1) *
        (FiberKernel.piKernel (kernels E.a)).density ((t, y.1), y.2) : ℝ) : ℂ) *
          G ((t, y.1), y.2) ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de)) =
      (E.M : ℂ) * ∫ t, (T.w.density t : ℂ) * ∫ y, (((tagKernel ℝ T.st T.Mt).density (t, y.1) *
        (FiberKernel.piKernel (kernels E.a)).density ((t, y.1), y.2) : ℝ) : ℂ) *
          G ((t, y.1), y.2) ∂fastHaar T.Mt T.dt (T.N * E.n) E.L E.de := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [hc]
  have hZc : ((∫ s, T.w.density s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  push_cast
  field_simp

end EngineSetup
end SchauderTranslates
