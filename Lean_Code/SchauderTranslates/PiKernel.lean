import Lean_Code.SchauderTranslates.FiberSlowSpace
import Lean_Code.SchauderTranslates.BoundedRepresentatives

/-!
# Conditionally independent fiber kernels

Finitely many fiber kernels over the same slow space, each with its own copy of the
fresh variables, combine into one product kernel. Fubini over the product of fresh
variables identifies the means of lifted atoms, the inner products within one copy, and
the inner products across different copies (only the means interact). These are the
facts behind the additivity of information in blueprint `tag:engines`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

theorem fintype_prod_ite_eq_mul {ι X : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (hab : a ≠ b)
    (u v : X → ℂ) (x : ι → X) :
    (∏ i, (if i = a then u (x i) else if i = b then v (x i) else 1)) = u (x a) * v (x b) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), if_pos rfl,
    ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    if_neg hab.symm, if_pos rfl]
  have h1 : ∏ i ∈ (Finset.univ.erase a).erase b,
      (if i = a then u (x i) else if i = b then v (x i) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_erase, Finset.mem_erase] at hi
    rw [if_neg hi.2.1, if_neg hi.1]
  rw [h1, one_mul, mul_comm]

theorem fintype_prod_ite_eq_one {ι X : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (u : X → ℂ) (x : ι → X) :
    (∏ i, (if i = a then u (x i) else 1)) = u (x a) := by
  rw [Finset.prod_ite_eq' Finset.univ a (fun i => u (x i)), if_pos (Finset.mem_univ a)]

namespace FiberKernel

variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν]
variable {m : ℕ}

/-- The product of finitely many fiber kernels, each acting on its own copy of the fresh
variables. -/
def piKernel (K : Fin m → FiberKernel S Y ν) :
    FiberKernel S (Fin m → Y) (Measure.pi fun _ : Fin m => ν) where
  density p := ∏ c, (K c).density (p.1, p.2 c)
  measurable := Finset.measurable_prod _ (fun c _ =>
    (K c).measurable.comp (measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd)))
  nonneg p := Finset.prod_nonneg (fun c _ => (K c).nonneg _)
  bound := ∏ c, max (K c).bound 0
  upper p := Finset.prod_le_prod (fun c _ => (K c).nonneg _)
    (fun c _ => ((K c).upper _).trans (le_max_left _ _))
  mass s := by
    have h := integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun c (y : Y) => (K c).density (s, y)) (μ := fun _ : Fin m => ν)
    simp only [(K _).mass, Finset.prod_const_one] at h
    exact h

variable (K : Fin m → FiberKernel S Y ν)

/-- Lift a function of the slow variable and one copy of the fresh variables. -/
def liftAt (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    BoundedMeasurableComplex (S × (Fin m → Y)) :=
  f.comp (fun p => (p.1, p.2 c)) (measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd))

@[simp] theorem liftAt_apply (c : Fin m) (f : BoundedMeasurableComplex (S × Y))
    (p : S × (Fin m → Y)) : liftAt c f p = f (p.1, p.2 c) := rfl

/-- The fresh-variable integral of a lifted atom times the product density, at one copy. -/
theorem integral_lift_one (s : S) (c : Fin m) (u : Y → ℂ) :
    (∫ y, ((piKernel K).density (s, y) : ℂ) * u (y c) ∂Measure.pi fun _ : Fin m => ν) =
      ∫ y, ((K c).density (s, y) : ℂ) * u y ∂ν := by
  classical
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun c' (y : Y) => ((K c').density (s, y) : ℂ) * (if c' = c then u y else 1))
    (μ := fun _ : Fin m => ν)
  have hl (y : Fin m → Y) : ((piKernel K).density (s, y) : ℂ) * u (y c) =
      ∏ c', ((K c').density (s, y c') : ℂ) * (if c' = c then u (y c') else 1) := by
    rw [Finset.prod_mul_distrib, fintype_prod_ite_eq_one c u y]
    simp only [piKernel, Complex.ofReal_prod]
  have hr : (∏ c', ∫ y, ((K c').density (s, y) : ℂ) * (if c' = c then u y else 1) ∂ν) =
      ∫ y, ((K c).density (s, y) : ℂ) * u y ∂ν := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
    simp only [ite_true]
    rw [Finset.prod_eq_one, one_mul]
    intro c' hc'
    simp only [if_neg (Finset.ne_of_mem_erase hc'), mul_one, integral_complex_ofReal, (K c').mass,
      Complex.ofReal_one]
  simp_rw [hl]
  rw [show (fun y : Fin m → Y => ∏ c', ((K c').density (s, y c') : ℂ) *
      (if c' = c then u (y c') else 1)) =
      (fun y : Fin m → Y => ∏ c', (fun c'' (z : Y) => ((K c'').density (s, z) : ℂ) *
        (if c'' = c then u z else 1)) c' (y c')) from rfl, h, hr]

/-- The fresh-variable integral of two atoms lifted to different copies. -/
theorem integral_lift_two (s : S) {c c' : Fin m} (hcc : c ≠ c') (u v : Y → ℂ) :
    (∫ y, ((piKernel K).density (s, y) : ℂ) * (u (y c) * v (y c')) ∂Measure.pi fun _ : Fin m => ν) =
      (∫ y, ((K c).density (s, y) : ℂ) * u y ∂ν) * ∫ y, ((K c').density (s, y) : ℂ) * v y ∂ν := by
  classical
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun c'' (y : Y) => ((K c'').density (s, y) : ℂ) *
      (if c'' = c then u y else if c'' = c' then v y else 1))
    (μ := fun _ : Fin m => ν)
  have hl (y : Fin m → Y) : ((piKernel K).density (s, y) : ℂ) * (u (y c) * v (y c')) =
      ∏ c'', ((K c'').density (s, y c'') : ℂ) *
        (if c'' = c then u (y c'') else if c'' = c' then v (y c'') else 1) := by
    rw [Finset.prod_mul_distrib, fintype_prod_ite_eq_mul c c' hcc u v y]
    simp only [piKernel, Complex.ofReal_prod]
  have hr : (∏ c'', ∫ y, ((K c'').density (s, y) : ℂ) *
      (if c'' = c then u y else if c'' = c' then v y else 1) ∂ν) =
      (∫ y, ((K c).density (s, y) : ℂ) * u y ∂ν) * ∫ y, ((K c').density (s, y) : ℂ) * v y ∂ν := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hcc.symm, Finset.mem_univ c'⟩)]
    simp only [ite_true, if_neg hcc.symm]
    rw [Finset.prod_eq_one, one_mul, mul_comm]
    intro c'' hc''
    rw [Finset.mem_erase, Finset.mem_erase] at hc''
    simp only [if_neg hc''.2.1, if_neg hc''.1, mul_one, integral_complex_ofReal, (K c'').mass,
      Complex.ofReal_one]
  simp_rw [hl]
  rw [show (fun y : Fin m → Y => ∏ c'', ((K c'').density (s, y c'') : ℂ) *
      (if c'' = c then u (y c'') else if c'' = c' then v (y c'') else 1)) =
      (fun y : Fin m → Y => ∏ c'', (fun c₀ (z : Y) => ((K c₀).density (s, z) : ℂ) *
        (if c₀ = c then u z else if c₀ = c' then v z else 1)) c'' (y c'')) from rfl, h, hr]

/-- The explicit mean of a lifted atom is the mean in its own copy. -/
theorem mean_liftAt (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) (s : S) :
    (piKernel K).mean (liftAt c f) s = (K c).mean f s := by
  simp only [mean, liftAt_apply]
  exact integral_lift_one K s c (fun y => f (s, y))

/-- The inner product of two atoms lifted to the same copy. -/
theorem inner_liftAt_same (ρ : Measure S) [IsFiniteMeasure ρ] (c : Fin m)
    (f g : BoundedMeasurableComplex (S × Y)) :
    inner ℂ ((liftAt c f).toL2 ((piKernel K).measure ρ)) ((liftAt c g).toL2 ((piKernel K).measure ρ)) =
      inner ℂ (f.toL2 ((K c).measure ρ)) (g.toL2 ((K c).measure ρ)) := by
  rw [BoundedMeasurableComplex.inner_toL2, BoundedMeasurableComplex.inner_toL2]
  let F := (f.conjugate.mul g)
  have hF : ∀ p, star (f p) * g p = F p := fun p => rfl
  have hl : (∫ p, star (liftAt c f p) * liftAt c g p ∂(piKernel K).measure ρ) =
      ∫ p, (liftAt c F) p ∂(piKernel K).measure ρ := rfl
  have hr : (∫ p, star (f p) * g p ∂(K c).measure ρ) = ∫ p, F p ∂(K c).measure ρ := rfl
  rw [hl, hr]
  have h1 := (piKernel K).mean_pairing ρ (BoundedMeasurableComplex.const S 1) (liftAt c F)
  have h2 := (K c).mean_pairing ρ (BoundedMeasurableComplex.const S 1) F
  simp only [BoundedMeasurableComplex.const, star_one, one_mul] at h1 h2
  change (∫ p, (liftAt c F) p ∂(piKernel K).measure ρ) = ∫ s, (piKernel K).mean (liftAt c F) s ∂ρ at h1
  rw [h1, h2]
  simp only [mean_liftAt]

/-- Atoms lifted to different copies interact only through their means. -/
theorem inner_liftAt_ne (ρ : Measure S) [IsFiniteMeasure ρ] {c c' : Fin m} (hcc : c ≠ c')
    (f g : BoundedMeasurableComplex (S × Y)) :
    inner ℂ ((liftAt c f).toL2 ((piKernel K).measure ρ)) ((liftAt c' g).toL2 ((piKernel K).measure ρ)) =
      inner ℂ (((K c).meanRepresentative f).toL2 ρ) (((K c').meanRepresentative g).toL2 ρ) := by
  rw [BoundedMeasurableComplex.inner_toL2, BoundedMeasurableComplex.inner_toL2]
  let F := ((liftAt c f).conjugate.mul (liftAt c' g))
  have h1 := (piKernel K).mean_pairing ρ (BoundedMeasurableComplex.const S 1) F
  simp only [BoundedMeasurableComplex.const, star_one, one_mul] at h1
  change (∫ p, star (liftAt c f p) * liftAt c' g p ∂(piKernel K).measure ρ) =
    ∫ s, (piKernel K).mean F s ∂ρ at h1
  rw [h1]
  apply integral_congr_ae
  filter_upwards [] with s
  change (piKernel K).mean F s = star ((K c).mean f s) * (K c').mean g s
  simp only [mean]
  have h := integral_lift_two K s hcc (fun y => star (f (s, y))) (fun y => g (s, y))
  change (∫ y, ((piKernel K).density (s, y) : ℂ) * (star (f (s, y c)) * g (s, y c'))
    ∂Measure.pi fun _ : Fin m => ν) = _
  rw [h]
  congr 1
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [Complex.conj_ofReal]

end FiberKernel
end SchauderTranslates
