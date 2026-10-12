import Lean_Code.SchauderTranslates.Lp.DisjointNorm

noncomputable section
open MeasureTheory
open scoped ENNReal Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Real interval indicators, viewed as complex Lᵖ classes. -/
def intervalAtom (p : ℝ≥0∞) (ab : ℝ × ℝ) : LebesgueLp p :=
  indicatorConstLp (s := Set.Ico ab.1 ab.2) p measurableSet_Ico
    (by simp [Real.volume_Ico]) (1 : ℂ)

theorem intervalAtom_ae (p : ℝ≥0∞) (ab : ℝ × ℝ) :
    (intervalAtom p ab : ℝ → ℂ) =ᵐ[volume]
      (Set.Ico ab.1 ab.2).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- The algebraic real span is precisely finite real combinations of bounded
interval indicators. There is no closure or regularity assumption here. -/
def stepSpace (p : ℝ≥0∞) : Submodule ℝ (LebesgueLp p) :=
  Submodule.span ℝ (Set.range (intervalAtom p))

def IsCompactStep (p : ℝ≥0∞) (f : LebesgueLp p) : Prop := f ∈ stepSpace p

theorem intervalAtom_isCompactStep (p : ℝ≥0∞) (ab : ℝ × ℝ) :
    IsCompactStep p (intervalAtom p ab) :=
  Submodule.subset_span (Set.mem_range_self ab)

theorem isCompactStep_zero (p : ℝ≥0∞) : IsCompactStep p 0 :=
  (stepSpace p).zero_mem

theorem IsCompactStep.add {p : ℝ≥0∞} {f g : LebesgueLp p}
    (hf : IsCompactStep p f) (hg : IsCompactStep p g) : IsCompactStep p (f + g) :=
  (stepSpace p).add_mem hf hg

theorem IsCompactStep.smul {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) (a : ℝ) : IsCompactStep p (a • f) :=
  (stepSpace p).smul_mem a hf

theorem IsCompactStep.finset_sum {p : ℝ≥0∞} {ι : Type*}
    (s : Finset ι) (f : ι → LebesgueLp p) (hf : ∀ i ∈ s, IsCompactStep p (f i)) :
    IsCompactStep p (∑ i ∈ s, f i) :=
  (stepSpace p).sum_mem hf

def translationLinear (p : ℝ≥0∞) (a : ℝ) : LebesgueLp p →ₗ[ℝ] LebesgueLp p :=
  Lp.compMeasurePreservingₗ ℝ (fun x : ℝ => x - a) (measurePreserving_sub_right volume a)

@[simp] theorem translationLinear_apply (p : ℝ≥0∞) (a : ℝ) (f : LebesgueLp p) :
    translationLinear p a f = translate p a f := rfl

theorem translate_add (p : ℝ≥0∞) (a : ℝ) (f g : LebesgueLp p) :
    translate p a (f + g) = translate p a f + translate p a g :=
  (translationLinear p a).map_add f g

theorem translate_sub (p : ℝ≥0∞) (a : ℝ) (f g : LebesgueLp p) :
    translate p a (f - g) = translate p a f - translate p a g :=
  (translationLinear p a).map_sub f g

theorem translate_real_smul (p : ℝ≥0∞) (a c : ℝ) (f : LebesgueLp p) :
    translate p a (c • f) = c • translate p a f :=
  (translationLinear p a).map_smul c f

theorem translate_finset_sum (p : ℝ≥0∞) (a : ℝ) {ι : Type*}
    (s : Finset ι) (f : ι → LebesgueLp p) :
    translate p a (∑ i ∈ s, f i) = ∑ i ∈ s, translate p a (f i) :=
  map_sum (translationLinear p a) _ _

@[simp] theorem translate_zero (p : ℝ≥0∞) (f : LebesgueLp p) : translate p 0 f = f := by
  apply Lp.ext
  simpa only [sub_zero] using translate_ae p 0 f

theorem translate_comp (p : ℝ≥0∞) (a b : ℝ) (f : LebesgueLp p) :
    translate p a (translate p b f) = translate p (a + b) f := by
  apply Lp.ext
  have hcomp := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae (translate_ae p b f)
  filter_upwards [translate_ae p a (translate p b f), hcomp, translate_ae p (a+b) f]
    with x ha hb hab
  rw [ha, hb, hab]
  congr 1
  ring

theorem translate_intervalAtom (p : ℝ≥0∞) (a : ℝ) (ab : ℝ × ℝ) :
    translate p a (intervalAtom p ab) = intervalAtom p (ab.1 + a, ab.2 + a) := by
  apply Lp.ext
  have hcomp := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae (intervalAtom_ae p ab)
  filter_upwards [translate_ae p a (intervalAtom p ab), hcomp,
    intervalAtom_ae p (ab.1 + a, ab.2 + a)] with x ht ho hn
  rw [ht, ho, hn]
  have hiff : x - a ∈ Set.Ico ab.1 ab.2 ↔ x ∈ Set.Ico (ab.1 + a) (ab.2 + a) := by
    constructor
    · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  by_cases hx : x ∈ Set.Ico (ab.1 + a) (ab.2 + a)
  · simp [hx, hiff.mpr hx]
  · simp [hx, mt hiff.mp hx]

theorem IsCompactStep.translate {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) (a : ℝ) : IsCompactStep p (translate p a f) := by
  have hle : (stepSpace p).map (translationLinear p a) ≤ stepSpace p := by
    rw [stepSpace, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨ab, rfl⟩, rfl⟩
    rw [translationLinear_apply, translate_intervalAtom]
    exact Submodule.subset_span (Set.mem_range_self (ab.1 + a, ab.2 + a))
  exact hle ⟨f, hf, rfl⟩

theorem norm_intervalAtom (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (ab : ℝ × ℝ) :
    ‖intervalAtom p ab‖ = (max (ab.2 - ab.1) 0) ^ (1 / p.toReal) := by
  rw [intervalAtom, norm_indicatorConstLp hp0 hpfin]
  simp [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal']

theorem initial_generator_unit (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖intervalAtom p (0, 1)‖ = 1 := by
  simp [norm_intervalAtom p hp0 hpfin]

theorem intervalAtom_supported (p : ℝ≥0∞) (ab : ℝ × ℝ) (R : ℝ)
    (hl : -R ≤ ab.1) (hr : ab.2 ≤ R) :
    SupportedOn (intervalAtom p ab) (Set.Icc (-R) R) := by
  filter_upwards [intervalAtom_ae p ab] with x hx
  intro hout
  have hi : x ∉ Set.Ico ab.1 ab.2 := by
    intro h
    exact hout ⟨hl.trans h.1, h.2.le.trans hr⟩
  simp [hx, hi]

/-- Every vector in the algebraic step span has a bounded support interval.
The radius is constructed from the finite algebraic expression. -/
theorem IsCompactStep.bounded_support {p : ℝ≥0∞} {f : LebesgueLp p}
    (hf : IsCompactStep p f) : ∃ R : ℝ, 0 ≤ R ∧ SupportedOn f (Set.Icc (-R) R) := by
  change f ∈ Submodule.span ℝ (Set.range (intervalAtom p)) at hf
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨ab, rfl⟩ := hz
    refine ⟨|ab.1| + |ab.2| + 1, by positivity, intervalAtom_supported p ab _ ?_ ?_⟩
    · linarith [neg_abs_le ab.1, abs_nonneg ab.2]
    · linarith [le_abs_self ab.2, abs_nonneg ab.1]
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := p) (μ := (volume : Measure ℝ))] with x hx
    intro _
    exact hx
  | add x y hx hy hix hiy =>
    obtain ⟨R, hR, hxR⟩ := hix
    obtain ⟨S, hS, hyS⟩ := hiy
    refine ⟨R + S, add_nonneg hR hS, ?_⟩
    have hxRS := hxR.mono (Set.Icc_subset_Icc (by linarith : -(R+S) ≤ -R) (by linarith : R ≤ R+S))
    have hyRS := hyS.mono (Set.Icc_subset_Icc (by linarith : -(R+S) ≤ -S) (by linarith : S ≤ R+S))
    exact hxRS.add hyRS
  | smul a x hx hix =>
    obtain ⟨R, hR, hxR⟩ := hix
    exact ⟨R, hR, hxR.real_smul a⟩

end SchauderTranslates.LpConstruction
