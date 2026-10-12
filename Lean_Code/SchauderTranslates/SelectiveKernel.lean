import Lean_Code.SchauderTranslates.BoundedRepresentatives
import Lean_Code.SchauderTranslates.ScalarData
import Lean_Code.SchauderTranslates.SeedMoments

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The actual selective kernel data. The slow representative is arbitrary;
it need not be one of the original carrier functions. -/
structure SelectiveKernelData (S : Type*) [MeasurableSpace S] (L d n : ℕ) where
  scalar : ScalarData d n
  e : BoundedMeasurableComplex S
  m : ℝ
  κ : ℝ
  mass_pos : 0 < m
  mass_le : m ≤ (1 / 2 : ℝ) ^ L
  coupling_bound : ∀ x, ‖(κ : ℂ) * e x‖ ≤ 1 / 4

namespace SelectiveKernelData
variable {S : Type*} [MeasurableSpace S] {L d n : ℕ}
variable (a : SelectiveKernelData S L d n)

/-- Instantiate the selective kernel from the checked seed parameter and a permitted
mass, using the representative's certified uniform bound. -/
def fromSeedParameter (ρ : Measure S) [IsProbabilityMeasure ρ] (s : ScalarData d n)
    (e : BoundedMeasurableComplex S) (hunit : (∫ x, ‖e x‖ ^ 2 ∂ρ) = 1)
    (m : ℝ) (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) : SelectiveKernelData S L d n where
  scalar := s
  e := e
  m := m
  κ := seedParameter e.bound
  mass_pos := hm
  mass_le := hm1
  coupling_bound := fun x => seedParameter_scaled_bound
    (one_le_bound_of_unit_energy ρ e e.measurable e.bound_nonneg e.norm_le hunit) (e.norm_le x)

def raw (p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) : ℝ :=
  a.scalar.density p.2.2 + (1 - a.scalar.density p.2.2) *
    seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2.1

def mass : ℝ := a.scalar.mass + (1 - a.scalar.mass) * a.m

theorem m_le_one : a.m ≤ 1 := a.mass_le.trans (pow_le_one₀ (by norm_num) (by norm_num))

theorem mass_positive : 0 < a.mass := by
  have hw := a.scalar.toTorusWeight.mass_pos
  have hm := mul_nonneg (sub_nonneg.mpr a.scalar.toTorusWeight.mass_le_one) a.mass_pos.le
  exact add_pos_of_pos_of_nonneg hw hm

theorem mass_le_one : a.mass ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left a.m_le_one (sub_nonneg.mpr a.scalar.toTorusWeight.mass_le_one)
  unfold mass
  linarith

theorem mass_eq {ε : ℝ} (hε : a.scalar.mass = 1 - ε) :
    a.mass = 1 - (1 - a.m) * ε := by unfold mass; rw [hε]; ring

theorem raw_measurable : Measurable a.raw := by
  unfold raw seedKernel seedProduct seedFactor
  have he := a.e.measurable
  have hw := a.scalar.measurable
  fun_prop

theorem raw_bounds (p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :
    0 < a.raw p ∧ a.raw p ≤ 1 := by
  have hw := a.scalar.positive p.2.2
  have hw1 := a.scalar.le_one p.2.2
  have hv := seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2.1
  unfold raw
  constructor
  · exact add_pos_of_pos_of_nonneg hw (mul_nonneg (by linarith) hv.1.le)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hv.2)]

theorem raw_floor {β : ℝ} (hβ : ∀ t, β ≤ a.scalar.density t)
    (p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) : β ≤ a.raw p := by
  have hv := (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2.1).1.le
  exact (hβ p.2.2).trans (le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr (a.scalar.le_one _)) hv))

theorem raw_integrable (x : S) :
    Integrable (fun y => a.raw (x, y)) ((torusMeasure L).prod (torusMeasure d)) := by
  apply Integrable.of_bound (a.raw_measurable.comp measurable_prodMk_left).aestronglyMeasurable 1
  filter_upwards [] with y
  simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (a.raw_bounds (x, y)).1] using (a.raw_bounds (x, y)).2

theorem raw_mass (x : S) :
    (∫ y, a.raw (x, y) ∂(torusMeasure L).prod (torusMeasure d)) = a.mass := by
  rw [integral_prod_symm _ (a.raw_integrable x)]
  have hv : Integrable (seedKernel L a.m ((a.κ : ℂ) * a.e x)) (torusMeasure L) :=
    (seedKernel_continuous _ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [raw]
  simp_rw [integral_add (integrable_const _) (hv.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul, seedKernel_integral]
  have hi : Integrable (fun t => 1 - a.scalar.density t) (torusMeasure d) :=
    (integrable_const (1 : ℝ)).sub a.scalar.toTorusWeight.integrable
  rw [integral_add a.scalar.toTorusWeight.integrable (hi.mul_const a.m), integral_mul_const]
  have hs := integral_sub (integrable_const (1 : ℝ) (μ := torusMeasure d)) a.scalar.toTorusWeight.integrable
  rw [hs]
  simp only [integral_const, probReal_univ, one_smul, mass, TorusWeight.mass]

/-- The normalized selective kernel has conditional mass exactly one. -/
def kernel : FiberKernel S (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))
    ((torusMeasure L).prod (torusMeasure d)) where
  density := fun p => a.raw p / a.mass
  measurable := a.raw_measurable.div_const _
  nonneg := fun p => div_nonneg (a.raw_bounds p).1.le a.mass_positive.le
  bound := 1 / a.mass
  upper := fun p => div_le_div_of_nonneg_right (a.raw_bounds p).2 a.mass_positive.le
  mass := fun x => by rw [integral_div, a.raw_mass, div_self a.mass_positive.ne']

theorem kernel_positive (p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :
    0 < a.kernel.density p := div_pos (a.raw_bounds p).1 a.mass_positive

theorem kernel_floor {β : ℝ} (hβ : ∀ t, β ≤ a.scalar.density t)
    (p : S × (UnitAddTorus (Fin L) × UnitAddTorus (Fin d))) :
    β / a.mass ≤ a.kernel.density p :=
  div_le_div_of_nonneg_right (a.raw_floor hβ p) a.mass_positive.le

end SelectiveKernelData
end SchauderTranslates
