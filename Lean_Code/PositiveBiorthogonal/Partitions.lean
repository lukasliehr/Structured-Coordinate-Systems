import Lean_Code.PositiveBiorthogonal.DisjointOperators

/-! Admissible finite interval partitions and their averaging formula. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal

/-- A nondegenerate bounded half-open interval, using the public statement's Ioc convention. -/
structure IntervalCell where
  left : ℝ
  right : ℝ
  proper : left < right

namespace IntervalCell

def carrier (D : IntervalCell) : Set ℝ := Ioc D.left D.right

def length (D : IntervalCell) : ℝ := D.right - D.left

theorem length_pos (D : IntervalCell) : 0 < D.length := sub_pos.mpr D.proper

theorem measurable (D : IntervalCell) : MeasurableSet D.carrier := measurableSet_Ioc

theorem measure_ne_top (D : IntervalCell) : volume D.carrier ≠ ∞ := measure_Ioc_lt_top.ne

theorem volume_real (D : IntervalCell) : volume.real D.carrier = D.length := by
  simp [carrier, length, Real.volume_Ioc, measureReal_def, D.proper.le]

theorem volume_pos (D : IntervalCell) : 0 < volume D.carrier := by
  apply (ENNReal.toReal_pos_iff.mp ?_).1
  change 0 < volume.real D.carrier
  rw [D.volume_real]
  exact D.length_pos

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

def indicator (D : IntervalCell) : L 𝕜 p :=
  indicatorConstLp p D.measurable D.measure_ne_top 1

theorem coe_indicator (D : IntervalCell) :
    ((D.indicator : L 𝕜 p) : ℝ → 𝕜) =ᵐ[volume] D.carrier.indicator (fun _ => 1) :=
  indicatorConstLp_coeFn (p := p) (hs := D.measurable) (hμs := D.measure_ne_top) (c := (1 : 𝕜))

theorem indicator_step (D : IntervalCell) : CompactlySupportedStep (D.indicator : L 𝕜 p) :=
  interval_indicator_step D.left D.right 1

theorem indicator_nonnegative (D : IntervalCell) : Nonnegative (D.indicator : L 𝕜 p) := by
  filter_upwards [D.coe_indicator (𝕜 := 𝕜) (p := p)] with x hx
  rw [hx]
  by_cases h : x ∈ D.carrier <;> simp [h]

theorem indicator_norm (D : IntervalCell) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖(D.indicator : L 𝕜 p)‖ = D.length ^ (1 / p.toReal) := by
  rw [indicator, PositiveBiorthogonal.indicator_norm _ _ _ hp0 hpfin, D.volume_real]

theorem indicator_norm_top (D : IntervalCell) : ‖(D.indicator : L 𝕜 ∞)‖ = 1 :=
  PositiveBiorthogonal.indicator_top_norm _ _ _ D.volume_pos.ne'

theorem pairing_indicator (D : IntervalCell) (f : L 𝕜 p) :
    pairing f (D.indicator : L 𝕜 q) = ∫ x in D.carrier, f x := by
  unfold pairing
  rw [← integral_indicator D.measurable]
  apply integral_congr_ae
  filter_upwards [D.coe_indicator (𝕜 := 𝕜) (p := q)] with x hx
  rw [hx]
  by_cases h : x ∈ D.carrier <;> simp [h]

theorem integrableOn [Fact (1 ≤ p)] (D : IntervalCell) (f : L 𝕜 p) :
    IntegrableOn f D.carrier volume := by
  obtain ⟨q, hpq⟩ := StatementAudit.conjugate_exists (Fact.out : 1 ≤ p)
  let := StatementAudit.conjugate_instance hpq
  have hi := (Lp.memLp f).integrable_mul (Lp.memLp (D.indicator : L 𝕜 q))
  apply (integrable_indicator_iff D.measurable).mp
  apply hi.congr
  filter_upwards [D.coe_indicator (𝕜 := 𝕜) (p := q)] with x hx
  rw [Pi.mul_apply, hx]
  by_cases h : x ∈ D.carrier <;> simp [h]

theorem pairing_indicators (D E : IntervalCell) :
    pairing (D.indicator : L 𝕜 p) (E.indicator : L 𝕜 q) = (volume.real (D.carrier ∩ E.carrier) : 𝕜) := by
  rw [E.pairing_indicator]
  change (∫ x in E.carrier, indicatorConstLp p D.measurable D.measure_ne_top (1 : 𝕜) x) = _
  rw [setIntegral_indicatorConstLp E.measurable D.measurable D.measure_ne_top,
    RCLike.real_smul_eq_coe_mul, mul_one]

end IntervalCell

def gridUnit (n : ℤ) : IntervalCell := ⟨n, (n : ℝ) + 1, by linarith⟩

/-- An ordered finite list of disjoint positive cells covering finitely many grid units. -/
structure ActivePartition where
  units : Finset ℤ
  units_nonempty : units.Nonempty
  R : ℕ
  R_pos : 0 < R
  cell : Fin R → IntervalCell
  disjoint : Pairwise (fun i j => Disjoint (cell i).carrier (cell j).carrier)
  cover : (⋃ i : Fin R, (cell i).carrier) = ⋃ n ∈ units, (gridUnit n).carrier
  in_grid : ∀ i : Fin R, ∃ n ∈ units, (cell i).carrier ⊆ (gridUnit n).carrier

namespace ActivePartition

def active (P : ActivePartition) : Set ℝ := ⋃ n ∈ P.units, (gridUnit n).carrier

theorem active_measurable (P : ActivePartition) : MeasurableSet P.active := by
  apply MeasurableSet.biUnion P.units.countable_toSet
  intro n _
  exact (gridUnit n).measurable

def minLength (P : ActivePartition) : ℝ :=
  (Finset.univ : Finset (Fin P.R)).inf' ⟨⟨0, P.R_pos⟩, Finset.mem_univ _⟩
    (fun i => (P.cell i).length)

theorem minLength_pos (P : ActivePartition) : 0 < P.minLength := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i _
  exact (P.cell i).length_pos

theorem minLength_le (P : ActivePartition) (i : Fin P.R) : P.minLength ≤ (P.cell i).length :=
  Finset.inf'_le _ (Finset.mem_univ i)

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

/-- The literal cellwise integral formula; its bounded projection properties are proved separately. -/
def average (P : ActivePartition) (f : L 𝕜 p) : L 𝕜 p :=
  ∑ i : Fin P.R, (((P.cell i).length : 𝕜)⁻¹ * ∫ x in (P.cell i).carrier, f x) •
    (P.cell i).indicator

end ActivePartition
end PositiveBiorthogonal
