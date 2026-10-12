import Lean_Code.PositiveBiorthogonal.IndicatorLimits
import Lean_Code.PositiveBiorthogonal.Partitions

/-! Bounded interval indicators are dense, by the pi-system induction theorem. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem indicatorConstLp_eq_smul_one (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (c : 𝕜) :
    indicatorConstLp p hs hfin c = c • indicatorConstLp p hs hfin (1 : 𝕜) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hfin) (c := c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hfin) (c := (1 : 𝕜)),
    Lp.coeFn_smul c (indicatorConstLp p hs hfin (1 : 𝕜))] with x hc h1 hsm
  rw [hc, hsm, Pi.smul_apply, h1]
  by_cases hx : x ∈ s <;> simp [hx]

theorem interval_indicator_mem (W : Submodule 𝕜 (L 𝕜 p))
    (hI : ∀ D : IntervalCell, D.indicator ∈ W) (a b : ℝ) (c : 𝕜) :
    indicatorConstLp p (measurableSet_Ioc (a := a) (b := b)) measure_Ioc_lt_top.ne c ∈ W := by
  by_cases hab : a < b
  · rw [indicatorConstLp_eq_smul_one]
    exact W.smul_mem c (hI ⟨a, b, hab⟩)
  · have he : Ioc a b = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hab)
    simp [he]

theorem indicator_inter_interval_mem (hp : p ≠ ∞) (W : Submodule 𝕜 (L 𝕜 p))
    (hW : IsClosed (W : Set (L 𝕜 p))) (hI : ∀ D : IntervalCell, D.indicator ∈ W)
    (D : IntervalCell) (c : 𝕜) (s : Set ℝ) (hs : MeasurableSet s) :
    indicatorConstLp p (hs.inter D.measurable)
      (measure_ne_top_of_subset inter_subset_right D.measure_ne_top) c ∈ W := by
  have hD : indicatorConstLp p D.measurable D.measure_ne_top c ∈ W := by
    rw [indicatorConstLp_eq_smul_one]
    exact W.smul_mem c (hI D)
  induction s, hs using MeasurableSpace.induction_on_inter
    (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id) with
  | empty => simp
  | basic t ht =>
    obtain ⟨a, b, hab, rfl⟩ := ht
    convert interval_indicator_mem W hI (max a D.left) (min b D.right) c using 1
    simp only [IntervalCell.carrier, Ioc_inter_Ioc]
  | compl t ht ih =>
    have he : indicatorConstLp p (ht.compl.inter D.measurable)
        (measure_ne_top_of_subset inter_subset_right D.measure_ne_top) c =
      indicatorConstLp p D.measurable D.measure_ne_top c -
        indicatorConstLp p (ht.inter D.measurable)
          (measure_ne_top_of_subset inter_subset_right D.measure_ne_top) c := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := p) (hs := ht.compl.inter D.measurable)
        (hμs := measure_ne_top_of_subset inter_subset_right D.measure_ne_top) (c := c),
        indicatorConstLp_coeFn (p := p) (hs := D.measurable) (hμs := D.measure_ne_top) (c := c),
        indicatorConstLp_coeFn (p := p) (hs := ht.inter D.measurable)
          (hμs := measure_ne_top_of_subset inter_subset_right D.measure_ne_top) (c := c),
        Lp.coeFn_sub (indicatorConstLp p D.measurable D.measure_ne_top c)
          (indicatorConstLp p (ht.inter D.measurable)
            (measure_ne_top_of_subset inter_subset_right D.measure_ne_top) c)] with x h1 h2 h3 h4
      rw [h1, h4, Pi.sub_apply, h2, h3]
      by_cases hx : x ∈ t <;> by_cases hD : x ∈ D.carrier <;> simp [hx, hD]
    rw [he]
    exact W.sub_mem hD ih
  | iUnion t hdis ht ih =>
    have hfin : volume (⋃ n, t n ∩ D.carrier) ≠ ∞ :=
      measure_ne_top_of_subset (iUnion_subset fun n => inter_subset_right) D.measure_ne_top
    have hm := indicatorConstLp_iUnion_mem hp W hW (fun n => t n ∩ D.carrier)
      (fun n => (ht n).inter D.measurable)
      (fun i j hij => (hdis hij).mono inter_subset_left inter_subset_left) hfin c ih
    simpa only [iUnion_inter] using hm

theorem measurable_indicator_mem_of_intervals (hp : p ≠ ∞) (W : Submodule 𝕜 (L 𝕜 p))
    (hW : IsClosed (W : Set (L 𝕜 p))) (hI : ∀ D : IntervalCell, D.indicator ∈ W)
    (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s ≠ ∞) (c : 𝕜) :
    indicatorConstLp p hs hfin c ∈ W := by
  let D (n : ℕ) : IntervalCell := ⟨-((n : ℝ) + 1), (n : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) n]⟩
  let t (n : ℕ) := s ∩ (D n).carrier
  have ht (n) : MeasurableSet (t n) := hs.inter (D n).measurable
  have hm : Monotone t := by
    intro a b hab x hx
    refine ⟨hx.1, ?_⟩
    have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    change -((b : ℝ) + 1) < x ∧ x ≤ (b : ℝ) + 1
    have hd := hx.2
    change -((a : ℝ) + 1) < x ∧ x ≤ (a : ℝ) + 1 at hd
    constructor <;> linarith [hd.1, hd.2]
  have heq : (⋃ n, t n) = s := by
    apply Subset.antisymm (iUnion_subset fun n => inter_subset_left)
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    apply mem_iUnion.mpr
    refine ⟨n, hx, ?_⟩
    change -((n : ℝ) + 1) < x ∧ x ≤ (n : ℝ) + 1
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  apply hW.mem_of_tendsto (indicatorConstLp_monotone_tendsto hp t ht hm s hs hfin heq c)
  exact Eventually.of_forall fun n => indicator_inter_interval_mem hp W hW hI (D n) c s hs

theorem eq_top_of_closed_contains_intervals (hp : p ≠ ∞) (W : Submodule 𝕜 (L 𝕜 p))
    (hW : IsClosed (W : Set (L 𝕜 p))) (hI : ∀ D : IntervalCell, D.indicator ∈ W) : W = ⊤ := by
  apply top_unique
  intro f hf
  apply Lp.induction hp (fun f : L 𝕜 p => f ∈ W) ?_ ?_ hW f
  · intro c s hs hfin
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact measurable_indicator_mem_of_intervals hp W hW hI s hs hfin.ne c
  · intro f g hf hg hdis hfm hgm
    exact W.add_mem hfm hgm

theorem interval_density (hp : p ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range (fun D : IntervalCell => (D.indicator : L 𝕜 p))) : Set (L 𝕜 p)) := by
  rw [dense_iff_closure_eq]
  change (↑((Submodule.span 𝕜 (Set.range (fun D : IntervalCell => (D.indicator : L 𝕜 p)))).topologicalClosure) : Set (L 𝕜 p)) = Set.univ
  rw [eq_top_of_closed_contains_intervals hp _ (Submodule.isClosed_topologicalClosure _)]
  · rfl
  · intro D
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨D, rfl⟩)

end PositiveBiorthogonal
