import Lean_Code.PositiveBiorthogonal.CellSpans
import Lean_Code.PositiveBiorthogonal.IntervalDensity
import Mathlib.MeasureTheory.Integral.Indicator

/-! Shrinking cells approximate interval indicators; the argument uses no infinity-norm density. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace PositiveBiorthogonal

theorem gridUnit_cover (x : ℝ) : ∃ z : ℤ, x ∈ (gridUnit z).carrier := by
  have h : x ∈ ⋃ z : ℤ, Ioc (z : ℝ) ((z : ℝ) + 1) := by
    rw [iUnion_Ioc_intCast ℝ]
    exact mem_univ x
  exact mem_iUnion.mp h

theorem IntervalCell.subset_of_mem_length_lt (B D : IntervalCell) (x : ℝ)
    (hx : x ∈ B.carrier) (hlen : B.length < min (x - D.left) (D.right - x)) :
    B.carrier ⊆ D.carrier := by
  intro y hy
  have h1 := lt_of_lt_of_le hlen (min_le_left _ _)
  have h2 := lt_of_lt_of_le hlen (min_le_right _ _)
  change B.left < x ∧ x ≤ B.right at hx
  change B.left < y ∧ y ≤ B.right at hy
  change D.left < y ∧ y ≤ D.right
  unfold IntervalCell.length at h1 h2
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

namespace ActivePartition

def insideCells (P : ActivePartition) (D : IntervalCell) : Finset (Fin P.R) := by
  classical
  exact Finset.univ.filter (fun i => (P.cell i).carrier ⊆ D.carrier)

@[simp] theorem mem_insideCells (P : ActivePartition) (D : IntervalCell) (i : Fin P.R) :
    i ∈ P.insideCells D ↔ (P.cell i).carrier ⊆ D.carrier := by
  classical
  simp [insideCells]

def insideUnion (P : ActivePartition) (D : IntervalCell) : Set ℝ :=
  ⋃ i ∈ P.insideCells D, (P.cell i).carrier

theorem insideUnion_measurable (P : ActivePartition) (D : IntervalCell) :
    MeasurableSet (P.insideUnion D) :=
  MeasurableSet.biUnion (P.insideCells D).countable_toSet (fun i _ => (P.cell i).measurable)

theorem insideUnion_subset (P : ActivePartition) (D : IntervalCell) :
    P.insideUnion D ⊆ D.carrier := by
  apply iUnion_subset
  intro i
  apply iUnion_subset
  intro hi
  exact (P.mem_insideCells D i).mp hi

theorem insideUnion_finite (P : ActivePartition) (D : IntervalCell) :
    volume (P.insideUnion D) ≠ ∞ :=
  measure_ne_top_of_subset (P.insideUnion_subset D) D.measure_ne_top

theorem insideUnion_indicator_mem {𝕜 : Type*} [RCLike 𝕜] {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (P : ActivePartition) (D : IntervalCell) (W : Submodule 𝕜 (L 𝕜 r))
    (hW : ∀ i, (P.cell i).indicator ∈ W) :
    indicatorConstLp r (P.insideUnion_measurable D) (P.insideUnion_finite D) (1 : 𝕜) ∈ W :=
  indicatorConstLp_finsetUnion_mem W (P.insideCells D) (fun i => (P.cell i).carrier)
    (fun i => (P.cell i).measurable) P.disjoint (fun i => (P.cell i).measure_ne_top) 1 (fun i _ => hW i)

end ActivePartition

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

theorem stage_mesh_eventually (z : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, z ∈ (C.stage k).part.units ∧
      ∀ i : Fin (C.stage k).part.R,
        ((C.stage k).part.cell i).carrier ⊆ (gridUnit z).carrier →
        ((C.stage k).part.cell i).length < ε := by
  obtain ⟨k₀, hk₀⟩ := (C.stage_unit_eventually z).exists
  have he : ∀ᶠ r in atTop, z ∈ (C.stage (k₀ + r)).part.units ∧
      ∀ i : Fin (C.stage (k₀ + r)).part.R,
        ((C.stage (k₀ + r)).part.cell i).carrier ⊆ (gridUnit z).carrier →
        ((C.stage (k₀ + r)).part.cell i).length < ε := by
    filter_upwards [mesh_decay_tendsto_zero.eventually (gt_mem_nhds hε)] with r hr
    exact ⟨C.stage_units_mono (Nat.le_add_right k₀ r) hk₀,
      fun i hi => (C.stage_mesh_decay k₀ r z hk₀ i hi).trans_lt hr⟩
  rw [← map_add_atTop_eq_nat k₀]
  change ∀ᶠ r in atTop, z ∈ (C.stage (r + k₀)).part.units ∧ _
  filter_upwards [he] with r hr
  exact (congrArg (fun n : ℕ => z ∈ (C.stage n).part.units ∧
    ∀ i : Fin (C.stage n).part.R,
      ((C.stage n).part.cell i).carrier ⊆ (gridUnit z).carrier →
      ((C.stage n).part.cell i).length < ε) (Nat.add_comm k₀ r)).mp hr

theorem eventually_mem_insideUnion (D : IntervalCell) (x : ℝ)
    (hx : x ∈ Ioo D.left D.right) :
    ∀ᶠ k in atTop, x ∈ (C.stage k).part.insideUnion D := by
  obtain ⟨z, hz⟩ := gridUnit_cover x
  have hε : 0 < min (x - D.left) (D.right - x) := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  filter_upwards [C.stage_mesh_eventually z _ hε] with k hk
  have hxA := (C.stage k).part.gridUnit_subset_active z hk.1 hz
  change x ∈ ⋃ u ∈ (C.stage k).part.units, (gridUnit u).carrier at hxA
  rw [← (C.stage k).part.cover] at hxA
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
  obtain ⟨u, hu, hU⟩ := (C.stage k).part.in_grid i
  have huz : u = z := by
    by_contra hne
    exact Set.disjoint_left.mp (gridUnit_disjoint hne) (hU hi) hz
  subst u
  have hsub := IntervalCell.subset_of_mem_length_lt ((C.stage k).part.cell i) D x hi (hk.2 i hU)
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨((C.stage k).part.mem_insideCells D i).mpr hsub, hi⟩⟩

theorem insideUnion_missing_measure_tendsto (D : IntervalCell) :
    Tendsto (fun k => volume (symmDiff ((C.stage k).part.insideUnion D) D.carrier)) atTop (𝓝 0) := by
  have h := tendsto_measure_of_ae_tendsto_indicator (μ := volume) atTop
    (A := (∅ : Set ℝ)) MeasurableSet.empty
    (fun k => ((C.stage k).part.insideUnion_measurable D).symmDiff D.measurable)
    D.measurable D.measure_ne_top
    (Eventually.of_forall fun k => by
      rw [symmDiff_of_le ((C.stage k).part.insideUnion_subset D)]
      exact sdiff_subset) ?_
  · simpa only [measure_empty] using h
  · have hne : ∀ᵐ x : ℝ, x ≠ D.right := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with x hxne
    by_cases hx : x ∈ D.carrier
    · have hxo : x ∈ Ioo D.left D.right := ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
      filter_upwards [C.eventually_mem_insideUnion D x hxo] with k hk
      simp [mem_symmDiff, hx, hk]
    · exact Eventually.of_forall fun k => by
        have hk : x ∉ (C.stage k).part.insideUnion D := fun h => hx ((C.stage k).part.insideUnion_subset D h)
        simp [mem_symmDiff, hx, hk]

theorem insideUnion_indicator_tendsto {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ∞)
    (D : IntervalCell) :
    Tendsto (fun k => indicatorConstLp r ((C.stage k).part.insideUnion_measurable D)
      ((C.stage k).part.insideUnion_finite D) (1 : 𝕜)) atTop (𝓝 (D.indicator : L 𝕜 r)) :=
  tendsto_indicatorConstLp_set hr (C.insideUnion_missing_measure_tendsto D)

theorem stage_cells_dense {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : r ≠ ∞)
    (W : Submodule 𝕜 (L 𝕜 r))
    (hW : ∀ k (i : Fin (C.stage k).part.R), ((C.stage k).part.cell i).indicator ∈ W) :
    Dense (W : Set (L 𝕜 r)) := by
  rw [dense_iff_closure_eq]
  change (↑W.topologicalClosure : Set (L 𝕜 r)) = Set.univ
  have he : W.topologicalClosure = ⊤ := eq_top_of_closed_contains_intervals hr _
    (Submodule.isClosed_topologicalClosure _) (fun D => by
      apply (Submodule.isClosed_topologicalClosure W).mem_of_tendsto (C.insideUnion_indicator_tendsto hr D)
      exact Eventually.of_forall fun k => Submodule.le_topologicalClosure _
        ((C.stage k).part.insideUnion_indicator_mem D W (hW k)))
  rw [he]
  rfl

theorem rawVector_dense : Dense (Submodule.span 𝕜 (Set.range C.rawVector) : Set (L 𝕜 p)) :=
  C.stage_cells_dense C.hpfin _ C.stage_cell_mem_rawVector_span

theorem rawCoefficient_dense (hq : q ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range C.rawCoefficient) : Set (L 𝕜 q)) :=
  C.stage_cells_dense hq _ C.stage_cell_mem_rawCoefficient_span

end ConstructionData
end PositiveBiorthogonal
