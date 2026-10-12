import Lean_Code.PositiveBiorthogonal.RawBiorthogonal

/-! Stage-cell membership in both finite raw spans. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem initialProjection_paired (v : ℕ → L 𝕜 p) (g : ℕ → L 𝕜 q)
    (n : ℕ) (f : L 𝕜 p) (h : L 𝕜 q) :
    pairing (initialProjection v (fun i => representedFunctional (g i)) n f) h =
      pairing f (initialProjection g (fun i => representedFunctional (v i)) n h) := by
  rw [← representedFunctional_apply, initialProjection_apply, map_sum,
    ← pairingCLM_apply, initialProjection_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pairing_comm, mul_comm]

theorem ActivePartition.averageCLM_paired (P : ActivePartition) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing (P.averageCLM (q := q) f) g = pairing f (P.averageCLM (q := p) g) := by
  rw [← representedFunctional_apply, P.averageCLM_apply, ActivePartition.average, map_sum,
    ← pairingCLM_apply, P.averageCLM_apply, ActivePartition.average, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, representedFunctional_apply, pairingCLM_apply, smul_eq_mul,
    IntervalCell.pairing_indicator, pairing_comm ((P.cell i).indicator : L 𝕜 p) g]
  ring

theorem initialProjection_mem_span (v : ℕ → L 𝕜 p) (c : ℕ → L 𝕜 p →L[𝕜] 𝕜)
    (n : ℕ) (f : L 𝕜 p) :
    initialProjection v c n f ∈ Submodule.span 𝕜 (Set.range v) := by
  rw [initialProjection_apply]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

theorem ActivePartition.gridUnit_cellwise (P : ActivePartition) (z : ℤ) (hz : z ∈ P.units) :
    P.Cellwise ((gridUnit z).indicator : L 𝕜 p) := by
  classical
  apply (P.cellwise_iff_ae_constant _).mpr
  refine ⟨fun i => if (P.cell i).carrier ⊆ (gridUnit z).carrier then 1 else 0, ?_⟩
  filter_upwards [(gridUnit z).coe_indicator (𝕜 := 𝕜) (p := p)] with x hx
  rw [hx]
  constructor
  · intro i hi
    by_cases hsub : (P.cell i).carrier ⊆ (gridUnit z).carrier
    · simp [hsub, hsub hi]
    · obtain ⟨u, hu, hU⟩ := P.in_grid i
      have huz : u ≠ z := by intro h; subst u; exact hsub hU
      have hxz : x ∉ (gridUnit z).carrier := fun h =>
        Set.disjoint_left.mp (gridUnit_disjoint huz) (hU hi) h
      simp [hsub, hxz]
  · intro ha
    have hxz : x ∉ (gridUnit z).carrier := fun h => ha (P.gridUnit_subset_active z hz h)
    simp [hxz]

namespace ConstructionData
variable (C : ConstructionData 𝕜 p q)

def rawDualProjection (n : ℕ) : L 𝕜 q →L[𝕜] L 𝕜 q :=
  initialProjection C.rawCoefficient (fun i => representedFunctional (C.rawVector i)) n

theorem rawDualProjection_stage (k : ℕ) :
    C.rawDualProjection (C.stage k).totalCount = (C.stage k).part.averageCLM (q := p) := by
  apply ContinuousLinearMap.ext
  intro g
  apply sub_eq_zero.mp
  apply pairing_separates_right (p := p)
  intro f
  rw [pairing_sub_right]
  apply sub_eq_zero.mpr
  change pairing f (initialProjection C.rawCoefficient
    (fun i => representedFunctional (C.rawVector i)) (C.stage k).totalCount g) = _
  rw [← initialProjection_paired]
  change pairing (C.rawProjection (C.stage k).totalCount f) g = _
  rw [C.rawProjection_stage, ActivePartition.averageCLM_paired]

theorem stage_cell_mem_rawVector_span (k : ℕ) (i : Fin (C.stage k).part.R) :
    ((C.stage k).part.cell i).indicator ∈ Submodule.span 𝕜 (Set.range C.rawVector) := by
  rw [← (C.stage k).part.averageCLM_indicator (q := q) i, ← C.rawProjection_stage]
  exact initialProjection_mem_span _ _ _ _

theorem stage_cell_mem_rawCoefficient_span (k : ℕ) (i : Fin (C.stage k).part.R) :
    ((C.stage k).part.cell i).indicator ∈ Submodule.span 𝕜 (Set.range C.rawCoefficient) := by
  rw [← (C.stage k).part.averageCLM_indicator (q := p) i, ← C.rawDualProjection_stage]
  exact initialProjection_mem_span _ _ _ _

theorem gridUnit_mem_rawVector_span (z : ℤ) :
    (gridUnit z).indicator ∈ Submodule.span 𝕜 (Set.range C.rawVector) := by
  obtain ⟨k, hk⟩ := (C.stage_unit_eventually z).exists
  have he := (C.stage k).part.averageCLM_fixed_of_cellwise (q := q) _
    ((C.stage k).part.gridUnit_cellwise (𝕜 := 𝕜) (p := p) z hk)
  rw [← he, ← C.rawProjection_stage]
  exact initialProjection_mem_span _ _ _ _

theorem gridUnit_mem_rawCoefficient_span (z : ℤ) :
    (gridUnit z).indicator ∈ Submodule.span 𝕜 (Set.range C.rawCoefficient) := by
  obtain ⟨k, hk⟩ := (C.stage_unit_eventually z).exists
  have he := (C.stage k).part.averageCLM_fixed_of_cellwise (q := p) _
    ((C.stage k).part.gridUnit_cellwise (𝕜 := 𝕜) (p := q) z hk)
  rw [← he, ← C.rawDualProjection_stage]
  exact initialProjection_mem_span _ _ _ _

end ConstructionData
end PositiveBiorthogonal
