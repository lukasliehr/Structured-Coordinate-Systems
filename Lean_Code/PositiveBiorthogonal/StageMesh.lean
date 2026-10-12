import Lean_Code.PositiveBiorthogonal.Stages

/-! Each already active grid unit has geometrically decreasing cell lengths. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace PositiveBiorthogonal

theorem IntervalCell.length_mono {D E : IntervalCell} (h : D.carrier ⊆ E.carrier) : D.length ≤ E.length := by
  rw [← D.volume_real, ← E.volume_real]
  exact measureReal_mono h E.measure_ne_top

theorem ActivePartition.gridUnit_subset_active (P : ActivePartition) (z : ℤ) (hz : z ∈ P.units) :
    (gridUnit z).carrier ⊆ P.active := by
  intro x hx
  exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hx⟩⟩

theorem prefixUnits_mono : Monotone prefixUnits := by
  intro a b hab
  exact Finset.image_subset_image (Finset.range_mono hab)

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

theorem stage_units_mono : Monotone (fun k => (C.stage k).part.units) := by
  intro k l hkl
  change (C.stage k).part.units ⊆ (C.stage l).part.units
  rw [(C.stage k).units_eq, (C.stage l).units_eq]
  exact prefixUnits_mono (C.stage_activeCount_strictMono.monotone hkl)

theorem stage_mesh_step (k : ℕ) (z : ℤ) (hz : z ∈ (C.stage k).part.units) (B : ℝ)
    (hB : ∀ i : Fin (C.stage k).part.R, ((C.stage k).part.cell i).carrier ⊆ (gridUnit z).carrier →
      ((C.stage k).part.cell i).length ≤ B)
    (i : Fin (C.stage (k + 1)).part.R)
    (hi : ((C.stage (k + 1)).part.cell i).carrier ⊆ (gridUnit z).carrier) :
    ((C.stage (k + 1)).part.cell i).length ≤ (2 / 3 : ℝ) * B := by
  have hcases := StageState.extendAfter_old_cell (S := C.stage k) (C.trace k) rfl i
  change (∃ j : Fin ((C.trace k).state (Fin.last (C.batchSize k))).R,
      (C.stage (k + 1)).part.cell i = ((C.trace k).state (Fin.last (C.batchSize k))).cell j) ∨
    ∃ j : Fin (2 * C.batchSize k), (C.stage (k + 1)).part.cell i = (C.fresh k).cell j at hcases
  rcases hcases with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hfinal := splittingSchedule_final_cells (C.stage k).part (C.steps k) (C.steps_ge_two k) j
    change ∃ l : Fin (C.stage k).part.R,
      (((C.trace k).state (Fin.last (C.batchSize k))).cell j).carrier ⊆ ((C.stage k).part.cell l).carrier ∧
      (((C.trace k).state (Fin.last (C.batchSize k))).cell j).length ≤
        (2 / 3 : ℝ) * ((C.stage k).part.cell l).length at hfinal
    obtain ⟨l, hl, hlen⟩ := hfinal
    rw [hj] at hi ⊢
    obtain ⟨u, hu, hU⟩ := (C.stage k).part.in_grid l
    have huz : u = z := by
      by_contra hne
      let D := ((C.trace k).state (Fin.last (C.batchSize k))).cell j
      have hx : D.right ∈ D.carrier := ⟨D.proper, le_rfl⟩
      exact Set.disjoint_left.mp (gridUnit_disjoint hne) (hU (hl hx)) (hi hx)
    subst u
    exact hlen.trans (mul_le_mul_of_nonneg_left (hB l hU) (by norm_num))
  · let D := (C.stage (k + 1)).part.cell i
    have hx : D.right ∈ D.carrier := ⟨D.proper, le_rfl⟩
    have hxF : D.right ∈ (C.fresh k).carrier := (C.fresh k).cell_subset j (by simpa [D, hj] using hx)
    have hxA : D.right ∈ (C.stage k).part.active :=
      (C.stage k).part.gridUnit_subset_active z hz (hi hx)
    exact False.elim (Set.disjoint_left.mp (C.fresh_disjoint k) hxF hxA)

theorem stage_mesh_decay (k₀ r : ℕ) (z : ℤ) (hz : z ∈ (C.stage k₀).part.units)
    (i : Fin (C.stage (k₀ + r)).part.R)
    (hi : ((C.stage (k₀ + r)).part.cell i).carrier ⊆ (gridUnit z).carrier) :
    ((C.stage (k₀ + r)).part.cell i).length ≤ (2 / 3 : ℝ) ^ r := by
  induction r with
  | zero =>
    have h := IntervalCell.length_mono hi
    simpa [gridUnit, IntervalCell.length] using h
  | succ r ih =>
    have hz' := C.stage_units_mono (Nat.le_add_right k₀ r) hz
    have h := C.stage_mesh_step (k₀ + r) z hz' ((2 / 3 : ℝ) ^ r) (fun j hj => ih j hj) i hi
    change ((C.stage (k₀ + (r + 1))).part.cell i).length ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ r at h
    exact h.trans_eq (by rw [pow_succ]; ring)

theorem mesh_decay_tendsto_zero : Tendsto (fun r : ℕ => (2 / 3 : ℝ) ^ r) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end ConstructionData
end PositiveBiorthogonal
