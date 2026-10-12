import Lean_Code.PositiveBiorthogonal.BatchScale

/-! The active-region indicator, with its exact finite-step and norm interpretations. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal
namespace ActivePartition

theorem active_measure_ne_top (P : ActivePartition) : volume P.active ≠ ∞ :=
  measure_biUnion_ne_top P.units.finite_toSet (fun n _ => (gridUnit n).measure_ne_top)

theorem cell_subset_active (P : ActivePartition) (i : Fin P.R) : (P.cell i).carrier ⊆ P.active := by
  rw [active, ← P.cover]
  exact subset_iUnion (fun j => (P.cell j).carrier) i

theorem active_volume_pos (P : ActivePartition) : 0 < volume P.active :=
  ((P.cell ⟨0, P.R_pos⟩).volume_pos).trans_le (measure_mono (P.cell_subset_active _))

theorem active_volume_real_pos (P : ActivePartition) : 0 < volume.real P.active :=
  ENNReal.toReal_pos P.active_volume_pos.ne' P.active_measure_ne_top

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

def indicator (P : ActivePartition) : L 𝕜 p :=
  indicatorConstLp p P.active_measurable P.active_measure_ne_top 1

theorem coe_indicator (P : ActivePartition) :
    ((P.indicator : L 𝕜 p) : ℝ → 𝕜) =ᵐ[volume] P.active.indicator (fun _ => 1) :=
  indicatorConstLp_coeFn (p := p) (hs := P.active_measurable)
    (hμs := P.active_measure_ne_top) (c := (1 : 𝕜))

theorem indicator_sum (P : ActivePartition) :
    (P.indicator : L 𝕜 p) = ∑ i : Fin P.R, (P.cell i).indicator := by
  apply Lp.ext
  have he := P.cell_sum_coe (p := p) (fun _ => (1 : 𝕜))
  simp only [one_smul] at he
  filter_upwards [P.coe_indicator (𝕜 := 𝕜) (p := p), he] with x hx hs
  rw [hx, hs]
  by_cases ha : x ∈ P.active
  · have hu : x ∈ ⋃ i : Fin P.R, (P.cell i).carrier := by rw [P.cover]; exact ha
    obtain ⟨i, hi⟩ := mem_iUnion.mp hu
    rw [P.cell_sum_on_cell (fun _ => (1 : 𝕜)) i x hi]
    simp [ha]
  · rw [P.cell_sum_off_active (fun _ => (1 : 𝕜)) x ha]
    simp [ha]

theorem indicator_step (P : ActivePartition) : CompactlySupportedStep (P.indicator : L 𝕜 p) := by
  rw [P.indicator_sum]
  exact step_finset_sum _ _ (fun i _ => (P.cell i).indicator_step)

theorem indicator_nonnegative (P : ActivePartition) : Nonnegative (P.indicator : L 𝕜 p) := by
  filter_upwards [P.coe_indicator (𝕜 := 𝕜) (p := p)] with x hx
  rw [hx]
  by_cases ha : x ∈ P.active <;> simp [ha]

theorem indicator_supported (P : ActivePartition) :
    ∀ᵐ x : ℝ, x ∉ P.active → (P.indicator : L 𝕜 p) x = 0 := by
  filter_upwards [P.coe_indicator (𝕜 := 𝕜) (p := p)] with x hx
  intro ha
  simp [hx, ha]

theorem pairing_indicator (P : ActivePartition) (f : L 𝕜 p) :
    pairing f (P.indicator : L 𝕜 q) = ∫ x in P.active, f x := by
  unfold pairing
  rw [← integral_indicator P.active_measurable]
  apply integral_congr_ae
  filter_upwards [P.coe_indicator (𝕜 := 𝕜) (p := q)] with x hx
  rw [hx]
  by_cases ha : x ∈ P.active <;> simp [ha]

theorem indicator_norm_top (P : ActivePartition) : ‖(P.indicator : L 𝕜 ∞)‖ = 1 :=
  PositiveBiorthogonal.indicator_top_norm _ _ _ P.active_volume_pos.ne'

theorem indicator_norm [Fact (1 ≤ p)] (P : ActivePartition) :
    ‖(P.indicator : L 𝕜 p)‖ = (volume.real P.active) ^ (1 / p.toReal) := by
  by_cases hp : p = ∞
  · subst p
    simp [P.indicator_norm_top]
  · exact PositiveBiorthogonal.indicator_norm _ _ _
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp

end ActivePartition
end PositiveBiorthogonal
