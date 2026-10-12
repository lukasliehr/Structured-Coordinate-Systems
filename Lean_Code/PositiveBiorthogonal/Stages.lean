import Lean_Code.PositiveBiorthogonal.StageState

/-! The actual least-choice stage recursion, with cumulative counts and local operators. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace PositiveBiorthogonal

structure ConstructionData (𝕜 : Type*) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] where
  hpfin : p ≠ ∞
  δ : ℝ
  δ_pos : 0 < δ
  η : ℝ
  η_pos : 0 < η
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_lt_one : ρ < 1
  aux : AuxiliaryFamily 𝕜 p q δ

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  (C : ConstructionData 𝕜 p q)

def tolerance (k : ℕ) : ℝ := C.ρ * (1 / 2 : ℝ) ^ (k + 1)

theorem tolerance_pos (k : ℕ) : 0 < C.tolerance k :=
  mul_pos C.ρ_pos (pow_pos (by norm_num) _)

def chooseSteps (P : ActivePartition) (k : ℕ) : ℕ :=
  Nat.find (C.aux.exists_small_splitting P C.η (C.tolerance k) (C.tolerance_pos k))

theorem chooseSteps_spec (P : ActivePartition) (k : ℕ) :
    2 ≤ C.chooseSteps P k ∧ C.aux.correctionSize P C.η (C.chooseSteps P k) < C.tolerance k :=
  Nat.find_spec (C.aux.exists_small_splitting P C.η (C.tolerance k) (C.tolerance_pos k))

theorem chooseSteps_min (P : ActivePartition) (k steps : ℕ)
    (hs : 2 ≤ steps) (hb : C.aux.correctionSize P C.η steps < C.tolerance k) :
    C.chooseSteps P k ≤ steps := Nat.find_min' _ ⟨hs, hb⟩

def nextState (k : ℕ) (S : StageState) : StageState :=
  S.extendAfter (splittingSchedule S.part (C.chooseSteps S.part k) (C.chooseSteps_spec S.part k).1) rfl

def stage : ℕ → StageState
  | 0 => initialStage
  | k + 1 => C.nextState k (stage k)

def steps (k : ℕ) : ℕ := C.chooseSteps (C.stage k).part k
def batchSize (k : ℕ) : ℕ := (C.stage k).part.R * C.steps k

theorem steps_ge_two (k : ℕ) : 2 ≤ C.steps k := (C.chooseSteps_spec _ _).1

theorem batchSize_ge_two (k : ℕ) : 2 ≤ C.batchSize k := by
  have hR := (C.stage k).part.R_pos
  have hL := C.steps_ge_two k
  unfold batchSize
  nlinarith

def trace (k : ℕ) : RefinementTrace (C.batchSize k) :=
  splittingSchedule (C.stage k).part (C.steps k) (C.steps_ge_two k)

@[simp] theorem trace_initial (k : ℕ) : (C.trace k).state 0 = (C.stage k).part := rfl

def fresh (k : ℕ) : UnitBlock (2 * C.batchSize k) := (C.stage k).fresh (2 * C.batchSize k)
def scale (k : ℕ) : ℝ := C.aux.batchScale (C.stage k).part (C.steps k) C.η

theorem scale_pos (k : ℕ) : 0 < C.scale k :=
  C.aux.batchScale_pos _ _ (C.steps_ge_two k) _ C.η_pos

theorem fresh_disjoint (k : ℕ) : Disjoint (C.fresh k).carrier (C.stage k).part.active :=
  (C.stage k).fresh_disjoint _

@[simp] theorem stage_activeCount_zero : (C.stage 0).activeCount = 1 := rfl
@[simp] theorem stage_totalCount_zero : (C.stage 0).totalCount = 1 := rfl

theorem stage_activeCount_succ (k : ℕ) :
    (C.stage (k + 1)).activeCount = (C.stage k).activeCount + 2 * C.batchSize k := rfl

theorem stage_totalCount_succ (k : ℕ) :
    (C.stage (k + 1)).totalCount = (C.stage k).totalCount + 3 * C.batchSize k := rfl

theorem stage_activeCount_strictMono : StrictMono (fun k => (C.stage k).activeCount) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [C.stage_activeCount_succ]
  have h := C.batchSize_ge_two k
  omega

theorem stage_totalCount_strictMono : StrictMono (fun k => (C.stage k).totalCount) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [C.stage_totalCount_succ]
  have h := C.batchSize_ge_two k
  omega

theorem stage_activeCount_lower (k : ℕ) : k + 1 ≤ (C.stage k).activeCount := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [C.stage_activeCount_succ]
    have h := C.batchSize_ge_two k
    omega

theorem stage_totalCount_lower (k : ℕ) : k + 1 ≤ (C.stage k).totalCount := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [C.stage_totalCount_succ]
    have h := C.batchSize_ge_two k
    omega

theorem stage_unit_eventually (z : ℤ) : ∀ᶠ k in atTop, z ∈ (C.stage k).part.units := by
  obtain ⟨i, rfl⟩ := gridEnumeration_surjective z
  filter_upwards [eventually_ge_atTop i] with k hk
  rw [(C.stage k).units_eq]
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (by have h := C.stage_activeCount_lower k; omega), rfl⟩

theorem fresh_pairwise_disjoint : Pairwise (fun k l => Disjoint (C.fresh k).carrier (C.fresh l).carrier) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · apply enumerated_blocks_disjoint
    rw [← C.stage_activeCount_succ]
    exact C.stage_activeCount_strictMono.monotone h
  · apply Disjoint.symm
    apply enumerated_blocks_disjoint
    rw [← C.stage_activeCount_succ]
    exact C.stage_activeCount_strictMono.monotone h

theorem stage_active_succ (k : ℕ) :
    (C.stage (k + 1)).part.active = (C.stage k).part.active ∪ (C.fresh k).carrier :=
  (C.stage k).extendAfter_active (C.trace k) rfl

theorem stage_active_mono : Monotone (fun k => (C.stage k).part.active) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [C.stage_active_succ]
  exact subset_union_left

theorem stage_cell_count_succ (k : ℕ) :
    (C.stage (k + 1)).part.R = (C.stage k).part.R * (C.steps k + 1) + 2 * C.batchSize k := by
  exact congrArg (fun n : ℕ => n + 2 * C.batchSize k)
    (splittingSchedule_final_count (C.stage k).part (C.steps k) (C.steps_ge_two k))

def localS (k : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  PositiveBiorthogonal.localS (q := q) (C.stage k).part ((C.fresh k).transfer (C.aux.z (C.batchSize k)))
    (C.scale k * splitTheta (C.steps k))

def localR (k : ℕ) : L 𝕜 q →L[𝕜] L 𝕜 q :=
  PositiveBiorthogonal.localR (C.stage k).part ((C.fresh k).transfer (C.aux.z (C.batchSize k)))
    (C.scale k * splitTheta (C.steps k))

theorem local_norms_lt (k : ℕ) : ‖C.localS k‖ < C.tolerance k ∧ ‖C.localR k‖ < C.tolerance k := by
  have hnorm := C.aux.local_correction_norms (C.stage k).part C.η C.η_pos (C.steps k)
    (C.steps_ge_two k) (C.fresh k)
  have hb := (C.chooseSteps_spec (C.stage k).part k).2
  exact ⟨hnorm.1.trans_lt hb, hnorm.2.trans_lt hb⟩

theorem local_paired (k : ℕ) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing (C.localS k f) g = pairing f (C.localR k g) :=
  local_corrections_paired _ _ _ f g

def batchVectors (k : ℕ) : Fin (3 * C.batchSize k) → L 𝕜 p :=
  C.aux.batchVectors (C.trace k) (C.fresh k) (C.scale k : 𝕜)

def batchCoefficients (k : ℕ) : Fin (3 * C.batchSize k) → L 𝕜 q :=
  C.aux.batchCoefficients (C.trace k) (C.fresh k) (C.scale k : 𝕜)

theorem batch_biorthogonal (k : ℕ) (i j : Fin (3 * C.batchSize k)) :
    pairing (C.batchVectors k i) (C.batchCoefficients k j) = if i = j then 1 else 0 :=
  C.aux.batch_biorthogonal (lt_of_lt_of_le (by decide : 0 < 2) (C.batchSize_ge_two k))
    (C.trace k) (C.fresh k) (C.fresh_disjoint k) _ i j

theorem batch_bound (k t : ℕ) (ht : t ≤ 3 * C.batchSize k) :
    ‖(C.stage k).part.averageCLM (q := q) + lpPrefix (C.batchVectors k) (C.batchCoefficients k) t‖ ≤
      1 + C.δ + C.η :=
  C.aux.scheduled_batch_bound C.hpfin C.δ_pos.le (C.stage k).part (C.steps k) (C.steps_ge_two k)
    (C.fresh k) (C.fresh_disjoint k) C.η C.η_pos t ht

end ConstructionData
end PositiveBiorthogonal
