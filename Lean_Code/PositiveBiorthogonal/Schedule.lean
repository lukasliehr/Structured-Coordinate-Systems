import Lean_Code.PositiveBiorthogonal.ScheduleState
import Lean_Code.PositiveBiorthogonal.HaarNorms

/-! The prescribed schedule: L consecutive geometric splits of each original cell. -/
noncomputable section
set_option autoImplicit false
open Set
namespace PositiveBiorthogonal

def scheduleVisit (P : ActivePartition) (L n : ℕ) : Fin P.R :=
  ⟨(n / L) % P.R, Nat.mod_lt _ P.R_pos⟩

theorem scheduleVisit_val (P : ActivePartition) {L n : ℕ} (hL : 0 < L)
    (hn : n < P.R * L) : (scheduleVisit P L n).val = n / L := by
  exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hL).mpr hn)

theorem scheduleVisit_eq_iff (P : ActivePartition) {L n : ℕ} (hL : 0 < L)
    (hn : n < P.R * L) (i : Fin P.R) :
    scheduleVisit P L n = i ↔ i.val * L ≤ n ∧ n < (i.val + 1) * L := by
  rw [Fin.ext_iff, scheduleVisit_val P hL hn]
  constructor
  · intro he
    constructor
    · simpa [he] using Nat.div_mul_le_self n L
    · exact (Nat.div_lt_iff_lt_mul hL).mp (by omega)
  · rintro ⟨hlo, hhi⟩
    exact Nat.div_eq_of_lt_le hlo hhi

theorem scheduleVisit_count (P : ActivePartition) {L n : ℕ} (hL : 0 < L)
    (hn : n ≤ P.R * L) (i : Fin P.R) :
    ((Finset.range n).filter (fun k => scheduleVisit P L k = i)).card =
      min n ((i.val + 1) * L) - i.val * L := by
  classical
  have he : (Finset.range n).filter (fun k => scheduleVisit P L k = i) =
      Finset.Ico (i.val * L) (min n ((i.val + 1) * L)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨hk, hi⟩
      obtain ⟨ha, hb⟩ := (scheduleVisit_eq_iff P hL (lt_of_lt_of_le hk hn) i).mp hi
      exact ⟨ha, hk, hb⟩
    · rintro ⟨ha, hk, hb⟩
      exact ⟨hk, (scheduleVisit_eq_iff P hL (lt_of_lt_of_le hk hn) i).mpr ⟨ha, hb⟩⟩
  rw [he, Nat.card_Ico]

theorem scheduleVisit_final_count (P : ActivePartition) {L : ℕ} (hL : 0 < L)
    (i : Fin P.R) :
    ((Finset.range (P.R * L)).filter (fun k => scheduleVisit P L k = i)).card = L := by
  rw [scheduleVisit_count P hL le_rfl]
  have hi : (i.val + 1) * L ≤ P.R * L := Nat.mul_le_mul_right L i.isLt
  rw [min_eq_right hi, Nat.add_mul, Nat.one_mul]
  omega

theorem scheduleVisit_current_count (P : ActivePartition) {L n : ℕ} (hL : 0 < L)
    (hn : n < P.R * L) :
    ((Finset.range n).filter (fun k => scheduleVisit P L k = scheduleVisit P L n)).card = n % L := by
  rw [scheduleVisit_count P hL hn.le, scheduleVisit_val P hL hn]
  have hu : n < (n / L + 1) * L :=
    (Nat.div_lt_iff_lt_mul hL).mp (Nat.lt_succ_self (n / L))
  rw [min_eq_left hu.le]
  have hd := Nat.mod_add_div' n L
  omega

def splittingSchedule (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L) : RefinementTrace (P.R * L) where
  state t := (GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
    (splitTheta_lt_one L hL) (scheduleVisit P L) t.val).part
  split j := geometricSplit (P.cell (scheduleVisit P L j.val)) (splitTheta L)
    (splitTheta_pos L hL) (splitTheta_lt_one L hL)
    ((GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
      (splitTheta_lt_one L hL) (scheduleVisit P L) j.val).count (scheduleVisit P L j.val))
  index j := (GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
    (splitTheta_lt_one L hL) (scheduleVisit P L) j.val).root (scheduleVisit P L j.val)
  parent j := ((GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
    (splitTheta_lt_one L hL) (scheduleVisit P L) j.val).root_cell (scheduleVisit P L j.val)).symm
  next j := rfl

@[simp] theorem splittingSchedule_initial (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L) :
    (splittingSchedule P L hL).state 0 = P := rfl

theorem splittingSchedule_split (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin (P.R * L)) :
    (splittingSchedule P L hL).split j =
      geometricSplit (P.cell (scheduleVisit P L j.val)) (splitTheta L)
        (splitTheta_pos L hL) (splitTheta_lt_one L hL) (j.val % L) := by
  dsimp [splittingSchedule]
  rw [GeometricState.run_count, scheduleVisit_current_count P (by omega) j.isLt]

theorem splittingSchedule_count (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (t : Fin (P.R * L + 1)) :
    ((splittingSchedule P L hL).state t).R = P.R + t.val :=
  (GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
    (splitTheta_lt_one L hL) (scheduleVisit P L) t.val).count_eq

theorem splittingSchedule_final_count (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L) :
    ((splittingSchedule P L hL).state (Fin.last (P.R * L))).R = P.R * (L + 1) := by
  rw [splittingSchedule_count]
  simp only [Fin.val_last]
  ring

theorem splittingSchedule_parent_lower (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin (P.R * L)) :
    P.minLength / 2 ≤ ((splittingSchedule P L hL).split j).parent.length := by
  rw [splittingSchedule_split]
  exact (div_le_div_of_nonneg_right (P.minLength_le _) (by norm_num)).trans
    (schedule_parent_lower _ L hL _ (Nat.mod_lt _ (by omega)).le)

theorem splittingSchedule_left_length (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin (P.R * L)) :
    ((splittingSchedule P L hL).split j).leftChild.length =
      splitTheta L * ((splittingSchedule P L hL).split j).parent.length := by
  rw [splittingSchedule_split, geometricSplit_left_length]

theorem splittingSchedule_right_length (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin (P.R * L)) :
    ((splittingSchedule P L hL).split j).rightChild.length =
      (1 - splitTheta L) * ((splittingSchedule P L hL).split j).parent.length := by
  rw [splittingSchedule_split, geometricSplit_right_length]

theorem splittingSchedule_final_cells (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin ((splittingSchedule P L hL).state (Fin.last (P.R * L))).R) :
    ∃ i : Fin P.R,
      (((splittingSchedule P L hL).state (Fin.last (P.R * L))).cell j).carrier ⊆ (P.cell i).carrier ∧
      (((splittingSchedule P L hL).state (Fin.last (P.R * L))).cell j).length ≤
        (2 / 3 : ℝ) * (P.cell i).length := by
  let S := GeometricState.run P (splitTheta L) (splitTheta_pos L hL)
    (splitTheta_lt_one L hL) (scheduleVisit P L) (P.R * L)
  change ∃ i : Fin P.R, (S.part.cell j).carrier ⊆ (P.cell i).carrier ∧
    (S.part.cell j).length ≤ (2 / 3 : ℝ) * (P.cell i).length
  rcases S.cell_cases j with ⟨i, rfl⟩ | ⟨i, k, hk⟩
  · refine ⟨i, ?_⟩
    rw [S.root_cell]
    have hc : S.count i = L := by
      dsimp [S]
      rw [GeometricState.run_count, scheduleVisit_final_count P (by omega)]
    rw [hc]
    exact ⟨geometricSplit_parent_subset _ _ _ _ _, schedule_final_remainder_upper _ L hL⟩
  · refine ⟨i, ?_⟩
    rw [hk]
    refine ⟨(IntervalSplit.left_subset _).trans (geometricSplit_parent_subset _ _ _ _ _), ?_⟩
    have hu := schedule_removed_upper (P.cell i) L hL k
    have hp := (P.cell i).length_pos
    linarith

theorem splittingSchedule_mesh (P : ActivePartition) (L : ℕ) (hL : 2 ≤ L)
    (j : Fin ((splittingSchedule P L hL).state (Fin.last (P.R * L))).R)
    (i : Fin P.R)
    (hi : (((splittingSchedule P L hL).state (Fin.last (P.R * L))).cell j).carrier ⊆
      (P.cell i).carrier) :
    (((splittingSchedule P L hL).state (Fin.last (P.R * L))).cell j).length ≤
      (2 / 3 : ℝ) * (P.cell i).length := by
  obtain ⟨k, hk, hb⟩ := splittingSchedule_final_cells P L hL j
  suffices k = i by simpa [this] using hb
  by_contra hki
  let D := ((splittingSchedule P L hL).state (Fin.last (P.R * L))).cell j
  have hx : D.right ∈ D.carrier := ⟨D.proper, le_rfl⟩
  exact Set.disjoint_left.mp (P.disjoint hki) (hk hx) (hi hx)

end PositiveBiorthogonal
