import Lean_Code.SchauderTranslates.Lp.InitialCells
import Mathlib.Data.List.OfFn

noncomputable section
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def permanentIntervals {p : ℝ≥0∞} (cs : List (PermanentCell p)) : Finset (ℝ × ℝ) := by
  classical
  exact cs.toFinset.biUnion PermanentCell.intervals

theorem permanentIntervals_mem {p : ℝ≥0∞} (cs : List (PermanentCell p)) (ab : ℝ × ℝ) :
    ab ∈ permanentIntervals cs ↔ ∃ c ∈ cs, ab ∈ c.intervals := by
  classical
  simp [permanentIntervals]

theorem permanentSupport_eq_intervalUnion {p : ℝ≥0∞} (cs : List (PermanentCell p)) :
    permanentSupport cs = finiteIntervalUnion (permanentIntervals cs) := by
  ext x
  simp only [permanentSupport, finiteIntervalUnion, Set.mem_iUnion,
    permanentIntervals_mem, PermanentCell.support_eq_intervalUnion]
  constructor
  · rintro ⟨c, hc, ab, hab, hx⟩
    exact ⟨ab, ⟨c, hc, hab⟩, hx⟩
  · rintro ⟨ab, ⟨c, hc, hab⟩, hx⟩
    exact ⟨c, hc, ab, hab, hx⟩

theorem permanentIntervals_positive {p : ℝ≥0∞} (cs : List (PermanentCell p))
    {ab : ℝ × ℝ} (hab : ab ∈ permanentIntervals cs) : ab.1 < ab.2 := by
  obtain ⟨c, hc, hab⟩ := (permanentIntervals_mem cs ab).mp hab
  exact c.intervals_positive hab

def fillerCells (p : ℝ≥0∞) (s : Finset (ℝ × ℝ)) (l u : ℝ) : List (PermanentCell p) :=
  (remainingIntervals s l u).attach.toList.map (fun ab =>
    .ordinary ab.val (remainingIntervals_positive s l u ab.property))

theorem fillerCells_mem (p : ℝ≥0∞) (s : Finset (ℝ × ℝ)) (l u : ℝ) (c : PermanentCell p) :
    c ∈ fillerCells p s l u ↔ ∃ ab : ↥(remainingIntervals s l u),
      c = .ordinary ab.val (remainingIntervals_positive s l u ab.property) := by
  simp only [fillerCells, List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
  exact exists_congr (fun ab => eq_comm)

theorem fillerCells_support (p : ℝ≥0∞) (s : Finset (ℝ × ℝ)) (l u : ℝ) :
    permanentSupport (fillerCells p s l u) = finiteIntervalUnion (remainingIntervals s l u) := by
  ext x
  simp only [permanentSupport, finiteIntervalUnion, Set.mem_iUnion, fillerCells_mem]
  constructor
  · rintro ⟨c, ⟨ab, rfl⟩, hx⟩
    exact ⟨ab.val, ab.property, hx⟩
  · rintro ⟨ab, hab, hx⟩
    exact ⟨.ordinary ab (remainingIntervals_positive s l u hab), ⟨⟨ab, hab⟩, rfl⟩, hx⟩

theorem fillerCells_disjoint (p : ℝ≥0∞) (s : Finset (ℝ × ℝ)) (l u : ℝ) :
    List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support)
      (fillerCells p s l u) := by
  rw [fillerCells, List.pairwise_map]
  apply List.Pairwise.imp (fun {ab cd} hne => ?_)
    (List.nodup_iff_pairwise_ne.mp (Finset.nodup_toList (remainingIntervals s l u).attach))
  exact remainingIntervals_pairwise_disjoint s l u ab.property cd.property
    (fun he => hne (Subtype.ext he))

def completeCells {p : ℝ≥0∞} (cs : List (PermanentCell p)) (R : ℝ) : List (PermanentCell p) :=
  cs ++ fillerCells p (permanentIntervals cs) (-R) R

theorem completeCells_prefix {p : ℝ≥0∞} (cs : List (PermanentCell p)) (R : ℝ) :
    cs <+: completeCells cs R := List.prefix_append _ _

theorem completeCells_disjoint {p : ℝ≥0∞} (cs : List (PermanentCell p)) (R : ℝ)
    (hcs : List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) cs) :
    List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) (completeCells cs R) := by
  rw [completeCells, List.pairwise_append]
  refine ⟨hcs, fillerCells_disjoint p _ _ _, ?_⟩
  intro c hc d hd
  obtain ⟨ab, rfl⟩ := (fillerCells_mem p _ _ _ d).mp hd
  apply (remainingIntervals_disjoint_old _ _ _ ab.property).symm.mono_left
  intro x hx
  rw [← permanentSupport_eq_intervalUnion]
  exact Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩

/-- Complete a finite permanent-cell family without changing any old cell. -/
theorem completeCells_partition {p : ℝ≥0∞} (cs : List (PermanentCell p)) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ ab ∈ permanentIntervals cs, -R ≤ ab.1 ∧ ab.2 ≤ R) :
    permanentSupport (completeCells cs R) = Set.Ico (-R) R := by
  rw [completeCells, permanentSupport_append, fillerCells_support, permanentSupport_eq_intervalUnion]
  apply finite_interval_allocation _ (by linarith)
  intro ab hab
  exact ⟨(hbound ab hab).1, (permanentIntervals_positive cs hab).le, (hbound ab hab).2⟩

/-- A radius for every endpoint of a finite family. This does not replace
the private supports by their enclosing intervals in the cell partition. -/
theorem permanentIntervals_bounded {p : ℝ≥0∞} (cs : List (PermanentCell p)) (r : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ r ≤ R ∧ ∀ ab ∈ permanentIntervals cs, -R ≤ ab.1 ∧ ab.2 ≤ R := by
  let s := permanentIntervals cs
  let B : ℝ := ∑ ab ∈ s, (|ab.1| + |ab.2|)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨B + |r|, by positivity, ?_, ?_⟩
  · exact (le_abs_self r).trans (by linarith)
  · intro ab hab
    have hsingle : |ab.1| + |ab.2| ≤ B := Finset.single_le_sum
      (f := fun cd : ℝ × ℝ => |cd.1| + |cd.2|) (s := s)
      (fun cd _ => add_nonneg (abs_nonneg cd.1) (abs_nonneg cd.2)) hab
    have hleft := neg_abs_le ab.1
    have hright := le_abs_self ab.2
    have ha := abs_nonneg r
    have hl := abs_nonneg ab.1
    have hr := abs_nonneg ab.2
    constructor <;> linarith

end SchauderTranslates.LpConstruction
