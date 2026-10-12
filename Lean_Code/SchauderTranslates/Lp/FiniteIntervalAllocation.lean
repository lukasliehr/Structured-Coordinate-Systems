import Lean_Code.SchauderTranslates.Lp.BreakpointPartition

noncomputable section

namespace SchauderTranslates.LpConstruction

def finiteIntervalUnion (s : Finset (ℝ × ℝ)) : Set ℝ := ⋃ ab ∈ s, Set.Ico ab.1 ab.2

def allocationBreakpoints (s : Finset (ℝ × ℝ)) (l u : ℝ) : Finset ℝ := by
  classical
  exact insert l (insert u (s.biUnion fun ab => {ab.1, ab.2}))

def remainingIntervals (s : Finset (ℝ × ℝ)) (l u : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (breakpointCells (allocationBreakpoints s l u)).filter
    (fun ab => ab.1 ∉ finiteIntervalUnion s)

theorem allocationBreakpoints_left (s : Finset (ℝ × ℝ)) (l u : ℝ) {ab : ℝ × ℝ}
    (hab : ab ∈ s) : ab.1 ∈ allocationBreakpoints s l u := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_biUnion.mpr ⟨ab, hab, by simp⟩))

theorem allocationBreakpoints_right (s : Finset (ℝ × ℝ)) (l u : ℝ) {ab : ℝ × ℝ}
    (hab : ab ∈ s) : ab.2 ∈ allocationBreakpoints s l u := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_biUnion.mpr ⟨ab, hab, by simp⟩))

theorem allocationBreakpoints_bound (s : Finset (ℝ × ℝ)) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ ab ∈ s, l ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ u)
    {x : ℝ} (hx : x ∈ allocationBreakpoints s l u) : x ∈ Set.Icc l u := by
  classical
  simp only [allocationBreakpoints, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | ⟨ab, hab, rfl | rfl⟩
  · exact ⟨le_rfl, hlu⟩
  · exact ⟨hlu, le_rfl⟩
  · exact ⟨(hs ab hab).1, (hs ab hab).2.1.trans (hs ab hab).2.2⟩
  · exact ⟨(hs ab hab).1.trans (hs ab hab).2.1, (hs ab hab).2.2⟩

theorem allocation_union_membership_constant (s : Finset (ℝ × ℝ)) (l u : ℝ)
    {ab : ℝ × ℝ} (hab : ab ∈ breakpointCells (allocationBreakpoints s l u))
    {x : ℝ} (hx : x ∈ Set.Ico ab.1 ab.2) :
    x ∈ finiteIntervalUnion s ↔ ab.1 ∈ finiteIntervalUnion s := by
  simp only [finiteIntervalUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨cd, hcd, hxold⟩
    exact ⟨cd, hcd, (breakpointCells_membership_constant _ hab
      (allocationBreakpoints_left s l u hcd) (allocationBreakpoints_right s l u hcd) hx).mp hxold⟩
  · rintro ⟨cd, hcd, hleft⟩
    exact ⟨cd, hcd, (breakpointCells_membership_constant _ hab
      (allocationBreakpoints_left s l u hcd) (allocationBreakpoints_right s l u hcd) hx).mpr hleft⟩

theorem remainingIntervals_positive (s : Finset (ℝ × ℝ)) (l u : ℝ)
    {ab : ℝ × ℝ} (hab : ab ∈ remainingIntervals s l u) : ab.1 < ab.2 := by
  classical
  exact ((breakpointCells_mem _ ab).mp (Finset.mem_filter.mp hab).1).2.1

theorem remainingIntervals_disjoint_old (s : Finset (ℝ × ℝ)) (l u : ℝ)
    {ab : ℝ × ℝ} (hab : ab ∈ remainingIntervals s l u) :
    Disjoint (Set.Ico ab.1 ab.2) (finiteIntervalUnion s) := by
  classical
  obtain ⟨hab, hleft⟩ := Finset.mem_filter.mp hab
  exact Set.disjoint_left.mpr (fun _ hx hold =>
    hleft ((allocation_union_membership_constant s l u hab hx).mp hold))

theorem remainingIntervals_pairwise_disjoint (s : Finset (ℝ × ℝ)) (l u : ℝ)
    {ab cd : ℝ × ℝ} (hab : ab ∈ remainingIntervals s l u)
    (hcd : cd ∈ remainingIntervals s l u) (hne : ab ≠ cd) :
    Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2) := by
  classical
  exact breakpointCells_disjoint _ (Finset.mem_filter.mp hab).1 (Finset.mem_filter.mp hcd).1 hne

theorem remainingIntervals_subset_committed (s : Finset (ℝ × ℝ)) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ ab ∈ s, l ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ u)
    {ab : ℝ × ℝ} (hab : ab ∈ remainingIntervals s l u) : Set.Ico ab.1 ab.2 ⊆ Set.Ico l u := by
  classical
  have h := (breakpointCells_mem _ ab).mp (Finset.mem_filter.mp hab).1
  have hl := allocationBreakpoints_bound s hlu hs h.1.1
  have hu := allocationBreakpoints_bound s hlu hs h.1.2
  exact fun _ hx => ⟨hl.1.trans hx.1, hx.2.trans_le hu.2⟩

/-- Every part of the enlarged committed interval not already allocated
is a finite disjoint union of positive-length intervals. Existing cells
are retained rather than subdivided or replaced. -/
theorem finite_interval_allocation (s : Finset (ℝ × ℝ)) {l u : ℝ} (hlu : l ≤ u)
    (hs : ∀ ab ∈ s, l ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ u) :
    finiteIntervalUnion s ∪ finiteIntervalUnion (remainingIntervals s l u) = Set.Ico l u := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨ab, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hab, hx⟩ := Set.mem_iUnion.mp hx
      exact ⟨(hs ab hab).1.trans hx.1, hx.2.trans_le (hs ab hab).2.2⟩
    · obtain ⟨ab, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hab, hx⟩ := Set.mem_iUnion.mp hx
      exact remainingIntervals_subset_committed s hlu hs hab hx
  · intro x hx
    by_cases hold : x ∈ finiteIntervalUnion s
    · exact Or.inl hold
    · obtain ⟨ab, hab, hxcell⟩ := breakpointCells_cover (allocationBreakpoints s l u)
        (by simp [allocationBreakpoints]) (by simp [allocationBreakpoints]) hx
      have hleft : ab.1 ∉ finiteIntervalUnion s :=
        fun h => hold ((allocation_union_membership_constant s l u hab hxcell).mpr h)
      exact Or.inr (Set.mem_iUnion.mpr ⟨ab, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hab, hleft⟩, hxcell⟩⟩)

end SchauderTranslates.LpConstruction
