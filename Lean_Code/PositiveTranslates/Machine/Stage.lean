import Lean_Code.PositiveTranslates.Machine.State

/-!
# One stage of the reference construction

`exists_step`: for every good state `S`, every packet size `N ≥ 1` with deficit at most
`1/2`, every admissible input `v` and every requested lower bound `Λ₀` there is a good
state `S'` with `Step hΓ S N v Λ₀ S'`.

The proof is set-level bookkeeping around three ingredients:

* `exists_coordCell` : a unit non-negative compact step function `e` supported in a closed
  set `P` is the first vector of a local basis of `U ∪ [a, b)`, where `U ⊆ P` is a finite
  union of half-open intervals and `[a, b)` is any "room" interval disjoint from `P`;
* `exists_gapCells` : a finite disjoint union of nondegenerate half-open intervals is the
  union of the regions of finitely many cells with local bases;
* `RawState.Good.extend` : appending new coordinate cells and gap cells which partition
  `[-R₂, R₂) \ [-R, R)` preserves the invariants;

combined in `exists_extension` (the geometric form of one stage: the private regions are
arbitrary pairwise disjoint closed sets outside `[-R₁, R₁]`) and applied to the positive
packet `stage_packet`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

namespace Machine

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A coordinate cell.** Let `e` be a non-negative compactly supported step function of
norm one which vanishes outside the closed set `P`, and let `[a, b)` be a nondegenerate
interval disjoint from `P`. Then there are a finite union `U ⊆ P` of half-open intervals and
a local basis of `U ∪ [a, b)` with first vector `e`. -/
theorem exists_coordCell (hp1 : 1 < p) (hp' : p ≠ ∞) {e : LebesgueLp p}
    (he : IsCompactStep p e) (hnn : IsNonneg e) (hnorm : ‖e‖ = 1) {P : Set ℝ}
    (hP : IsClosed P) (hsupp : SupportedOn e P) {a b : ℝ} (hab : a < b)
    (hroom : Disjoint P (Ico a b)) :
    ∃ (U : Set ℝ) (β : ℕ → LebesgueLp p), U ⊆ P ∧ Removable U ∧ MeasurableSet U ∧ β 0 = e ∧
      LocalBasis p β (U ∪ Ico a b) 2 := by
  have hne : e ≠ 0 := by
    rintro rfl
    simp at hnorm
  obtain ⟨m, I, c, hm, hI, hc, hord, hrep, -, hdisj⟩ :=
    exists_ordered_positive_normalForm he hnn hne
  have hsub : ∀ k, Ico (I k).1 (I k).2 ⊆ P := by
    intro k x hx
    by_contra hxP
    obtain ⟨l, u, hxlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hP.isOpen_compl.mem_nhds hxP)
    have hvan : SupportedOn e (Ico x u)ᶜ :=
      hsupp.mono fun y hy hyI => hlu ⟨lt_of_lt_of_le hxlu.1 hyI.1, hyI.2⟩ hy
    exact Set.disjoint_left.mp (hdisj x u hvan k) hx ⟨le_rfl, hxlu.2⟩
  have hnorm' : ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 := hrep ▸ hnorm
  obtain ⟨β, hβ0, hβ⟩ := (exists_localBasis p hp1 hp' one_lt_two).2 m I c a b hI hc
    (pairwise_disjoint_Ico_of_ordered hord) (fun k => hroom.mono_left (hsub k)) hab hnorm' hm
  exact ⟨⋃ k, Ico (I k).1 (I k).2, β, iUnion_subset hsub,
    removable_iUnion fun k => removable_Ico _ _,
    MeasurableSet.iUnion fun _ => measurableSet_Ico, hβ0.trans hrep.symm, hβ⟩

/-- **Gap cells.** A finite disjoint union of nondegenerate half-open intervals is the
union of the pairwise disjoint regions of finitely many cells carrying local bases. -/
theorem exists_gapCells (hp1 : 1 < p) (hp' : p ≠ ∞) {W : Set ℝ} (hW : GapList W) :
    ∃ l : List (Cell p), (∀ c ∈ l, MeasurableSet c.A ∧ LocalBasis p c.β c.A 2) ∧
      (l.Pairwise fun c c' => Disjoint c.A c'.A) ∧ (⋃ c ∈ l, c.A) = W := by
  induction hW with
  | empty => exact ⟨[], by simp, List.Pairwise.nil, by simp⟩
  | cons a b X hab hdis _ ih =>
    obtain ⟨l, hl, hpw, hun⟩ := ih
    obtain ⟨β, hβ⟩ := (exists_localBasis p hp1 hp' one_lt_two).1 a b hab
    refine ⟨⟨Ico a b, β⟩ :: l, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨measurableSet_Ico, hβ⟩
      · exact hl c hc
    · refine List.pairwise_cons.mpr ⟨fun c hc => ?_, hpw⟩
      refine hdis.mono_right ?_
      rw [← hun]
      exact Set.subset_biUnion_of_mem (u := fun c : Cell p => c.A) hc
    · rw [← hun]
      ext x
      simp

/-- **Appending cells preserves the invariants.** New coordinate cells `C i` (`i < N`) and
gap cells which together partition `[-R₂, R₂) \ [-R, R)` are appended to a good state, the
stage is recorded, and the births are replaced by an arbitrary list. -/
theorem RawState.Good.extend {S : RawState p} (hS : S.Good) {N : ℕ} (hN : 1 ≤ N)
    (C : Fin N → Cell p) (gaps : List (Cell p)) (R₂ : ℝ)
    (births' : List (ℝ × LebesgueLp p))
    (hR₂ : (S.stages.length : ℝ) + 1 ≤ R₂)
    (hCmeas : ∀ i, MeasurableSet (C i).A) (hCbasis : ∀ i, LocalBasis p (C i).β (C i).A 2)
    (hCdisj : ∀ i j, i ≠ j → Disjoint (C i).A (C j).A)
    (hCold : ∀ i, Disjoint (C i).A (Ico (-S.R) S.R))
    (hCsub : ∀ i, (C i).A ⊆ Ico (-R₂) R₂) (hRR : S.R ≤ R₂)
    (hgaps : ∀ c ∈ gaps, MeasurableSet c.A ∧ LocalBasis p c.β c.A 2)
    (hgdisj : gaps.Pairwise fun c c' => Disjoint c.A c'.A)
    (hgunion : (⋃ c ∈ gaps, c.A) = Ico (-R₂) R₂ \ (Ico (-S.R) S.R ∪ ⋃ i, (C i).A)) :
    RawState.Good (⟨R₂, S.cells ++ (List.ofFn C ++ gaps),
      S.stages ++ [(S.cells.length, N)], births'⟩ : RawState p) := by
  have hgsub : ∀ c ∈ gaps, c.A ⊆ Ico (-R₂) R₂ \ (Ico (-S.R) S.R ∪ ⋃ i, (C i).A) := by
    intro c hc
    rw [← hgunion]
    exact Set.subset_biUnion_of_mem (u := fun c : Cell p => c.A) hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the radius
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    exact hR₂
  · -- measurability
    intro c hc
    simp only [List.mem_append, List.mem_ofFn] at hc
    rcases hc with hc | ⟨i, rfl⟩ | hc
    · exact hS.meas c hc
    · exact hCmeas i
    · exact (hgaps c hc).1
  · -- local bases
    intro c hc
    simp only [List.mem_append, List.mem_ofFn] at hc
    rcases hc with hc | ⟨i, rfl⟩ | hc
    · exact hS.basis c hc
    · exact hCbasis i
    · exact (hgaps c hc).2
  · -- disjointness
    refine List.pairwise_append.mpr ⟨hS.disj, List.pairwise_append.mpr
      ⟨List.pairwise_ofFn.mpr fun i j hij => hCdisj i j hij.ne, hgdisj, ?_⟩, ?_⟩
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      rw [Set.disjoint_left]
      intro x hx hx'
      exact (hgsub b hb hx').2 (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
    · intro a ha b hb
      have haS := hS.subset ha
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
        exact ((hCold i).mono_right haS).symm
      · rw [Set.disjoint_left]
        intro x hx hx'
        exact (hgsub b hb hx').2 (Or.inl (haS hx))
  · -- the cover
    ext x
    have hold : (∃ c ∈ S.cells, x ∈ c.A) ↔ x ∈ Ico (-S.R) S.R := by
      rw [← hS.cover]
      simp only [mem_iUnion, exists_prop]
    have hgap : (∃ c ∈ gaps, x ∈ c.A) ↔
        x ∈ Ico (-R₂) R₂ \ (Ico (-S.R) S.R ∪ ⋃ i, (C i).A) := by
      rw [← hgunion]
      simp only [mem_iUnion, exists_prop]
    simp only [mem_iUnion, exists_prop, List.mem_append, List.mem_ofFn]
    constructor
    · rintro ⟨c, hc | ⟨i, rfl⟩ | hc, hx⟩
      · exact Ico_subset_Ico (neg_le_neg hRR) hRR (hold.mp ⟨c, hc, hx⟩)
      · exact hCsub i hx
      · exact (hgap.mp ⟨c, hc, hx⟩).1
    · intro hx
      by_cases h1 : x ∈ Ico (-S.R) S.R
      · obtain ⟨c, hc, hxc⟩ := hold.mpr h1
        exact ⟨c, Or.inl hc, hxc⟩
      · by_cases h2 : ∃ i, x ∈ (C i).A
        · obtain ⟨i, hi⟩ := h2
          exact ⟨C i, Or.inr (Or.inl ⟨i, rfl⟩), hi⟩
        · obtain ⟨c, hc, hxc⟩ :=
            hgap.mpr ⟨hx, fun h => h.elim h1 fun h => h2 (mem_iUnion.mp h)⟩
          exact ⟨c, Or.inr (Or.inr hc), hxc⟩
  · -- the number of cells
    have := hS.len
    simp only [List.length_append, List.length_ofFn, List.length_singleton]
    omega
  · -- the stages
    intro a ha
    simp only [List.length_append, List.length_ofFn]
    rcases List.mem_append.mp ha with ha | ha
    · have := hS.block a ha
      omega
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨hN, by omega⟩

/-- **One stage, geometric form.** Let `S` be a good state with committed radius
`R ≤ R₁`, and let `e i` (`i < N`) be non-negative unit compact step functions supported in
pairwise disjoint closed sets `Pr i ⊆ [-(R₁ + ρ), R₁ + ρ]` which do not meet `[-R₁, R₁]`.
Then there is a good state which keeps the cells of `S`, has `N` new coordinate cells with
first vectors `e i` (the cells number `S.cells.length + i`), records the stage, and has any
prescribed list of births. -/
theorem exists_extension (hp1 : 1 < p) (hp' : p ≠ ∞) {S : RawState p} (hS : S.Good) {N : ℕ}
    (hN : 1 ≤ N) {R₁ ρ : ℝ} (hR₁ : S.R ≤ R₁) (hρ : 0 ≤ ρ) (Pr : Fin N → Set ℝ)
    (hPclosed : ∀ i, IsClosed (Pr i)) (hPsub : ∀ i, Pr i ⊆ Icc (-(R₁ + ρ)) (R₁ + ρ))
    (hPdisj : ∀ i j, i ≠ j → Disjoint (Pr i) (Pr j))
    (hPbase : ∀ i, Disjoint (Pr i) (Icc (-R₁) R₁))
    (e : Fin N → LebesgueLp p) (hestep : ∀ i, IsCompactStep p (e i))
    (henn : ∀ i, IsNonneg (e i)) (henorm : ∀ i, ‖e i‖ = 1)
    (hesupp : ∀ i, SupportedOn (e i) (Pr i)) (births' : List (ℝ × LebesgueLp p)) :
    ∃ S' : RawState p, S'.Good ∧ S.cells <+: S'.cells ∧
      S'.stages = S.stages ++ [(S.cells.length, N)] ∧ S'.births = births' ∧
      ∀ i : Fin N, S'.cellβ (S.cells.length + i) 0 = e i := by
  have hR₁0 : 0 ≤ R₁ := hS.radius_nonneg.trans hR₁
  -- the rooms `[a i, a i + 1)`, to the right of all private regions
  obtain ⟨a, ha⟩ : ∃ a : Fin N → ℝ, ∀ i, a i = R₁ + ρ + 1 + ((i : ℕ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have ha1 : ∀ i, R₁ + ρ + 1 ≤ a i := by
    intro i
    have h : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [ha]
    linarith
  have ha2 : ∀ i, a i + 1 ≤ R₁ + ρ + 1 + N := by
    intro i
    have h : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.2
    rw [ha]
    linarith
  have hrr : ∀ i j, i ≠ j → Disjoint (Ico (a i) (a i + 1)) (Ico (a j) (a j + 1)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hx'
    apply hij
    have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) + 1 := by
      have := hx.1
      have := hx'.2
      rw [ha] at *
      linarith
    have h2 : ((j : ℕ) : ℝ) < ((i : ℕ) : ℝ) + 1 := by
      have := hx'.1
      have := hx.2
      rw [ha] at *
      linarith
    have h1' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  have hPr : ∀ i j, Disjoint (Pr i) (Ico (a j) (a j + 1)) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 := (hPsub i hx).2
    have h2 := hx'.1
    have h3 := ha1 j
    linarith
  -- the coordinate cells
  have hcell : ∀ i : Fin N, ∃ (U : Set ℝ) (β : ℕ → LebesgueLp p), U ⊆ Pr i ∧ Removable U ∧
      MeasurableSet U ∧ β 0 = e i ∧ LocalBasis p β (U ∪ Ico (a i) (a i + 1)) 2 :=
    fun i => exists_coordCell hp1 hp' (hestep i) (henn i) (henorm i) (hPclosed i) (hesupp i)
      (lt_add_one _) (hPr i i)
  choose U β hUP hUrem hUmeas hβ0 hβ using hcell
  -- the new radius
  obtain ⟨R₂, hR₂a, hR₂b⟩ : ∃ R₂ : ℝ, R₁ + ρ + 1 + N ≤ R₂ ∧ (S.stages.length : ℝ) + 1 ≤ R₂ :=
    ⟨max (R₁ + ρ + 1 + N) (S.stages.length + 1), le_max_left _ _, le_max_right _ _⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- the gap cells
  have hrem : Removable (Ico (-S.R) S.R ∪ ⋃ i, (U i ∪ Ico (a i) (a i + 1))) :=
    (removable_Ico _ _).union (removable_iUnion fun i => (hUrem i).union (removable_Ico _ _))
  obtain ⟨gaps, hg, hgd, hgu⟩ := exists_gapCells hp1 hp' (hrem.gapList_diff (-R₂) R₂)
  have hgood : RawState.Good (⟨R₂,
      S.cells ++ (List.ofFn (fun i => (⟨U i ∪ Ico (a i) (a i + 1), β i⟩ : Cell p)) ++ gaps),
      S.stages ++ [(S.cells.length, N)], births'⟩ : RawState p) := by
    refine hS.extend hN _ gaps R₂ births' hR₂b (fun i => (hUmeas i).union measurableSet_Ico)
      hβ ?_ ?_ ?_ (by linarith) hg hgd hgu
    · -- the new coordinate cells are pairwise disjoint
      intro i j hij
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      exact ⟨⟨(hPdisj i j hij).mono (hUP i) (hUP j), (hPr i j).mono_left (hUP i)⟩,
        ((hPr j i).mono_left (hUP j)).symm, hrr i j hij⟩
    · -- they do not meet the old committed interval
      intro i
      rw [disjoint_union_left]
      constructor
      · exact (hPbase i).mono (hUP i)
          ((Ico_subset_Ico (neg_le_neg hR₁) hR₁).trans Ico_subset_Icc_self)
      · rw [Set.disjoint_left]
        intro x hx hx'
        have h1 := hx.1
        have h2 := hx'.2
        have h3 := ha1 i
        linarith
    · -- they lie in the new committed interval
      intro i x hx
      rcases hx with hx | hx
      · have h := hPsub i (hUP i hx)
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · have h1 := ha1 i
        have h2 := ha2 i
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨_, hgood, List.prefix_append _ _, rfl, rfl, fun i => ?_⟩
  show ((S.cells ++ (List.ofFn (fun i => (⟨U i ∪ Ico (a i) (a i + 1), β i⟩ : Cell p)) ++
    gaps)).getD (S.cells.length + i) default).β 0 = e i
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact hβ0 i

variable {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ)

/-- **One stage of the reference construction.** For a good state `S`, a packet size
`N ≥ 1` with deficit at most `1/2`, an admissible input `v` and a requested lower bound
`Λ₀` there is a good successor state. -/
theorem exists_step (hp : 2 < p) (hp' : p ≠ ∞) {S : RawState p} (hS : S.Good) {N : ℕ}
    (hN : 1 ≤ N) (hdef : posDeficit p.toReal N ≤ 1 / 2) {v : LebesgueLp p}
    (hv : Admissible v) (Λ₀ : ℝ) : ∃ S' : RawState p, S'.Good ∧ Step hΓ S N v Λ₀ S' := by
  have hp1 : 1 < p := lt_trans (by norm_num) hp
  have P := stage_packet hΓ hp hp' hS hN hdef hv Λ₀
  have hΛpos : ∀ i, 0 < stageParams hΓ S N v Λ₀ i := stageParams_pos hΓ S N v Λ₀
  obtain ⟨S', hgood, hcells, hstages, hbirths, hcoord⟩ :=
    exists_extension hp1 hp' hS hN (R₁ := stageRadius S v)
      (ρ := ∑ i, stageParams hΓ S N v Λ₀ i) (le_max_left _ _)
      (Finset.sum_nonneg fun i _ => (hΛpos i).le)
      (fun i => modesRegion (stageRadius S v) (stageParams hΓ S N v Λ₀) (privateModes i))
      (fun i => isClosed_biUnion_finset fun _ _ => isClosed_Icc)
      (privateRegion_subset_Icc (fun i => (hΛpos i).le) (le_sum_of_pos hΛpos))
      P.regions_disjoint P.region_disjoint_base
      (posRemainder p v S.target (stageParams hΓ S N v Λ₀))
      P.remainder_step P.remainder_nonneg P.remainder_norm P.remainder_supported
      (S.births ++ List.ofFn fun i : Fin N =>
        (stageParams hΓ S N v Λ₀ i,
          translate p (stageParams hΓ S N v Λ₀ i)
            (referenceFunction p v S.target (stageParams hΓ S N v Λ₀))))
  exact ⟨S', hgood, hcells, hstages, hbirths, hcoord⟩

end Machine

end StructuredBases.PositiveTranslates
