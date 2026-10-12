import Lean_Code.PositiveTranslates.Packet.Main
import Lean_Code.PositiveTranslates.Local.Main
import Lean_Code.PositiveTranslates.Global.Main
import Lean_Code.PositiveTranslates.Forest.Main
import Lean_Code.PositiveTranslates.Machine.Intervals

/-!
# States of the reference construction

The finite-stage data of the reference construction for the paper's Theorem
`thm:translate-properties`(iii) (namespace `StructuredBases.PositiveTranslates.Machine`).

* `Cell p` : a region `A ⊆ ℝ` together with a sequence `β` of `Lᵖ` classes (its local
  basis);
* `RawState p` : the committed radius `R`, the list of cells created so far, the list of
  completed stages — the stage `s` is recorded as the pair (index of its first coordinate
  cell, number `N s` of its coordinate cells) — and the list of births (parameter,
  reference vector);
* `RawState.Good` : the invariants. The regions are measurable, pairwise disjoint, and
  their union is `[-R, R)`; every cell carries a `LocalBasis` with prefix constant `2`;
  `R` is at least the number `t` of completed stages; there are at least `t + 2` cells;
  the coordinate cells of every completed stage exist;
* `RawState.target` : the function to be approximated at the next stage `t`. With
  `(j, n) = stagePair t` it is the root number `j` of the cell list (`rootVec`) if `n = 0`
  and the normalized average of the coordinates of the stage `stageOf (j, n - 1)` if
  `n ≥ 1`. For a good state it is a non-negative compact step function of norm one
  supported in `[-R, R]` (`RawState.Good.isTarget`);
* `stageParams` : the parameters of the next stage, `placement hΓ R₁ T N` with
  `R₁ = max R (supportRadius v)` and `T = max Λ₀ (maxParam births)`;
* `Step` : the relation between a state and its successor;
* `initRaw` : the initial state.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

namespace Machine

/-- A cell of the reference construction: a region and a sequence of functions (its local
basis). -/
structure Cell (p : ℝ≥0∞) where
  /-- the region of the cell -/
  A : Set ℝ
  /-- the local basis of the cell -/
  β : ℕ → LebesgueLp p

instance (p : ℝ≥0∞) : Inhabited (Cell p) := ⟨⟨∅, fun _ => 0⟩⟩

/-- The finite-stage data of the reference construction. -/
structure RawState (p : ℝ≥0∞) where
  /-- the committed radius: the cells partition `[-R, R)` -/
  R : ℝ
  /-- the cells created so far -/
  cells : List (Cell p)
  /-- the completed stages: (index of the first coordinate cell, number of coordinate
  cells) -/
  stages : List (ℕ × ℕ)
  /-- the births: translation parameters and reference vectors -/
  births : List (ℝ × LebesgueLp p)

variable {p : ℝ≥0∞}

namespace RawState

/-- The local basis of the cell number `c` (zero if there is no such cell). -/
def cellβ (S : RawState p) (c : ℕ) : ℕ → LebesgueLp p := (S.cells.getD c default).β

/-- The cell number `c` is a coordinate cell: it is the cell `0` or one of the coordinate
cells of a completed stage. -/
def flag (S : RawState p) (c : ℕ) : Bool :=
  decide (c = 0 ∨ ∃ a ∈ S.stages, a.1 ≤ c ∧ c < a.1 + a.2)

/-- The index of the first coordinate cell of the stage `s`. -/
def start (S : RawState p) (s : ℕ) : ℕ := (S.stages.getD s (0, 0)).1

/-- The number of coordinate cells of the stage `s`. -/
def size (S : RawState p) (s : ℕ) : ℕ := (S.stages.getD s (0, 0)).2

/-- The normalized average of the coordinates of the stage `s`. -/
def avg (S : RawState p) (s : ℕ) : LebesgueLp p :=
  (((S.size s : ℝ) ^ (-1 / p.toReal) : ℝ) : ℂ) •
    ∑ i ∈ Finset.range (S.size s), S.cellβ (S.start s + i) 0

theorem flag_eq_true_iff (S : RawState p) (c : ℕ) :
    S.flag c = true ↔ c = 0 ∨ ∃ a ∈ S.stages, a.1 ≤ c ∧ c < a.1 + a.2 := by
  unfold flag
  exact decide_eq_true_iff

theorem cellβ_eq (S : RawState p) {c : ℕ} (hc : c < S.cells.length) :
    S.cellβ c = (S.cells[c]).β := by
  unfold cellβ
  rw [List.getD_eq_getElem _ _ hc]

theorem start_eq (S : RawState p) {s : ℕ} (hs : s < S.stages.length) :
    S.start s = (S.stages[s]).1 := by
  unfold start
  rw [List.getD_eq_getElem _ _ hs]

theorem size_eq (S : RawState p) {s : ℕ} (hs : s < S.stages.length) :
    S.size s = (S.stages[s]).2 := by
  unfold size
  rw [List.getD_eq_getElem _ _ hs]

variable [Fact (1 ≤ p)]

/-- The target of the next stage `t` (`t` is the number of completed stages): with
`(j, n) = stagePair t`, the root number `j` if `n = 0`, and the average of the coordinates of
the stage `stageOf (j, n - 1)` if `n ≥ 1`. -/
def target (S : RawState p) : LebesgueLp p :=
  if (stagePair S.stages.length).2 = 0 then
    rootVec S.cellβ S.flag (stagePair S.stages.length).1
  else S.avg (stageOf ((stagePair S.stages.length).1, (stagePair S.stages.length).2 - 1))

/-- The invariants of the reference construction (the prefix constant of all local bases
is `2`). -/
structure Good (S : RawState p) : Prop where
  /-- the committed radius is at least the number of completed stages -/
  radius : (S.stages.length : ℝ) ≤ S.R
  /-- the regions are measurable -/
  meas : ∀ c ∈ S.cells, MeasurableSet c.A
  /-- every cell carries a local basis -/
  basis : ∀ c ∈ S.cells, LocalBasis p c.β c.A 2
  /-- the regions are pairwise disjoint -/
  disj : S.cells.Pairwise fun c c' => Disjoint c.A c'.A
  /-- the regions cover the committed interval -/
  cover : (⋃ c ∈ S.cells, c.A) = Ico (-S.R) S.R
  /-- there are at least `t + 2` cells -/
  len : S.stages.length + 2 ≤ S.cells.length
  /-- every completed stage has at least one coordinate cell, and its coordinate cells
  exist -/
  block : ∀ a ∈ S.stages, 1 ≤ a.2 ∧ a.1 + a.2 ≤ S.cells.length

namespace Good

variable {S : RawState p}

theorem radius_nonneg (hS : S.Good) : 0 ≤ S.R := (Nat.cast_nonneg _).trans hS.radius

theorem subset (hS : S.Good) {c : Cell p} (hc : c ∈ S.cells) : c.A ⊆ Ico (-S.R) S.R := by
  rw [← hS.cover]
  exact Set.subset_biUnion_of_mem (u := fun c : Cell p => c.A) hc

theorem localBasis (hS : S.Good) {c : ℕ} (hc : c < S.cells.length) :
    LocalBasis p (S.cellβ c) (S.cells[c]).A 2 := by
  rw [S.cellβ_eq hc]
  exact hS.basis _ (List.getElem_mem hc)

theorem subset_getElem (hS : S.Good) {c : ℕ} (hc : c < S.cells.length) :
    (S.cells[c]).A ⊆ Icc (-S.R) S.R :=
  (hS.subset (List.getElem_mem hc)).trans Ico_subset_Icc_self

theorem disjoint_getElem (hS : S.Good) {c c' : ℕ} (hc : c < S.cells.length)
    (hc' : c' < S.cells.length) (hne : c ≠ c') :
    Disjoint (S.cells[c]).A (S.cells[c']).A := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_getElem.mp hS.disj c c' hc hc' h
  · exact (List.pairwise_iff_getElem.mp hS.disj c' c hc' hc h).symm

theorem one_le_size (hS : S.Good) {s : ℕ} (hs : s < S.stages.length) : 1 ≤ S.size s := by
  rw [S.size_eq hs]
  exact (hS.block _ (List.getElem_mem hs)).1

theorem start_add_size_le (hS : S.Good) {s : ℕ} (hs : s < S.stages.length) :
    S.start s + S.size s ≤ S.cells.length := by
  rw [S.size_eq hs, S.start_eq hs]
  exact (hS.block _ (List.getElem_mem hs)).2

end Good

end RawState

/-- The properties of a target of a stage with committed radius `R`. -/
structure IsTarget [Fact (1 ≤ p)] (R : ℝ) (h : LebesgueLp p) : Prop where
  /-- a compactly supported step function -/
  step : IsCompactStep p h
  /-- non-negative almost everywhere -/
  nonneg : IsNonneg h
  /-- a unit vector -/
  norm : ‖h‖ = 1
  /-- vanishing outside the committed interval -/
  supported : SupportedOn h (Icc (-R) R)

namespace RawState.Good

variable [Fact (1 ≤ p)] {S : RawState p}

/-- Every local basis vector of an existing cell is a target. -/
theorem isTarget_cellβ (hS : S.Good) {c : ℕ} (hc : c < S.cells.length) (n : ℕ) :
    IsTarget S.R (S.cellβ c n) where
  step := (hS.localBasis hc).step n
  nonneg := (hS.localBasis hc).nonneg n
  norm := (hS.localBasis hc).norm n
  supported := ((hS.localBasis hc).supported n).mono (hS.subset_getElem hc)

/-- The average of the coordinates of a completed stage is a target. -/
theorem isTarget_avg (hS : S.Good) (hp' : p ≠ ∞) {s : ℕ} (hs : s < S.stages.length) :
    IsTarget S.R (S.avg s) := by
  have h1 := hS.one_le_size hs
  have h2 := hS.start_add_size_le hs
  have hc : ∀ i ∈ Finset.range (S.size s), S.start s + i < S.cells.length := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  have hx : (0 : ℝ) ≤ (S.size s : ℝ) ^ (-1 / p.toReal) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [avg, Local.ofReal_smul_eq]
    exact (IsCompactStep.finset_sum _ _ fun i hi => (hS.isTarget_cellβ (hc i hi) 0).step).smul _
  · rw [avg, Local.ofReal_smul_eq]
    exact (IsNonneg.finset_sum _ _ fun i hi => (hS.isTarget_cellβ (hc i hi) 0).nonneg).smul hx
  · have hp0 : p ≠ 0 := lpExponent_ne_zero p
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
    have hdis : ∀ i ∈ Finset.range (S.size s), ∀ j ∈ Finset.range (S.size s), i ≠ j →
        ∀ᵐ x ∂(volume : Measure ℝ),
          S.cellβ (S.start s + i) 0 x = 0 ∨ S.cellβ (S.start s + j) 0 x = 0 := by
      intro i hi j hj hij
      exact ((hS.localBasis (hc i hi)).supported 0).ae_disjoint
        ((hS.localBasis (hc j hj)).supported 0)
        (hS.disjoint_getElem (hc i hi) (hc j hj) (by omega))
    have hsum : ‖∑ i ∈ Finset.range (S.size s), S.cellβ (S.start s + i) 0‖ ^ p.toReal =
        (S.size s : ℝ) := by
      rw [norm_finset_sum_rpow _ _ hp0 hp' hdis,
        Finset.sum_congr rfl fun i hi => by
          rw [(hS.isTarget_cellβ (hc i hi) 0).norm, Real.one_rpow]]
      simp
    have hnorm : ‖∑ i ∈ Finset.range (S.size s), S.cellβ (S.start s + i) 0‖ =
        (S.size s : ℝ) ^ (1 / p.toReal) := by
      rw [← hsum, one_div, Real.rpow_rpow_inv (norm_nonneg _) hr.ne']
    have hpos : (0 : ℝ) < S.size s := by exact_mod_cast h1
    have hexp : -1 / p.toReal + 1 / p.toReal = 0 := by ring
    rw [avg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hx, hnorm,
      ← Real.rpow_add hpos, hexp, Real.rpow_zero]
  · rw [avg, Local.ofReal_smul_eq]
    exact (SupportedOn.finset_sum _ _
      fun i hi => (hS.isTarget_cellβ (hc i hi) 0).supported).real_smul _

/-- **The target of a good state** is a non-negative compactly supported step function of
norm one, supported in the committed interval. -/
theorem isTarget (hS : S.Good) (hp' : p ≠ ∞) : IsTarget S.R S.target := by
  unfold target
  split_ifs with h
  · have h1 := stagePair_fst_add_snd_le S.stages.length
    have h2 := Nat.unpair_left_le (stagePair S.stages.length).1
    have h3 := hS.len
    exact hS.isTarget_cellβ (by omega) _
  · exact hS.isTarget_avg hp' (predStage_lt h)

end RawState.Good

/-! ### The parameters of a stage -/

/-- A radius `r ≥ 0` such that the compact step function `v` vanishes outside `[-r, r]`
(zero if `v` is not a compact step function). -/
def supportRadius (v : LebesgueLp p) : ℝ := by
  classical
  exact if h : IsCompactStep p v then Classical.choose h.bounded_support else 0

theorem supportRadius_nonneg (v : LebesgueLp p) : 0 ≤ supportRadius v := by
  unfold supportRadius
  split_ifs with h
  · exact (Classical.choose_spec h.bounded_support).1
  · exact le_rfl

theorem supportedOn_supportRadius {v : LebesgueLp p} (h : IsCompactStep p v) :
    SupportedOn v (Icc (-supportRadius v) (supportRadius v)) := by
  unfold supportRadius
  rw [dif_pos h]
  exact (Classical.choose_spec h.bounded_support).2

/-- An upper bound for the parameters of a list of births. -/
def maxParam (l : List (ℝ × LebesgueLp p)) : ℝ := l.foldr (fun b m => max b.1 m) 0

theorem le_maxParam {l : List (ℝ × LebesgueLp p)} {b : ℝ × LebesgueLp p} (hb : b ∈ l) :
    b.1 ≤ maxParam l := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact le_max_left _ _
    · exact (ih hb').trans (le_max_right _ _)

/-- The radius used for the packet of the next stage: the input `v` and the target live in
`[-R₁, R₁]`. -/
def stageRadius (S : RawState p) (v : LebesgueLp p) : ℝ := max S.R (supportRadius v)

theorem stageRadius_nonneg (S : RawState p) (v : LebesgueLp p) : 0 ≤ stageRadius S v :=
  (supportRadius_nonneg v).trans (le_max_right _ _)

/-- The threshold above which the parameters of the next stage are chosen. -/
def stageThreshold (S : RawState p) (Λ₀ : ℝ) : ℝ := max Λ₀ (maxParam S.births)

variable {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ)

/-- The parameters of the next stage. They are defined for all inputs. -/
def stageParams (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) : Fin N → ℝ :=
  placement hΓ (stageRadius S v) (stageThreshold S Λ₀) N

theorem stageParams_mem (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) (i : Fin N) :
    stageParams hΓ S N v Λ₀ i ∈ Γ := placement_mem hΓ _ _ N i

theorem lt_stageParams (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) (i : Fin N) :
    Λ₀ < stageParams hΓ S N v Λ₀ i :=
  lt_of_le_of_lt (le_max_left _ _) (lt_placement hΓ _ _ N i)

theorem stageParams_pos (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) (i : Fin N) :
    0 < stageParams hΓ S N v Λ₀ i := placement_pos hΓ _ _ N i

theorem lt_stageParams_of_mem (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ)
    (i : Fin N) {b : ℝ × LebesgueLp p} (hb : b ∈ S.births) :
    b.1 < stageParams hΓ S N v Λ₀ i :=
  lt_of_le_of_lt ((le_maxParam hb).trans (le_max_right _ _)) (lt_placement hΓ _ _ N i)

theorem stageParams_injective (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) :
    Function.Injective (stageParams hΓ S N v Λ₀) :=
  (placement_strictMono hΓ (stageRadius_nonneg S v) _ N).injective

variable [Fact (1 ≤ p)]

/-- **The positive packet of a stage.** For a good state, a size `N ≥ 1` with deficit at
most `1/2` and an admissible input `v`, the parameters `stageParams` and the remainders
`posRemainder` form a positive packet for `v` and the target, with radius `stageRadius`. -/
theorem stage_packet (hp : 2 < p) (hp' : p ≠ ∞) {S : RawState p} (hS : S.Good) {N : ℕ}
    (hN : 1 ≤ N) (hdef : posDeficit p.toReal N ≤ 1 / 2) {v : LebesgueLp p}
    (hv : Admissible v) (Λ₀ : ℝ) :
    PositivePacket p (stageRadius S v) v S.target (stageParams hΓ S N v Λ₀)
      (posRemainder p v S.target (stageParams hΓ S N v Λ₀)) := by
  have hT := hS.isTarget hp'
  have hv0 : v ≠ 0 := by
    intro h0
    have h := hv.lower
    rw [h0, norm_zero] at h
    norm_num at h
  refine positive_packet_placement hp hp' hΓ _ (stageRadius_nonneg S v) hv.step hT.step
    hv.nonneg hT.nonneg ?_ ?_ hv0 hT.norm hN (lt_of_le_of_lt hdef (by norm_num))
  · exact (supportedOn_supportRadius hv.step).mono
      (Icc_subset_Icc (neg_le_neg (le_max_right _ _)) (le_max_right _ _))
  · exact hT.supported.mono (Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _))

/-- The relation between a state `S` and its successor `S'` after a stage with packet size
`N`, input `v` and requested lower bound `Λ₀` for the parameters. -/
structure Step (S : RawState p) (N : ℕ) (v : LebesgueLp p) (Λ₀ : ℝ) (S' : RawState p) :
    Prop where
  /-- the old cells are kept, new cells are appended -/
  cells : S.cells <+: S'.cells
  /-- the stage is recorded: its coordinate cells are the first `N` new cells -/
  stages : S'.stages = S.stages ++ [(S.cells.length, N)]
  /-- the new births -/
  births : S'.births = S.births ++ List.ofFn fun i : Fin N =>
    (stageParams hΓ S N v Λ₀ i,
      translate p (stageParams hΓ S N v Λ₀ i)
        (referenceFunction p v S.target (stageParams hΓ S N v Λ₀)))
  /-- the first vectors of the new coordinate cells are the remainders of the packet -/
  coord : ∀ i : Fin N, S'.cellβ (S.cells.length + i) 0 =
    posRemainder p v S.target (stageParams hΓ S N v Λ₀) i

/-! ### The initial state -/

/-- A local basis of `[0, 2)` whose first vector is the indicator of `[0, 1)`. -/
theorem exists_initCell (hp1 : 1 < p) (hp' : p ≠ ∞) :
    ∃ β : ℕ → LebesgueLp p, β 0 = intervalAtom p (0, 1) ∧ LocalBasis p β (Ico 0 2) 2 := by
  have hp0 : p ≠ 0 := lpExponent_ne_zero p
  have hsum : ∑ _k : Fin 1, ((1 : ℝ) : ℂ) • intervalAtom p ((0 : ℝ), (1 : ℝ)) =
      intervalAtom p (0, 1) := by simp
  obtain ⟨β, hβ0, hβ⟩ := (exists_localBasis p hp1 hp' one_lt_two).2 1 (fun _ => (0, 1))
    (fun _ => 1) 1 2 (fun _ => by norm_num) (fun _ => one_pos)
    (fun k l hkl => absurd (Subsingleton.elim k l) hkl)
    (fun _ => by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_lt.mpr hx'.1))
    (by norm_num) (by rw [hsum]; exact initial_generator_unit p hp0 hp') one_pos
  refine ⟨β, hβ0.trans hsum, hβ.congr_set ?_⟩
  ext x
  simp only [mem_union, mem_iUnion, mem_Ico, exists_const]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases h : x < 1
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨not_lt.mp h, h2⟩

/-- The initial state: radius `2`, the coordinate cell `[0, 2)` with first vector
`𝟙_[0,1)`, the gap cell `[-2, 0)`, no completed stage, and the birth `(0, 𝟙_[0,1))`. -/
def initRaw (hp1 : 1 < p) (hp' : p ≠ ∞) : RawState p where
  R := 2
  cells := [⟨Ico 0 2, Classical.choose (exists_initCell hp1 hp')⟩,
    ⟨Ico (-2) 0, Classical.choose
      ((exists_localBasis p hp1 hp' one_lt_two).1 (-2) 0 (by norm_num))⟩]
  stages := []
  births := [(0, intervalAtom p (0, 1))]

theorem initRaw_cellβ_zero (hp1 : 1 < p) (hp' : p ≠ ∞) :
    (initRaw hp1 hp').cellβ 0 0 = intervalAtom p (0, 1) :=
  (Classical.choose_spec (exists_initCell hp1 hp')).1

theorem initRaw_good (hp1 : 1 < p) (hp' : p ≠ ∞) : (initRaw hp1 hp').Good where
  radius := by simp [initRaw]
  meas := by
    intro c hc
    simp only [initRaw, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact measurableSet_Ico
  basis := by
    intro c hc
    simp only [initRaw, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (Classical.choose_spec (exists_initCell hp1 hp')).2
    · exact Classical.choose_spec
        ((exists_localBasis p hp1 hp' one_lt_two).1 (-2) 0 (by norm_num))
  disj := by
    simp only [initRaw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.1 (not_le.mpr hx'.2)
  cover := by
    ext x
    simp only [initRaw, List.mem_cons, List.not_mem_nil, or_false, mem_iUnion, exists_prop,
      exists_eq_or_imp, exists_eq_left, mem_Ico]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by linarith, h2⟩
      · exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      by_cases h : x < 0
      · exact Or.inr ⟨h1, h⟩
      · exact Or.inl ⟨not_lt.mp h, h2⟩
  len := by simp [initRaw]
  block := by simp [initRaw]

end Machine

end StructuredBases.PositiveTranslates
