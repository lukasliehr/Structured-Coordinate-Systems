import Lean_Code.PositiveTranslates.Machine.Stage
import Lean_Code.Basis.Transport

/-!
# Runs of the reference construction

A *good run* (`GoodRun`) is a sequence of good states `S t`, starting from the initial
state, in which every state is obtained from the previous one by a stage (`Step`) with a
packet size `N t ≥ 1` of deficit at most `1/2` and an admissible input `v t`.

Along a good run the cell lists are increasing prefixes of one sequence of cells
(`runCell`), whose regions `runA S c` are measurable, pairwise disjoint and cover the line,
and which carry the local bases `runβ S c`. The global splitting
(`Lean_Code/PositiveTranslates/Global/Main.lean`) for the flags `runFlag` and the abstract
positive forest (`Lean_Code/PositiveTranslates/Forest/Main.lean`) give a positive forest
`F` (`GoodRun.exists_forest`) whose targets are the targets of the states
(`GoodRun.target_eq`) and whose sequence consists of the birth vectors up to the positive
scales of the packets (`GoodRun.births_eq`). Hence the birth vectors of a good run form a
Schauder basis of `Lᵖ(ℝ)` all of whose partial sum projections have norm at most
`4 · 2 · (1 + 2) + 13 · 2 = 50` (`GoodRun.exists_basis`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

namespace Machine

/-- A Schauder basis of a subspace is a Schauder basis of every equal subspace. -/
theorem exists_schauderBasis_of_eq {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {X X' : Submodule ℂ Z} (hXX' : X = X') (b : SchauderBasis ℂ X) {D : ℝ}
    (hD : ∀ m, ‖b.proj m‖ ≤ D) :
    ∃ b' : SchauderBasis ℂ X', (∀ j, ((b' j : X') : Z) = ((b j : X) : Z)) ∧
      ∀ m, ‖b'.proj m‖ ≤ D := by
  subst hXX'
  exact ⟨b, fun _ => rfl, hD⟩

variable {p : ℝ≥0∞}

/-! ### The global data of a sequence of states -/

/-- The cell number `c` of a sequence of states (meaningful for good runs, where the cell
lists are increasing prefixes and `S c` has more than `c` cells). -/
def runCell (S : ℕ → RawState p) (c : ℕ) : Cell p := (S c).cells.getD c default

/-- The region of the cell number `c`. -/
def runA (S : ℕ → RawState p) (c : ℕ) : Set ℝ := (runCell S c).A

/-- The local basis of the cell number `c`. -/
def runβ (S : ℕ → RawState p) (c : ℕ) : ℕ → LebesgueLp p := (runCell S c).β

/-- The coordinate cells of a run: the cell `0` and the first `N s` cells created at the
stage `s`. -/
def runFlag (S : ℕ → RawState p) (N : ℕ → ℕ) (c : ℕ) : Bool :=
  @decide (c = 0 ∨ ∃ s, (S s).cells.length ≤ c ∧ c < (S s).cells.length + N s)
    (Classical.propDecidable _)

/-- The indices of the coordinate cells: `0` for the initial vector and
`(S s).cells.length + i` for the `i`-th coordinate of the stage `s`. -/
def runIndex (S : ℕ → RawState p) (N : ℕ → ℕ) : Option (Σ s, Fin (N s)) → ℕ
  | none => 0
  | some ⟨s, i⟩ => (S s).cells.length + i

theorem runFlag_eq_true_iff (S : ℕ → RawState p) (N : ℕ → ℕ) (c : ℕ) :
    runFlag S N c = true ↔
      c = 0 ∨ ∃ s, (S s).cells.length ≤ c ∧ c < (S s).cells.length + N s := by
  unfold runFlag
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem runFlag_runIndex (S : ℕ → RawState p) (N : ℕ → ℕ) (x : Option (Σ s, Fin (N s))) :
    runFlag S N (runIndex S N x) = true := by
  rw [runFlag_eq_true_iff]
  rcases x with _ | ⟨s, i⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨s, Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _⟩

theorem exists_runIndex_of_flag {S : ℕ → RawState p} {N : ℕ → ℕ} {c : ℕ}
    (hc : runFlag S N c = true) : ∃ x, runIndex S N x = c := by
  rcases (runFlag_eq_true_iff S N c).mp hc with rfl | ⟨s, h1, h2⟩
  · exact ⟨none, rfl⟩
  · refine ⟨some ⟨s, ⟨c - (S s).cells.length, by omega⟩⟩, ?_⟩
    show (S s).cells.length + (c - (S s).cells.length) = c
    omega

variable [Fact (1 ≤ p)] {Γ : Set ℝ} {hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ}

/-- A run of the reference construction driven by admissible inputs. -/
structure GoodRun (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (hp1 : 1 < p) (hp' : p ≠ ∞)
    (S : ℕ → RawState p) (N : ℕ → ℕ) (v : ℕ → LebesgueLp p) (Λ₀ : ℕ → ℝ) : Prop where
  /-- the run starts from the initial state -/
  init : S 0 = initRaw hp1 hp'
  /-- all states are good -/
  good : ∀ t, (S t).Good
  /-- the packet sizes are positive -/
  size : ∀ t, 1 ≤ N t
  /-- the deficits are at most `1/2` -/
  deficit : ∀ t, posDeficit p.toReal (N t) ≤ 1 / 2
  /-- the inputs are admissible -/
  adm : ∀ t, Admissible (v t)
  /-- every state is the successor of the previous one -/
  step : ∀ t, Step hΓ (S t) (N t) (v t) (Λ₀ t) (S (t + 1))

namespace GoodRun

variable {hp1 : 1 < p} {hp' : p ≠ ∞} {S : ℕ → RawState p} {N : ℕ → ℕ}
  {v : ℕ → LebesgueLp p} {Λ₀ : ℕ → ℝ}

/-! ### Stages and cells along a run -/

theorem stages_length (h : GoodRun hΓ hp1 hp' S N v Λ₀) (t : ℕ) :
    (S t).stages.length = t := by
  induction t with
  | zero =>
    rw [h.init]
    rfl
  | succ t ih =>
    rw [(h.step t).stages, List.length_append, ih]
    rfl

theorem cells_prefix (h : GoodRun hΓ hp1 hp' S N v Λ₀) {s t : ℕ} (hst : s ≤ t) :
    (S s).cells <+: (S t).cells := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih => exact ih.trans (h.step t).cells

theorem add_two_le_len (h : GoodRun hΓ hp1 hp' S N v Λ₀) (t : ℕ) :
    t + 2 ≤ (S t).cells.length := by
  have := (h.good t).len
  rwa [h.stages_length] at this

theorem len_mono (h : GoodRun hΓ hp1 hp' S N v Λ₀) {s t : ℕ} (hst : s ≤ t) :
    (S s).cells.length ≤ (S t).cells.length :=
  (h.cells_prefix hst).length_le

/-- The stage `s` is recorded in every later state. -/
theorem stages_getElem? (h : GoodRun hΓ hp1 hp' S N v Λ₀) {s t : ℕ} (hst : s < t) :
    (S t).stages[s]? = some ((S s).cells.length, N s) := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [(h.step t).stages]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hst) with hlt | heq
    · rw [List.getElem?_append_left (by rw [h.stages_length]; exact hlt)]
      exact ih hlt
    · have h1 := List.getElem?_concat_length (l := (S t).stages)
        (a := ((S t).cells.length, N t))
      rw [h.stages_length] at h1
      rw [heq]
      exact h1

theorem mem_stages_iff (h : GoodRun hΓ hp1 hp' S N v Λ₀) (t : ℕ) (a : ℕ × ℕ) :
    a ∈ (S t).stages ↔ ∃ s < t, a = ((S s).cells.length, N s) := by
  constructor
  · intro ha
    obtain ⟨s, hs, hsa⟩ := List.mem_iff_getElem.mp ha
    have hst : s < t := by rwa [h.stages_length] at hs
    have h1 := h.stages_getElem? hst
    rw [List.getElem?_eq_getElem hs, hsa] at h1
    exact ⟨s, hst, Option.some.inj h1⟩
  · rintro ⟨s, hst, rfl⟩
    exact List.mem_of_getElem? (h.stages_getElem? hst)

theorem start_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) {s t : ℕ} (hst : s < t) :
    (S t).start s = (S s).cells.length := by
  rw [RawState.start, List.getD_eq_getElem?_getD, h.stages_getElem? hst]
  rfl

theorem size_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) {s t : ℕ} (hst : s < t) :
    (S t).size s = N s := by
  rw [RawState.size, List.getD_eq_getElem?_getD, h.stages_getElem? hst]
  rfl

/-- The coordinate cells of the stage `s` exist after that stage. -/
theorem block_le (h : GoodRun hΓ hp1 hp' S N v Λ₀) (s : ℕ) :
    (S s).cells.length + N s ≤ (S (s + 1)).cells.length :=
  ((h.good (s + 1)).block _
    ((h.mem_stages_iff _ _).mpr ⟨s, Nat.lt_succ_self s, rfl⟩)).2

/-- Every cell of every state is the corresponding cell of the run. -/
theorem getElem?_cells (h : GoodRun hΓ hp1 hp' S N v Λ₀) {t c : ℕ}
    (hc : c < (S t).cells.length) : (S t).cells[c]? = some (runCell S c) := by
  have hcc : c < (S c).cells.length := by
    have := h.add_two_le_len c
    omega
  have hrun : (S c).cells[c]? = some (runCell S c) := by
    rw [runCell, List.getD_eq_getElem _ _ hcc, List.getElem?_eq_getElem hcc]
  rcases le_total t c with htc | hct
  · obtain ⟨r, hr⟩ := h.cells_prefix htc
    rw [← hrun, ← hr, List.getElem?_append_left hc]
  · obtain ⟨r, hr⟩ := h.cells_prefix hct
    rw [← hr, List.getElem?_append_left hcc, hrun]

theorem getElem_cells (h : GoodRun hΓ hp1 hp' S N v Λ₀) {t c : ℕ}
    (hc : c < (S t).cells.length) : (S t).cells[c] = runCell S c := by
  have h1 := h.getElem?_cells hc
  rw [List.getElem?_eq_getElem hc] at h1
  exact Option.some.inj h1

theorem runCell_mem (h : GoodRun hΓ hp1 hp' S N v Λ₀) {t c : ℕ}
    (hc : c < (S t).cells.length) : runCell S c ∈ (S t).cells := by
  rw [← h.getElem_cells hc]
  exact List.getElem_mem hc

theorem lt_len_self (h : GoodRun hΓ hp1 hp' S N v Λ₀) (c : ℕ) : c < (S c).cells.length := by
  have := h.add_two_le_len c
  omega

theorem cellβ_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) {t c : ℕ}
    (hc : c < (S t).cells.length) : (S t).cellβ c = runβ S c := by
  rw [RawState.cellβ_eq _ hc, h.getElem_cells hc]
  rfl

/-! ### The cells of a run partition the line -/

theorem runA_measurable (h : GoodRun hΓ hp1 hp' S N v Λ₀) (c : ℕ) :
    MeasurableSet (runA S c) :=
  (h.good c).meas _ (h.runCell_mem (h.lt_len_self c))

theorem runβ_localBasis (h : GoodRun hΓ hp1 hp' S N v Λ₀) (c : ℕ) :
    LocalBasis p (runβ S c) (runA S c) 2 :=
  (h.good c).basis _ (h.runCell_mem (h.lt_len_self c))

theorem runA_disjoint (h : GoodRun hΓ hp1 hp' S N v Λ₀) :
    Pairwise fun i j => Disjoint (runA S i) (runA S j) := by
  intro i j hij
  have hlen := h.add_two_le_len (max i j)
  have hi : i < (S (max i j)).cells.length := by
    have := le_max_left i j
    omega
  have hj : j < (S (max i j)).cells.length := by
    have := le_max_right i j
    omega
  have hd := (h.good (max i j)).disjoint_getElem hi hj hij
  rwa [h.getElem_cells hi, h.getElem_cells hj] at hd

theorem runA_iUnion (h : GoodRun hΓ hp1 hp' S N v Λ₀) : ⋃ c, runA S c = univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨t, ht⟩ := exists_nat_gt |x|
  have hR : (t : ℝ) ≤ (S t).R := by
    have := (h.good t).radius
    rwa [h.stages_length] at this
  have hx : x ∈ Ico (-(S t).R) (S t).R :=
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [← (h.good t).cover] at hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
  rw [h.getElem_cells hk] at hxc
  exact mem_iUnion.mpr ⟨k, hxc⟩

/-! ### Flags and indices of the coordinate cells -/

theorem flag_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) {t c : ℕ} (hc : c < (S t).cells.length) :
    (S t).flag c = runFlag S N c := by
  rw [Bool.eq_iff_iff, RawState.flag_eq_true_iff, runFlag_eq_true_iff]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, ha, h1, h2⟩
    obtain ⟨s, -, rfl⟩ := (h.mem_stages_iff t a).mp ha
    exact ⟨s, h1, h2⟩
  · rintro ⟨s, h1, h2⟩
    have hst : s < t := by
      by_contra hcon
      have := h.len_mono (not_lt.mp hcon)
      omega
    exact ⟨_, (h.mem_stages_iff t _).mpr ⟨s, hst, rfl⟩, h1, h2⟩

theorem runIndex_injective (h : GoodRun hΓ hp1 hp' S N v Λ₀) :
    Function.Injective (runIndex S N) := by
  have key : ∀ (s s' : ℕ) (i : Fin (N s)) (i' : Fin (N s')), s < s' →
      (S s).cells.length + i ≠ (S s').cells.length + i' := by
    intro s s' i i' hss' heq
    have h1 := h.block_le s
    have h2 := h.len_mono (show s + 1 ≤ s' from hss')
    have := i.2
    omega
  rintro (_ | ⟨s, i⟩) (_ | ⟨s', i'⟩) hxy
  · rfl
  · exfalso
    have := h.add_two_le_len s'
    simp only [runIndex] at hxy
    omega
  · exfalso
    have := h.add_two_le_len s
    simp only [runIndex] at hxy
    omega
  · simp only [runIndex] at hxy
    rcases lt_trichotomy s s' with hlt | rfl | hgt
    · exact absurd hxy (key s s' i i' hlt)
    · have hii : i = i' := Fin.ext (by omega)
      rw [hii]
    · exact absurd hxy.symm (key s' s i' i hgt)

/-! ### The positive forest of a run -/

/-- **The positive forest of a good run.** Its projection is the coordinate projection of
the global splitting for the cells of the run; its coordinates of the stage `s` are the
first vectors of the coordinate cells created at that stage; its roots are the roots of
the cells; both constants are `2`. -/
theorem exists_forest (h : GoodRun hΓ hp1 hp' S N v Λ₀) :
    ∃ F : PositiveForest (LebesgueLp p) p.toReal, F.B = 2 ∧ F.D = 2 ∧ F.N = N ∧
      F.e0 = runβ S 0 0 ∧
      (∀ s (i : ℕ) (hi : i < F.N s),
        F.coord s ⟨i, hi⟩ = runβ S ((S s).cells.length + i) 0) ∧
      (∀ j, F.root j = rootVec (runβ S) (runFlag S N) j) := by
  obtain ⟨PY, hPY⟩ := exists_globalSplitting_of_iUnion_eq_univ hp' h.runA_measurable
    h.runA_disjoint h.runA_iUnion h.runβ_localBasis (runFlag S N)
  obtain ⟨b₀, hb₀, hb₀proj⟩ := hPY.exists_root_basis
  have hker : (Submodule.span ℂ (Set.range (rootVec (runβ S) (runFlag S N)))).topologicalClosure =
      LinearMap.ker (PY : LebesgueLp p →ₗ[ℂ] LebesgueLp p) := by
    ext x
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, ← hPY.apply_eq_zero_iff,
      LinearMap.mem_ker]
    rfl
  obtain ⟨b, hb, hbproj⟩ := exists_schauderBasis_of_eq hker b₀ hb₀proj
  have hfix : ∀ x, PY (cellCoord (runβ S) (runIndex S N x)) =
      cellCoord (runβ S) (runIndex S N x) :=
    fun x => hPY.apply_coord _ (runFlag_runIndex S N x)
  have hdense : ∀ y, PY y = y → y ∈ closure (Submodule.span ℂ
      (Set.range fun x => cellCoord (runβ S) (runIndex S N x)) : Set (LebesgueLp p)) := by
    intro y hy
    refine closure_mono (SetLike.coe_subset_coe.mpr (Submodule.span_mono ?_))
      (hPY.mem_coord_closure y hy)
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨x, rfl⟩ := exists_runIndex_of_flag hc
    exact ⟨x, rfl⟩
  have hbnorm : ∀ j, ‖b j‖ = 1 := by
    intro j
    rw [Submodule.coe_norm, hb j, hb₀ j]
    exact hPY.root_norm j
  refine ⟨PositiveForest.ofFamily (cellCoord (runβ S)) hPY.coord_norm_rpow N h.size
    (runIndex S N) h.runIndex_injective PY hPY.apply_apply 2 hPY.norm_le hfix hdense b hbnorm
    2 hbproj, rfl, rfl, rfl, rfl, fun s i hi => rfl, fun j => ?_⟩
  exact (hb j).trans (hb₀ j)

section Forest

variable {F : PositiveForest (LebesgueLp p) p.toReal}

/-- The averages of the forest are the averages of the states. -/
theorem avg_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) (hFN : F.N = N)
    (hFcoord : ∀ s (i : ℕ) (hi : i < F.N s),
      F.coord s ⟨i, hi⟩ = runβ S ((S s).cells.length + i) 0)
    {s t : ℕ} (hst : s < t) : F.avg s = (S t).avg s := by
  have hN : F.N s = N s := congrFun hFN s
  have h1 : ∑ i : Fin (F.N s), F.coord s i =
      ∑ i ∈ Finset.range (F.N s), runβ S ((S s).cells.length + i) 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => runβ S ((S s).cells.length + i) 0) (F.N s)]
    exact Finset.sum_congr rfl fun i _ => hFcoord s i i.2
  have h2 : ∑ i ∈ Finset.range (N s), (S t).cellβ ((S s).cells.length + i) 0 =
      ∑ i ∈ Finset.range (N s), runβ S ((S s).cells.length + i) 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have h3 := h.block_le s
    have h4 := h.len_mono (show s + 1 ≤ t from hst)
    rw [h.cellβ_eq (by omega)]
  rw [PositiveForest.avg, h1, hN, RawState.avg, h.size_eq hst, h.start_eq hst, h2]

/-- **The targets of the forest are the targets of the states.** -/
theorem target_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) (hFN : F.N = N)
    (hFcoord : ∀ s (i : ℕ) (hi : i < F.N s),
      F.coord s ⟨i, hi⟩ = runβ S ((S s).cells.length + i) 0)
    (hFroot : ∀ j, F.root j = rootVec (runβ S) (runFlag S N) j) (t : ℕ) :
    F.target t = (S t).target := by
  rw [PositiveForest.target, RawState.target, h.stages_length]
  split_ifs with hn
  · rw [hFroot]
    have h1 := stagePair_fst_add_snd_le t
    have h2 := Nat.unpair_left_le (stagePair t).1
    have h3 := h.add_two_le_len t
    have hc : (Nat.unpair (stagePair t).1).1 < (S t).cells.length := by omega
    simp only [rootVec]
    rw [h.cellβ_eq hc, h.flag_eq hc]
  · exact h.avg_eq hFN hFcoord (predStage_lt hn)

/-- **The births of a stage are scaled atoms of the forest**: the packet identity
`T_{λᵢ} V = d (eᵢ + 2 N^{-1/q} h)`. -/
theorem birth_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) (hp : 2 < p) (hFN : F.N = N)
    (hFcoord : ∀ s (i : ℕ) (hi : i < F.N s),
      F.coord s ⟨i, hi⟩ = runβ S ((S s).cells.length + i) 0)
    (hFroot : ∀ j, F.root j = rootVec (runβ S) (runFlag S N) j) (t : ℕ) (i : Fin (N t)) :
    translate p (stageParams hΓ (S t) (N t) (v t) (Λ₀ t) i)
        (referenceFunction p (v t) (S t).target (stageParams hΓ (S t) (N t) (v t) (Λ₀ t))) =
      ((posScale p.toReal ‖v t‖ (N t) : ℝ) : ℂ) • F.seq (F.offset t + i) := by
  have hN : F.N t = N t := congrFun hFN t
  have hi : (i : ℕ) < F.N t := by
    rw [hN]
    exact i.2
  have P := stage_packet hΓ hp hp' (h.good t) (h.size t) (h.deficit t) (h.adm t) (Λ₀ t)
  have hlen : (S t).cells.length + i < (S (t + 1)).cells.length := by
    have := h.block_le t
    have := i.2
    omega
  have hcoord : F.coord t ⟨i, hi⟩ =
      posRemainder p (v t) (S t).target (stageParams hΓ (S t) (N t) (v t) (Λ₀ t)) i := by
    rw [hFcoord t i hi, ← h.cellβ_eq hlen]
    exact (h.step t).coord i
  rw [P.translate_eq i, F.seq_offset_add' t hi, PositiveForest.atom, hcoord,
    h.target_eq hFN hFcoord hFroot t, hN, Local.ofReal_smul_eq, Local.ofReal_smul_eq]

/-- **The births of a run are the sequence of the forest, up to positive scales.** -/
theorem births_eq (h : GoodRun hΓ hp1 hp' S N v Λ₀) (hp : 2 < p) (hFN : F.N = N)
    (hFe0 : F.e0 = runβ S 0 0)
    (hFcoord : ∀ s (i : ℕ) (hi : i < F.N s),
      F.coord s ⟨i, hi⟩ = runβ S ((S s).cells.length + i) 0)
    (hFroot : ∀ j, F.root j = rootVec (runβ S) (runFlag S N) j)
    (dd : ℕ → ℂ) (hdd0 : dd 0 = 1)
    (hdd : ∀ t (i : ℕ), i < N t →
      dd (F.offset t + i) = ((posScale p.toReal ‖v t‖ (N t) : ℝ) : ℂ)) (t : ℕ) :
    (S t).births.length = F.offset t ∧
      ∀ n, n < F.offset t → ((S t).births[n]?).map Prod.snd = some (dd n • F.seq n) := by
  induction t with
  | zero =>
    have hb : (S 0).births = [(0, intervalAtom p (0, 1))] := by
      rw [h.init]
      rfl
    have he0 : F.e0 = intervalAtom p (0, 1) := by
      rw [hFe0]
      show (S 0).cellβ 0 0 = _
      rw [h.init]
      exact initRaw_cellβ_zero hp1 hp'
    refine ⟨by rw [hb, F.offset_zero]; rfl, fun n hn => ?_⟩
    rw [F.offset_zero] at hn
    obtain rfl : n = 0 := by omega
    rw [hb, F.seq_zero, hdd0, one_smul, he0]
    rfl
  | succ t ih =>
    have hN : F.N t = N t := congrFun hFN t
    refine ⟨by rw [(h.step t).births, List.length_append, List.length_ofFn, ih.1,
      F.offset_succ, hN], fun n hn => ?_⟩
    rw [(h.step t).births]
    rcases lt_or_ge n (F.offset t) with hlt | hge
    · rw [List.getElem?_append_left (by rw [ih.1]; exact hlt)]
      exact ih.2 n hlt
    · rw [F.offset_succ, hN] at hn
      have hi : n - F.offset t < N t := by omega
      have hn' : n = F.offset t + (n - F.offset t) := by omega
      rw [List.getElem?_append_right (by rw [ih.1]; exact hge), ih.1,
        List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn,
        Option.map_some]
      congr 1
      rw [h.birth_eq hp hFN hFcoord hFroot t ⟨n - F.offset t, hi⟩,
        ← hdd t (n - F.offset t) hi, ← hn']

end Forest

/-- **The birth vectors of a good run form a Schauder basis** of `Lᵖ(ℝ)` all of whose
partial sum projections have norm at most `50 = 4 · 2 · (1 + 2) + 13 · 2`. -/
theorem exists_basis (h : GoodRun hΓ hp1 hp' S N v Λ₀) (hp : 2 < p) :
    ∃ Bas : SchauderBasis ℂ (LebesgueLp p),
      (∀ t n (hn : n < (S t).births.length), Bas n = ((S t).births.get ⟨n, hn⟩).2) ∧
      ∀ M, ‖Bas.proj M‖ ≤ 50 := by
  classical
  obtain ⟨F, hFB, hFD, hFN, hFe0, hFcoord, hFroot⟩ := h.exists_forest
  have hr : 1 ≤ p.toReal := by
    have := two_lt_toReal hp hp'
    linarith
  have hdpos : ∀ t, 0 < posScale p.toReal ‖v t‖ (N t) := fun t =>
    posScale_pos (lt_of_lt_of_le (by norm_num) (h.adm t).lower)
      (lt_of_le_of_lt (h.deficit t) (by norm_num))
  obtain ⟨dd, hdddef⟩ : ∃ dd : ℕ → ℂ, ∀ n, dd n = if n = 0 then 1 else
      ((posScale p.toReal ‖v (F.stageIdx n)‖ (N (F.stageIdx n)) : ℝ) : ℂ) := ⟨_, fun _ => rfl⟩
  have hddne : ∀ n, dd n ≠ 0 := by
    intro n
    rw [hdddef]
    split_ifs
    · exact one_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (hdpos _).ne'
  have hdd0 : dd 0 = 1 := by rw [hdddef, if_pos rfl]
  have hdd : ∀ t (i : ℕ), i < N t →
      dd (F.offset t + i) = ((posScale p.toReal ‖v t‖ (N t) : ℝ) : ℂ) := by
    intro t i hi
    have hne : F.offset t + i ≠ 0 := by
      have := F.offset_pos t
      omega
    rw [hdddef, if_neg hne, F.stageIdx_offset_add t (by rw [congrFun hFN t]; exact hi)]
  have hbirths := h.births_eq hp hFN hFe0 hFcoord hFroot dd hdd0 hdd
  refine ⟨StructuredBases.rescale (F.basis hr) dd hddne, fun t n hn => ?_, fun M => ?_⟩
  · have h1 := (hbirths t).2 n (by rw [← (hbirths t).1]; exact hn)
    rw [List.getElem?_eq_getElem hn, Option.map_some] at h1
    rw [StructuredBases.rescale_apply, PositiveForest.basis_apply, List.get_eq_getElem]
    exact (Option.some.inj h1).symm
  · rw [StructuredBases.rescale_proj]
    refine (F.norm_basis_proj_le hr M).trans ?_
    rw [hFB, hFD]
    norm_num

end GoodRun

end Machine

end StructuredBases.PositiveTranslates
