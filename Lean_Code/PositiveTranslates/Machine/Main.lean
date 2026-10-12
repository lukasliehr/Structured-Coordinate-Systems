import Lean_Code.PositiveTranslates.Machine.Run

/-!
# The reference construction as a stage machine

This is the top file of `Lean_Code/PositiveTranslates/Machine/`. It constructs the
*reference construction* of the paper's Theorem `thm:translate-properties`(iii) (sections
"Constructing the functions on the line" and the proof of (iii)) as an instance of the
interface `StageMachine` of `Lean_Code/PositiveTranslates/StageMachine.lean`:

* `Machine.stageMachine hΓ hp hp' : StageMachine p Γ` for `2 < p < ∞` and every set
  `Γ ⊆ ℝ` that is unbounded above;
* `nonempty_stageMachine` : the existence statement consumed by the analytic half
  (`Lean_Code/PositiveTranslates/Analytic/Main.lean`).

## The construction

* **States** (`Machine/State.lean`): the good raw states `{S : RawState p // S.Good}`. A
  state consists of a committed radius `R`, a finite list of cells (regions partitioning
  `[-R, R)`, each with a non-negative compact-step local basis of prefix constant `2`), the
  list of completed stages (position and number of their coordinate cells) and the list of
  births.
* **Target** of the next stage `t`, `(j, n) = stagePair t`: the root number `j` of the cell
  list if `n = 0`, and the normalized average of the coordinates of the stage
  `stageOf (j, n - 1)` if `n ≥ 1`.
* **Parameters**: `placement hΓ R₁ T N` with `R₁` at least the committed radius and a
  support radius of the input, and `T` at least the requested bound and all old parameters.
* **One stage** (`Machine/Stage.lean`): the positive packet gives unit remainders `eᵢ` in
  pairwise disjoint closed private regions outside `[-R₁, R₁]`; every `eᵢ` becomes the first
  vector of a new coordinate cell (its positivity intervals together with a room interval);
  the rest of a larger committed interval is filled with gap cells; the translates
  `T_{λᵢ} V` are appended to the births.
* **Runs** (`Machine/Run.lean`): the cells of a run partition the line; the global
  splitting and the abstract positive forest show that the births, which are positive
  multiples of the vectors of the forest, form a Schauder basis with all partial sum
  projections bounded by `K = 4 · 2 · (1 + 2) + 13 · 2 = 50`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

namespace Machine

variable {p : ℝ≥0∞}

theorem one_lt_of_two_lt (hp : 2 < p) : 1 < p := lt_trans (by norm_num) hp

/-- The smallest packet size allowed by the machine: from this size on the deficit
`2^p (N-1) N^{-(p-1)}` is at most `1/2`. -/
def minSize (hp : 2 < p) (hp' : p ≠ ∞) : ℕ :=
  Classical.choose (exists_posDeficit_le_half (two_lt_toReal hp hp'))

theorem one_le_minSize (hp : 2 < p) (hp' : p ≠ ∞) : 1 ≤ minSize hp hp' :=
  (Classical.choose_spec (exists_posDeficit_le_half (two_lt_toReal hp hp'))).1

theorem posDeficit_le_of_minSize_le (hp : 2 < p) (hp' : p ≠ ∞) {N : ℕ}
    (hN : minSize hp hp' ≤ N) : posDeficit p.toReal N ≤ 1 / 2 :=
  (Classical.choose_spec (exists_posDeficit_le_half (two_lt_toReal hp hp'))).2 N hN

/-- The states of the machine: the raw states satisfying the invariants. -/
abbrev GoodState (p : ℝ≥0∞) [Fact (1 ≤ p)] : Type := {S : RawState p // S.Good}

variable [Fact (1 ≤ p)] {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ)

/-- The next state: a successor chosen by `exists_step` when the packet size is at least
`minSize` and the input is admissible, and the unchanged state otherwise. -/
def nextState (hp : 2 < p) (hp' : p ≠ ∞) (S : GoodState p) (N : ℕ) (v : LebesgueLp p)
    (Λ₀ : ℝ) : GoodState p := by
  classical
  exact if h : minSize hp hp' ≤ N ∧ Admissible v then
    ⟨Classical.choose (exists_step hΓ hp hp' S.2 ((one_le_minSize hp hp').trans h.1)
        (posDeficit_le_of_minSize_le hp hp' h.1) h.2 Λ₀),
      (Classical.choose_spec (exists_step hΓ hp hp' S.2 ((one_le_minSize hp hp').trans h.1)
        (posDeficit_le_of_minSize_le hp hp' h.1) h.2 Λ₀)).1⟩
  else S

theorem nextState_step (hp : 2 < p) (hp' : p ≠ ∞) (S : GoodState p) {N : ℕ}
    (hN : minSize hp hp' ≤ N) {v : LebesgueLp p} (hv : Admissible v) (Λ₀ : ℝ) :
    Step hΓ S.1 N v Λ₀ (nextState hΓ hp hp' S N v Λ₀).1 := by
  unfold nextState
  rw [dif_pos ⟨hN, hv⟩]
  exact (Classical.choose_spec (exists_step hΓ hp hp' S.2 ((one_le_minSize hp hp').trans hN)
    (posDeficit_le_of_minSize_le hp hp' hN) hv Λ₀)).2

/-- **The reference construction** of the paper's Theorem `thm:translate-properties`(iii)
as a stage machine, for `2 < p < ∞` and a parameter set `Γ` that is unbounded above. The
basis constant of every run is at most `50`. -/
def stageMachine (hp : 2 < p) (hp' : p ≠ ∞) : StageMachine p Γ where
  State := GoodState p
  init := ⟨initRaw (one_lt_of_two_lt hp) hp', initRaw_good (one_lt_of_two_lt hp) hp'⟩
  births := fun S => S.1.births
  target := fun S => S.1.target
  minSize := fun _ => minSize hp hp'
  params := fun S N v Λ₀ => stageParams hΓ S.1 N v Λ₀
  next := nextState hΓ hp hp'
  K := 50
  births_init := rfl
  target_step := fun S => (S.2.isTarget hp').step
  target_nonneg := fun S => (S.2.isTarget hp').nonneg
  target_norm := fun S => (S.2.isTarget hp').norm
  minSize_pos := fun _ => one_le_minSize hp hp'
  deficit_le := fun _ _ hN => posDeficit_le_of_minSize_le hp hp' hN
  params_mem := fun S N v Λ₀ i => stageParams_mem hΓ S.1 N v Λ₀ i
  params_gt := fun S N v Λ₀ i => lt_stageParams hΓ S.1 N v Λ₀ i
  params_gt_old := fun S N v Λ₀ i _ hb => lt_stageParams_of_mem hΓ S.1 N v Λ₀ i hb
  params_injective := fun S N v Λ₀ => stageParams_injective hΓ S.1 N v Λ₀
  births_next := fun S _ _ Λ₀ hN hv => (nextState_step hΓ hp hp' S hN hv Λ₀).births
  reference_edit_norm := fun S _ _ Λ₀ hN hv =>
    (stage_packet hΓ hp hp' S.2 ((one_le_minSize hp hp').trans hN)
      (posDeficit_le_of_minSize_le hp hp' hN) hv Λ₀).edit_norm
  reference_norm_ge := fun S _ _ Λ₀ hN hv =>
    (stage_packet hΓ hp hp' S.2 ((one_le_minSize hp hp').trans hN)
      (posDeficit_le_of_minSize_le hp hp' hN) hv Λ₀).norm_le
  basis_of_run := by
    intro S N v Λ₀ hS0 hnext hmin hadm
    have hrun : GoodRun hΓ (one_lt_of_two_lt hp) hp' (fun t => (S t).1) N v Λ₀ :=
      { init := congrArg Subtype.val hS0
        good := fun t => (S t).2
        size := fun t => (one_le_minSize hp hp').trans (hmin t)
        deficit := fun t => posDeficit_le_of_minSize_le hp hp' (hmin t)
        adm := hadm
        step := fun t => by
          rw [hnext t]
          exact nextState_step hΓ hp hp' (S t) (hmin t) (hadm t) (Λ₀ t) }
    exact hrun.exists_basis hp

/-- The basis constant of the reference construction. -/
@[simp] theorem stageMachine_K (hp : 2 < p) (hp' : p ≠ ∞) :
    (stageMachine hΓ hp hp').K = 50 := rfl

end Machine

set_option linter.unusedVariables false in
/-- **The reference construction exists.** For `2 < p < ∞` and every set `Γ ⊆ ℝ` that
contains `0` and is unbounded above there is a stage machine with parameters in `Γ`: the
reference construction of the paper's Theorem `thm:translate-properties`(iii). (The
hypothesis `0 ∈ Γ` is not used by the construction: the parameter `0` of the initial vector
`𝟙_[0,1)` is part of the interface, and all later parameters `Machine.stageParams` are
positive elements of `Γ`.) -/
@[nolint unusedArguments]
theorem nonempty_stageMachine (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (Γ : Set ℝ) (h0 : (0 : ℝ) ∈ Γ) (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) :
    Nonempty (StageMachine p Γ) :=
  ⟨Machine.stageMachine hΓ hp hp'⟩

end StructuredBases.PositiveTranslates
