import Mathlib

/-!
# The schedule of the positive forest

Targets are indexed by `j : ℕ`, the families of target `j` by `n : ℕ`. The stages are
grouped in rounds `J = 0, 1, 2, …`; round `J` consists of the `J + 2` stages

`(J, 0), (0, J + 1), (1, J), (2, J - 1), …, (J, 1)`

in this order: first the first family of the new target `J`, then one further family for
each of the targets `0, …, J`.

* `stagePair : ℕ → ℕ × ℕ` is the resulting enumeration (defined by the successor rule
  `nextPair`), `stageOf : ℕ × ℕ → ℕ` its inverse (given by a closed formula in terms of
  `roundStart`), `stageEquiv : ℕ ≃ ℕ × ℕ` the bundled bijection.
* `stagePair_roundStart`, `stagePair_roundStart_add`: the explicit description of the rounds.
* `stageOf_lt_stageOf_succ`: for each target the families occur in increasing order.
* `stageOf_first_strictMono`: the first families `(j, 0)` occur in increasing order of `j`.
* `succStage`, `predStage`: the next / previous family of the same target.
* `sum_range_succStage`, `sum_range_firstStage`: the two reindexing lemmas used to rewrite
  sums over stages.
* `sum_stage_weight_le`: at every moment `s⋆`, the families which are the latest started family
  of their target (or whose successor is just being introduced) have total weight
  `∑ 2⁻ⁿ ≤ 3`. This is the only quantitative property of the schedule which is used.
-/

open scoped BigOperators

namespace StructuredBases.PositiveTranslates

/-! ### Definition of the enumeration -/

/-- The pair following `(j, n)` in the schedule:
`(J, 0) ↦ (0, J + 1)`, `(j, n + 2) ↦ (j + 1, n + 1)`, `(J, 1) ↦ (J + 1, 0)`. -/
def nextPair : ℕ × ℕ → ℕ × ℕ
  | (j, 0) => (0, j + 1)
  | (j, 1) => (j + 1, 0)
  | (j, n + 2) => (j + 1, n + 1)

/-- `stagePair s = (j, n)` means that stage `s` is the `n`-th family of target `j`. -/
def stagePair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | s + 1 => nextPair (stagePair s)

/-- The first stage of round `J`; round `J` has `J + 2` stages. -/
def roundStart : ℕ → ℕ
  | 0 => 0
  | J + 1 => roundStart J + (J + 2)

/-- The stage at which the `n`-th family of target `j` is introduced:
`(j, 0)` opens round `j`, and `(j, n + 1)` is the stage number `j + 1` of round `j + n`. -/
def stageOf : ℕ × ℕ → ℕ
  | (j, 0) => roundStart j
  | (j, n + 1) => roundStart (j + n) + (j + 1)

@[simp] theorem stagePair_zero : stagePair 0 = (0, 0) := rfl

theorem stagePair_succ (s : ℕ) : stagePair (s + 1) = nextPair (stagePair s) := rfl

@[simp] theorem roundStart_zero : roundStart 0 = 0 := rfl

theorem roundStart_succ (J : ℕ) : roundStart (J + 1) = roundStart J + (J + 2) := rfl

theorem stageOf_first (j : ℕ) : stageOf (j, 0) = roundStart j := rfl

theorem stageOf_later (j n : ℕ) : stageOf (j, n + 1) = roundStart (j + n) + (j + 1) := rfl

/-- Closed formula: round `J` starts at the stage `J (J + 3) / 2`. -/
theorem two_mul_roundStart (J : ℕ) : 2 * roundStart J = J * (J + 3) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [roundStart_succ, mul_add, ih]
    ring

theorem roundStart_strictMono : StrictMono roundStart :=
  strictMono_nat_of_lt_succ fun J => by rw [roundStart_succ]; omega

theorem le_roundStart (J : ℕ) : J ≤ roundStart J := roundStart_strictMono.le_apply

/-! ### The two maps are inverse to each other -/

theorem stageOf_nextPair (p : ℕ × ℕ) : stageOf (nextPair p) = stageOf p + 1 := by
  obtain ⟨j, n⟩ := p
  match n with
  | 0 => simp [nextPair, stageOf]
  | 1 =>
    simp only [nextPair, stageOf, add_zero]
    rw [roundStart_succ]
    omega
  | n + 2 =>
    simp only [nextPair, stageOf]
    have h : j + 1 + n = j + (n + 1) := by omega
    rw [h]
    omega

@[simp] theorem stageOf_stagePair (s : ℕ) : stageOf (stagePair s) = s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [stagePair_succ, stageOf_nextPair, ih]

/-- The pair preceding a pair different from `(0, 0)`. -/
private def prevPair : ℕ × ℕ → ℕ × ℕ
  | (0, 0) => (0, 0)
  | (0, n + 1) => (n, 0)
  | (j + 1, 0) => (j, 1)
  | (j + 1, n + 1) => (j, n + 2)

private theorem nextPair_prevPair {p : ℕ × ℕ} (hp : p ≠ (0, 0)) : nextPair (prevPair p) = p := by
  obtain ⟨j, n⟩ := p
  match j, n with
  | 0, 0 => exact absurd rfl hp
  | 0, n + 1 => rfl
  | j + 1, 0 => rfl
  | j + 1, n + 1 => rfl

@[simp] theorem stagePair_stageOf (p : ℕ × ℕ) : stagePair (stageOf p) = p := by
  have key : ∀ s : ℕ, ∀ p : ℕ × ℕ, stageOf p = s → stagePair s = p := by
    intro s
    induction s with
    | zero =>
      intro p hp
      by_contra hne
      have h0 : p ≠ (0, 0) := fun h => hne (by rw [h]; rfl)
      have h1 := stageOf_nextPair (prevPair p)
      rw [nextPair_prevPair h0, hp] at h1
      omega
    | succ s ih =>
      intro p hp
      have h0 : p ≠ (0, 0) := by
        rintro rfl
        simp [stageOf] at hp
      have h1 := stageOf_nextPair (prevPair p)
      rw [nextPair_prevPair h0, hp] at h1
      have h2 : stagePair s = prevPair p := ih _ (by omega)
      rw [stagePair_succ, h2, nextPair_prevPair h0]
  exact key _ p rfl

/-- The schedule as a bijection between stages and pairs (target, family). -/
def stageEquiv : ℕ ≃ ℕ × ℕ where
  toFun := stagePair
  invFun := stageOf
  left_inv := stageOf_stagePair
  right_inv := stagePair_stageOf

@[simp] theorem stageEquiv_apply (s : ℕ) : stageEquiv s = stagePair s := rfl

@[simp] theorem stageEquiv_symm_apply (p : ℕ × ℕ) : stageEquiv.symm p = stageOf p := rfl

theorem stagePair_bijective : Function.Bijective stagePair := stageEquiv.bijective

theorem stageOf_bijective : Function.Bijective stageOf := stageEquiv.symm.bijective

theorem stagePair_injective : Function.Injective stagePair := stagePair_bijective.1

theorem stageOf_injective : Function.Injective stageOf := stageOf_bijective.1

theorem stageOf_eq_iff {p : ℕ × ℕ} {s : ℕ} : stageOf p = s ↔ stagePair s = p :=
  ⟨fun h => by rw [← h, stagePair_stageOf], fun h => by rw [← h, stageOf_stagePair]⟩

/-! ### Explicit description of the rounds -/

/-- Round `J` starts with the first family of the new target `J`. -/
theorem stagePair_roundStart (J : ℕ) : stagePair (roundStart J) = (J, 0) := by
  rw [← stageOf_first, stagePair_stageOf]

/-- The stage number `j + 1` of round `J` (`j ≤ J`) is the family `J + 1 - j` of target `j`. -/
theorem stagePair_roundStart_add {J j : ℕ} (hj : j ≤ J) :
    stagePair (roundStart J + (j + 1)) = (j, J + 1 - j) := by
  have h : stageOf (j, (J - j) + 1) = roundStart J + (j + 1) := by
    rw [stageOf_later]
    have : j + (J - j) = J := by omega
    rw [this]
  rw [← h, stagePair_stageOf]
  have : J - j + 1 = J + 1 - j := by omega
  rw [this]

/-- Every stage belongs to exactly one round: it is either the opening stage
`roundStart J` or one of the stages `roundStart J + (j + 1)`, `j ≤ J`. -/
theorem exists_roundStart_eq (s : ℕ) :
    ∃ J, s = roundStart J ∨ ∃ j ≤ J, s = roundStart J + (j + 1) := by
  rcases hp : stagePair s with ⟨j, n⟩
  have hs : s = stageOf (j, n) := by rw [← hp, stageOf_stagePair]
  match n with
  | 0 => exact ⟨j, Or.inl hs⟩
  | n + 1 => exact ⟨j + n, Or.inr ⟨j, by omega, hs⟩⟩

/-! ### Order properties -/

/-- For each target the families occur in increasing order. -/
theorem stageOf_lt_stageOf_succ (j n : ℕ) : stageOf (j, n) < stageOf (j, n + 1) := by
  match n with
  | 0 =>
    rw [stageOf_first, stageOf_later]
    simp
  | n + 1 =>
    rw [stageOf_later, stageOf_later]
    have h : j + (n + 1) = j + n + 1 := by omega
    rw [h, roundStart_succ]
    omega

theorem stageOf_family_strictMono (j : ℕ) : StrictMono fun n => stageOf (j, n) :=
  strictMono_nat_of_lt_succ fun n => stageOf_lt_stageOf_succ j n

/-- The first families occur in increasing order of the targets. -/
theorem stageOf_first_strictMono : StrictMono fun j => stageOf (j, 0) :=
  roundStart_strictMono

theorem stageOf_first_lt_iff {i j : ℕ} : stageOf (i, 0) < stageOf (j, 0) ↔ i < j :=
  stageOf_first_strictMono.lt_iff_lt

theorem stageOf_first_le_stageOf (j n : ℕ) : stageOf (j, 0) ≤ stageOf (j, n) :=
  (stageOf_family_strictMono j).monotone (Nat.zero_le n)

theorem add_le_stageOf (j n : ℕ) : j + n ≤ stageOf (j, n) := by
  match n with
  | 0 => simpa [stageOf_first] using le_roundStart j
  | n + 1 =>
    rw [stageOf_later]
    have := le_roundStart (j + n)
    omega

theorem le_stageOf_first (j : ℕ) : j ≤ stageOf (j, 0) := le_roundStart j

theorem stagePair_fst_add_snd_le (s : ℕ) : (stagePair s).1 + (stagePair s).2 ≤ s := by
  have h := add_le_stageOf (stagePair s).1 (stagePair s).2
  rwa [Prod.mk.eta, stageOf_stagePair] at h

/-- For every moment `s⋆`, the targets whose first family was introduced before `s⋆` form
an initial segment. -/
theorem exists_stageOf_first_lt_iff (sStar : ℕ) :
    ∃ q ≤ sStar, ∀ j, stageOf (j, 0) < sStar ↔ j < q := by
  classical
  have hex : ∃ q, sStar ≤ stageOf (q, 0) := ⟨sStar, le_stageOf_first sStar⟩
  refine ⟨Nat.find hex, ?_, fun j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Nat.find_min' hex (le_stageOf_first sStar)
  · by_contra hj
    have h1 : stageOf (Nat.find hex, 0) ≤ stageOf (j, 0) :=
      stageOf_first_strictMono.monotone (not_lt.mp hj)
    have h2 := Nat.find_spec hex
    omega
  · exact not_le.mp (Nat.find_min hex h)

/-! ### Rounds and their monotonicity -/

/-- The round to which a pair belongs. -/
def roundOf (p : ℕ × ℕ) : ℕ := p.1 + (p.2 - 1)

theorem roundOf_le_roundOf_nextPair (p : ℕ × ℕ) : roundOf p ≤ roundOf (nextPair p) := by
  obtain ⟨j, n⟩ := p
  match n with
  | 0 => simp [nextPair, roundOf]
  | 1 => simp [nextPair, roundOf]
  | n + 2 => simp only [nextPair, roundOf]; omega

/-- Later stages belong to later (or equal) rounds. -/
theorem roundOf_stagePair_monotone : Monotone fun s => roundOf (stagePair s) :=
  monotone_nat_of_le_succ fun s => by
    rw [stagePair_succ]
    exact roundOf_le_roundOf_nextPair _

/-- A stage lies in the round `roundOf (stagePair s)`. -/
theorem roundStart_roundOf_le (s : ℕ) : roundStart (roundOf (stagePair s)) ≤ s := by
  rcases hp : stagePair s with ⟨j, n⟩
  have hs : s = stageOf (j, n) := by rw [← hp, stageOf_stagePair]
  match n with
  | 0 => simp [roundOf, hs, stageOf_first]
  | n + 1 =>
    rw [hs, stageOf_later]
    simp [roundOf]

theorem lt_roundStart_roundOf_succ (s : ℕ) : s < roundStart (roundOf (stagePair s) + 1) := by
  rcases hp : stagePair s with ⟨j, n⟩
  have hs : s = stageOf (j, n) := by rw [← hp, stageOf_stagePair]
  match n with
  | 0 =>
    rw [hs, stageOf_first]
    simp only [roundOf, Nat.zero_sub, add_zero]
    exact roundStart_strictMono (Nat.lt_succ_self j)
  | n + 1 =>
    rw [hs, stageOf_later, roundStart_succ]
    simp only [roundOf, Nat.add_sub_cancel]
    omega

/-! ### Successor and predecessor inside a target -/

/-- The stage of the next family of the same target. -/
def succStage (s : ℕ) : ℕ := stageOf ((stagePair s).1, (stagePair s).2 + 1)

/-- The stage of the previous family of the same target (only meaningful if
`(stagePair s).2 ≠ 0`). -/
def predStage (s : ℕ) : ℕ := stageOf ((stagePair s).1, (stagePair s).2 - 1)

@[simp] theorem succStage_stageOf (j n : ℕ) : succStage (stageOf (j, n)) = stageOf (j, n + 1) := by
  simp [succStage]

@[simp] theorem stagePair_succStage (s : ℕ) :
    stagePair (succStage s) = ((stagePair s).1, (stagePair s).2 + 1) := by
  simp [succStage]

@[simp] theorem predStage_stageOf_succ (j n : ℕ) :
    predStage (stageOf (j, n + 1)) = stageOf (j, n) := by
  simp [predStage]

@[simp] theorem predStage_succStage (s : ℕ) : predStage (succStage s) = s := by
  simp [predStage]

theorem succStage_predStage {s : ℕ} (hs : (stagePair s).2 ≠ 0) : succStage (predStage s) = s := by
  simp only [predStage, succStage_stageOf]
  have h : (stagePair s).2 - 1 + 1 = (stagePair s).2 := by omega
  rw [h, Prod.mk.eta, stageOf_stagePair]

theorem lt_succStage (s : ℕ) : s < succStage s := by
  have h := stageOf_lt_stageOf_succ (stagePair s).1 (stagePair s).2
  rwa [Prod.mk.eta, stageOf_stagePair] at h

theorem predStage_lt {s : ℕ} (hs : (stagePair s).2 ≠ 0) : predStage s < s := by
  have h := lt_succStage (predStage s)
  rwa [succStage_predStage hs] at h

theorem succStage_injective : Function.Injective succStage := fun s t h => by
  have := congrArg predStage h
  simpa using this

theorem stagePair_snd_succStage_ne (s : ℕ) : (stagePair (succStage s)).2 ≠ 0 := by simp

/-- The first stage of the target of `s`. -/
def firstStage (s : ℕ) : ℕ := stageOf ((stagePair s).1, 0)

@[simp] theorem firstStage_stageOf (j n : ℕ) : firstStage (stageOf (j, n)) = stageOf (j, 0) := by
  simp [firstStage]

@[simp] theorem firstStage_succStage (s : ℕ) : firstStage (succStage s) = firstStage s := by
  simp [firstStage]

theorem firstStage_eq_self {s : ℕ} (hs : (stagePair s).2 = 0) : firstStage s = s := by
  rw [firstStage, ← hs, Prod.mk.eta, stageOf_stagePair]

/-- Within a target, a later family is not introduced before the successor of an earlier
family. -/
theorem succStage_le_of_snd_lt {s t : ℕ} (h1 : (stagePair s).1 = (stagePair t).1)
    (h2 : (stagePair s).2 < (stagePair t).2) : succStage s ≤ t := by
  have h := (stageOf_family_strictMono (stagePair t).1).monotone (Nat.succ_le_of_lt h2)
  simp only [Nat.succ_eq_add_one] at h
  rwa [Prod.mk.eta, stageOf_stagePair, ← h1] at h

/-! ### Reindexing sums over stages -/

section Reindex

variable {M : Type*} [AddCommMonoid M]

/-- Reindexing by the successor inside the targets: the stages which are not a first
family are exactly the successors. -/
theorem sum_range_succStage (T : ℕ) (G : ℕ → M) (hG : ∀ s, T ≤ s → G s = 0) :
    ∑ s ∈ Finset.range T, G (succStage s) =
      ∑ s ∈ Finset.range T, if (stagePair s).2 = 0 then 0 else G s := by
  classical
  have h1 : ∑ s ∈ Finset.range T, G (succStage s) =
      ∑ s ∈ (Finset.range T).filter (fun s => succStage s < T), G (succStage s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · exact hG _ (not_lt.mp h)
  have h2 : ∑ s ∈ Finset.range T, (if (stagePair s).2 = 0 then 0 else G s) =
      ∑ s ∈ (Finset.range T).filter (fun s => (stagePair s).2 ≠ 0), G s := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : (stagePair s).2 = 0 <;> simp [h]
  have h3 : (Finset.range T).filter (fun s => (stagePair s).2 ≠ 0) =
      ((Finset.range T).filter (fun s => succStage s < T)).image succStage := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hs, hn⟩
      exact ⟨predStage s, ⟨(predStage_lt hn).trans hs, by rwa [succStage_predStage hn]⟩,
        succStage_predStage hn⟩
    · rintro ⟨t, ⟨_, ht⟩, rfl⟩
      exact ⟨ht, stagePair_snd_succStage_ne t⟩
  rw [h1, h2, h3, Finset.sum_image fun _ _ _ _ h => succStage_injective h]

/-- Reindexing the first families by their targets. -/
theorem sum_range_firstStage (T : ℕ) (G : ℕ → M) (hG : ∀ s, T ≤ s → G s = 0) :
    ∑ j ∈ Finset.range T, G (stageOf (j, 0)) =
      ∑ s ∈ Finset.range T, if (stagePair s).2 = 0 then G s else 0 := by
  classical
  have h1 : ∑ j ∈ Finset.range T, G (stageOf (j, 0)) =
      ∑ j ∈ (Finset.range T).filter (fun j => stageOf (j, 0) < T), G (stageOf (j, 0)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · exact hG _ (not_lt.mp h)
  have h2 : ∑ s ∈ Finset.range T, (if (stagePair s).2 = 0 then G s else 0) =
      ∑ s ∈ (Finset.range T).filter (fun s => (stagePair s).2 = 0), G s := by
    rw [Finset.sum_filter]
  have h3 : (Finset.range T).filter (fun s => (stagePair s).2 = 0) =
      ((Finset.range T).filter (fun j => stageOf (j, 0) < T)).image fun j => stageOf (j, 0) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hs, hn⟩
      have hs' : stageOf ((stagePair s).1, 0) = s := by
        rw [← hn, Prod.mk.eta, stageOf_stagePair]
      exact ⟨(stagePair s).1, ⟨lt_of_le_of_lt (by
        have := stagePair_fst_add_snd_le s
        omega) hs, by rwa [hs']⟩, hs'⟩
    · rintro ⟨j, ⟨_, hj⟩, rfl⟩
      exact ⟨hj, by simp⟩
  rw [h1, h2, h3, Finset.sum_image fun i _ j _ h => by
    simpa using congrArg (fun s => (stagePair s).1) h]

end Reindex

/-- For non-negative weights vanishing beyond `T`, summing over the successors loses mass. -/
theorem sum_range_succStage_le (T : ℕ) (g : ℕ → ℝ) (h0 : ∀ s, 0 ≤ g s)
    (hg : ∀ s, T ≤ s → g s = 0) :
    ∑ s ∈ Finset.range T, g (succStage s) ≤ ∑ s ∈ Finset.range T, g s := by
  rw [sum_range_succStage T g hg]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs
  · exact h0 s
  · exact le_rfl

/-- For non-negative weights vanishing on the first families, passing to the successors
gains mass. -/
theorem sum_range_le_sum_succStage (T : ℕ) (g : ℕ → ℝ) (h0 : ∀ s, 0 ≤ g s)
    (hg : ∀ j, g (stageOf (j, 0)) = 0) :
    ∑ s ∈ Finset.range T, g s ≤ ∑ s ∈ Finset.range T, g (succStage s) := by
  have h1 := sum_range_succStage T (fun s => if s < T then g s else 0)
    (fun s hs => if_neg (not_lt.mpr hs))
  calc ∑ s ∈ Finset.range T, g s
      = ∑ s ∈ Finset.range T, if (stagePair s).2 = 0 then 0 else if s < T then g s else 0 := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [if_pos (Finset.mem_range.mp hs)]
        split_ifs with h
        · rw [← firstStage_eq_self h]
          exact hg _
        · rfl
    _ = ∑ s ∈ Finset.range T, if succStage s < T then g (succStage s) else 0 := h1.symm
    _ ≤ ∑ s ∈ Finset.range T, g (succStage s) := by
        refine Finset.sum_le_sum fun s _ => ?_
        split_ifs
        · exact le_rfl
        · exact h0 _

/-! ### The weight estimate -/

/-- The stages `s ≤ s⋆ < succStage s` (the latest family of each started target) have
total weight `∑ 2⁻ⁿ ≤ 2`: the target `j` is at least in its family `J - j`, where `J` is
the current round. -/
theorem sum_stage_weight_active_le (sStar T : ℕ) :
    ∑ s ∈ Finset.range T,
      (if s ≤ sStar ∧ sStar < succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0) ≤ 2 := by
  classical
  set J := roundOf (stagePair sStar) with hJ
  set A := (Finset.range T).filter (fun s => s ≤ sStar ∧ sStar < succStage s) with hA
  have hmem : ∀ s ∈ A, (stagePair s).1 ≤ J ∧ J - (stagePair s).1 ≤ (stagePair s).2 := by
    intro s hs
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hs
    have e1 : roundOf (stagePair s) ≤ J := roundOf_stagePair_monotone h1
    have e2 : J ≤ roundOf (stagePair (succStage s)) := roundOf_stagePair_monotone h2.le
    rw [stagePair_succStage] at e2
    simp only [roundOf, Nat.add_sub_cancel] at e1 e2
    constructor <;> omega
  have hinj : Set.InjOn (fun s => (stagePair s).1) (A : Set ℕ) := by
    intro s hs t ht hst
    have hs' := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
    have ht' := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    simp only at hst
    apply stagePair_injective
    refine Prod.ext hst ?_
    rcases lt_trichotomy (stagePair s).2 (stagePair t).2 with h | h | h
    · have := succStage_le_of_snd_lt hst h
      omega
    · exact h
    · have := succStage_le_of_snd_lt hst.symm h
      omega
  calc ∑ s ∈ Finset.range T,
        (if s ≤ sStar ∧ sStar < succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0)
      = ∑ s ∈ A, (1 / 2 : ℝ) ^ (stagePair s).2 := by rw [hA, Finset.sum_filter]
    _ ≤ ∑ s ∈ A, (1 / 2 : ℝ) ^ (J - (stagePair s).1) :=
        Finset.sum_le_sum fun s hs =>
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (hmem s hs).2
    _ = ∑ j ∈ A.image (fun s => (stagePair s).1), (1 / 2 : ℝ) ^ (J - j) :=
        (Finset.sum_image (f := fun j => (1 / 2 : ℝ) ^ (J - j)) hinj).symm
    _ ≤ ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ (J - j) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro j hj
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmem s hs).1)
    _ = ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_range.mp hj
        congr 1
        omega
    _ ≤ 2 := sum_geometric_two_le _

/-- **Weight estimate.** At every moment `s⋆`, the stages `s ≤ s⋆ ≤ succStage s` have total
weight `∑ 2⁻ⁿ ≤ 3`, where `n` is the family index of `s`. -/
theorem sum_stage_weight_le (sStar T : ℕ) :
    ∑ s ∈ Finset.range T,
      (if s ≤ sStar ∧ sStar ≤ succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0) ≤ 3 := by
  classical
  have hone : ∑ s ∈ Finset.range T, (if succStage s = sStar then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    have : ((Finset.range T).filter fun s => succStage s = sStar).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact succStage_injective
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    exact_mod_cast this
  calc ∑ s ∈ Finset.range T,
        (if s ≤ sStar ∧ sStar ≤ succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0)
      ≤ ∑ s ∈ Finset.range T,
          ((if s ≤ sStar ∧ sStar < succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0) +
            (if succStage s = sStar then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have hw : (1 / 2 : ℝ) ^ (stagePair s).2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (stagePair s).2 := by positivity
        by_cases h1 : s ≤ sStar ∧ sStar ≤ succStage s
        · rw [if_pos h1]
          by_cases h2 : succStage s = sStar
          · rw [if_pos h2]
            split_ifs <;> linarith
          · rw [if_neg h2, if_pos ⟨h1.1, lt_of_le_of_ne h1.2 (Ne.symm h2)⟩]
            linarith
        · rw [if_neg h1]
          split_ifs <;> linarith
    _ = ∑ s ∈ Finset.range T,
          (if s ≤ sStar ∧ sStar < succStage s then (1 / 2 : ℝ) ^ (stagePair s).2 else 0) +
        ∑ s ∈ Finset.range T, (if succStage s = sStar then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ 2 + 1 := add_le_add (sum_stage_weight_active_le sStar T) hone
    _ = 3 := by norm_num

end StructuredBases.PositiveTranslates
