import Lean_Code.Basis.Criterion
import Lean_Code.PositiveTranslates.Forest.Blocks

/-!
# The positive forest: data and the sequence

`PositiveForest Z r` packages the abstract Banach space data of the "positive forest"
(paper, proof of `thm:translate-properties`(iii)):

* a bounded projection `PY` on a complex Banach space `Z`, with range `Y` and kernel `X`;
* a unit vector `e0` and, for every stage `s`, vectors `coord s i` (`i : Fin (N s)`) in `Y`
  which together behave like the unit vector basis of `ℓ^r` and span a dense subspace of `Y`;
* a normalized basis `root j` of `X` with basis constant `D`.

From these data we define, following the fixed schedule `stagePair` of
`Lean_Code/PositiveTranslates/Forest/Schedule.lean`,

* `avg s = (N s)^{-1/r} • ∑ᵢ coord s i` (a unit vector),
* `target s = root j` if `stagePair s = (j, 0)` and `target s = avg (stageOf (j, n - 1))` if
  `stagePair s = (j, n)` with `n ≥ 1`,
* `atom s i = coord s i + (2 (N s)^{-(r-1)/r}) • target s`,
* `seq`: `e0`, followed by the atoms of stage `0`, then those of stage `1`, …; the atom
  `atom s i` has the index `offset s + i`, `offset s = 1 + ∑_{s' < s} N s'`.

The main theorem (`PositiveForest.exists_schauderBasis` in `Forest/Main.lean`) says that
`seq` is a Schauder basis of `Z` with basis constant at most `4 D (1 + B) + 13 B`.
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates

open Forest

/-- The data of the positive forest in a complex normed space `Z` with exponent `r`
(in the application `Z = L^r(ℝ)`; the theorems assume `1 ≤ r`).

How to verify the fields in the application:

* `lr_norm` is the statement that `e0` and the vectors `coord s i` behave like the unit
  vector basis of `ℓ^r`. It is only required for coefficient families living on an initial
  segment `Finset.range T` of the stages (with arbitrary functions as coefficients); this is
  the weakest of the equivalent formulations — every finitely supported family lives on
  such a segment — and it is also the form which the proof uses. A user who has a family
  `g : ι → Z` of pairwise disjointly supported unit functions in `L^r`, i.e. a family with
  `‖∑_{x ∈ S} c x • g x‖^r = ∑_{x ∈ S} ‖c x‖^r` for all finite `S`, obtains `lr_norm` from
  `lr_norm_of_family` (file `Forest/Tools.lean`) by specifying an injection
  `Option (Σ s, Fin (N s)) → ι`; `lr_norm_of_sigma` treats a hypothesis stated on finite
  subsets of `Σ s, Fin (N s)`. Conversely, the identity for an arbitrary finite set of
  stages is `PositiveForest.lr_norm_finset`.
* `coord_dense` says that the range of `PY` is contained in the closed span of `e0` and the
  coordinates (the other inclusion follows from `PY_e0`, `PY_coord`).
* `root_dense` and `root_prefix` say that `root` is a basis of `ker PY` with basis constant
  at most `D`; for the vectors of a `SchauderBasis` of the kernel whose partial sum
  projections have norm `≤ D` they are `mem_closure_span_of_schauderBasis` and
  `root_prefix_of_schauderBasis` (file `Forest/Tools.lean`). Together with `norm_root` they
  imply `1 ≤ D` (`PositiveForest.one_le_D`).
* The norm of `e0` is not a field: `‖e0‖ = 1` follows from `lr_norm`
  (`PositiveForest.norm_e0`), as does `‖coord s i‖ = 1` (`PositiveForest.norm_coord`).

The hypotheses are consistent: `Forest/Model.lean` constructs a positive forest in
`ℓ^p × ℓ^p`. -/
structure PositiveForest (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z] (r : ℝ) where
  /-- The bounded projection onto the closed span `Y` of `e0` and the coordinates. -/
  PY : Z →L[ℂ] Z
  /-- A bound for the norm of the projection `PY`. -/
  B : ℝ
  /-- The basis constant of the roots. -/
  D : ℝ
  /-- The first vector of the sequence. -/
  e0 : Z
  /-- The roots: a normalized basis of `X = ker PY`. -/
  root : ℕ → Z
  /-- The number of coordinate vectors (and of atoms) of stage `s`. -/
  N : ℕ → ℕ
  /-- The coordinate vectors of stage `s`. -/
  coord : (s : ℕ) → Fin (N s) → Z
  /-- `PY` is a projection. -/
  PY_idem : ∀ z, PY (PY z) = PY z
  /-- `PY` has norm at most `B`. -/
  norm_PY_le : ‖PY‖ ≤ B
  /-- Every stage has at least one coordinate vector. -/
  N_pos : ∀ s, 1 ≤ N s
  /-- `e0` lies in the range `Y` of `PY`. -/
  PY_e0 : PY e0 = e0
  /-- The coordinate vectors lie in the range `Y` of `PY`. -/
  PY_coord : ∀ s i, PY (coord s i) = coord s i
  /-- `e0` and the coordinate vectors behave like the unit vector basis of `ℓ^r`. -/
  lr_norm : ∀ (c0 : ℂ) (T : ℕ) (c : (s : ℕ) → Fin (N s) → ℂ),
    ‖c0 • e0 + ∑ s ∈ Finset.range T, ∑ i, c s i • coord s i‖ ^ r =
      ‖c0‖ ^ r + ∑ s ∈ Finset.range T, ∑ i, ‖c s i‖ ^ r
  /-- The range of `PY` is contained in the closed span of `e0` and the coordinates. -/
  coord_dense : ∀ y, PY y = y →
    y ∈ closure (Submodule.span ℂ (insert e0 (⋃ s, Set.range (coord s))) : Set Z)
  /-- The roots lie in the kernel `X` of `PY`. -/
  PY_root : ∀ j, PY (root j) = 0
  /-- The roots are unit vectors. -/
  norm_root : ∀ j, ‖root j‖ = 1
  /-- The kernel of `PY` is contained in the closed span of the roots. -/
  root_dense : ∀ x, PY x = 0 → x ∈ closure (Submodule.span ℂ (Set.range root) : Set Z)
  /-- The prefix inequality of the roots (basis constant at most `D`). -/
  root_prefix : ∀ (t : ℕ → ℂ) (m M : ℕ), m ≤ M →
    ‖∑ j ∈ Finset.range m, t j • root j‖ ≤ D * ‖∑ j ∈ Finset.range M, t j • root j‖

namespace PositiveForest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ} (F : PositiveForest Z r)

/-! ### The derived vectors -/

/-- The normalized average `u s = (N s)^{-1/r} • ∑ᵢ coord s i` of the coordinates of stage
`s`; it is a unit vector (`PositiveForest.norm_avg`). -/
def avg (s : ℕ) : Z := (((F.N s : ℝ) ^ (-1 / r) : ℝ) : ℂ) • ∑ i, F.coord s i

/-- The target `h s` of stage `s`: the root `root j` if `stagePair s = (j, 0)`, and the
average of the previous family `(j, n - 1)` of the same target if `stagePair s = (j, n)` with
`n ≥ 1`. -/
def target (s : ℕ) : Z :=
  if (stagePair s).2 = 0 then F.root (stagePair s).1
  else F.avg (stageOf ((stagePair s).1, (stagePair s).2 - 1))

/-- The atoms `x s i = coord s i + (2 (N s)^{-(r-1)/r}) • h s` of stage `s`. -/
def atom (s : ℕ) (i : Fin (F.N s)) : Z :=
  F.coord s i + ((2 * (F.N s : ℝ) ^ (-(r - 1) / r) : ℝ) : ℂ) • F.target s

theorem avg_eq (s : ℕ) : F.avg s = (primalScale r (F.N s) : ℂ) • ∑ i, F.coord s i := rfl

theorem atom_eq (s : ℕ) (i : Fin (F.N s)) :
    F.atom s i = F.coord s i + (2 * (dualScale r (F.N s) : ℂ)) • F.target s := by
  rw [atom, dualScale]
  push_cast
  rfl

theorem target_eq (s : ℕ) :
    F.target s = if (stagePair s).2 = 0 then F.root (stagePair s).1 else F.avg (predStage s) :=
  rfl

/-- The target of the first family of target `j` is the root `root j`. -/
@[simp] theorem target_stageOf_zero (j : ℕ) : F.target (stageOf (j, 0)) = F.root j := by
  simp [target]

/-- The target of the family `(j, n + 1)` is the average of the family `(j, n)`. -/
@[simp] theorem target_stageOf_succ (j n : ℕ) :
    F.target (stageOf (j, n + 1)) = F.avg (stageOf (j, n)) := by
  simp [target]

/-- The target of the next family of the same target is the average of the present one. -/
@[simp] theorem target_succStage (s : ℕ) : F.target (succStage s) = F.avg s := by
  rw [target_eq, if_neg (stagePair_snd_succStage_ne s), predStage_succStage]

theorem N_pos' (s : ℕ) : 0 < F.N s := F.N_pos s

/-! ### The enumeration of the atoms -/

/-- The index of the first atom of stage `s` in the sequence `seq`:
`offset s = 1 + ∑_{s' < s} N s'`. -/
def offset (s : ℕ) : ℕ := 1 + ∑ s' ∈ Finset.range s, F.N s'

@[simp] theorem offset_zero : F.offset 0 = 1 := by simp [offset]

theorem offset_succ (s : ℕ) : F.offset (s + 1) = F.offset s + F.N s := by
  simp [offset, Finset.sum_range_succ, add_assoc]

theorem offset_strictMono : StrictMono F.offset :=
  strictMono_nat_of_lt_succ fun s => by
    rw [offset_succ]
    have := F.N_pos s
    omega

theorem offset_pos (s : ℕ) : 1 ≤ F.offset s := by simp [offset]

theorem lt_offset (s : ℕ) : s < F.offset s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [offset_succ]
    have := F.N_pos s
    omega

theorem exists_lt_offset_succ (n : ℕ) : ∃ s, n < F.offset (s + 1) :=
  ⟨n, (Nat.lt_succ_self n).trans (F.lt_offset (n + 1))⟩

/-- The stage to which the `n`-th vector of `seq` belongs (`n ≥ 1`): the least `s` with
`n < offset (s + 1)`. -/
def stageIdx (n : ℕ) : ℕ := Nat.find (F.exists_lt_offset_succ n)

theorem lt_offset_stageIdx_succ (n : ℕ) : n < F.offset (F.stageIdx n + 1) :=
  Nat.find_spec (F.exists_lt_offset_succ n)

theorem offset_stageIdx_le {n : ℕ} (hn : 1 ≤ n) : F.offset (F.stageIdx n) ≤ n := by
  rcases Nat.eq_zero_or_pos (F.stageIdx n) with h | h
  · rw [h, offset_zero]
    exact hn
  · have hmin : ¬ n < F.offset (F.stageIdx n - 1 + 1) :=
      Nat.find_min (F.exists_lt_offset_succ n) (Nat.sub_lt h Nat.one_pos)
    rw [Nat.sub_add_cancel h] at hmin
    exact not_lt.mp hmin

theorem sub_offset_stageIdx_lt {n : ℕ} (hn : 1 ≤ n) :
    n - F.offset (F.stageIdx n) < F.N (F.stageIdx n) := by
  have h1 := F.lt_offset_stageIdx_succ n
  rw [offset_succ] at h1
  have h2 := F.offset_stageIdx_le hn
  omega

theorem stageIdx_offset_add (s : ℕ) {i : ℕ} (hi : i < F.N s) :
    F.stageIdx (F.offset s + i) = s := by
  unfold stageIdx
  rw [Nat.find_eq_iff]
  refine ⟨by rw [offset_succ]; omega, fun t ht h => ?_⟩
  have : F.offset (t + 1) ≤ F.offset s := F.offset_strictMono.monotone (Nat.succ_le_of_lt ht)
  omega

/-- The sequence of the positive forest: `seq 0 = e0`, followed by the atoms of stage `0`
(in the order of `i`), then those of stage `1`, and so on; see `seq_offset_add`. -/
def seq (n : ℕ) : Z :=
  if h : n = 0 then F.e0
  else F.atom (F.stageIdx n)
    ⟨n - F.offset (F.stageIdx n), F.sub_offset_stageIdx_lt (Nat.one_le_iff_ne_zero.mpr h)⟩

@[simp] theorem seq_zero : F.seq 0 = F.e0 := by simp [seq]

theorem atom_congr {s t : ℕ} (h : s = t) {i i' : ℕ} (hi : i < F.N s) (hi' : i' < F.N t)
    (hii : i = i') : F.atom s ⟨i, hi⟩ = F.atom t ⟨i', hi'⟩ := by
  subst h
  subst hii
  rfl

/-- The atom `atom s i` is the vector number `offset s + i` of the sequence. -/
theorem seq_offset_add (s : ℕ) (i : Fin (F.N s)) : F.seq (F.offset s + i) = F.atom s i := by
  have hne : F.offset s + i ≠ 0 := by
    have := F.offset_pos s
    omega
  have hs := F.stageIdx_offset_add s i.2
  rw [seq, dif_neg hne]
  exact F.atom_congr hs _ i.2 (by rw [hs]; omega)

theorem seq_offset_add' (s : ℕ) {i : ℕ} (hi : i < F.N s) :
    F.seq (F.offset s + i) = F.atom s ⟨i, hi⟩ :=
  F.seq_offset_add s ⟨i, hi⟩

/-- Every index `n ≥ 1` is of the form `offset s + i`. -/
theorem exists_offset_add {n : ℕ} (hn : 1 ≤ n) :
    ∃ s, ∃ i : Fin (F.N s), n = F.offset s + i :=
  ⟨F.stageIdx n, ⟨n - F.offset (F.stageIdx n), F.sub_offset_stageIdx_lt hn⟩, by
    have := F.offset_stageIdx_le hn
    simp only
    omega⟩

/-- The representation `n = offset s + i` is unique. -/
theorem offset_add_inj {s t : ℕ} {i : Fin (F.N s)} {j : Fin (F.N t)}
    (h : F.offset s + i = F.offset t + j) : s = t ∧ (i : ℕ) = j := by
  have hs := F.stageIdx_offset_add s i.2
  have ht := F.stageIdx_offset_add t j.2
  rw [h, ht] at hs
  subst hs
  exact ⟨rfl, by omega⟩

/-- Every index `n ≥ 1` is of the form `offset s + i` for a unique pair `(s, i)`. -/
theorem existsUnique_offset_add {n : ℕ} (hn : 1 ≤ n) :
    ∃! p : (Σ s, Fin (F.N s)), n = F.offset p.1 + (p.2 : ℕ) := by
  obtain ⟨s, i, hsi⟩ := F.exists_offset_add hn
  refine ⟨⟨s, i⟩, hsi, ?_⟩
  rintro ⟨t, j⟩ htj
  simp only at htj
  obtain ⟨hst, hij⟩ := F.offset_add_inj (hsi.symm.trans htj)
  subst hst
  have : i = j := Fin.ext hij
  subst this
  rfl

/-- The vectors of `seq` are `e0` and the atoms. -/
theorem range_seq : Set.range F.seq = insert F.e0 (⋃ s, Set.range (F.atom s)) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with h | h
    · left
      rw [h, seq_zero]
    · right
      obtain ⟨s, i, hsi⟩ := F.exists_offset_add h
      exact ⟨s, i, by rw [hsi, seq_offset_add]⟩
  · rintro (rfl | ⟨s, i, rfl⟩)
    · exact ⟨0, F.seq_zero⟩
    · exact ⟨_, F.seq_offset_add s i⟩

/-- Partial sums up to the beginning of a stage, sorted by stages. -/
theorem sum_range_offset (a : ℕ → ℂ) (T : ℕ) :
    ∑ n ∈ Finset.range (F.offset T), a n • F.seq n =
      a 0 • F.e0 +
        ∑ s ∈ Finset.range T, ∑ i : Fin (F.N s), a (F.offset s + i) • F.atom s i := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [offset_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, add_assoc]
    congr 2
    rw [← Fin.sum_univ_eq_sum_range
      (fun x => a (F.offset T + x) • F.seq (F.offset T + x)) (F.N T)]
    exact Finset.sum_congr rfl fun i _ => by rw [seq_offset_add]

end PositiveForest

end StructuredBases.PositiveTranslates
