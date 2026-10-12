import Lean_Code.SchauderTranslates.Lp.PacketSupport

/-!
# Placement of packet parameters inside a prescribed unbounded set

Paper, Lemma `tr:lem:placement`. Let `Γ ⊆ ℝ` be unbounded above. We choose successively
`γ₀, γ₁, … ∈ Γ` with

`γ_j > 4 ∑_{i<j} γ_i + 4R`, `γ_j > T`, `γ_j > 0`   (paper, eq. `tr:eq:placement`),

and show that the first `N` of them are strictly increasing and satisfy the separation
property `SeparatedModeIntervals R Λ` consumed by the packet files of
`Lean_Code/SchauderTranslates/Lp/`: the intervals `[c - R, c + R]` with centers
`c ∈ {0} ∪ {±Λ i} ∪ {Λ i - Λ j}` are pairwise disjoint.

Main declarations (namespace `StructuredBases.PositiveTranslates`):

* `Lacunary R Λ` : the growth condition `Λ j > 4 ∑_{i<j} Λ i + 4R`;
* `separated_of_lacunary` : `Lacunary R Λ → SeparatedModeIntervals R Λ` (for `R ≥ 0`, `Λ > 0`);
* `placementSeq hΓ R T : ℕ → ℝ`, `placement hΓ R T N : Fin N → ℝ` : the explicit choice;
* `exists_placement` : the existence statement.
-/

noncomputable section
open scoped BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates SchauderTranslates.LpConstruction

/-! ### The growth condition and the separation it implies -/

/-- The growth condition of the paper, eq. `tr:eq:placement`:
`Λ j > 4 ∑_{i<j} Λ i + 4R` for every `j`. -/
def Lacunary {N : ℕ} (R : ℝ) (Λ : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, 4 * ∑ i ∈ Finset.Iio j, Λ i + 4 * R < Λ j

/-- Every symbolic center of a packet has coefficients in `{-1, 0, 1}`. -/
theorem abs_packetMode_le_one {N : ℕ} {k : Fin N → ℤ} (hk : k ∈ packetModes N) (i : Fin N) :
    |k i| ≤ 1 := by
  classical
  simp only [packetModes, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hk
  rcases hk with rfl | ⟨⟨j, rfl⟩ | ⟨j, rfl⟩⟩ | ⟨⟨j, l⟩, rfl⟩
  · simp
  · simp only [Pi.single_apply]
    split_ifs <;> simp
  · simp only [Pi.neg_apply, Pi.single_apply]
    split_ifs <;> simp
  · simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp

/-- The quantitative heart of the placement lemma: a nonzero integer combination of
lacunary parameters with coefficients in `{-2, …, 2}` has modulus larger than `2R`. -/
theorem two_mul_lt_abs_frequencyDot {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ} (hR : 0 ≤ R)
    (hpos : ∀ i, 0 < Λ i) (hlac : Lacunary R Λ) {m : Fin N → ℤ} (hm : m ≠ 0)
    (hb : ∀ i, |m i| ≤ 2) : 2 * R < |frequencyDot m Λ| := by
  classical
  have hs : (Finset.univ.filter fun i => m i ≠ 0).Nonempty := by
    by_contra hne
    apply hm
    funext i
    by_contra hi
    exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = (Finset.univ.filter fun i => m i ≠ 0).max' hs := ⟨_, rfl⟩
  have hmj : m j ≠ 0 := by
    have hmem := Finset.max'_mem _ hs
    rw [← hjdef] at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hgt : ∀ i, j < i → m i = 0 := by
    intro i hi
    by_contra hne
    have hle : i ≤ (Finset.univ.filter fun i => m i ≠ 0).max' hs :=
      Finset.le_max' _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    rw [← hjdef] at hle
    exact absurd hi (not_lt.mpr hle)
  have hsplit : frequencyDot m Λ =
      (m j : ℝ) * Λ j + ∑ i ∈ Finset.univ.erase j, (m i : ℝ) * Λ i :=
    (Finset.add_sum_erase Finset.univ (fun i => (m i : ℝ) * Λ i) (Finset.mem_univ j)).symm
  have hrest : |∑ i ∈ Finset.univ.erase j, (m i : ℝ) * Λ i| ≤ 2 * ∑ i ∈ Finset.Iio j, Λ i := by
    calc |∑ i ∈ Finset.univ.erase j, (m i : ℝ) * Λ i|
        ≤ ∑ i ∈ Finset.univ.erase j, |(m i : ℝ) * Λ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Iio j, |(m i : ℝ) * Λ i| := by
          symm
          apply Finset.sum_subset
          · intro i hi
            exact Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_Iio.mp hi), Finset.mem_univ i⟩
          · intro i hi hni
            have hij : j < i := by
              rcases lt_trichotomy i j with h | h | h
              · exact absurd (Finset.mem_Iio.mpr h) hni
              · exact absurd h (Finset.mem_erase.mp hi).1
              · exact h
            simp [hgt i hij]
      _ ≤ ∑ i ∈ Finset.Iio j, 2 * Λ i := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_pos (hpos i)]
          have h2 : |(m i : ℝ)| ≤ 2 := by exact_mod_cast hb i
          exact mul_le_mul_of_nonneg_right h2 (hpos i).le
      _ = 2 * ∑ i ∈ Finset.Iio j, Λ i := by rw [Finset.mul_sum]
  have hmain : Λ j ≤ |(m j : ℝ) * Λ j| := by
    rw [abs_mul, abs_of_pos (hpos j)]
    have h1 : (1 : ℝ) ≤ |(m j : ℝ)| := by exact_mod_cast Int.one_le_abs hmj
    nlinarith [hpos j]
  have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.Iio j, Λ i :=
    Finset.sum_nonneg (fun i _ => (hpos i).le)
  have hl := hlac j
  have habs : |(m j : ℝ) * Λ j| ≤
      |frequencyDot m Λ| + |∑ i ∈ Finset.univ.erase j, (m i : ℝ) * Λ i| := by
    have h := abs_sub (frequencyDot m Λ) (∑ i ∈ Finset.univ.erase j, (m i : ℝ) * Λ i)
    rwa [hsplit, add_sub_cancel_right, ← hsplit] at h
  linarith

/-- Paper, Lemma `tr:lem:placement` (disjointness part): lacunary positive parameters
satisfy the separation hypothesis of the packet lemmas. -/
theorem separated_of_lacunary {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ} (hR : 0 ≤ R)
    (hpos : ∀ i, 0 < Λ i) (hlac : Lacunary R Λ) : SeparatedModeIntervals R Λ := by
  intro k hk l hl hkl
  apply disjoint_center_intervals
  rw [← frequencyDot_sub]
  apply two_mul_lt_abs_frequencyDot hR hpos hlac (sub_ne_zero.mpr hkl)
  intro i
  have h1 := abs_packetMode_le_one hk i
  have h2 := abs_packetMode_le_one hl i
  calc |(k - l) i| = |k i - l i| := rfl
    _ ≤ |k i| + |l i| := abs_sub _ _
    _ ≤ 2 := by linarith

/-- Shrinking the radius preserves separation. -/
theorem separatedModeIntervals_mono {N : ℕ} {R R' : ℝ} {Λ : Fin N → ℝ}
    (h : SeparatedModeIntervals R Λ) (hRR' : R' ≤ R) : SeparatedModeIntervals R' Λ := by
  intro k hk l hl hkl
  exact (h k hk l hl hkl).mono
    (Set.Icc_subset_Icc (by linarith) (by linarith))
    (Set.Icc_subset_Icc (by linarith) (by linarith))

/-- For increasing parameters the last one is the largest: `Λ i ≤ Λ (N-1)`. -/
theorem le_last_of_monotone {N : ℕ} {Λ : Fin N → ℝ} (hmono : Monotone Λ) (hN : 1 ≤ N)
    (i : Fin N) : Λ i ≤ Λ ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ :=
  hmono (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt))

/-! ### The successive choice inside `Γ` -/

/-- Partial sums `∑_{i<n} γ_i` of the successively chosen parameters. -/
def placementSum {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (R T : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => placementSum hΓ R T n +
      Classical.choose (hΓ (max (max T 0) (4 * placementSum hΓ R T n + 4 * R)))

/-- The `n`-th parameter: an element of `Γ` larger than `T`, `0` and
`4 ∑_{i<n} γ_i + 4R`. -/
def placementSeq {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (R T : ℝ) (n : ℕ) : ℝ :=
  Classical.choose (hΓ (max (max T 0) (4 * placementSum hΓ R T n + 4 * R)))

/-- The first `N` parameters, as a family indexed by `Fin N`. -/
def placement {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (R T : ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => placementSeq hΓ R T i

section Choice

variable {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) (R T : ℝ)

theorem placementSeq_spec (n : ℕ) :
    placementSeq hΓ R T n ∈ Γ ∧
      max (max T 0) (4 * placementSum hΓ R T n + 4 * R) < placementSeq hΓ R T n :=
  Classical.choose_spec (hΓ (max (max T 0) (4 * placementSum hΓ R T n + 4 * R)))

theorem placementSeq_mem (n : ℕ) : placementSeq hΓ R T n ∈ Γ :=
  (placementSeq_spec hΓ R T n).1

theorem lt_placementSeq (n : ℕ) : T < placementSeq hΓ R T n :=
  lt_of_le_of_lt ((le_max_left T 0).trans (le_max_left _ _)) (placementSeq_spec hΓ R T n).2

theorem placementSeq_pos (n : ℕ) : 0 < placementSeq hΓ R T n :=
  lt_of_le_of_lt ((le_max_right T 0).trans (le_max_left _ _)) (placementSeq_spec hΓ R T n).2

theorem placementSum_lt_placementSeq (n : ℕ) :
    4 * placementSum hΓ R T n + 4 * R < placementSeq hΓ R T n :=
  lt_of_le_of_lt (le_max_right _ _) (placementSeq_spec hΓ R T n).2

theorem placementSum_succ (n : ℕ) :
    placementSum hΓ R T (n + 1) = placementSum hΓ R T n + placementSeq hΓ R T n := rfl

theorem placementSum_eq_sum (n : ℕ) :
    placementSum hΓ R T n = ∑ i ∈ Finset.range n, placementSeq hΓ R T i := by
  induction n with
  | zero => simp [placementSum]
  | succ n ih => rw [placementSum_succ, Finset.sum_range_succ, ih]

theorem placementSum_nonneg (n : ℕ) : 0 ≤ placementSum hΓ R T n := by
  rw [placementSum_eq_sum]
  exact Finset.sum_nonneg (fun i _ => (placementSeq_pos hΓ R T i).le)

theorem placement_apply (N : ℕ) (i : Fin N) :
    placement hΓ R T N i = placementSeq hΓ R T i := rfl

theorem placement_mem (N : ℕ) (i : Fin N) : placement hΓ R T N i ∈ Γ :=
  placementSeq_mem hΓ R T i

theorem lt_placement (N : ℕ) (i : Fin N) : T < placement hΓ R T N i :=
  lt_placementSeq hΓ R T i

theorem placement_pos (N : ℕ) (i : Fin N) : 0 < placement hΓ R T N i :=
  placementSeq_pos hΓ R T i

theorem sum_Iio_placement (N : ℕ) (j : Fin N) :
    ∑ i ∈ Finset.Iio j, placement hΓ R T N i = placementSum hΓ R T j := by
  rw [placementSum_eq_sum, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
  rfl

theorem placement_lacunary (N : ℕ) : Lacunary R (placement hΓ R T N) := by
  intro j
  rw [sum_Iio_placement]
  exact placementSum_lt_placementSeq hΓ R T j

end Choice

/-- The chosen parameters are strictly increasing. -/
theorem placementSeq_strictMono {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) {R : ℝ}
    (hR : 0 ≤ R) (T : ℝ) : StrictMono (placementSeq hΓ R T) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := placementSum_lt_placementSeq hΓ R T (n + 1)
  rw [placementSum_succ] at h1
  have h2 := placementSum_nonneg hΓ R T n
  have h3 := placementSeq_pos hΓ R T n
  linarith

theorem placement_strictMono {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) {R : ℝ}
    (hR : 0 ≤ R) (T : ℝ) (N : ℕ) : StrictMono (placement hΓ R T N) :=
  fun _ _ hij => placementSeq_strictMono hΓ hR T (Fin.lt_def.mp hij)

/-- The chosen parameters satisfy the separation hypothesis of the packet lemmas. -/
theorem placement_separated {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) {R : ℝ}
    (hR : 0 ≤ R) (T : ℝ) (N : ℕ) : SeparatedModeIntervals R (placement hΓ R T N) :=
  separated_of_lacunary hR (placement_pos hΓ R T N) (placement_lacunary hΓ R T N)

/-- **Placement inside a prescribed set** (paper, Lemma `tr:lem:placement`).
If `Γ` is unbounded above then for every radius `R ≥ 0`, every `N` and every threshold `T`
there are `Λ 0 < ⋯ < Λ (N-1)` in `Γ`, all larger than `T` and positive, such that the
intervals `[c - R, c + R]` with centers `c ∈ {0} ∪ {±Λ i} ∪ {Λ i - Λ j : i ≠ j}` are
pairwise disjoint (in the form `SeparatedModeIntervals R Λ` used by the packet lemmas). -/
theorem exists_placement {Γ : Set ℝ} (hΓ : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ) {R : ℝ} (hR : 0 ≤ R)
    (N : ℕ) (T : ℝ) :
    ∃ Λ : Fin N → ℝ, (∀ i, Λ i ∈ Γ) ∧ (∀ i, T < Λ i) ∧ (∀ i, 0 < Λ i) ∧ StrictMono Λ ∧
      SeparatedModeIntervals R Λ :=
  ⟨placement hΓ R T N, placement_mem hΓ R T N, lt_placement hΓ R T N, placement_pos hΓ R T N,
    placement_strictMono hΓ hR T N, placement_separated hΓ hR T N⟩

end StructuredBases.PositiveTranslates
