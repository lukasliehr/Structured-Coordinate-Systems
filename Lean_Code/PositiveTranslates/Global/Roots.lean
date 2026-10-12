import Lean_Code.PositiveTranslates.Global.LocalCoordinates

/-!
# Coordinates and roots of a family of local bases

Every cell `c` carries a local basis `β c`.  A *coordinate cell* (`isCoord c = true`)
contributes its first vector `β c 0` as a coordinate; all other local basis vectors are
roots.  The roots are enumerated by `Nat.unpair`, cell by cell in their local order.

This file contains the definitions and the properties inherited directly from
`LocalBasis` (norms, positivity, step structure, supports) together with the `ℓᵖ` identity
for the coordinates.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coordinate of the cell `c`: the first vector of its local basis.  It is used as a
coordinate only when `isCoord c`. -/
def cellCoord (β : ℕ → ℕ → LebesgueLp p) (c : ℕ) : LebesgueLp p := β c 0

/-- The position in the local basis of the `k`-th root of the cell `c`. -/
def rootIndex (isCoord : ℕ → Bool) (c k : ℕ) : ℕ := if isCoord c then k + 1 else k

/-- The roots: with `(c, k) = Nat.unpair j`, the `j`-th root is the `k`-th local basis
vector of the cell `c` that is not its coordinate. -/
def rootVec (β : ℕ → ℕ → LebesgueLp p) (isCoord : ℕ → Bool) (j : ℕ) : LebesgueLp p :=
  β (Nat.unpair j).1 (if isCoord (Nat.unpair j).1 then (Nat.unpair j).2 + 1 else (Nat.unpair j).2)

omit [Fact (1 ≤ p)] in
theorem cellCoord_apply (β : ℕ → ℕ → LebesgueLp p) (c : ℕ) : cellCoord β c = β c 0 := rfl

omit [Fact (1 ≤ p)] in
theorem rootVec_eq_rootIndex (β : ℕ → ℕ → LebesgueLp p) (isCoord : ℕ → Bool) (j : ℕ) :
    rootVec β isCoord j =
      β (Nat.unpair j).1 (rootIndex isCoord (Nat.unpair j).1 (Nat.unpair j).2) := rfl

omit [Fact (1 ≤ p)] in
theorem rootVec_pair (β : ℕ → ℕ → LebesgueLp p) (isCoord : ℕ → Bool) (c k : ℕ) :
    rootVec β isCoord (Nat.pair c k) = β c (if isCoord c then k + 1 else k) := by
  simp only [rootVec, Nat.unpair_pair]

omit [Fact (1 ≤ p)] in
theorem rootVec_pair_of_coord (β : ℕ → ℕ → LebesgueLp p) {isCoord : ℕ → Bool} {c : ℕ}
    (hc : isCoord c = true) (k : ℕ) : rootVec β isCoord (Nat.pair c k) = β c (k + 1) := by
  rw [rootVec_pair, if_pos hc]

omit [Fact (1 ≤ p)] in
theorem rootVec_pair_of_not_coord (β : ℕ → ℕ → LebesgueLp p) {isCoord : ℕ → Bool} {c : ℕ}
    (hc : ¬ isCoord c = true) (k : ℕ) : rootVec β isCoord (Nat.pair c k) = β c k := by
  rw [rootVec_pair, if_neg hc]

theorem rootIndex_lt_rootIndex_iff (isCoord : ℕ → Bool) (c : ℕ) {k K : ℕ} :
    rootIndex isCoord c k < rootIndex isCoord c K ↔ k < K := by
  unfold rootIndex
  split_ifs <;> omega

theorem rootIndex_ne_zero_of_coord {isCoord : ℕ → Bool} {c : ℕ} (hc : isCoord c = true) (k : ℕ) :
    rootIndex isCoord c k ≠ 0 := by
  simp [rootIndex, hc]

/-- The number of roots of the cell `c` among the first `m` roots. -/
def rootCount (c m : ℕ) : ℕ :=
  Nat.find (⟨m, Nat.right_le_pair c m⟩ : ∃ k, m ≤ Nat.pair c k)

theorem lt_rootCount_iff {c m k : ℕ} : k < rootCount c m ↔ Nat.pair c k < m := by
  unfold rootCount
  rw [Nat.lt_find_iff]
  constructor
  · intro h
    exact not_le.mp (h k le_rfl)
  · intro h k' hk' hm
    have hle : Nat.pair c k' ≤ Nat.pair c k := by
      rcases hk'.lt_or_eq with hlt | heq
      · exact (Nat.pair_lt_pair_right c hlt).le
      · rw [heq]
    omega

section LocalBases

variable {A : ℕ → Set ℝ} {β : ℕ → ℕ → LebesgueLp p} {B : ℝ}
  (hβ : ∀ c, LocalBasis p (β c) (A c) B) (isCoord : ℕ → Bool)

include hβ

theorem rootVec_norm (j : ℕ) : ‖rootVec β isCoord j‖ = 1 := (hβ _).norm _

theorem rootVec_ne_zero (j : ℕ) : rootVec β isCoord j ≠ 0 := (hβ _).basis_ne_zero _

theorem rootVec_nonneg (j : ℕ) : IsNonneg (rootVec β isCoord j) := (hβ _).nonneg _

theorem rootVec_step (j : ℕ) : IsCompactStep p (rootVec β isCoord j) := (hβ _).step _

theorem rootVec_supported (j : ℕ) : SupportedOn (rootVec β isCoord j) (A (Nat.unpair j).1) :=
  (hβ _).supported _

theorem cellCoord_norm (c : ℕ) : ‖cellCoord β c‖ = 1 := (hβ c).norm 0

theorem cellCoord_ne_zero (c : ℕ) : cellCoord β c ≠ 0 := (hβ c).basis_ne_zero 0

theorem cellCoord_nonneg (c : ℕ) : IsNonneg (cellCoord β c) := (hβ c).nonneg 0

theorem cellCoord_step (c : ℕ) : IsCompactStep p (cellCoord β c) := (hβ c).step 0

theorem cellCoord_supported (c : ℕ) : SupportedOn (cellCoord β c) (A c) := (hβ c).supported 0

variable (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))

include hdis

/-- Coordinates of different cells are a.e. disjoint. -/
theorem cellCoord_ae_disjoint :
    Pairwise (fun i j => ∀ᵐ x ∂volume, cellCoord β i x = 0 ∨ cellCoord β j x = 0) :=
  fun _ _ hij => ((hβ _).supported 0).ae_disjoint ((hβ _).supported 0) (hdis hij)

/-- **The `ℓᵖ` identity for the coordinates.**  The coordinates are disjointly supported
unit vectors, so finite combinations have the `ℓᵖ` norm of their coefficients. -/
theorem cellCoord_sum_norm_rpow (hpfin : p ≠ ∞) (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ c ∈ s, a c • cellCoord β c‖ ^ p.toReal = ∑ c ∈ s, ‖a c‖ ^ p.toReal := by
  rw [norm_finset_sum_rpow s (fun c => a c • cellCoord β c) (lpExponent_ne_zero p) hpfin
    (fun i _ j _ hij => ae_disjoint_complex_smul (a i) (a j) (cellCoord_ae_disjoint hβ hdis hij))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [norm_smul, cellCoord_norm hβ c, mul_one]

/-- The `ℓᵖ` identity for the coordinates, for finitely supported coefficient families. -/
theorem cellCoord_linearCombination_norm_rpow (hpfin : p ≠ ∞) (a : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (cellCoord β) a‖ ^ p.toReal =
      ∑ c ∈ a.support, ‖a c‖ ^ p.toReal := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact cellCoord_sum_norm_rpow hβ hdis hpfin a.support a

end LocalBases

end StructuredBases.PositiveTranslates
