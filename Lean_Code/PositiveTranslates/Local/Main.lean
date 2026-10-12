import Lean_Code.PositiveTranslates.Local.Cells
import Lean_Code.PositiveTranslates.Local.NormalForm

/-!
# Uniform local non-negative bases

For `1 < p < ∞` (complex scalars, `LebesgueLp p = Lp ℂ p volume` on the real line) there is
one constant `B` such that

* (a) for every bounded interval `[a, b)` the space `Lᵖ([a, b))` has a normalized Schauder
  basis of non-negative compactly supported step functions with all partial sum projections
  bounded by `B`;
* (b) the same holds for `Lᵖ((⋃ₖ Iₖ) ∪ [a, b))` with a prescribed first basis vector
  `e = ∑ₖ cₖ 𝟙_{Iₖ}`, where the `Iₖ` are finitely many pairwise disjoint intervals, the `cₖ` are
  positive, `‖e‖ = 1`, and the "room" interval `[a, b)` is disjoint from the `Iₖ`.

This is the step-function form of Lemma `tr:lem:positive-complement` of the paper (there the
basis vectors are smooth; here they are step functions and no approximation is needed).
Every `B > 1` works (`exists_localBasis`); `exists_localBasis_constant` records `B = 2`.

## Main statements

* `LocalBasis` (`Local/Defs.lean`): the basis property, in the form of the finite prefix
  criterion.
* `exists_localBasis_constant`, `exists_localBasis`: the uniform local bases (a), (b).
* `exists_cellIsometry`: the underlying positive isometries of `Lᵖ(ℝ)` onto `Lᵖ(A)`, which
  preserve compactly supported step functions (`IsCellIsometry`, `Local/Defs.lean`); in case
  (b) they send `𝟙_[0,1)` to `e`. All local bases are the images of one model basis of `Lᵖ(ℝ)`
  with first vector `𝟙_[0,1)` under such isometries, so every estimate on finite linear
  combinations of the model basis holds for all of them with the same constant
  (`norm_linearCombination_isometry`).
* `exists_localBasis_of_model`: (a), (b) for an arbitrary model basis `r` of `Lᵖ(ℝ)` with
  `r 0 = 𝟙_[0,1)`, together with `‖∑ₙ tₙ βₙ‖ = ‖∑ₙ tₙ rₙ‖` for the resulting local bases `β`.
* `exists_positive_normalForm`, `exists_ordered_positive_normalForm` (`Local/NormalForm.lean`):
  every nonzero non-negative compact step function has the form required in (b).
* `exists_localBasis_of_step`: (b) for a step function given abstractly.

## Proof

1. `Local/RootVector.lean`, `Local/Model.lean`: the non-negative basis of `Lᵖ(ℝ)` from
   `Lean_Code/PositiveBiorthogonal` has first vector `𝟙_(0,1]`; normalized in `Lᵖ` it is a
   local basis of the whole line (`exists_model_basis`).
2. `Local/Rearrangement*.lean`: countably many pairs (source interval, target interval) define
   a positive operator on `Lᵖ(ℝ)` which maps `Lᵖ(⋃ sources)` isometrically onto
   `Lᵖ(⋃ targets)` and preserves compact step functions.
3. `Local/Dyadic.lean`: unit intervals to the dyadic pieces of `[0, 2)`, with `[0, 1)` fixed.
4. `Local/Cells.lean`: `[0, 2)` to `[a, b)`; and `[0, 1)` to `⋃ₖ Iₖ` (cut into pieces of
   lengths `cₖ^p |Iₖ|`), `[1, 2)` to `[a, b)`, which sends `𝟙_[0,1)` to `e`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

/-- **Uniform cell isometries.** Let `p` be a finite exponent.

(a) For every bounded interval `[a, b)` there is a positive linear isometry of `Lᵖ(ℝ)` onto
`Lᵖ([a, b))` which preserves compactly supported step functions.

(b) If `Iₖ = [(I k).1, (I k).2)`, `k < m`, are nondegenerate pairwise disjoint intervals, the
numbers `c k` are positive, `[a, b)` is a nondegenerate interval disjoint from all `Iₖ`, and
`e = ∑ₖ cₖ 𝟙_{Iₖ}` has norm one, then there is such an isometry onto
`Lᵖ((⋃ₖ Iₖ) ∪ [a, b))` which sends the indicator of `[0, 1)` to `e`. -/
theorem exists_cellIsometry (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ a b : ℝ, a < b →
      ∃ T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p, IsCellIsometry T (Set.Ico a b)) ∧
    (∀ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (a b : ℝ),
        (∀ k, (I k).1 < (I k).2) → (∀ k, 0 < c k) →
        Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) →
        (∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) → a < b →
        ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 →
        ∃ T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p,
          IsCellIsometry T ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) ∧
          T (intervalAtom p (0, 1)) = ∑ k, (c k : ℂ) • intervalAtom p (I k)) :=
  ⟨fun a b hab => exists_cellIsometry_Ico hp a b hab,
    fun m I c a b hI hc hdis hroom hab hnorm =>
      exists_cellIsometry_first_vector hp m I c a b hI hc hdis hroom hab hnorm⟩

/-- **Uniform local bases from an arbitrary model basis.** Let `p` be a finite exponent and
let `r` be a `LocalBasis` of the whole line with prefix constant `B` and first vector
`𝟙_[0,1)`. Then every interval `[a, b)` (part (a)) and every cell `(⋃ₖ Iₖ) ∪ [a, b)` with
prescribed first vector `e = ∑ₖ cₖ 𝟙_{Iₖ}` (part (b), hypotheses as in `exists_cellIsometry`) has
a `LocalBasis β` with the same prefix constant `B` such that all finite linear combinations of
`β` have the same norms as the corresponding combinations of `r`:
`‖∑ₙ tₙ βₙ‖ = ‖∑ₙ tₙ rₙ‖`.

Hence every estimate between the coefficients and the norm of a finite combination which
holds for the model `r` (for instance a lower `ℓᵖ` estimate) holds for all these local bases
with the same constant. -/
theorem exists_localBasis_of_model (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {r : ℕ → LebesgueLp p} {B : ℝ} (hr : LocalBasis p r Set.univ B)
    (hr0 : r 0 = intervalAtom p (0, 1)) :
    (∀ a b : ℝ, a < b → ∃ β, LocalBasis p β (Set.Ico a b) B ∧
      ∀ t : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ β t‖ = ‖Finsupp.linearCombination ℂ r t‖) ∧
    (∀ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (a b : ℝ),
        (∀ k, (I k).1 < (I k).2) → (∀ k, 0 < c k) →
        Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) →
        (∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) → a < b →
        ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 →
        ∃ β, β 0 = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
          LocalBasis p β ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) B ∧
          ∀ t : ℕ →₀ ℂ,
            ‖Finsupp.linearCombination ℂ β t‖ = ‖Finsupp.linearCombination ℂ r t‖) := by
  constructor
  · intro a b hab
    obtain ⟨T, hT⟩ := exists_cellIsometry_Ico hp a b hab
    exact ⟨_, LocalBasis.of_cellIsometry hT hr, norm_linearCombination_isometry T r⟩
  · intro m I c a b hI hc hdis hroom hab hnorm
    obtain ⟨T, hT, hT0⟩ :=
      exists_cellIsometry_first_vector hp m I c a b hI hc hdis hroom hab hnorm
    refine ⟨fun n => T (r n), ?_, LocalBasis.of_cellIsometry hT hr,
      norm_linearCombination_isometry T r⟩
    change T (r 0) = _
    rw [hr0, hT0]

/-- **Uniform local non-negative bases, every constant `B > 1`.**
Let `1 < p < ∞` and `B > 1`.

(a) Every bounded interval `[a, b)` has a `LocalBasis` with prefix constant `B`.

(b) If `Iₖ = [(I k).1, (I k).2)`, `k < m`, are nondegenerate pairwise disjoint intervals, the
numbers `c k` are positive, `[a, b)` is a nondegenerate interval disjoint from all `Iₖ`, and
`e = ∑ₖ cₖ 𝟙_{Iₖ}` has norm one, then `(⋃ₖ Iₖ) ∪ [a, b)` has a `LocalBasis` with prefix
constant `B` and first vector `e`.

(The hypothesis `0 < m` in (b) follows from `‖e‖ = 1`; it is part of the requested
interface.) -/
theorem exists_localBasis (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) :
    (∀ a b : ℝ, a < b → ∃ β, LocalBasis p β (Set.Ico a b) B) ∧
    (∀ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (a b : ℝ),
        (∀ k, (I k).1 < (I k).2) → (∀ k, 0 < c k) →
        Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) →
        (∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) → a < b →
        ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 → 0 < m →
        ∃ β, β 0 = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
          LocalBasis p β ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) B) :=
  ⟨fun a b hab => exists_localBasis_Ico p hp1 hp hB a b hab,
    fun m I c a b hI hc hdis hroom hab hnorm _ =>
      exists_localBasis_first_vector p hp1 hp hB m I c a b hI hc hdis hroom hab hnorm⟩

/-- **Uniform local non-negative bases.** For `1 < p < ∞` there is a constant `B` (namely
`B = 2`; any `B > 1` works, see `exists_localBasis`) such that

(a) every bounded interval `[a, b)` has a normalized non-negative compact-step Schauder basis
with prefix constant `B`;

(b) for every non-negative unit step function `e = ∑ₖ cₖ 𝟙_{Iₖ}`, given by finitely many
nondegenerate pairwise disjoint intervals and positive values, and every nondegenerate "room"
interval `[a, b)` disjoint from the `Iₖ`, the set `(⋃ₖ Iₖ) ∪ [a, b)` has such a basis with
first vector `e`. -/
theorem exists_localBasis_constant (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ B : ℝ, 1 ≤ B ∧
      -- (a) every bounded interval
      (∀ a b : ℝ, a < b → ∃ β, LocalBasis p β (Set.Ico a b) B) ∧
      -- (b) prescribed first vector: `e` a non-negative unit step function given by finitely
      --     many pairwise disjoint intervals with positive values, plus a disjoint "room"
      --     interval
      (∀ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (a b : ℝ),
          (∀ k, (I k).1 < (I k).2) → (∀ k, 0 < c k) →
          Pairwise (fun k l => Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico (I l).1 (I l).2)) →
          (∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) → a < b →
          ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 → 0 < m →
          ∃ β, β 0 = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
            LocalBasis p β ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) B) :=
  ⟨2, one_le_two, exists_localBasis p hp1 hp one_lt_two⟩

/-- **Local basis whose first vector is a given step function.** Let `1 < p < ∞`, `B > 1`,
let `e` be a compactly supported step function with `e ≥ 0` almost everywhere and `‖e‖ = 1`,
and let `[a, b)` be a nondegenerate interval on which `e` vanishes almost everywhere.
Then `e = ∑ₖ cₖ 𝟙_{Iₖ}` with positive `cₖ` and nondegenerate intervals `Iₖ` listed from left to
right (in particular pairwise disjoint) and disjoint from `[a, b)`; the union `⋃ₖ Iₖ` is, up to a
null set, the set where `e ≠ 0`; and `(⋃ₖ Iₖ) ∪ [a, b)` has a `LocalBasis` with prefix constant
`B` whose first vector is `e`.

This combines `exists_ordered_positive_normalForm` with part (b) of `exists_localBasis`. -/
theorem exists_localBasis_of_step (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    {B : ℝ} (hB : 1 < B) {e : LebesgueLp p} (he : IsCompactStep p e) (hpos : IsNonneg e)
    (hnorm : ‖e‖ = 1) {a b : ℝ} (hab : a < b) (hroom : SupportedOn e (Set.Ico a b)ᶜ) :
    ∃ (m : ℕ) (I : Fin m → ℝ × ℝ) (c : Fin m → ℝ) (β : ℕ → LebesgueLp p),
      0 < m ∧ (∀ k, (I k).1 < (I k).2) ∧ (∀ k, 0 < c k) ∧
      (∀ k l, k < l → (I k).2 ≤ (I l).1) ∧
      e = ∑ k, (c k : ℂ) • intervalAtom p (I k) ∧
      (∀ᵐ x : ℝ, e x ≠ 0 ↔ x ∈ ⋃ k, Set.Ico (I k).1 (I k).2) ∧
      (∀ k, Disjoint (Set.Ico (I k).1 (I k).2) (Set.Ico a b)) ∧
      β 0 = e ∧ LocalBasis p β ((⋃ k, Set.Ico (I k).1 (I k).2) ∪ Set.Ico a b) B := by
  have hne : e ≠ 0 := by
    rintro rfl
    simp at hnorm
  obtain ⟨m, I, c, hm, hI, hc, hord, hrep, hsupp, hdisj⟩ :=
    exists_ordered_positive_normalForm he hpos hne
  have hnorm' : ‖∑ k, (c k : ℂ) • intervalAtom p (I k)‖ = 1 := hrep ▸ hnorm
  obtain ⟨β, hβ0, hβ⟩ := exists_localBasis_first_vector p hp1 hp hB m I c a b hI hc
    (pairwise_disjoint_Ico_of_ordered hord) (hdisj a b hroom) hab hnorm'
  exact ⟨m, I, c, β, hm, hI, hc, hord, hrep, hsupp, hdisj a b hroom, hβ0.trans hrep.symm, hβ⟩

end StructuredBases.PositiveTranslates
