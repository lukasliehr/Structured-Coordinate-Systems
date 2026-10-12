import Lean_Code.PositiveTranslates.Forest.Estimates
import Lean_Code.PositiveTranslates.Forest.Density
import Lean_Code.PositiveTranslates.Forest.Tools
import Lean_Code.PositiveTranslates.Forest.Model

/-!
# The positive forest is a Schauder basis

`PositiveForest.exists_schauderBasis`: for a positive forest `F` in a complex Banach space
`Z` with exponent `1 ≤ r`, the sequence `F.seq` (the vector `e0` followed by the atoms of
the stages `0, 1, 2, …`) is a Schauder basis of `Z`, and all its partial sum projections
have norm at most `4 D (1 + B) + 13 B`.

The proof combines

* the finite prefix inequality `PositiveForest.prefix_bound` (from
  `norm_e0_add_synth_cut_le` in `Forest/Estimates.lean`),
* completeness `PositiveForest.dense_span_seq` and `PositiveForest.seq_ne_zero`
  (`Forest/Density.lean`),
* the criterion `StructuredBases.exists_schauderBasis_of_prefix_bound`.
-/

noncomputable section

open scoped BigOperators

namespace StructuredBases.PositiveTranslates.PositiveForest

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {r : ℝ}

/-- The constant of the positive forest is non-negative. -/
theorem constant_nonneg (F : PositiveForest Z r) : 0 ≤ 4 * F.D * (1 + F.B) + 13 * F.B := by
  have h1 := F.D_nonneg
  have h2 := F.B_nonneg
  positivity

/-- **Finite prefix inequality** for the sequence of a positive forest. -/
theorem prefix_bound (F : PositiveForest Z r) (hr : 1 ≤ r) (M : ℕ) (a : ℕ →₀ ℂ) :
    ‖∑ n ∈ Finset.range M, a n • F.seq n‖ ≤
      (4 * F.D * (1 + F.B) + 13 * F.B) * ‖Finsupp.linearCombination ℂ F.seq a‖ :=
  F.prefix_bound_of_cut_bound F.constant_nonneg
    (fun _ c0 _ hv _ hs k => F.norm_e0_add_synth_cut_le hr c0 hv hs k) M a

/-- **The positive forest.** The sequence `F.seq` — the vector `e0`, followed by the atoms
`atom s i = coord s i + (2 (N s)^{-(r-1)/r}) • target s` of the stages `s = 0, 1, 2, …` — is a
Schauder basis of `Z`, and all its partial sum projections have norm at most
`4 D (1 + B) + 13 B`, where `B ≥ ‖PY‖` and `D` is the basis constant of the roots. -/
theorem exists_schauderBasis [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) :
    ∃ b : SchauderBasis ℂ Z, ⇑b = F.seq ∧ ∀ M, ‖b.proj M‖ ≤ 4 * F.D * (1 + F.B) + 13 * F.B :=
  exists_schauderBasis_of_prefix_bound F.seq (F.seq_ne_zero hr)
    (F.dense_span_seq (by linarith)) (F.prefix_bound hr)

/-! ### A chosen basis -/

/-- A Schauder basis of `Z` whose vectors are the sequence `F.seq` of the positive forest
(chosen by `PositiveForest.exists_schauderBasis`). -/
def basis [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) : SchauderBasis ℂ Z :=
  (F.exists_schauderBasis hr).choose

@[simp] theorem coe_basis [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) :
    ⇑(F.basis hr) = F.seq :=
  (F.exists_schauderBasis hr).choose_spec.1

theorem basis_apply [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) (n : ℕ) :
    F.basis hr n = F.seq n := by
  rw [coe_basis]

/-- The first vector of the basis is `e0`. -/
theorem basis_zero [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) :
    F.basis hr 0 = F.e0 := by
  rw [basis_apply, seq_zero]

/-- The vector number `offset s + i` of the basis is the atom `atom s i`. -/
theorem basis_offset_add [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) (s : ℕ)
    (i : Fin (F.N s)) : F.basis hr (F.offset s + i) = F.atom s i := by
  rw [basis_apply, seq_offset_add]

/-- All partial sum projections of the basis have norm at most `4 D (1 + B) + 13 B`. -/
theorem norm_basis_proj_le [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) (M : ℕ) :
    ‖(F.basis hr).proj M‖ ≤ 4 * F.D * (1 + F.B) + 13 * F.B :=
  (F.exists_schauderBasis hr).choose_spec.2 M

/-- The basis constant of the basis is at most `4 D (1 + B) + 13 B`. -/
theorem nnnormProjBound_basis_le [CompleteSpace Z] (F : PositiveForest Z r) (hr : 1 ≤ r) :
    ((F.basis hr).nnnormProjBound : ℝ) ≤ 4 * F.D * (1 + F.B) + 13 * F.B :=
  (nnnormProjBound_le_iff _).mpr (F.norm_basis_proj_le hr)

end StructuredBases.PositiveTranslates.PositiveForest

/-! ### Sanity check -/

namespace StructuredBases.PositiveTranslates.ForestModel

open scoped ENNReal

/-- The hypotheses of the main theorem are satisfiable: for the model forest in `ℓ^p × ℓ^p`
(`Forest/Model.lean`, `B = D = 1`) the main theorem gives a Schauder basis with basis
constant at most `4 · 1 · (1 + 1) + 13 · 1 = 21`. -/
theorem exists_basis {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ b : SchauderBasis ℂ (Space p), ⇑b = (forest hp).seq ∧ ∀ M, ‖b.proj M‖ ≤ 21 := by
  have hr : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
    simpa using h
  obtain ⟨b, hb, hM⟩ := (forest hp).exists_schauderBasis hr
  refine ⟨b, hb, fun M => (hM M).trans ?_⟩
  change 4 * (1 : ℝ) * (1 + 1) + 13 * 1 ≤ 21
  norm_num

end StructuredBases.PositiveTranslates.ForestModel
