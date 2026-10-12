import Lean_Code.SchauderTranslates.FiniteRowOrder
import Lean_Code.SchauderTranslates.OrderedGramPrefixes

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- A row-ordered activated list satisfies the actual ordered-synthesis bound whenever each
row's checked metric bound is below the same budget. Zero and full prefixes are included. -/
theorem activationData_ordered_centered_prefix (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)})
    (he : Monotone (fun i => scalarRowEquiv n (e i).1.1))
    {q : ℝ} (hq : 1 ≤ q)
    (hrows : ∀ j : Unit ⊕ Fin n,
      metricRowBound s.realRawGram (fun i : precedingScalarRows n j => (i : Unit ⊕ Fin n)) j ≤ q) :
    (s.activationData p freq hfreq a₀ hzero e).CenteredPrefixSqBound q := by
  apply ((s.activationData p freq hfreq a₀ hzero e).centeredPrefixSqBound_iff_gram
    (zero_le_one.trans hq)).mpr
  intro k
  by_cases hk : k < m
  · let k' : Fin m := ⟨k, hk⟩
    obtain ⟨cut, hcut⟩ := row_ordered_prefix_mask a₀ e he k'
    have hD : finitePrefixMatrix m k = Matrix.diagonal (fun i : Fin m =>
        if (e i).1.1 ∈ precedingScalarRows n (e k').1.1 ∨
          ((e i).1.1 = (e k').1.1 ∧ (e i).1.2 ∈ cut) then (1 : ℂ) else 0) := by
      apply congrArg Matrix.diagonal
      funext i
      change (if i < k' then (1 : ℂ) else 0) = _
      simp only [hcut i]
    rw [hD]
    exact (s.activationData_centered_prefix hs hb hfloor hp0 hp1 freq hfreq a₀ hzero e
      (precedingScalarRows n (e k').1.1) (e k').1.1 (not_mem_precedingScalarRows _) cut).trans
        (hrows _)
  · rw [finitePrefixMatrix_all (le_of_not_gt hk)]
    exact gramConjugate_one_sq_le (s.activationData p freq hfreq a₀ hzero e).centeredGram_posDef hq

/-- A fixed row-compatible enumeration of the nonconstant symmetric-window characters. -/
def orderedCutoffEquiv (n N : ℕ) :
    Fin (Fintype.card (CutoffNonconstant n N)) ≃ CutoffNonconstant n N :=
  Classical.choose (exists_activation_row_order n (cutoffConstantIndex n N).2)

theorem orderedCutoffEquiv_monotone (n N : ℕ) :
    Monotone (fun i => scalarRowEquiv n (orderedCutoffEquiv n N i).1.1) :=
  Classical.choose_spec (exists_activation_row_order n (cutoffConstantIndex n N).2)

/-- The actual ordered finite block used by scalar induction. -/
def orderedCutoffData (s : ScalarData d n) (p : ℝ) (N : ℕ) :
    ScalarData (d + 1) (Fintype.card (CutoffNonconstant n N)) :=
  s.cutoffData p N (orderedCutoffEquiv n N)

theorem orderedCutoffData_centered_prefix (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (hrows : ∀ j : Unit ⊕ Fin n,
      metricRowBound s.realRawGram (fun i : precedingScalarRows n j => (i : Unit ⊕ Fin n)) j ≤ q) :
    (s.orderedCutoffData p N).CenteredPrefixSqBound q :=
  s.activationData_ordered_centered_prefix hs hb hfloor hp0 hp1 _ Subtype.val_injective
    (cutoffConstantIndex n N).2 rfl (orderedCutoffEquiv n N) (orderedCutoffEquiv_monotone n N) hq hrows

end ScalarData
end SchauderTranslates
