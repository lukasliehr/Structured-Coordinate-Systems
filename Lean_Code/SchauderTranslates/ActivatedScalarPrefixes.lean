import Lean_Code.SchauderTranslates.ActivatedScalarEstimates
import Lean_Code.SchauderTranslates.GramReindex

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The checked row-mask estimate holds for the actual finite scalar torus block, with its
chosen nonconstant enumeration. This exposes the precise mask that an ordered prefix must match. -/
theorem activationData_centered_prefix (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)})
    (old : Finset (Unit ⊕ Fin n)) (j : Unit ⊕ Fin n) (hj : j ∉ old) (cut : Finset ν) :
    ‖gramConjugate (s.activationData p freq hfreq a₀ hzero e).centeredGram
      (Matrix.diagonal (fun i : Fin m =>
        if (e i).1.1 ∈ old ∨ ((e i).1.1 = j ∧ (e i).1.2 ∈ cut) then (1 : ℂ) else 0))‖ ^ 2 ≤
      metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j := by
  let S := s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀
  let δ := fun q : {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)} =>
    if q.1.1 ∈ old ∨ (q.1.1 = j ∧ q.1.2 ∈ cut) then (1 : ℂ) else 0
  have hC : 0 ≤ metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j :=
    zero_le_one.trans (metricRowBound_ge_one s.realRawGram_posDef s.realRawGram_le_one _ j
      (fun k h => hj (h ▸ k.property)))
  have h := (s.finiteActivatedScalarGram_prefix hs hb hfloor hp0 hp1 freq hfreq a₀ old j hj cut).2
  have hr := gramConjugate_reindex_bound S.centeredGram_posDef (Matrix.diagonal δ) e hC h
  rw [diagonal_submatrix_equiv] at hr
  rw [s.activationData_centeredGram hb hfloor hp0 hp1]
  exact hr

end ScalarData
end SchauderTranslates
