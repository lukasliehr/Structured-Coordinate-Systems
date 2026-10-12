import Lean_Code.SchauderTranslates.FiniteActivatedPrefix
import Lean_Code.SchauderTranslates.CenteredMetricGram

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
namespace ScalarData
variable {d n : ℕ}

theorem finiteActivatedGram_diagonal (s : ScalarData d n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (q : (Unit ⊕ Fin n) × ν) :
    s.finiteActivatedGram p freq q q = ((1 - p * (1 - s.mass) : ℝ) : ℂ) := by
  change s.activatedMoment p q.1 q.1 (freq q.2) (freq q.2) = _
  rw [← s.activatedGram_fourier_entry]
  change inner ℂ (circleRow (EuclideanSpace.single q.1 1) (freq q.2))
    (activationOperator (activationSet p) (activationSet_measurable p)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram)
      (circleRow (EuclideanSpace.single q.1 1) (freq q.2))) = _
  rw [circleRow_activation_diagonal _ hp0 hp1, s.rawGram_diagonal]
  push_cast
  ring

/-- Finite activated scalar data, with a chosen mode in the constant old row distinguished.
Choosing its frequency to be zero makes this exactly the constant character. -/
def finiteActivatedScalarGram (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) :
    FiniteScalarGram {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)} :=
  markedScalarGram (s.finiteActivatedGram p freq) (s.finiteActivatedGram_posDef hb hfloor p freq hfreq)
    (Sum.inl (), a₀) (1 - p * (1 - s.mass)) (s.activationMass_pos hp0 hp1)
    (s.finiteActivatedGram_diagonal hp0 hp1 freq _)

/-- Actual raw and normalized centered prefix bounds, with no lost mass factor. -/
theorem finiteActivatedScalarGram_prefix (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν)
    (old : Finset (Unit ⊕ Fin n)) (j : Unit ⊕ Fin n) (hj : j ∉ old) (cut : Finset ν) :
    let S := s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀
    let D := Matrix.diagonal (fun q : {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)} =>
      if q.1.1 ∈ old ∨ (q.1.1 = j ∧ q.1.2 ∈ cut) then (1 : ℂ) else 0)
    let C := metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j
    ‖gramConjugate S.rawCenteredGram D‖ ^ 2 ≤ C ∧ ‖gramConjugate S.centeredGram D‖ ^ 2 ≤ C := by
  let δ := fun q : (Unit ⊕ Fin n) × ν =>
    if q.1 ∈ old ∨ (q.1 = j ∧ q.2 ∈ cut) then (1 : ℂ) else 0
  have hC : 0 ≤ metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j :=
    zero_le_one.trans (metricRowBound_ge_one s.realRawGram_posDef s.realRawGram_le_one _ j
      (fun k h => hj (h ▸ k.property)))
  have hbound := s.finiteActivatedGram_prefix_norm hs hb hfloor p freq hfreq old j hj cut
  exact ⟨markedScalarGram_centered_prefix _ _ _ _ _ _ δ hC hbound,
    markedScalarGram_normalized_prefix _ _ _ _ _ _ δ hC hbound⟩

end ScalarData

/-- Rare activation controls every finite row cut, before and after removing the initial constant.
The constant coordinate is explicitly the old constant row crossed with frequency zero. -/
theorem rare_activation_prefix {d n : ℕ} (s : ScalarData d n) (hs : s.IsEven)
    {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ s.density x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    (old : Finset (Unit ⊕ Fin n)) (j : Unit ⊕ Fin n) (hj : j ∉ old) (cut : Finset ν) :
    let S := s.finiteActivatedScalarGram hb hfloor hp0 hp1 freq hfreq a₀
    let D := Matrix.diagonal (fun q : {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)} =>
      if q.1.1 ∈ old ∨ (q.1.1 = j ∧ q.1.2 ∈ cut) then (1 : ℂ) else 0)
    let C := metricRowBound s.realRawGram (fun k : old => (k : Unit ⊕ Fin n)) j
    (∀ z, activationCharacter (s.augmentedFrequency (Sum.inl ())) (freq a₀) z = 1) ∧
    ‖gramConjugate (s.finiteActivatedGram p freq) (rowMaskMatrix old j cut)‖ ^ 2 ≤ C ∧
    ‖gramConjugate S.rawCenteredGram D‖ ^ 2 ≤ C ∧ ‖gramConjugate S.centeredGram D‖ ^ 2 ≤ C := by
  refine ⟨?_, s.finiteActivatedGram_prefix_norm hs hb hfloor p freq hfreq old j hj cut,
    s.finiteActivatedScalarGram_prefix hs hb hfloor hp0 hp1 freq hfreq a₀ old j hj cut⟩
  intro z
  simp [activationCharacter, ScalarData.augmentedFrequency, hzero, UnitAddTorus.mFourier, fourier_apply]

end SchauderTranslates
