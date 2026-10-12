import Lean_Code.SchauderTranslates.ActivationTorus
import Lean_Code.SchauderTranslates.ActivatedCenteredPrefix
import Lean_Code.SchauderTranslates.ScalarInverseNorm

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ} {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The old row and new circle mode jointly determine the flat character. -/
theorem activationFrequency_pair_injective (s : ScalarData d n) (freq : ν → ℤ)
    (hfreq : Function.Injective freq) :
    Function.Injective (fun q : (Unit ⊕ Fin n) × ν =>
      activationFrequency (s.augmentedFrequency q.1) (freq q.2)) := by
  intro q r h
  have he := @activationFrequency_injective d
    (s.augmentedFrequency q.1, freq q.2) (s.augmentedFrequency r.1, freq r.2) h
  exact Prod.ext (s.augmentedFrequency_injective (congrArg Prod.fst he))
    (hfreq (congrArg Prod.snd he))

/-- A finite activated character list as genuine scalar data. The equivalence `e` specifies
its order; later prefix estimates use an order compatible with whole-row/partial-row masks. -/
def activationData (s : ScalarData d n) (p : ℝ) (freq : ν → ℤ)
    (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    ScalarData (d + 1) m where
  toTorusWeight := s.toTorusWeight.activation p
  frequencies i := activationFrequency (s.augmentedFrequency (e i).1.1) (freq (e i).1.2)
  injective := (s.activationFrequency_pair_injective freq hfreq).comp
    (Subtype.val_injective.comp e.injective)
  nonconstant i := by
    intro h
    have h₀ : activationFrequency (s.augmentedFrequency (Sum.inl ())) (freq a₀) = 0 := by
      simp [augmentedFrequency, hzero]
    have he := @activationFrequency_pair_injective d n ν _ _ s freq hfreq
      (e i).1 (Sum.inl (), a₀) (h.trans h₀.symm)
    exact (e i).property he

@[simp] theorem activationData_mass (s : ScalarData d n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).mass = 1 - p * (1 - s.mass) :=
  s.toTorusWeight.activation_mass hp0 hp1

theorem activationData_even (s : ScalarData d n) (hs : s.IsEven) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).IsEven := s.activationWeight_even hs p

theorem activationData_positiveFloor (s : ScalarData d n) (hs : s.HasPositiveFloor) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).HasPositiveFloor := by
  obtain ⟨b, hb, hf⟩ := hs
  have hb1 : b ≤ 1 := (hf 0).trans (s.le_one 0)
  exact ⟨b, hb, s.toTorusWeight.activation_floor hb1 hf p⟩

/-- Reinsert the constant coordinate and retain the chosen order of nonconstant entries. -/
def activationIndexEquiv (n : ℕ) (a₀ : ν) {m : ℕ}
    (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (Unit ⊕ Fin m) ≃ ((Unit ⊕ Fin n) × ν) :=
  (Equiv.sumCongr (Equiv.refl Unit) e).trans (splitConstantEquiv (Sum.inl (), a₀))

theorem activationData_augmentedFrequency (s : ScalarData d n) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)})
    (q : Unit ⊕ Fin m) :
    (s.activationData p freq hfreq a₀ hzero e).augmentedFrequency q =
      activationFrequency (s.augmentedFrequency (activationIndexEquiv n a₀ e q).1)
        (freq (activationIndexEquiv n a₀ e q).2) := by
  cases q with
  | inl u => cases u; simp [augmentedFrequency, activationIndexEquiv, hzero]
  | inr a => rfl

/-- The entire augmented Gram is exactly a reindexing of the actual finite activation Gram. -/
theorem activationData_rawGram (s : ScalarData d n) (p : ℝ)
    (freq : ν → ℤ) (hfreq : Function.Injective freq) (a₀ : ν) (hzero : freq a₀ = 0)
    {m : ℕ} (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) :
    (s.activationData p freq hfreq a₀ hzero e).rawGram =
      (s.finiteActivatedGram p freq).submatrix (activationIndexEquiv n a₀ e)
        (activationIndexEquiv n a₀ e) := by
  ext q r
  change inner ℂ ((s.toTorusWeight.activation p).vector
    ((s.activationData p freq hfreq a₀ hzero e).augmentedFrequency q))
    ((s.toTorusWeight.activation p).vector
    ((s.activationData p freq hfreq a₀ hzero e).augmentedFrequency r)) = _
  rw [activationData_augmentedFrequency, activationData_augmentedFrequency,
    s.activationWeight_inner]
  rfl

end ScalarData
end SchauderTranslates
