import Lean_Code.SchauderTranslates.ActivationMoments

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The new circle is coordinate zero; the old coordinates occupy its successor tail. -/
def activationTorusEquiv (d : ℕ) : UnitAddTorus (Fin (d + 1)) ≃ᵐ
    UnitAddTorus (Fin d) × UnitAddCircle :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => UnitAddCircle) 0).trans
    MeasurableEquiv.prodComm

@[simp] theorem activationTorusEquiv_apply (d : ℕ) (x : UnitAddTorus (Fin (d + 1))) :
    activationTorusEquiv d x = ((fun j => x j.succ), x 0) := by
  simp [activationTorusEquiv, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

theorem activationTorusEquiv_measurePreserving (d : ℕ) :
    MeasurePreserving (activationTorusEquiv d) (torusMeasure (d + 1))
      ((torusMeasure d).prod AddCircle.haarAddCircle) := by
  exact (Measure.measurePreserving_swap).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) 0)

/-- One additional circle frequency, in the same flat coordinates as the density. -/
def activationFrequency {d : ℕ} (k : Fin d → ℤ) (l : ℤ) : Fin (d + 1) → ℤ := Fin.cons l k

@[simp] theorem activationFrequency_zero {d : ℕ} :
    activationFrequency (0 : Fin d → ℤ) 0 = 0 := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [activationFrequency]

theorem activationFrequency_injective {d : ℕ} :
    Function.Injective (fun p : (Fin d → ℤ) × ℤ => activationFrequency p.1 p.2) := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ h
  have hl : l = l' := congrFun h 0
  have hk : k = k' := by
    funext i
    exact congrFun h i.succ
  exact Prod.ext hk hl

/-- Flat characters are precisely the product characters used in the activation analysis. -/
theorem activationFrequency_character {d : ℕ} (k : Fin d → ℤ) (l : ℤ)
    (x : UnitAddTorus (Fin (d + 1))) :
    UnitAddTorus.mFourier (activationFrequency k l) x =
      activationCharacter k l (activationTorusEquiv d x) := by
  simp [UnitAddTorus.mFourier, Fin.prod_univ_succ, activationFrequency,
    activationCharacter, mul_comm]

namespace TorusWeight
variable {d : ℕ}

/-- Rare activation as an actual scalar torus weight, suitable for the next induction stage. -/
def activation (w : TorusWeight d) (p : ℝ) : TorusWeight (d + 1) where
  density x := activatedDensity w p (activationTorusEquiv d x)
  measurable := (activatedDensity_measurable w p).comp (activationTorusEquiv d).measurable
  positive _x := (activatedDensity_bounds w p _).1
  le_one _x := (activatedDensity_bounds w p _).2

theorem activation_mass (w : TorusWeight d) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (w.activation p).mass = 1 - p * (1 - w.mass) := by
  change (∫ x, activatedDensity w p (activationTorusEquiv d x) ∂torusMeasure (d + 1)) = _
  rw [(activationTorusEquiv_measurePreserving d).integral_comp']
  exact activatedDensity_mass w hp0 hp1

theorem activation_floor (w : TorusWeight d) {b : ℝ} (hb : b ≤ 1)
    (hw : ∀ x, b ≤ w.density x) (p : ℝ) (x : UnitAddTorus (Fin (d + 1))) :
    b ≤ (w.activation p).density x := activatedDensity_floor w hb hw p _

end TorusWeight

namespace ScalarData
variable {d n : ℕ}

theorem activationWeight_even (s : ScalarData d n) (hs : s.IsEven) (p : ℝ)
    (x : UnitAddTorus (Fin (d + 1))) :
    (s.toTorusWeight.activation p).density (-x) = (s.toTorusWeight.activation p).density x := by
  change activatedDensity s.toTorusWeight p (activationTorusEquiv d (-x)) =
    activatedDensity s.toTorusWeight p (activationTorusEquiv d x)
  simp only [activationTorusEquiv_apply]
  exact activatedDensity_even s hs p ((fun j => x j.succ), x 0)

/-- The actual L² Gram of the flat activated weight equals the checked Fubini moment. -/
theorem activationWeight_inner (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    inner ℂ ((s.toTorusWeight.activation p).vector (activationFrequency (s.augmentedFrequency i) k))
      ((s.toTorusWeight.activation p).vector (activationFrequency (s.augmentedFrequency j) l)) =
        s.activatedMoment p i j k l := by
  rw [TorusWeight.vector_inner]
  simp only [TorusWeight.activation, activationFrequency_character]
  exact (activationTorusEquiv_measurePreserving d).integral_comp'
    (fun z => (activatedDensity s.toTorusWeight p z : ℂ) *
      star (activationCharacter (s.augmentedFrequency i) k z) *
      activationCharacter (s.augmentedFrequency j) l z)

end ScalarData
end SchauderTranslates
