import Lean_Code.SchauderTranslates.ScalarData
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Group the flat coordinates of a product torus into its independent copies. -/
def torusCopiesEquiv (L d : ℕ) :
    UnitAddTorus (Fin (L * d)) ≃ᵐ (Fin L → UnitAddTorus (Fin d)) where
  toFun x i j := x (finProdFinEquiv (i, j))
  invFun x k := x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by
    funext k
    exact congrArg x (finProdFinEquiv.apply_symm_apply k)
  right_inv x := by funext i j; simp
  measurable_toFun := by
    change Measurable (fun (x : UnitAddTorus (Fin (L*d))) (i : Fin L) (j : Fin d) => x (finProdFinEquiv (i, j)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun (x : Fin L → UnitAddTorus (Fin d)) (k : Fin (L*d)) => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    fun_prop

/-- Flattening preserves the actual product Haar probability measure. -/
theorem torusCopiesEquiv_measurePreserving (L d : ℕ) :
    MeasurePreserving (torusCopiesEquiv L d) (torusMeasure (L * d))
      (Measure.pi (fun _ : Fin L => torusMeasure d)) := by
  let f : UnitAddTorus (Fin (L * d)) →+ (Fin L → UnitAddTorus (Fin d)) :=
    { toFun := torusCopiesEquiv L d
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : (torusMeasure (L * d)).IsAddHaarMeasure := by
    rw [torusMeasure_eq_volume]; infer_instance
  let : (torusMeasure d).IsAddHaarMeasure := by
    rw [torusMeasure_eq_volume]; infer_instance
  let : BorelSpace (UnitAddTorus (Fin d)) := inferInstance
  let : SecondCountableTopology (UnitAddTorus (Fin d)) := inferInstance
  let : BorelSpace (Fin L → UnitAddTorus (Fin d)) := Pi.borelSpace
  let : MeasurableAdd (UnitAddTorus (Fin d)) := inferInstance
  let : (Measure.pi (fun _ : Fin L => torusMeasure d)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact f.measurePreserving (by
    change Continuous (fun (x : UnitAddTorus (Fin (L*d))) (i : Fin L) (j : Fin d) => x (finProdFinEquiv (i, j)))
    fun_prop) (torusCopiesEquiv L d).surjective (by simp)

/-- Fubini in flat torus coordinates, for a separate factor in every copy. -/
theorem integral_torus_copies_prod {𝕜 : Type*} [RCLike 𝕜] (L d : ℕ)
    (f : Fin L → UnitAddTorus (Fin d) → 𝕜) :
    (∫ x, ∏ i, f i (torusCopiesEquiv L d x i) ∂torusMeasure (L * d)) =
      ∏ i, ∫ x, f i x ∂torusMeasure d := by
  rw [(torusCopiesEquiv_measurePreserving L d).integral_comp'
    (fun x => ∏ i, f i (x i))]
  exact integral_fintype_prod_eq_prod f

namespace TorusWeight
variable {d : ℕ}

/-- Independent copies of a torus density, represented on a finite flat torus. -/
def product (w : TorusWeight d) (L : ℕ) : TorusWeight (L * d) where
  density x := ∏ i : Fin L, w.density (torusCopiesEquiv L d x i)
  measurable := Finset.measurable_prod _ (fun i _ => w.measurable.comp (by fun_prop))
  positive x := Finset.prod_pos (fun i _ => w.positive _)
  le_one x := Finset.prod_le_one (fun i _ => (w.positive _).le) (fun i _ => w.le_one _)

theorem product_mass (w : TorusWeight d) (L : ℕ) : (w.product L).mass = w.mass ^ L := by
  change (∫ x, ∏ i : Fin L, w.density (torusCopiesEquiv L d x i)
    ∂torusMeasure (L * d)) = _
  rw [integral_torus_copies_prod]
  simp [mass]

/-- Tensor products retain evenness. -/
theorem product_even (w : TorusWeight d) (h : ∀ x, w.density (-x) = w.density x)
    (L : ℕ) (x : UnitAddTorus (Fin (L * d))) :
    (w.product L).density (-x) = (w.product L).density x := by
  change (∏ i : Fin L, w.density (torusCopiesEquiv L d (-x) i)) = _
  apply Finset.prod_congr rfl
  intro i _
  exact h (torusCopiesEquiv L d x i)

/-- Tensor products retain an explicit positive floor. -/
theorem product_floor (w : TorusWeight d) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x, b ≤ w.density x) (L : ℕ) (x : UnitAddTorus (Fin (L * d))) :
    b ^ L ≤ (w.product L).density x := by
  calc
    b ^ L = ∏ _ : Fin L, b := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => hb) (fun _ _ => h _)

end TorusWeight
end SchauderTranslates
