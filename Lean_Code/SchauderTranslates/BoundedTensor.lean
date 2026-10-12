import Lean_Code.SchauderTranslates.SelectiveMeans
import Mathlib.Analysis.Matrix.Order

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder Kronecker InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace BoundedMeasurableComplex
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem inner_tensor (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : BoundedMeasurableComplex A) (h k : BoundedMeasurableComplex B) :
    inner ℂ ((f.tensor h).toL2 (μ.prod ν)) ((g.tensor k).toL2 (μ.prod ν)) =
      inner ℂ (f.toL2 μ) (g.toL2 μ) * inner ℂ (h.toL2 ν) (k.toL2 ν) := by
  rw [inner_toL2, inner_toL2, inner_toL2]
  have hi := (f.conjugate.mul g).integral_tensor (h.conjugate.mul k) μ ν
  dsimp only [mul, conjugate] at hi
  convert hi using 1
  congr 1
  funext p
  change star (f p.1 * h p.2) * (g p.1 * k p.2) = _
  rw [star_mul]
  ring

theorem inner_pullbackFst (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (f g : BoundedMeasurableComplex A) :
    inner ℂ ((f.pullbackFst B).toL2 (μ.prod ν)) ((g.pullbackFst B).toL2 (μ.prod ν)) =
      inner ℂ (f.toL2 μ) (g.toL2 μ) := by
  have h := inner_tensor μ ν f g (const B 1) (const B 1)
  have hf := toL2_congr (f.tensor (const B 1)) (f.pullbackFst B) (μ.prod ν)
    (Filter.Eventually.of_forall (fun p => by change f p.1 * 1 = f p.1; ring))
  have hg := toL2_congr (g.tensor (const B 1)) (g.pullbackFst B) (μ.prod ν)
    (Filter.Eventually.of_forall (fun p => by change g p.1 * 1 = g p.1; ring))
  have hc : inner ℂ ((const B 1).toL2 ν) ((const B 1).toL2 ν) = 1 := by
    rw [inner_toL2]
    simp [const]
  rw [hf, hg, hc, mul_one] at h
  exact h

end BoundedMeasurableComplex

namespace SelectiveKernelData
open BoundedMeasurableComplex
variable {S ι κ : Type*} [MeasurableSpace S] {L d : ℕ}
variable (ρ : Measure S) [IsFiniteMeasure ρ]

theorem rowColumn_inner
    (r u : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q v : BoundedMeasurableComplex (UnitAddTorus (Fin d))) :
    inner ℂ ((rowColumn r q).toL2 (ρ.prod ((torusMeasure L).prod (torusMeasure d))))
      ((rowColumn u v).toL2 (ρ.prod ((torusMeasure L).prod (torusMeasure d)))) =
      inner ℂ (r.toL2 (ρ.prod (torusMeasure L))) (u.toL2 (ρ.prod (torusMeasure L))) *
        inner ℂ (q.toL2 (torusMeasure d)) (v.toL2 (torusMeasure d)) := by
  rw [inner_toL2]
  have h := (measurePreserving_prodAssoc ρ (torusMeasure L) (torusMeasure d)).integral_comp'
    (fun p => star (rowColumn r q p) * rowColumn u v p)
  rw [← h]
  change (∫ p, star ((r.tensor q) p) * (u.tensor v) p ∂(ρ.prod (torusMeasure L)).prod (torusMeasure d)) = _
  rw [← inner_toL2, inner_tensor]

theorem rowColumn_gram [Fintype ι] [Fintype κ]
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q : κ → BoundedMeasurableComplex (UnitAddTorus (Fin d))) :
    Matrix.gram ℂ (fun i : κ × ι => (rowColumn (r i.2) (q i.1)).toL2
      (ρ.prod ((torusMeasure L).prod (torusMeasure d)))) =
      (Matrix.gram ℂ (fun k => (q k).toL2 (torusMeasure d))) ⊗ₖ
        (Matrix.gram ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L)))) := by
  apply Matrix.ext
  intro i j
  change inner ℂ ((rowColumn (r i.2) (q i.1)).toL2 (ρ.prod ((torusMeasure L).prod (torusMeasure d))))
    ((rowColumn (r j.2) (q j.1)).toL2 (ρ.prod ((torusMeasure L).prod (torusMeasure d)))) =
    inner ℂ ((q i.1).toL2 (torusMeasure d)) ((q j.1).toL2 (torusMeasure d)) *
      inner ℂ ((r i.2).toL2 (ρ.prod (torusMeasure L))) ((r j.2).toL2 (ρ.prod (torusMeasure L)))
  rw [rowColumn_inner, mul_comm]

theorem rowColumn_independent [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (r : ι → BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q : κ → BoundedMeasurableComplex (UnitAddTorus (Fin d)))
    (hr : LinearIndependent ℂ (fun i => (r i).toL2 (ρ.prod (torusMeasure L))))
    (hq : LinearIndependent ℂ (fun k => (q k).toL2 (torusMeasure d))) :
    LinearIndependent ℂ (fun i : κ × ι => (rowColumn (r i.2) (q i.1)).toL2
      (ρ.prod ((torusMeasure L).prod (torusMeasure d)))) := by
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [rowColumn_gram]
  exact (Matrix.posDef_gram_iff_linearIndependent.mpr hq).kronecker
    (Matrix.posDef_gram_iff_linearIndependent.mpr hr)

end SelectiveKernelData
end SchauderTranslates
