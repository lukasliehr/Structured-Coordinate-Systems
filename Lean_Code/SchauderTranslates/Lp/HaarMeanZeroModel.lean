import Lean_Code.SchauderTranslates.Lp.HaarFullBasis

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

abbrev HaarMeanZeroIndex := Σ n, Fin (2 ^ n)

instance haarMeanZeroIndex_infinite : Infinite HaarMeanZeroIndex :=
  Infinite.of_injective (fun n : ℕ => (⟨n, ⟨0, by positivity⟩⟩ : HaarMeanZeroIndex))
    (fun _ _ h => congrArg Sigma.fst h)

def haarMeanZeroOrdering : ℕ ≃ HaarMeanZeroIndex := Classical.choice inferInstance

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def haarIntegral : HaarLp p →L[ℂ] ℂ := haarCoefficientMap p q none

theorem haarIntegral_apply (f : HaarLp p) : haarIntegral p q f = ∫ x, f x ∂haarMeasure := by
  rw [haarIntegral, haarCoefficientMap_apply]
  apply integral_congr_ae
  filter_upwards [haarConstant_ae_one p] with x hx
  change f x * star (haarConstant p x) = f x
  rw [hx, star_one, mul_one]

def haarMeanZero : Submodule ℂ (HaarLp p) := (haarIntegral p q).ker

theorem haarMeanZero_mem_iff (f : HaarLp p) :
    f ∈ haarMeanZero p q ↔ (∫ x, f x ∂haarMeasure) = 0 := by
  rw [haarMeanZero, LinearMap.mem_ker]
  change haarIntegral p q f = 0 ↔ _
  rw [haarIntegral_apply]

theorem haarNormalizedAtom_mem_meanZero (i : HaarMeanZeroIndex) :
    haarNormalizedAtom p (some i) ∈ haarMeanZero p q := by
  change haarCoefficientMap p q none (haarNormalizedAtom p (some i)) = 0
  rw [haarNormalizedAtom, map_smul, haarCoefficientMap_atom]
  simp

def haarMeanZeroAtom (i : HaarMeanZeroIndex) : haarMeanZero p q :=
  ⟨haarNormalizedAtom p (some i), haarNormalizedAtom_mem_meanZero p q i⟩

def haarMeanZeroCoordinate (i : HaarMeanZeroIndex) : haarMeanZero p q →L[ℂ] ℂ :=
  (haarNormalizedCoordinate p q (some i)).comp (haarMeanZero p q).subtypeL

theorem haarMeanZeroAtom_norm (i : HaarMeanZeroIndex) : ‖haarMeanZeroAtom p q i‖ = 1 :=
  haarNormalizedAtom_norm p (some i)

theorem haarMeanZeroCoordinate_atom (i j : HaarMeanZeroIndex) :
    haarMeanZeroCoordinate p q i (haarMeanZeroAtom p q j) = if i = j then 1 else 0 := by
  simpa only [haarMeanZeroCoordinate, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, haarMeanZeroAtom, Option.some.injEq] using
      haarNormalizedCoordinate_atom p q (some i) (some j)

theorem haarNormalizedCoordinate_none_meanZero (f : haarMeanZero p q) :
    haarNormalizedCoordinate p q none f = 0 := by
  have hf : haarCoefficientMap p q none f = 0 := f.property
  simp [haarNormalizedCoordinate, hf]

end SchauderTranslates.LpConstruction
