import Lean_Code.SchauderTranslates.FejerMoments

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {d : ℕ}

/-- Continuous Haar-space vectors for the nonnegative, possibly vanishing, Fejer density. -/
def fejerCharacter (N : ℕ) (k : Fin d → ℤ) : C(UnitAddTorus (Fin d), ℂ) where
  toFun x := (Real.sqrt (torusFejerKernel d N x) : ℂ) * UnitAddTorus.mFourier k x
  continuous_toFun := (Complex.continuous_ofReal.comp (torusFejerKernel_continuous d N).sqrt).mul
    (UnitAddTorus.mFourier k).continuous

def fejerVector (N : ℕ) (k : Fin d → ℤ) : Lp ℂ 2 (torusMeasure d) :=
  ContinuousMap.toLp 2 (torusMeasure d) ℂ (fejerCharacter N k)

theorem fejerVector_inner (N : ℕ) (k l : Fin d → ℤ) :
    inner ℂ (fejerVector N k) (fejerVector N l) = (torusFejerMultiplier N (k - l) : ℂ) := by
  rw [fejerVector, fejerVector, ContinuousMap.inner_toLp]
  rw [← torusFejerKernel_moment N (k - l)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [fejerCharacter, ContinuousMap.coe_mk, map_mul, Complex.conj_ofReal,
    torus_character_difference]
  have hs : (Real.sqrt (torusFejerKernel d N x) : ℂ) ^ 2 = (torusFejerKernel d N x : ℂ) := by
    exact_mod_cast Real.sq_sqrt (torusFejerKernel_nonneg d N x)
  rw [← hs]
  simp only [Complex.star_def]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The correlation matrix for any finite character list; distinctness is unnecessary. -/
def fejerCorrelation (freq : ι → Fin d → ℤ) (N : ℕ) : Matrix ι ι ℂ :=
  fun i j => (torusFejerMultiplier N (freq i - freq j) : ℂ)

theorem fejerCorrelation_eq_gram (freq : ι → Fin d → ℤ) (N : ℕ) :
    fejerCorrelation freq N = Matrix.gram ℂ (fun i => fejerVector N (freq i)) := by
  ext i j
  exact (fejerVector_inner N (freq i) (freq j)).symm

theorem fejerCorrelation_posSemidef (freq : ι → Fin d → ℤ) (N : ℕ) :
    (fejerCorrelation freq N).PosSemidef := by
  rw [fejerCorrelation_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

@[simp] theorem fejerCorrelation_diag (freq : ι → Fin d → ℤ) (N : ℕ) (i : ι) :
    fejerCorrelation freq N i i = 1 := by
  simp [fejerCorrelation]

end SchauderTranslates
