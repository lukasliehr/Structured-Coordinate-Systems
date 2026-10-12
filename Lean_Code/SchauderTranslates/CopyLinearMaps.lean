import Lean_Code.SchauderTranslates.IndependentCopies

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
  [∀ i, CompleteSpace (F i)]

/-- The algebraic mean-coordinate lift used to transport finite synthesis. -/
def liftCopiesLinear (T : ∀ i, F i →L[𝕜] E) :
    WithLp 2 (E × PiLp 2 F) →ₗ[𝕜] WithLp 2 (E × PiLp 2 F) where
  toFun := liftCopies T
  map_add' z w := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change z.fst + w.fst + copyMean T (z.snd + w.snd) =
        (z.fst + copyMean T z.snd) + (w.fst + copyMean T w.snd)
      rw [map_add]
      abel
    · rfl
  map_smul' a z := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change a • z.fst + copyMean T (a • z.snd) = a • (z.fst + copyMean T z.snd)
      simp
    · rfl

def unliftCopiesLinear (T : ∀ i, F i →L[𝕜] E) :
    WithLp 2 (E × PiLp 2 F) →ₗ[𝕜] WithLp 2 (E × PiLp 2 F) where
  toFun := unliftCopies T
  map_add' z w := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change z.fst + w.fst - copyMean T (z.snd + w.snd) =
        (z.fst - copyMean T z.snd) + (w.fst - copyMean T w.snd)
      rw [map_add]
      abel
    · rfl
  map_smul' a z := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change a • z.fst - copyMean T (a • z.snd) = a • (z.fst - copyMean T z.snd)
      simp [smul_sub]
    · rfl

def orthogonalCopyCutLinear (k : ι) (P : F k →L[𝕜] F k) :
    WithLp 2 (E × PiLp 2 F) →ₗ[𝕜] WithLp 2 (E × PiLp 2 F) where
  toFun := orthogonalCopyCut k P
  map_add' z w := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · rfl
    · ext i
      by_cases hi : i = k
      · subst i
        simp [orthogonalCopyCut, copyHead, PiLp.single, -PiLp.toLp_single]
      · by_cases hik : i < k
        <;> simp [orthogonalCopyCut, copyHead, PiLp.single, -PiLp.toLp_single,
          Pi.single_eq_of_ne hi, hik]
  map_smul' a z := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · rfl
    · ext i
      by_cases hi : i = k
      · subst i
        simp [orthogonalCopyCut, copyHead, PiLp.single, -PiLp.toLp_single]
      · by_cases hik : i < k
        <;> simp [orthogonalCopyCut, copyHead, PiLp.single, -PiLp.toLp_single,
          Pi.single_eq_of_ne hi, hik]

/-- A lifted cut is linear, so checking it on the finite family determines its action on all sums. -/
def liftedCopyCutLinear (T : ∀ i, F i →L[𝕜] E) (k : ι) (P : F k →L[𝕜] F k) :
    WithLp 2 (E × PiLp 2 F) →ₗ[𝕜] WithLp 2 (E × PiLp 2 F) :=
  (liftCopiesLinear T).comp ((orthogonalCopyCutLinear k P).comp (unliftCopiesLinear T))

@[simp] theorem liftedCopyCutLinear_apply (T : ∀ i, F i →L[𝕜] E) (k : ι)
    (P : F k →L[𝕜] F k) (z : WithLp 2 (E × PiLp 2 F)) :
    liftedCopyCutLinear T k P z = liftedCopyCut T k P z := rfl

end SchauderTranslates
