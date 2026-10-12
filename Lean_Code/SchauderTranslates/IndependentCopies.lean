import Lean_Code.SchauderTranslates.CopyBounds

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
  [∀ i, CompleteSpace (F i)]

/-- The aggregate mean map on an orthogonal finite sum of copies. -/
def copyMean (T : ∀ i, F i →L[𝕜] E) : PiLp 2 F →L[𝕜] E :=
  ∑ i, (T i).comp (PiLp.proj 2 F i)

omit [DecidableEq ι] [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
@[simp] theorem copyMean_apply (T : ∀ i, F i →L[𝕜] E) (x : PiLp 2 F) :
    copyMean T x = ∑ i, T i (x i) := by simp [copyMean]

omit [DecidableEq ι] in
theorem copyMean_adjoint_apply (T : ∀ i, F i →L[𝕜] E) (z : E) :
    ((copyMean T)†) z = WithLp.toLp 2 (fun i => ((T i)†) z) := by
  apply ext_inner_right 𝕜
  intro x
  simp only [adjoint_inner_left, copyMean_apply, inner_sum, PiLp.inner_apply]

omit [DecidableEq ι] in
theorem copyMean_mul_adjoint (T : ∀ i, F i →L[𝕜] E) :
    (copyMean T).comp ((copyMean T)†) = ∑ i, (T i).comp ((T i)†) := by
  ext z
  simp [copyMean_adjoint_apply]

omit [DecidableEq ι] in
theorem copyMean_norm_sq (T : ∀ i, F i →L[𝕜] E) :
    ‖copyMean T‖ ^ 2 = ‖∑ i, (T i).comp ((T i)†)‖ := by
  have h := norm_adjoint_comp_self ((copyMean T)†)
  rw [adjoint_adjoint, copyMean_mul_adjoint] at h
  simpa only [LinearIsometryEquiv.norm_map, pow_two] using h.symm

section General
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The Hilbert row norm upper bound also covers a zero-dimensional target. -/
theorem hilbertRow_norm_sq_le (T : G →L[𝕜] E) : ‖hilbertRow T‖ ^ 2 ≤ 1 + ‖T‖ ^ 2 := by
  rcases subsingleton_or_nontrivial E with h | h
  · have := h
    have hz : hilbertRow T = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have := h
    exact (hilbertRow_norm_sq T).le

omit [CompleteSpace E] in
/-- An active copy's coupling uses the complementary coordinate projection. -/
theorem copy_coupling_norm_sq [FiniteDimensional 𝕜 G]
    (T : G →L[𝕜] E) (P : G →L[𝕜] G) (hP : ∀ x, P (P x) = P x)
    {q η : ℝ} (hq : 1 ≤ q) (hη : 0 ≤ η) (hT : ‖T‖ ^ 2 ≤ η) (hPn : ‖P‖ ^ 2 ≤ q) :
    ‖T.comp (1 - P)‖ ^ 2 ≤ q * η := by
  have hc : ‖1 - P‖ ^ 2 ≤ q :=
    (complementary_projection_norm_sq_le P hP).trans (max_le hq hPn)
  have hn := opNorm_comp_le T (1 - P)
  have hs := pow_le_pow_left₀ (norm_nonneg (T.comp (1 - P))) hn 2
  have hb := mul_le_mul hT hc (sq_nonneg ‖1 - P‖) hη
  nlinarith

end General

section Ordered
variable [LinearOrder ι]

/-- Completed and not-yet-started orthogonal copies at a cut. -/
def copyHead (k : ι) (x : PiLp 2 F) : PiLp 2 F :=
  WithLp.toLp 2 (fun i => if i < k then x i else 0)

def copyTail (k : ι) (x : PiLp 2 F) : PiLp 2 F :=
  WithLp.toLp 2 (fun i => if k < i then x i else 0)

omit [DecidableEq ι] [∀ i, CompleteSpace (F i)] in
theorem copyHead_norm_sq (k : ι) (x : PiLp 2 F) :
    ‖copyHead k x‖ ^ 2 = ∑ i, if i < k then ‖x i‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [copyHead, apply_ite]

omit [DecidableEq ι] [∀ i, CompleteSpace (F i)] in
theorem copyTail_norm_sq (k : ι) (x : PiLp 2 F) :
    ‖copyTail k x‖ ^ 2 = ∑ i, if k < i then ‖x i‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [copyTail, apply_ite]

omit [∀ i, CompleteSpace (F i)] in
theorem copy_norm_decomposition (k : ι) (x : PiLp 2 F) :
    ‖x‖ ^ 2 = ‖copyHead k x‖ ^ 2 + ‖x k‖ ^ 2 + ‖copyTail k x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, copyHead_norm_sq, copyTail_norm_sq]
  calc
    _ = ∑ i, ((if i < k then ‖x i‖ ^ 2 else 0) +
        (if i = k then ‖x i‖ ^ 2 else 0) + (if k < i then ‖x i‖ ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i k with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_ge h.le]
      · simp [h]
      · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le]
    _ = _ := by simp [Finset.sum_add_distrib]

omit [Fintype ι] [∀ i, CompleteSpace (F i)] in
theorem copy_decomposition (k : ι) (x : PiLp 2 F) :
    x = copyHead k x + PiLp.single 2 k (x k) + copyTail k x := by
  ext i
  rcases lt_trichotomy i k with h | h | h
  · simp [copyHead, copyTail, PiLp.single, -PiLp.toLp_single, h, ne_of_lt h, not_lt_of_ge h.le]
  · subst i; simp [copyHead, copyTail, PiLp.single, -PiLp.toLp_single]
  · simp [copyHead, copyTail, PiLp.single, -PiLp.toLp_single, h, (ne_of_lt h).symm, not_lt_of_ge h.le]

omit [∀ i, CompleteSpace (F i)] in
theorem copyHead_single_inner (k : ι) (x : PiLp 2 F) (y : F k) :
    inner 𝕜 (copyHead k x) (PiLp.single 2 k y) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = k
  · subst i; simp [copyHead, PiLp.single, -PiLp.toLp_single]
  · simp [PiLp.single, -PiLp.toLp_single, Pi.single_eq_of_ne hi]

include 𝕜 in
omit [∀ i, CompleteSpace (F i)] in
theorem copyCut_norm_sq (k : ι) (x : PiLp 2 F) (y : F k) :
    ‖copyHead k x + PiLp.single 2 k y‖ ^ 2 = ‖copyHead k x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), copyHead_single_inner (𝕜 := 𝕜), PiLp.norm_single]
  simp

omit [LinearOrder ι] [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
theorem copyMean_single (T : ∀ i, F i →L[𝕜] E) (k : ι) (y : F k) :
    copyMean T (PiLp.single 2 k y) = T k y := by
  rw [copyMean_apply]
  calc
    _ = T k ((PiLp.single 2 k y) k) := by
      apply Finset.sum_eq_single k
      · intro i _ hi
        simp [PiLp.single, -PiLp.toLp_single, Pi.single_eq_of_ne hi]
      · simp
    _ = _ := by simp [PiLp.single, -PiLp.toLp_single]

/-- Lift the copies by their mean maps, keeping the entire base space first. -/
def liftCopies (T : ∀ i, F i →L[𝕜] E) (z : WithLp 2 (E × PiLp 2 F)) :
    WithLp 2 (E × PiLp 2 F) := WithLp.toLp 2 (z.fst + copyMean T z.snd, z.snd)

def unliftCopies (T : ∀ i, F i →L[𝕜] E) (z : WithLp 2 (E × PiLp 2 F)) :
    WithLp 2 (E × PiLp 2 F) := WithLp.toLp 2 (z.fst - copyMean T z.snd, z.snd)

def orthogonalCopyCut (k : ι) (P : F k →L[𝕜] F k) (z : WithLp 2 (E × PiLp 2 F)) :
    WithLp 2 (E × PiLp 2 F) :=
  WithLp.toLp 2 (z.fst, copyHead k z.snd + PiLp.single 2 k (P (z.snd k)))

def liftedCopyCut (T : ∀ i, F i →L[𝕜] E) (k : ι) (P : F k →L[𝕜] F k)
    (z : WithLp 2 (E × PiLp 2 F)) : WithLp 2 (E × PiLp 2 F) :=
  liftCopies T (orthogonalCopyCut k P (unliftCopies T z))

omit [LinearOrder ι] [DecidableEq ι] [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
theorem liftCopies_unlift (T : ∀ i, F i →L[𝕜] E) (z : WithLp 2 (E × PiLp 2 F)) :
    liftCopies T (unliftCopies T z) = z := by
  simp [liftCopies, unliftCopies]
  rfl

omit [LinearOrder ι] [DecidableEq ι] [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
theorem unliftCopies_lift (T : ∀ i, F i →L[𝕜] E) (z : WithLp 2 (E × PiLp 2 F)) :
    unliftCopies T (liftCopies T z) = z := by
  simp [liftCopies, unliftCopies]
  rfl

omit [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
theorem liftedCopyCut_apply (T : ∀ i, F i →L[𝕜] E) (k : ι) (P : F k →L[𝕜] F k)
    (z : WithLp 2 (E × PiLp 2 F)) :
    liftedCopyCut T k P z = WithLp.toLp 2
      (z.fst - copyMean T (copyTail k z.snd) - T k ((1 - P : F k →L[𝕜] F k) (z.snd k)),
        copyHead k z.snd + PiLp.single 2 k (P (z.snd k))) := by
  have hm : copyMean T z.snd = copyMean T (copyHead k z.snd) + T k (z.snd k) +
      copyMean T (copyTail k z.snd) := by
    have h := congrArg (copyMean T) (copy_decomposition k z.snd)
    simpa only [map_add, copyMean_single] using h
  change WithLp.toLp 2
      (z.fst - copyMean T z.snd + copyMean T (copyHead k z.snd + PiLp.single 2 k (P (z.snd k))),
        copyHead k z.snd + PiLp.single 2 k (P (z.snd k))) = _
  congr 2
  rw [hm, map_add, copyMean_single]
  simp only [sub_apply, one_apply_eq_self, map_sub]
  abel

/-- Every cut in a lifted copy obeys the uniform concatenation bound. -/
theorem independent_copies_prefix (T : ∀ i, F i →L[𝕜] E) (k : ι)
    [FiniteDimensional 𝕜 (F k)] (P : F k →L[𝕜] F k)
    (hP : ∀ x, P (P x) = P x) {q Z η : ℝ}
    (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hq : 1 + Z < q)
    (hTotal : ‖∑ i, (T i).comp ((T i)†)‖ ≤ Z)
    (hCurrent : ‖(T k).comp ((T k)†)‖ ≤ η) (hPn : ‖P‖ ^ 2 ≤ q)
    (z : WithLp 2 (E × PiLp 2 F)) :
    ‖liftedCopyCut T k P z‖ ^ 2 ≤
      (q + q ^ 2 * η / (q - 1 - Z)) * ‖z‖ ^ 2 := by
  let A := hilbertRow (-copyMean T)
  let U := (T k).comp (1 - P)
  let M := hilbertTriangular A U P
  let C := q + q ^ 2 * η / (q - 1 - Z)
  have hδ : 0 < q - 1 - Z := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hC : 1 ≤ C := by
    have hd : 0 ≤ q ^ 2 * η / (q - 1 - Z) := by positivity
    dsimp [C]
    linarith
  have hA : ‖A‖ ^ 2 ≤ 1 + Z := by
    have h := hilbertRow_norm_sq_le (-copyMean T)
    rw [norm_neg, copyMean_norm_sq] at h
    exact h.trans (by linarith)
  have hT : ‖T k‖ ^ 2 ≤ η := by
    have h := norm_adjoint_comp_self ((T k)†)
    rw [adjoint_adjoint] at h
    simp only [LinearIsometryEquiv.norm_map] at h
    nlinarith
  have hU : ‖U‖ ^ 2 ≤ q * η := copy_coupling_norm_sq (T k) P hP hq1 hη hT hPn
  have hM : ‖M‖ ^ 2 ≤ C := hilbertTriangular_norm_sq_le A U P hZ hη hq hA hU hPn
  let w : WithLp 2 (WithLp 2 (E × PiLp 2 F) × F k) :=
    WithLp.toLp 2 (WithLp.toLp 2 (z.fst, copyTail k z.snd), z.snd k)
  have hw : ‖M w‖ ^ 2 ≤ C * ‖w‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg (M w)) (M.le_opNorm w) 2
    have hb := mul_le_mul_of_nonneg_right hM (sq_nonneg ‖w‖)
    nlinarith
  have hinput : ‖z‖ ^ 2 = ‖w‖ ^ 2 + ‖copyHead k z.snd‖ ^ 2 := by
    have hn := copy_norm_decomposition k z.snd
    simp only [w, WithLp.prod_norm_sq_eq_of_L2]
    change ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 =
      (‖z.fst‖ ^ 2 + ‖copyTail k z.snd‖ ^ 2) + ‖z.snd k‖ ^ 2 + ‖copyHead k z.snd‖ ^ 2
    linarith
  have hm : M w = WithLp.toLp 2
      (z.fst - copyMean T (copyTail k z.snd) - T k ((1 - P : F k →L[𝕜] F k) (z.snd k)),
        P (z.snd k)) := by
    simp [M, A, U, w, hilbertRow_apply, sub_eq_add_neg]
  have houtput : ‖liftedCopyCut T k P z‖ ^ 2 = ‖M w‖ ^ 2 + ‖copyHead k z.snd‖ ^ 2 := by
    rw [liftedCopyCut_apply, hm, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖z.fst - copyMean T (copyTail k z.snd) - T k ((1 - P : F k →L[𝕜] F k) (z.snd k))‖ ^ 2 +
        ‖copyHead k z.snd + PiLp.single 2 k (P (z.snd k))‖ ^ 2 = _
    rw [copyCut_norm_sq (𝕜 := 𝕜)]
    dsimp only [WithLp.fst, WithLp.snd]
    ring
  change ‖liftedCopyCut T k P z‖ ^ 2 ≤ C * ‖z‖ ^ 2
  rw [houtput, hinput]
  nlinarith [mul_le_mul_of_nonneg_right hC (sq_nonneg ‖copyHead k z.snd‖)]

/-- The lifted sum of copies, without any separate vector in the base space. -/
def liftedCopyVector (T : ∀ i, F i →L[𝕜] E) (x : PiLp 2 F) :
    WithLp 2 (E × PiLp 2 F) := liftCopies T (WithLp.toLp 2 (0, x))

omit [CompleteSpace E] [∀ i, CompleteSpace (F i)] in
/-- The span of the lifted copies is invariant under every subsequent cut. -/
theorem liftedCopyCut_vector (T : ∀ i, F i →L[𝕜] E) (k : ι)
    (P : F k →L[𝕜] F k) (x : PiLp 2 F) :
    liftedCopyCut T k P (liftedCopyVector T x) =
      liftedCopyVector T (copyHead k x + PiLp.single 2 k (P (x k))) := by
  simp only [liftedCopyVector, liftedCopyCut, unliftCopies_lift]
  rfl

/-- The same bound holds for the concatenation omitting the base space. -/
theorem independent_copies_without_base (T : ∀ i, F i →L[𝕜] E) (k : ι)
    [FiniteDimensional 𝕜 (F k)] (P : F k →L[𝕜] F k)
    (hP : ∀ x, P (P x) = P x) {q Z η : ℝ}
    (hZ : 0 ≤ Z) (hη : 0 ≤ η) (hq : 1 + Z < q)
    (hTotal : ‖∑ i, (T i).comp ((T i)†)‖ ≤ Z)
    (hCurrent : ‖(T k).comp ((T k)†)‖ ≤ η) (hPn : ‖P‖ ^ 2 ≤ q)
    (x : PiLp 2 F) :
    ‖liftedCopyVector T (copyHead k x + PiLp.single 2 k (P (x k)))‖ ^ 2 ≤
      (q + q ^ 2 * η / (q - 1 - Z)) * ‖liftedCopyVector T x‖ ^ 2 := by
  simpa only [liftedCopyCut_vector] using
    independent_copies_prefix T k P hP hZ hη hq hTotal hCurrent hPn (liftedCopyVector T x)

end Ordered
end SchauderTranslates
