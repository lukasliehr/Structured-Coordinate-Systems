import Lean_Code.SchauderTranslates.FiniteHilbert

noncomputable section
open Filter Matrix
open scoped Topology BigOperators ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real quadratic form of a coefficient Gram, on Euclidean coefficient space. -/
def gramQuadratic (B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ x (B.toEuclideanLin x)).re

theorem gramQuadratic_eq_dot (B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    gramQuadratic B x = (star (WithLp.ofLp x) ⬝ᵥ B *ᵥ (WithLp.ofLp x)).re := by
  simp [gramQuadratic, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

theorem continuous_gramQuadratic : Continuous
    (fun z : Matrix ι ι ℂ × EuclideanSpace ℂ ι => gramQuadratic z.1 z.2) := by
  simp only [gramQuadratic_eq_dot, dotProduct, Matrix.mulVec]
  fun_prop

theorem gramQuadratic_real_smul (B : Matrix ι ι ℂ) (r : ℝ) (x : EuclideanSpace ℂ ι) :
    gramQuadratic B ((r : ℂ) • x) = r ^ 2 * gramQuadratic B x := by
  simp [gramQuadratic, Complex.mul_re]
  ring

theorem gramQuadratic_pos_of_unit (B : Matrix ι ι ℂ)
    (h : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → 0 < gramQuadratic B x)
    (x : EuclideanSpace ℂ ι) (hx : x ≠ 0) : 0 < gramQuadratic B x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
    simp [norm_smul, hn.ne']
  have hp := h _ hu
  rw [gramQuadratic_real_smul] at hp
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp hp

/-- Positive definiteness is stable under Hermitian perturbations. -/
theorem gram_posDef_eventually {B : Matrix ι ι ℂ} (hB : B.PosDef) :
    ∀ᶠ G : Matrix ι ι ℂ in 𝓝 B, G.IsHermitian → G.PosDef := by
  have hu : ∀ᶠ G : Matrix ι ι ℂ in 𝓝 B,
      ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℂ ι) 1, 0 < gramQuadratic G x := by
    apply (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hx0 : WithLp.ofLp x ≠ 0 := by
      intro he
      have : x = 0 := (WithLp.equiv 2 (ι → ℂ)).injective he
      simp [this] at hx
    have hpos : 0 < gramQuadratic B x := by
      rw [gramQuadratic_eq_dot]
      exact hB.re_dotProduct_pos hx0
    exact (isOpen_lt continuous_const continuous_gramQuadratic).mem_nhds hpos
  filter_upwards [hu] with G hG hHerm
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hHerm.im_star_dotProduct_mulVec_self x⟩
  have hunit : ∀ y : EuclideanSpace ℂ ι, ‖y‖ = 1 → 0 < gramQuadratic G y := by
    intro y hy
    exact hG y (by simpa using hy)
  have hx' : WithLp.toLp 2 x ≠ (0 : EuclideanSpace ℂ ι) := by
    intro he
    exact hx (congrArg WithLp.ofLp he)
  change 0 < (star x ⬝ᵥ G *ᵥ x).re
  simpa only [gramQuadratic_eq_dot, WithLp.ofLp_toLp] using
    gramQuadratic_pos_of_unit G hunit (WithLp.toLp 2 x) hx'

/-- Matrix inversion is continuous at a positive definite Gram. -/
theorem gram_inverse_continuousAt {B : Matrix ι ι ℂ} (hB : B.PosDef) :
    ContinuousAt (fun G : Matrix ι ι ℂ => G⁻¹) B := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  apply ContinuousInv₀.continuousAt_inv₀
  exact ne_of_gt hB.det_pos

/-- Capture of a target with source moments `v` in a list with Gram `B`. -/
def gramCapture (B : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ B⁻¹ *ᵥ v).re

theorem gramCapture_continuousAt {B : Matrix ι ι ℂ} (hB : B.PosDef) (v : ι → ℂ) :
    ContinuousAt (fun z : Matrix ι ι ℂ × (ι → ℂ) => gramCapture z.1 z.2) (B, v) := by
  have hi := (gram_inverse_continuousAt hB).comp
    (continuous_fst.continuousAt : ContinuousAt
      (fun z : Matrix ι ι ℂ × (ι → ℂ) => z.1) (B, v))
  have hq : Continuous (fun z : Matrix ι ι ℂ × (ι → ℂ) =>
      (star z.2 ⬝ᵥ z.1 *ᵥ z.2).re) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hp : ContinuousAt (fun z : Matrix ι ι ℂ × (ι → ℂ) => (z.1⁻¹, z.2))
      (B, v) := hi.prodMk continuous_snd.continuousAt
  exact (hq.continuousAt (x := (B⁻¹, v))).comp (x := (B, v))
    (f := fun z : Matrix ι ι ℂ × (ι → ℂ) => (z.1⁻¹, z.2)) hp

/-- The Gram difference expressing a strict coordinate-projection bound. -/
def prefixGramDifference (K : ℝ) (E B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (K ^ 2) • B - Eᴴ * B * E

omit [DecidableEq ι] in
theorem prefixGramDifference_hermitian (K : ℝ) (E : Matrix ι ι ℂ)
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) : (prefixGramDifference K E B).IsHermitian :=
  (hB.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_conjTranspose_mul_mul E hB)

omit [DecidableEq ι] in
theorem continuous_prefixGramDifference (K : ℝ) (E : Matrix ι ι ℂ) :
    Continuous (prefixGramDifference K E) := by
  unfold prefixGramDifference
  fun_prop

theorem prefixGramDifference_quadratic (K : ℝ) (E B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    gramQuadratic (prefixGramDifference K E B) x =
      K ^ 2 * gramQuadratic B x - gramQuadratic B (E.toEuclideanLin x) := by
  have hE : star (WithLp.ofLp x) ⬝ᵥ (Eᴴ * B * E) *ᵥ WithLp.ofLp x =
      star (E *ᵥ WithLp.ofLp x) ⬝ᵥ B *ᵥ (E *ᵥ WithLp.ofLp x) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [gramQuadratic_eq_dot, prefixGramDifference, Matrix.sub_mulVec,
    Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hE, Matrix.ofLp_toLpLin]
  simp [Complex.real_smul, pow_two, Complex.mul_re, Complex.mul_im]

/-- Positive definiteness of the difference is the strict quadratic prefix inequality. -/
theorem prefixGramDifference_posDef_iff (K : ℝ) (E : Matrix ι ι ℂ)
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    (prefixGramDifference K E B).PosDef ↔
      ∀ x : EuclideanSpace ℂ ι, x ≠ 0 →
        gramQuadratic B (E.toEuclideanLin x) < K ^ 2 * gramQuadratic B x := by
  constructor
  · intro h x hx
    have hx' : WithLp.ofLp x ≠ 0 := fun he => hx ((WithLp.equiv 2 _).injective he)
    have hp := h.re_dotProduct_pos hx'
    change 0 < (star (WithLp.ofLp x) ⬝ᵥ prefixGramDifference K E B *ᵥ WithLp.ofLp x).re at hp
    rw [← gramQuadratic_eq_dot] at hp
    rw [prefixGramDifference_quadratic] at hp
    linarith
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (prefixGramDifference_hermitian K E hB)
    intro x hx
    apply RCLike.pos_iff.mpr
    refine ⟨?_, (prefixGramDifference_hermitian K E hB).im_star_dotProduct_mulVec_self x⟩
    have hx' : WithLp.toLp 2 x ≠ (0 : EuclideanSpace ℂ ι) := by
      intro he
      exact hx (congrArg WithLp.ofLp he)
    have hp := h (WithLp.toLp 2 x) hx'
    have hp' : 0 < gramQuadratic (prefixGramDifference K E B) (WithLp.toLp 2 x) := by
      rw [prefixGramDifference_quadratic]
      linarith
    change 0 < (star x ⬝ᵥ prefixGramDifference K E B *ᵥ x).re
    simpa only [gramQuadratic_eq_dot, WithLp.ofLp_toLp] using hp'

/-- All finite strict Gram conclusions persist simultaneously under Hermitian perturbation. -/
theorem finite_gram_stability {κ : Type*} [Finite κ]
    (E : κ → Matrix ι ι ℂ) (K : κ → ℝ)
    {B : Matrix ι ι ℂ} (hB : B.PosDef)
    (hp : ∀ i, (prefixGramDifference (K i) (E i) B).PosDef)
    (v : ι → ℂ) (s error : ℝ) (herr : s - gramCapture B v < error) :
    ∀ᶠ z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) in 𝓝 (B, (v, s)),
      z.1.IsHermitian → z.1.PosDef ∧
      (∀ i, (prefixGramDifference (K i) (E i) z.1).PosDef) ∧
      z.2.2 - gramCapture z.1 z.2.1 < error := by
  have hbase : ∀ᶠ z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) in 𝓝 (B, (v, s)),
      z.1.IsHermitian → z.1.PosDef :=
    continuous_fst.continuousAt (gram_posDef_eventually hB)
  have hprefix (i : κ) : ∀ᶠ z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) in 𝓝 (B, (v, s)),
      z.1.IsHermitian → (prefixGramDifference (K i) (E i) z.1).PosDef := by
    have hc : Continuous (fun z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) =>
        prefixGramDifference (K i) (E i) z.1) :=
      (continuous_prefixGramDifference _ _).comp continuous_fst
    filter_upwards [hc.continuousAt (gram_posDef_eventually (hp i))] with z hz hHerm
    exact hz (prefixGramDifference_hermitian _ _ hHerm)
  have hc : ContinuousAt
      (fun z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) => z.2.2 - gramCapture z.1 z.2.1)
      (B, (v, s)) := by
    apply ContinuousAt.sub (by fun_prop)
    exact (gramCapture_continuousAt hB v).comp (x := (B, (v, s)))
      (f := fun z : Matrix ι ι ℂ × ((ι → ℂ) × ℝ) => (z.1, z.2.1)) (by fun_prop)
  have he := hc (gt_mem_nhds herr)
  filter_upwards [hbase, Filter.eventually_all.mpr hprefix, he] with z hb hp he hHerm
  exact ⟨hb hHerm, fun i => hp i hHerm, he⟩

section Synthesis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteSynthesis (u : ι → H) (c : ι → ℂ) : H := ∑ i, c i • u i

def sourceMoments (u : ι → H) (f : H) : ι → ℂ := fun i => inner ℂ (u i) f

omit [DecidableEq ι] in
theorem sourceMoments_synthesis (u : ι → H) (c : ι → ℂ) :
    sourceMoments u (finiteSynthesis u c) = Matrix.gram ℂ u *ᵥ c := by
  ext i
  simp [sourceMoments, finiteSynthesis, Matrix.mulVec,
    dotProduct, mul_comm]

omit [DecidableEq ι] in
theorem synthesis_inner_source (u : ι → H) (c : ι → ℂ) (f : H) :
    inner ℂ (finiteSynthesis u c) f = star c ⬝ᵥ sourceMoments u f := by
  simp [finiteSynthesis, sourceMoments, dotProduct, mul_comm]

omit [DecidableEq ι] in
theorem inner_synthesis_source (u : ι → H) (c : ι → ℂ) (f : H) :
    inner ℂ f (finiteSynthesis u c) = star (sourceMoments u f) ⬝ᵥ c := by
  simp [finiteSynthesis, sourceMoments, dotProduct, mul_comm]

theorem synthesis_norm_sq (u : ι → H) (c : EuclideanSpace ℂ ι) :
    ‖finiteSynthesis u (WithLp.ofLp c)‖ ^ 2 = gramQuadratic (Matrix.gram ℂ u) c := by
  rw [gramQuadratic_eq_dot, Matrix.star_dotProduct_gram_mulVec]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- The candidate orthogonal projection computed by the normal equations. -/
def gramProjection (u : ι → H) (f : H) : H :=
  finiteSynthesis u ((Matrix.gram ℂ u)⁻¹ *ᵥ sourceMoments u f)

theorem gramProjection_source (u : ι → H) (hu : LinearIndependent ℂ u) (f : H) :
    sourceMoments u (gramProjection u f) = sourceMoments u f := by
  have hdet : IsUnit (Matrix.gram ℂ u).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.posDef_gram_of_linearIndependent hu).isUnit
  rw [gramProjection, sourceMoments_synthesis, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem gramProjection_orthogonal (u : ι → H) (hu : LinearIndependent ℂ u) (f : H)
    (c : ι → ℂ) : inner ℂ (finiteSynthesis u c) (f - gramProjection u f) = 0 := by
  rw [inner_sub_right, synthesis_inner_source, synthesis_inner_source, gramProjection_source u hu]
  exact sub_self _

theorem gramProjection_norm_sq (u : ι → H) (hu : LinearIndependent ℂ u) (f : H) :
    ‖gramProjection u f‖ ^ 2 = gramCapture (Matrix.gram ℂ u) (sourceMoments u f) := by
  have ho := gramProjection_orthogonal u hu f
    ((Matrix.gram ℂ u)⁻¹ *ᵥ sourceMoments u f)
  change inner ℂ (gramProjection u f) (f - gramProjection u f) = 0 at ho
  rw [inner_sub_right, sub_eq_zero] at ho
  have hre : (inner ℂ (gramProjection u f) f).re = ‖gramProjection u f‖ ^ 2 := by
    rw [ho]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hs : (inner ℂ f (gramProjection u f)).re =
      (inner ℂ (gramProjection u f) f).re := by
    exact inner_re_symm (𝕜 := ℂ) _ _
  rw [gramProjection, inner_synthesis_source] at hs
  change gramCapture (Matrix.gram ℂ u) (sourceMoments u f) = _ at hs
  simpa using (hs.trans hre).symm

/-- The squared projection error is exactly `s - v* G⁻¹ v`. -/
theorem gram_projection_error (u : ι → H) (hu : LinearIndependent ℂ u) (f : H) :
    ‖f - gramProjection u f‖ ^ 2 =
      ‖f‖ ^ 2 - gramCapture (Matrix.gram ℂ u) (sourceMoments u f) := by
  have hn := gramProjection_norm_sq u hu f
  rw [norm_sub_sq (𝕜 := ℂ), gramProjection, inner_synthesis_source]
  change ‖f‖ ^ 2 - 2 * gramCapture (Matrix.gram ℂ u) (sourceMoments u f) +
    ‖gramProjection u f‖ ^ 2 = _
  rw [hn]
  ring

/-- The normal-equation candidate minimizes the error over all coefficients. -/
theorem gramProjection_minimal (u : ι → H) (hu : LinearIndependent ℂ u) (f : H)
    (c : ι → ℂ) : ‖f - gramProjection u f‖ ^ 2 ≤ ‖f - finiteSynthesis u c‖ ^ 2 := by
  have hc := gramProjection_orthogonal u hu f c
  have hp := gramProjection_orthogonal u hu f
    ((Matrix.gram ℂ u)⁻¹ *ᵥ sourceMoments u f)
  have ho : inner ℂ (gramProjection u f - finiteSynthesis u c)
      (f - gramProjection u f) = 0 := by
    rw [inner_sub_left, hc]
    simpa only [gramProjection, sub_zero] using hp
  have hr : f - finiteSynthesis u c =
      (gramProjection u f - finiteSynthesis u c) + (f - gramProjection u f) := by abel
  rw [hr, norm_add_sq (𝕜 := ℂ), ho]
  simp only [map_zero, mul_zero, add_zero]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem gram_projection_error_inf (u : ι → H) (hu : LinearIndependent ℂ u) (f : H) :
    sInf (Set.range (fun c : ι → ℂ => ‖f - finiteSynthesis u c‖ ^ 2)) =
      ‖f‖ ^ 2 - gramCapture (Matrix.gram ℂ u) (sourceMoments u f) := by
  have hm : IsLeast (Set.range (fun c : ι → ℂ => ‖f - finiteSynthesis u c‖ ^ 2))
      (‖f - gramProjection u f‖ ^ 2) := by
    refine ⟨⟨(Matrix.gram ℂ u)⁻¹ *ᵥ sourceMoments u f, rfl⟩, ?_⟩
    rintro y ⟨c, rfl⟩
    exact gramProjection_minimal u hu f c
  rw [hm.csInf_eq, gram_projection_error u hu f]

end Synthesis

end SchauderTranslates
