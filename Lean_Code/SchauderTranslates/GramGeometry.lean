import Lean_Code.SchauderTranslates.HilbertBlocks
import Lean_Code.SchauderTranslates.FiniteGram

noncomputable section
open ContinuousLinearMap Matrix
open scoped InnerProductSpace InnerProduct MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

section Selected
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The selected Gram formula uses Hilbert operator norms, including rectangular maps. -/
theorem selected_gram_norm (X Y : F →L[𝕜] E) (S : F →L[𝕜] F)
    (hS : S† = S) (hSS : S.comp S = (X†).comp X) :
    ‖X.comp (Y†)‖ ^ 2 = ‖S.comp ((Y†).comp (Y.comp S))‖ := by
  have h₁ := norm_adjoint_comp_self (X.comp (Y†))
  have h₂ := norm_adjoint_comp_self (S.comp (Y†))
  have h₃ := norm_adjoint_comp_self ((S.comp (Y†))†)
  have he : ((X.comp (Y†))†).comp (X.comp (Y†)) =
      ((S.comp (Y†))†).comp (S.comp (Y†)) := by
    simp only [adjoint_comp, adjoint_adjoint, hS, comp_assoc]
    rw [← comp_assoc S S, hSS]
    simp only [comp_assoc]
  rw [he] at h₁
  have he' : ((S.comp (Y†))†)†.comp ((S.comp (Y†))†) =
      S.comp ((Y†).comp (Y.comp S)) := by
    simp only [adjoint_comp, adjoint_adjoint, hS, comp_assoc]
  rw [he'] at h₃
  simp only [LinearIsometryEquiv.norm_map] at h₃
  nlinarith [h₁, h₂, h₃]

end Selected

section Matrix
variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- The positive matrix square root acting on Euclidean coefficient space. -/
def gramRoot (B : Matrix ι ι 𝕜) : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι :=
  (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)

def gramRootInv (B : Matrix ι ι 𝕜) : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι :=
  (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)⁻¹

theorem gramRoot_adjoint (B : Matrix ι ι 𝕜) : (gramRoot B)† = gramRoot B := by
  change star ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)) = _
  have hmap : (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (star (CFC.sqrt B)) =
      star ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)) :=
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)).map_star' _
  rw [← hmap, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq]
  rfl

theorem gramRoot_square {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) :
    (gramRoot B).comp (gramRoot B) = (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B := by
  change (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B) * (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B) = _
  rw [← map_mul, CFC.sqrt_mul_sqrt_self B hB.nonneg]

theorem gramRoot_isUnit {B : Matrix ι ι 𝕜} (hB : B.PosDef) : IsUnit (CFC.sqrt B) := by
  have h : IsUnit (CFC.sqrt B * CFC.sqrt B) := by
    rw [CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg]
    exact hB.isUnit
  exact (IsUnit.mul_iff.mp h).1

theorem gramRoot_mul_inv {B : Matrix ι ι 𝕜} (hB : B.PosDef) :
    (gramRoot B).comp (gramRootInv B) = 1 := by
  change (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B) * (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)⁻¹ = _
  rw [← map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (gramRoot_isUnit hB)),
    map_one]

theorem gramRoot_inv_mul {B : Matrix ι ι 𝕜} (hB : B.PosDef) :
    (gramRootInv B).comp (gramRoot B) = 1 := by
  change (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B)⁻¹ * (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (CFC.sqrt B) = _
  rw [← map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gramRoot_isUnit hB)),
    map_one]

theorem gramRoot_norm_sq {B : Matrix ι ι 𝕜} (hB : B.PosSemidef)
    (x : EuclideanSpace 𝕜 ι) :
    ‖gramRoot B x‖ ^ 2 = RCLike.re (inner 𝕜 x ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B x)) := by
  have hi : inner 𝕜 (gramRoot B x) (gramRoot B x) =
      inner 𝕜 x ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B x) := by
    rw [← adjoint_inner_right, gramRoot_adjoint, ← ContinuousLinearMap.comp_apply, gramRoot_square hB]
  rw [← hi, inner_self_eq_norm_sq]

/-- Conjugation by the positive square root represents a coordinate projection. -/
def gramConjugate (B D : Matrix ι ι 𝕜) :
    EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι :=
  (gramRoot B).comp (((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D).comp (gramRootInv B))

theorem gramConjugate_bound_iff {B : Matrix ι ι 𝕜} (hB : B.PosDef)
    (D : Matrix ι ι 𝕜) {C : ℝ} (hC : 0 ≤ C) :
    ‖gramConjugate B D‖ ^ 2 ≤ C ↔ ∀ x : EuclideanSpace 𝕜 ι,
      ‖gramRoot B ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D x)‖ ^ 2 ≤ C * ‖gramRoot B x‖ ^ 2 := by
  have hc (x : EuclideanSpace 𝕜 ι) :
      gramConjugate B D (gramRoot B x) = gramRoot B ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D x) := by
    change gramRoot B ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D (gramRootInv B (gramRoot B x))) = _
    have hi : gramRootInv B (gramRoot B x) = x := by
      simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
        congrArg (fun f : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι => f x)
          (gramRoot_inv_mul hB)
    rw [hi]
  constructor
  · intro h x
    have hn := (gramConjugate B D).le_opNorm (gramRoot B x)
    have hn2 := pow_le_pow_left₀ (norm_nonneg (gramConjugate B D (gramRoot B x))) hn 2
    rw [hc] at hn2
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖gramRoot B x‖)]
  · intro h
    apply opNorm_sq_le_of_pointwise _ hC
    intro x
    have hx : gramRoot B (gramRootInv B x) = x := by
      rw [← ContinuousLinearMap.comp_apply, gramRoot_mul_inv hB, one_apply_eq_self]
    simpa only [hx, gramConjugate, ContinuousLinearMap.comp_apply] using h (gramRootInv B x)

/-- The coefficient quadratic form for either the real or complex scalar field. -/
def coefficientQuadratic (B : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) : ℝ :=
  RCLike.re (inner 𝕜 x ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B x))

theorem coefficientQuadratic_eq_dot (B : Matrix ι ι 𝕜) (x : EuclideanSpace 𝕜 ι) :
    coefficientQuadratic B x = RCLike.re
      (star (WithLp.ofLp x) ⬝ᵥ B *ᵥ (WithLp.ofLp x)) := by
  simp [coefficientQuadratic, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, dotProduct_comm]

theorem matrix_posSemidef_iff_quadratic {B : Matrix ι ι 𝕜} (hB : B.IsHermitian) :
    B.PosSemidef ↔ ∀ x : EuclideanSpace 𝕜 ι, 0 ≤ coefficientQuadratic B x := by
  constructor
  · intro h x
    rw [coefficientQuadratic_eq_dot]
    exact h.re_dotProduct_nonneg _
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hB
    intro x
    apply RCLike.nonneg_iff.mpr
    refine ⟨?_, hB.im_star_dotProduct_mulVec_self x⟩
    simpa only [coefficientQuadratic_eq_dot, WithLp.ofLp_toLp] using h (WithLp.toLp 2 x)

/-- The non-strict Gram inequality for an arbitrary coordinate operator. -/
def gramDifference (C : ℝ) (D B : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  C • B - D.conjTranspose * B * D

omit [DecidableEq ι] in
theorem gramDifference_hermitian (C : ℝ) (D : Matrix ι ι 𝕜)
    {B : Matrix ι ι 𝕜} (hB : B.IsHermitian) : (gramDifference C D B).IsHermitian :=
  (hB.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_conjTranspose_mul_mul D hB)

theorem gramDifference_quadratic (C : ℝ) (D B : Matrix ι ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    coefficientQuadratic (gramDifference C D B) x = C * coefficientQuadratic B x -
      coefficientQuadratic B ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D x) := by
  have hD : star (WithLp.ofLp x) ⬝ᵥ (D.conjTranspose * B * D) *ᵥ WithLp.ofLp x =
      star (D *ᵥ WithLp.ofLp x) ⬝ᵥ B *ᵥ (D *ᵥ WithLp.ofLp x) := by
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [coefficientQuadratic_eq_dot, gramDifference, Matrix.sub_mulVec,
    Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, hD, Matrix.ofLp_toEuclideanCLM]
  simp only [map_sub]
  congr 1
  exact (RCLike.reCLM.map_smul C _)

/-- Squared prefix norm is equivalent to a positive semidefinite Gram difference. -/
theorem gram_prefix_iff {B : Matrix ι ι 𝕜} (hB : B.PosDef)
    (D : Matrix ι ι 𝕜) (K : ℝ) :
    ‖gramConjugate B D‖ ^ 2 ≤ K ^ 2 ↔ (gramDifference (K ^ 2) D B).PosSemidef := by
  rw [gramConjugate_bound_iff hB D (sq_nonneg K),
    matrix_posSemidef_iff_quadratic (gramDifference_hermitian _ _ hB.isHermitian)]
  simp only [gramDifference_quadratic, sub_nonneg]
  simp only [gramRoot_norm_sq hB.posSemidef, coefficientQuadratic]

omit [DecidableEq ι] in
theorem gramDifference_add (C : ℝ) (D B₀ B₁ : Matrix ι ι 𝕜) :
    gramDifference C D (B₀ + B₁) = gramDifference C D B₀ + gramDifference C D B₁ := by
  simp only [gramDifference, smul_add, Matrix.mul_add, Matrix.add_mul]
  abel

omit [DecidableEq ι] in
theorem gramDifference_real_smul (C r : ℝ) (D B : Matrix ι ι 𝕜) :
    gramDifference C D (r • B) = r • gramDifference C D B := by
  simp only [gramDifference, smul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [mul_comm]

omit [DecidableEq ι] in
/-- Positive sums of Grams preserve the same non-strict prefix bound. -/
theorem gram_prefix_positive_sum (C : ℝ) (D B₀ B₁ : Matrix ι ι 𝕜)
    (h₀ : (gramDifference C D B₀).PosSemidef)
    (h₁ : (gramDifference C D B₁).PosSemidef)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (gramDifference C D (r • B₀ + s • B₁)).PosSemidef := by
  rw [gramDifference_add, gramDifference_real_smul, gramDifference_real_smul]
  exact (h₀.smul hr).add (h₁.smul hs)

end Matrix

section Rectangular
variable {𝕜 ι κ ν : Type*} [RCLike 𝕜]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- Rectangular matrices always act between Euclidean, rather than supremum-norm, spaces. -/
def matrixHilbertMap (A : Matrix ι κ 𝕜) : EuclideanSpace 𝕜 κ →L[𝕜] EuclideanSpace 𝕜 ι :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq ι] in
theorem matrixHilbertMap_mul (A : Matrix ι κ 𝕜) (B : Matrix κ ν 𝕜) :
    matrixHilbertMap (A * B) = (matrixHilbertMap A).comp (matrixHilbertMap B) := by
  apply ContinuousLinearMap.ext
  intro x
  change WithLp.toLp 2 ((A * B) *ᵥ WithLp.ofLp x) =
    WithLp.toLp 2 (A *ᵥ (B *ᵥ WithLp.ofLp x))
  rw [Matrix.mulVec_mulVec]

theorem matrixHilbertMap_adjoint (A : Matrix ι κ 𝕜) :
    matrixHilbertMap A.conjTranspose = (matrixHilbertMap A)† := by
  unfold matrixHilbertMap
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_toContinuousLinearMap _

theorem matrixHilbertMap_square (B : Matrix ι ι 𝕜) :
    matrixHilbertMap B = (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B := rfl

/-- The columns of the identity selected by an index map. -/
def selectionColumns (e : κ → ι) : Matrix ι κ 𝕜 := (1 : Matrix ι ι 𝕜).submatrix id e

omit [Fintype κ] [DecidableEq κ] in
theorem selectionColumns_compress (B : Matrix ι ι 𝕜) (e : κ → ι) :
    (selectionColumns (𝕜 := 𝕜) e).conjTranspose * B * selectionColumns (𝕜 := 𝕜) e = B.submatrix e e := by
  simp only [selectionColumns, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  have hleft : (1 : Matrix ι ι 𝕜).submatrix e id * B = B.submatrix e id := by
    simpa using Matrix.one_submatrix_mul e (Equiv.refl ι) B
  rw [hleft]
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, Matrix.submatrix_submatrix,
    Function.comp_id] using Matrix.mul_submatrix_one (Equiv.refl ι) e (B.submatrix e id)

theorem gramRootInv_eq_root_inverse {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) :
    gramRootInv B = gramRoot B⁻¹ := by
  unfold gramRootInv gramRoot
  rw [hB.inv_sqrt]

theorem gramRootInv_adjoint {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) :
    (gramRootInv B)† = gramRootInv B := by
  rw [gramRootInv_eq_root_inverse hB, gramRoot_adjoint]

/-- Gram of the selected square-root columns. -/
theorem gram_selected_columns {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (e : κ → ι) :
    (((gramRoot B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e)))†).comp
      ((gramRoot B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))) =
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := κ)) (B.submatrix e e) := by
  rw [adjoint_comp, gramRoot_adjoint]
  simp only [comp_assoc]
  rw [← comp_assoc (gramRoot B) (gramRoot B), gramRoot_square hB]
  change ((matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))†).comp
    ((matrixHilbertMap B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))) = _
  rw [← matrixHilbertMap_adjoint, ← matrixHilbertMap_mul, ← matrixHilbertMap_mul,
    ← Matrix.mul_assoc, selectionColumns_compress, matrixHilbertMap_square]

/-- Multiplying the selected primal and dual columns gives the coordinate projection. -/
theorem gram_selected_factorization {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (e : κ → ι) :
    ((gramRoot B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))).comp
      (((gramRootInv B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e)))†) =
    gramConjugate B (selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose) := by
  rw [adjoint_comp, gramRootInv_adjoint hB]
  change _ = (gramRoot B).comp ((matrixHilbertMap
    (selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose)).comp (gramRootInv B))
  rw [matrixHilbertMap_mul, matrixHilbertMap_adjoint]
  simp only [comp_assoc]

/-- Explicit selected-block norm formula, valid also for an empty selected set. -/
theorem gram_selected_block_norm {B : Matrix ι ι 𝕜} (hB : B.PosDef) (e : κ → ι) :
    ‖gramConjugate B (selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose)‖ ^ 2 =
      ‖(gramRoot (B.submatrix e e)).comp
        ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := κ)) (B⁻¹.submatrix e e) |>.comp
          (gramRoot (B.submatrix e e)))‖ := by
  let X := (gramRoot B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))
  let Y := (gramRootInv B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e))
  let S := gramRoot (B.submatrix e e)
  have hX := gram_selected_columns hB.posSemidef e
  have hY : (Y†).comp Y =
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := κ)) (B⁻¹.submatrix e e) := by
    dsimp [Y]
    rw [gramRootInv_eq_root_inverse hB.posSemidef]
    exact gram_selected_columns hB.inv.posSemidef e
  have hSS : S.comp S = (X†).comp X :=
    (gramRoot_square (hB.posSemidef.submatrix e)).trans hX.symm
  have hn := selected_gram_norm X Y S (gramRoot_adjoint _) hSS
  have htail : S.comp ((Y†).comp (Y.comp S)) = S.comp
      (((Y†).comp Y).comp S) := congrArg (fun A => S.comp A) (comp_assoc (Y†) Y S).symm
  rw [htail, hY] at hn
  rw [gram_selected_factorization hB.posSemidef e] at hn
  exact hn

omit [Fintype κ] in
theorem selectionColumns_isometry (e : κ → ι) (he : Function.Injective e) :
    (selectionColumns (𝕜 := 𝕜) e).conjTranspose * selectionColumns (𝕜 := 𝕜) e = 1 := by
  have h := selectionColumns_compress (1 : Matrix ι ι 𝕜) e
  simpa only [Matrix.mul_one, Matrix.submatrix_one _ he] using h

theorem selection_projection_idempotent (e : κ → ι) (he : Function.Injective e) :
    (selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose) *
      (selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose) =
    selectionColumns (𝕜 := 𝕜) e * (selectionColumns (𝕜 := 𝕜) e).conjTranspose := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (selectionColumns (𝕜 := 𝕜) e).conjTranspose,
    selectionColumns_isometry e he, Matrix.one_mul]

end Rectangular

section Synthesis
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The abstract Gram operator bound is exactly the bound on finite synthesis. -/
theorem synthesis_gram_prefix_iff (u : ι → H) (hu : LinearIndependent ℂ u)
    (D : Matrix ι ι ℂ) (K : ℝ) :
    ‖gramConjugate (Matrix.gram ℂ u) D‖ ^ 2 ≤ K ^ 2 ↔
      ∀ c : ι → ℂ, ‖finiteSynthesis u (D *ᵥ c)‖ ^ 2 ≤ K ^ 2 * ‖finiteSynthesis u c‖ ^ 2 := by
  have hB := Matrix.posDef_gram_of_linearIndependent hu
  have hn (z : EuclideanSpace ℂ ι) :
      ‖gramRoot (Matrix.gram ℂ u) z‖ ^ 2 = ‖finiteSynthesis u (WithLp.ofLp z)‖ ^ 2 := by
    rw [gramRoot_norm_sq hB.posSemidef, synthesis_norm_sq]
    rfl
  rw [gramConjugate_bound_iff hB D (sq_nonneg K)]
  simp only [hn, Matrix.ofLp_toEuclideanCLM]
  constructor
  · intro h c
    exact h (WithLp.toLp 2 c)
  · intro h c
    exact h c.ofLp

end Synthesis
end SchauderTranslates
