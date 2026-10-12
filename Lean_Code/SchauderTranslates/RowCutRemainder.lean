import Lean_Code.SchauderTranslates.RowCutEndpoints

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ η K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Scalar coefficient coordinates commute with selection of whole rows. -/
theorem familyCoordinateSelection_coordinate (e : κ → ι) (v : K) (f : ι → K) :
    WithLp.toLp 2 (fun i => inner ℝ v (familyCoordinateSelection e f i)) =
      coordinateSelection e (WithLp.toLp 2 (fun i => inner ℝ v (f i))) := by
  ext i
  simp only [coordinateSelection_apply_coordinate, familyCoordinateSelection, inner_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- Selecting rows amplifies a scalar quadratic estimate to finite families in any Hilbert space. -/
theorem familyCoordinateSelection_energy_bound (B : Matrix ι ι ℝ) (e : κ → ι) (C : ℝ)
    (h : ∀ x : EuclideanSpace ℝ ι,
      coefficientQuadratic B (coordinateSelection e x) ≤ C * coefficientQuadratic B x)
    (f : ι → K) :
    matrixEnergy B (familyCoordinateSelection e f) ≤ C * matrixEnergy B f := by
  let V := Submodule.span ℝ (Set.range f)
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let g : ι → V := fun i => ⟨f i, Submodule.subset_span (Set.mem_range_self i)⟩
  let b := stdOrthonormalBasis ℝ V
  have hg : matrixEnergy B (familyCoordinateSelection e g) ≤ C * matrixEnergy B g := by
    rw [matrixEnergy_orthonormalBasis b, matrixEnergy_orthonormalBasis b, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [familyCoordinateSelection_coordinate]
    exact h _
  simpa [matrixEnergy, familyCoordinateSelection, Submodule.coe_inner, g,
    apply_ite] using hg

@[simp] theorem coefficientQuadratic_one (x : EuclideanSpace ℝ ι) :
    coefficientQuadratic (1 : Matrix ι ι ℝ) x = ‖x‖ ^ 2 := by
  simp [coefficientQuadratic]

/-- Whole-row cuts satisfy the uniform row bound also on an infinite spatial remainder. -/
theorem familyCoordinateSelection_activation_bound {B : Matrix ι ι ℝ}
    (hB : B.PosDef) (hBI : B ≤ 1) (e : κ → ι) (he : Function.Injective e)
    (j : ι) (hj : ∀ i, e i ≠ j) (Q : K →L[ℝ] K) (f : ι → K) :
    activationEnergy B Q (familyCoordinateSelection e f) ≤
      metricRowBound B e j * activationEnergy B Q f := by
  have hq : (fun i => Q (familyCoordinateSelection e f i)) =
      familyCoordinateSelection e (fun i => Q (f i)) := by
    ext i
    simp [familyCoordinateSelection, apply_ite]
  have hi : (fun i => familyCoordinateSelection e f i - Q (familyCoordinateSelection e f i)) =
      familyCoordinateSelection e (fun i => f i - Q (f i)) := by
    ext i
    rw [congrFun hq i]
    simp only [familyCoordinateSelection, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  have ha := familyCoordinateSelection_energy_bound B e (metricRowBound B e j)
    (fun x => by simpa [endpointCoefficientCut] using
      endpointCoefficientCut_active_bound hB hBI e he j hj (δ := 0) (Or.inl rfl) x)
    (fun i => Q (f i))
  have hb := familyCoordinateSelection_energy_bound (1 : Matrix ι ι ℝ) e (metricRowBound B e j)
    (fun x => by simpa [endpointCoefficientCut] using
      endpointCoefficientCut_inactive_bound hB hBI e he j hj (δ := 0) (Or.inl rfl) x)
    (fun i => f i - Q (f i))
  simpa only [activationEnergy, hq, hi, mul_add] using add_le_add ha hb

/-- The zero part of the first projection requires only the old endpoint bound. -/
theorem familyRowCut_remainder_bound {B : Matrix ι ι ℝ}
    (hB : B.PosDef) (hBI : B ≤ 1) (e : κ → ι) (he : Function.Injective e)
    (j : ι) (hj : ∀ i, e i ≠ j) (F Q : K →L[ℝ] K)
    (f : ι → K) (hf : F (f j) = 0) :
    activationEnergy B Q (familyRowCut e j F f) ≤ metricRowBound B e j * activationEnergy B Q f := by
  simpa [familyRowCut, hf] using familyCoordinateSelection_activation_bound hB hBI e he j hj Q f

end SchauderTranslates
