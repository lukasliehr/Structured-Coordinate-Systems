import Lean_Code.PositiveL1.Abstract
import Lean_Code.PositiveL1.Indicators
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Splitting schemes of measurable sets

A sequence `A : ℕ → Set α` of measurable sets of positive finite measure which follows the
splitting scheme of `Lean_Code/PositiveL1/Abstract.lean` (`SplitCells`) gives rise to a
`SplitSystem` in `L¹(μ)`: the cell vectors are the normalised indicators `𝟙_{A k} / μ(A k)`
and the cell functionals are the set integrals `f ↦ ∫_{A k} f`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal NNReal ComplexOrder

namespace StructuredBases
namespace PositiveL1

variable {α : Type*} [MeasurableSpace α] {𝕜 : Type*} [RCLike 𝕜] {μ : Measure α}

/-! ### Set integrals as functionals on `L¹` -/

variable (𝕜 μ) in
/-- The set integral `f ↦ ∫ x in s, f x ∂μ` as a continuous linear functional on `L¹(μ)`. -/
def setIntegralCLM (s : Set α) : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  (L1.integralCLM' 𝕜).comp (LpToLpRestrictCLM α 𝕜 𝕜 μ 1 s)

theorem setIntegralCLM_apply (s : Set α) (f : Lp 𝕜 1 μ) :
    setIntegralCLM 𝕜 μ s f = ∫ x in s, f x ∂μ := by
  rw [setIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq' 𝕜,
    L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 s f)

/-- The integrals of an `L¹` function over finitely many pairwise disjoint measurable sets
have total size at most the norm of the function. -/
theorem sum_norm_setIntegral_le {ι : Type*} (t : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hdisj : Set.Pairwise (↑t) (Disjoint on A))
    (f : Lp 𝕜 1 μ) : ∑ i ∈ t, ‖∫ x in A i, f x ∂μ‖ ≤ ‖f‖ := by
  have hint : Integrable (fun x => ‖f x‖) μ := (L1.integrable_coeFn f).norm
  calc ∑ i ∈ t, ‖∫ x in A i, f x ∂μ‖
      ≤ ∑ i ∈ t, ∫ x in A i, ‖f x‖ ∂μ :=
        Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ x in ⋃ i ∈ t, A i, ‖f x‖ ∂μ :=
        (integral_biUnion_finset t hA hdisj (fun i _ => hint.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ∂μ :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => norm_nonneg _)
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

/-! ### Normalised indicators -/

variable (𝕜) in
/-- The normalised indicator `𝟙_s / μ(s)` as an element of `L¹(μ)`. -/
def cellVec (s : Set α) (hs : MeasurableSet s) (hμ : μ s ≠ ∞) : Lp 𝕜 1 μ :=
  indicatorConstLp 1 hs hμ (((μ.real s)⁻¹ : ℝ) : 𝕜)

theorem coeFn_cellVec {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    (cellVec 𝕜 s hs hμ : α → 𝕜) =ᵐ[μ] s.indicator fun _ => (((μ.real s)⁻¹ : ℝ) : 𝕜) :=
  indicatorConstLp_coeFn

theorem norm_cellVec {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) (h0 : μ s ≠ 0) :
    ‖cellVec 𝕜 s hs hμ‖ = 1 := by
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 hμ
  rw [cellVec, norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top,
    RCLike.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  simp [hpos.ne']

theorem setIntegral_cellVec {s t : Set α} (ht : MeasurableSet t) (hs : MeasurableSet s)
    (hμ : μ s ≠ ∞) :
    ∫ x in t, cellVec 𝕜 s hs hμ x ∂μ = ((μ.real (s ∩ t) * (μ.real s)⁻¹ : ℝ) : 𝕜) := by
  rw [cellVec, setIntegral_indicatorConstLp ht hs hμ, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

theorem cellVec_nonneg {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    ∀ᵐ x ∂μ, 0 ≤ cellVec 𝕜 s hs hμ x := by
  filter_upwards [coeFn_cellVec (𝕜 := 𝕜) hs hμ] with x hx
  rw [hx]
  by_cases h : x ∈ s
  · rw [indicator_of_mem h]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr measureReal_nonneg)
  · rw [indicator_of_notMem h]

theorem cellVec_eq_smul_indL {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) :
    cellVec 𝕜 s hs hμ = (((μ.real s)⁻¹ : ℝ) : 𝕜) • indL 𝕜 μ s :=
  indicatorConstLp_eq_smul_indL hs hμ _

theorem indL_eq_smul_cellVec {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) (h0 : μ s ≠ 0) :
    indL 𝕜 μ s = ((μ.real s : ℝ) : 𝕜) • cellVec 𝕜 s hs hμ := by
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 hμ
  rw [cellVec_eq_smul_indL, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hpos.ne',
    RCLike.ofReal_one, one_smul]

/-! ### Splitting schemes of sets -/

/-- A sequence of measurable sets following the splitting scheme: the sets with index in
`Finset.Icc n (3 * n)` are pairwise disjoint, `A n` is the disjoint union of `A (3 * n + 1)`
and `A (3 * n + 2)`, and the first of these has the proportion `θ` of the measure of
`A n`. -/
structure SplitCells (μ : Measure α) (θ : ℝ) (A : ℕ → Set α) : Prop where
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  measurable : ∀ k, MeasurableSet (A k)
  measure_ne_top : ∀ k, μ (A k) ≠ ∞
  measure_ne_zero : ∀ k, μ (A k) ≠ 0
  disjoint : ∀ n i j, n ≤ i → i ≤ 3 * n → n ≤ j → j ≤ 3 * n → i ≠ j → Disjoint (A i) (A j)
  union : ∀ n, A (3 * n + 1) ∪ A (3 * n + 2) = A n
  measure_left : ∀ n, μ.real (A (3 * n + 1)) = θ * μ.real (A n)
  measure_right : ∀ n, μ.real (A (3 * n + 2)) = (1 - θ) * μ.real (A n)

namespace SplitCells

variable {θ : ℝ} {A : ℕ → Set α}

variable (𝕜) in
/-- The normalised indicators of the cells. -/
def vec (h : SplitCells μ θ A) (k : ℕ) : Lp 𝕜 1 μ :=
  cellVec 𝕜 (A k) (h.measurable k) (h.measure_ne_top k)

variable (𝕜) in
/-- The integrals over the cells. -/
def fn (_h : SplitCells μ θ A) (k : ℕ) : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  setIntegralCLM 𝕜 μ (A k)

theorem measureReal_pos (h : SplitCells μ θ A) (k : ℕ) : 0 < μ.real (A k) :=
  ENNReal.toReal_pos (h.measure_ne_zero k) (h.measure_ne_top k)

theorem vec_nonneg (h : SplitCells μ θ A) (k : ℕ) : ∀ᵐ x ∂μ, 0 ≤ h.vec 𝕜 k x :=
  cellVec_nonneg _ _

theorem vec_split (h : SplitCells μ θ A) (n : ℕ) :
    h.vec 𝕜 n = (θ : 𝕜) • h.vec 𝕜 (3 * n + 1) + (1 - (θ : 𝕜)) • h.vec 𝕜 (3 * n + 2) := by
  have hm := (h.measureReal_pos n).ne'
  have hd : Disjoint (A (3 * n + 1)) (A (3 * n + 2)) :=
    h.disjoint (n + 1) _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have hu : indL 𝕜 μ (A n) = indL 𝕜 μ (A (3 * n + 1)) + indL 𝕜 μ (A (3 * n + 2)) := by
    rw [← h.union n, indL_union (h.measurable _) (h.measurable _) (h.measure_ne_top _)
      (h.measure_ne_top _) hd]
  have hc1 : (((μ.real (A n))⁻¹ : ℝ) : 𝕜) * ((μ.real (A (3 * n + 1)) : ℝ) : 𝕜) = (θ : 𝕜) := by
    rw [h.measure_left, ← RCLike.ofReal_mul]
    congr 1
    field_simp
  have hc2 : (((μ.real (A n))⁻¹ : ℝ) : 𝕜) * ((μ.real (A (3 * n + 2)) : ℝ) : 𝕜) =
      1 - (θ : 𝕜) := by
    have h1 : ((1 - θ : ℝ) : 𝕜) = 1 - (θ : 𝕜) := by rw [RCLike.ofReal_sub, RCLike.ofReal_one]
    rw [h.measure_right, ← RCLike.ofReal_mul, ← h1]
    congr 1
    field_simp
  rw [vec, cellVec_eq_smul_indL, hu,
    indL_eq_smul_cellVec (h.measurable (3 * n + 1)) (h.measure_ne_top _) (h.measure_ne_zero _),
    indL_eq_smul_cellVec (h.measurable (3 * n + 2)) (h.measure_ne_top _) (h.measure_ne_zero _),
    smul_add, smul_smul, smul_smul, hc1, hc2]
  rfl

/-- The normalised indicators and the set integrals of a splitting scheme of sets form a
`SplitSystem` in `L¹(μ)`. -/
theorem splitSystem (h : SplitCells μ θ A) : SplitSystem θ (h.vec 𝕜) (h.fn 𝕜) where
  theta_nonneg := h.theta_pos.le
  theta_le_one := h.theta_lt_one.le
  norm_le k := (norm_cellVec _ _ (h.measure_ne_zero k)).le
  sum_le n f := by
    simp only [fn, setIntegralCLM_apply]
    refine sum_norm_setIntegral_le _ A (fun i _ => h.measurable i) ?_ f
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_Icc] at hi hj
    exact h.disjoint n i j hi.1 hi.2 hj.1 hj.2 hij
  dual n i hi j hj := by
    rw [Finset.mem_Icc] at hi hj
    rw [fn, setIntegralCLM_apply, vec, setIntegral_cellVec (h.measurable i)]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, inter_self, mul_inv_cancel₀ (h.measureReal_pos i).ne', RCLike.ofReal_one]
    · rw [if_neg hij, (h.disjoint n j i hj.1 hj.2 hi.1 hi.2 (Ne.symm hij)).inter_eq]
      simp
  split := h.vec_split

/-- The functions of the sequence built from a splitting scheme of sets are non-negative. -/
theorem splitSeq_nonneg (h : SplitCells μ θ A) (k : ℕ) :
    ∀ᵐ x ∂μ, 0 ≤ splitSeq (h.vec 𝕜) k x := by
  refine splitSeq_induction (h.vec 𝕜) (P := fun f : Lp 𝕜 1 μ => ∀ᵐ x ∂μ, 0 ≤ f x)
    (fun i => h.vec_nonneg i) (fun i j => ?_) k
  filter_upwards [h.vec_nonneg (𝕜 := 𝕜) i, h.vec_nonneg (𝕜 := 𝕜) j,
    Lp.coeFn_add (h.vec 𝕜 i) (h.vec 𝕜 j)] with x hi hj hx
  rw [hx]
  exact add_nonneg hi hj

/-- The indicators of the cells lie in the span of the sequence. -/
theorem indL_mem_span (h : SplitCells μ θ A) (k : ℕ) :
    indL 𝕜 μ (A k) ∈ Submodule.span 𝕜 (Set.range (splitSeq (h.vec 𝕜))) := by
  rw [h.splitSystem.span_splitSeq,
    indL_eq_smul_cellVec (h.measurable k) (h.measure_ne_top k) (h.measure_ne_zero k)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end SplitCells

end PositiveL1
end StructuredBases
