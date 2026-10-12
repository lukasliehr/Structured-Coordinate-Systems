import Lean_Code.PositiveTranslates.Local.Rearrangement

/-!
# Piecewise affine rearrangements: the operator on `Lᵖ(ℝ)`

For a rearrangement `R` (countably many pairs of source and target intervals) and a finite
exponent `p`, `R.op hpfin : Lᵖ(ℝ) →ₗ[ℂ] Lᵖ(ℝ)` is the class of the weighted composition
`R.fn p F`. It is

* contractive (`norm_op_le`), and isometric on the functions supported in the union of the
  source intervals (`norm_op_of_supported`);
* supported in the union of the target intervals (`op_supported`);
* inverted on that subspace by the operator of the inverse rearrangement (`symm_op_op`);
* positive (`op_nonneg`).

Consequently it maps `Lᵖ(⋃ sources)` isometrically onto `Lᵖ(⋃ targets)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction
open Local

namespace Rearrangement

variable {ι : Type*} [Countable ι] (R : Rearrangement ι) {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem memLp_fn (hpfin : p ≠ ∞) (F : LebesgueLp p) : MemLp (R.fn p F) p volume :=
  ⟨(R.fn_measurable (Lp.stronglyMeasurable F).measurable).aestronglyMeasurable,
    (R.eLpNorm_fn_le exponent_ne_zero hpfin F).trans_lt (Lp.memLp F).2⟩

/-- The operator of a rearrangement: the `Lᵖ` class of `x ↦ ρᵢ^{1/p} F (αᵢ x)` on the `i`-th
target interval, zero elsewhere. -/
def op (hpfin : p ≠ ∞) : LebesgueLp p →ₗ[ℂ] LebesgueLp p where
  toFun F := (R.memLp_fn hpfin F).toLp (R.fn p F)
  map_add' F G := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (R.memLp_fn hpfin (F + G)),
      Lp.coeFn_add ((R.memLp_fn hpfin F).toLp _) ((R.memLp_fn hpfin G).toLp _),
      MemLp.coeFn_toLp (R.memLp_fn hpfin F), MemLp.coeFn_toLp (R.memLp_fn hpfin G),
      R.fn_congr_ae (p := p) (Lp.coeFn_add F G)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, R.fn_add, Pi.add_apply]
  map_smul' a F := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (R.memLp_fn hpfin (a • F)),
      Lp.coeFn_smul a ((R.memLp_fn hpfin F).toLp _),
      MemLp.coeFn_toLp (R.memLp_fn hpfin F),
      R.fn_congr_ae (p := p) (Lp.coeFn_smul a F)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1, h2, Pi.smul_apply, h3, h4, R.fn_smul, Pi.smul_apply]

variable (hpfin : p ≠ ∞)

theorem op_ae (F : LebesgueLp p) : R.op hpfin F =ᵐ[volume] R.fn p F :=
  MemLp.coeFn_toLp (R.memLp_fn hpfin F)

/-- Computation of `R.op` from any representative. -/
theorem op_eq_of_ae {F G : LebesgueLp p} {f₀ : ℝ → ℂ} (hF : F =ᵐ[volume] f₀)
    (hG : G =ᵐ[volume] R.fn p f₀) : R.op hpfin F = G := by
  apply Lp.ext
  exact (R.op_ae hpfin F).trans ((R.fn_congr_ae hF).trans hG.symm)

theorem norm_op_le (F : LebesgueLp p) : ‖R.op hpfin F‖ ≤ ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (R.op_ae hpfin F)]
  exact ENNReal.toReal_mono (Lp.memLp F).2.ne (R.eLpNorm_fn_le exponent_ne_zero hpfin F)

/-- The operator of a rearrangement as a continuous linear map. -/
def opL : LebesgueLp p →L[ℂ] LebesgueLp p :=
  (R.op hpfin).mkContinuous 1 (fun F => by simpa using R.norm_op_le hpfin F)

@[simp] theorem opL_apply (F : LebesgueLp p) : R.opL hpfin F = R.op hpfin F := rfl

theorem op_supported (F : LebesgueLp p) : SupportedOn (R.op hpfin F) R.tgtUnion := by
  filter_upwards [R.op_ae hpfin F] with x hx hout
  rw [hx, R.fn_of_notMem hout]

/-- On functions supported in the union of the source intervals the inverse rearrangement
undoes the rearrangement. -/
theorem symm_op_op {F : LebesgueLp p} (hF : SupportedOn F R.srcUnion) :
    R.symm.op hpfin (R.op hpfin F) = F := by
  apply R.symm.op_eq_of_ae hpfin (R.op_ae hpfin F)
  rw [R.symm_fn_fn]
  filter_upwards [hF] with x hx
  by_cases hmem : x ∈ R.srcUnion
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, hx hmem]

/-- The operator is isometric on functions supported in the union of the source intervals. -/
theorem norm_op_of_supported {F : LebesgueLp p} (hF : SupportedOn F R.srcUnion) :
    ‖R.op hpfin F‖ = ‖F‖ := by
  apply le_antisymm (R.norm_op_le hpfin F)
  calc ‖F‖ = ‖R.symm.op hpfin (R.op hpfin F)‖ := by rw [R.symm_op_op hpfin hF]
    _ ≤ ‖R.op hpfin F‖ := R.symm.norm_op_le hpfin _

/-- The operator maps onto the functions supported in the union of the target intervals. -/
theorem exists_op_eq {G : LebesgueLp p} (hG : SupportedOn G R.tgtUnion) :
    ∃ F : LebesgueLp p, SupportedOn F R.srcUnion ∧ R.op hpfin F = G :=
  ⟨R.symm.op hpfin G, R.symm.op_supported hpfin G, R.symm.symm_op_op hpfin hG⟩

/-- The operator is positive. -/
theorem op_nonneg {F : LebesgueLp p} (hF : IsNonneg F) : IsNonneg (R.op hpfin F) := by
  have hall : ∀ᵐ x : ℝ, ∀ i, 0 ≤ F (R.aff i x) := R.ae_aff hF
  filter_upwards [R.op_ae hpfin F, hall] with x hx hx0
  rw [hx]
  by_cases hmem : x ∈ R.tgtUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    rw [R.fn_of_mem hi]
    exact mul_nonneg (Complex.zero_le_real.mpr (R.weight_pos p i).le) (hx0 i)
  · rw [R.fn_of_notMem hmem]

end Rearrangement

end StructuredBases.PositiveTranslates
