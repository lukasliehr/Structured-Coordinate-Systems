import Lean_Code.SchauderTranslates.Lp.LpSupportedSubmodule

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) (s : Set α)

/-- Complex-linear restriction on Lᵖ equivalence classes. -/
def lpRestrictToSet : Lp ℂ p μ →ₗ[ℂ] Lp ℂ p (μ.restrict s) where
  toFun f := ((Lp.memLp f).restrict s).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s),
      Lp.coeFn_add (((Lp.memLp f).restrict s).toLp f) (((Lp.memLp g).restrict s).toLp g),
      MemLp.coeFn_toLp ((Lp.memLp f).restrict s), MemLp.coeFn_toLp ((Lp.memLp g).restrict s),
      ae_restrict_of_ae (Lp.coeFn_add f g)] with x hsum hadd hf hg hfg
    rw [hsum, hadd, Pi.add_apply, hf, hg, hfg]
    rfl
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (a • f)).restrict s),
      Lp.coeFn_smul a (((Lp.memLp f).restrict s).toLp f),
      MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
      ae_restrict_of_ae (Lp.coeFn_smul a f)] with x hsum ha hf haf
    simp only [RingHom.id_apply]
    rw [hsum, ha, Pi.smul_apply, hf, haf]
    rfl

theorem lpRestrictToSet_ae (f : Lp ℂ p μ) : lpRestrictToSet p μ s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

theorem lpRestrictToSet_norm_le (f : Lp ℂ p μ) : ‖lpRestrictToSet p μ s f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (lpRestrictToSet_ae p μ s f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_restrict_le _ _ _ _)

def lpRestriction : Lp ℂ p μ →L[ℂ] Lp ℂ p (μ.restrict s) :=
  (lpRestrictToSet p μ s).mkContinuous 1 (fun f => by simpa using lpRestrictToSet_norm_le p μ s f)

theorem lpRestriction_ae (f : Lp ℂ p μ) : lpRestriction p μ s f =ᵐ[μ.restrict s] f :=
  lpRestrictToSet_ae p μ s f

theorem lpRestriction_norm_le : ‖lpRestriction p μ s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

variable (hs : MeasurableSet s)

def lpCellProjection : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  (lpExtendByZeroIsometry p μ s hs).toContinuousLinearMap.comp (lpRestriction p μ s)

theorem lpCellProjection_ae (f : Lp ℂ p μ) : lpCellProjection p μ s hs f =ᵐ[μ] s.indicator f := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (lpRestriction_ae p μ s f)
  exact (lpExtendByZero_ae p μ s hs (lpRestriction p μ s f)).trans he

theorem lpCellProjection_norm_le (f : Lp ℂ p μ) : ‖lpCellProjection p μ s hs f‖ ≤ ‖f‖ := by
  change ‖lpExtendByZeroIsometry p μ s hs (lpRestriction p μ s f)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact lpRestrictToSet_norm_le p μ s f

theorem lpCellProjection_norm_eq (f : Lp ℂ p μ) :
    ‖lpCellProjection p μ s hs f‖ = ‖lpRestriction p μ s f‖ :=
  (lpExtendByZeroIsometry p μ s hs).norm_map _

theorem lpRestriction_norm_rpow (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (f : Lp ℂ p μ) :
    ‖lpRestriction p μ s f‖ ^ p.toReal = ∫ x, ‖f x‖ ^ p.toReal ∂μ.restrict s := by
  rw [← integral_norm_rpow (lpRestriction p μ s f) hp0 hpfin]
  apply integral_congr_ae
  filter_upwards [lpRestriction_ae p μ s f] with x hx
  rw [hx]

theorem lpCellProjection_supported (f : Lp ℂ p μ) : SupportedOn (lpCellProjection p μ s hs f) s :=
  lpExtendByZero_supported p μ s hs (lpRestriction p μ s f)

theorem lpCellProjection_eq_of_supported (f : Lp ℂ p μ) (hf : SupportedOn f s) :
    lpCellProjection p μ s hs f = f := by
  apply Lp.ext
  filter_upwards [lpCellProjection_ae p μ s hs f, hf] with x hx hfx
  rw [hx]
  by_cases hxs : x ∈ s
  · exact Set.indicator_of_mem hxs _
  · rw [Set.indicator_of_notMem hxs, hfx hxs]

theorem lpRestriction_extendByZero (f : Lp ℂ p (μ.restrict s)) :
    lpRestriction p μ s (lpExtendByZero p μ s hs f) = f := by
  apply Lp.ext
  have hExt := ae_restrict_of_ae (s := s) (lpExtendByZero_ae p μ s hs f)
  filter_upwards [lpRestriction_ae p μ s (lpExtendByZero p μ s hs f), hExt,
    ae_restrict_mem hs] with x hR hE hxs
  rw [hR, hE]
  exact Set.indicator_of_mem hxs _

end SchauderTranslates.LpConstruction
