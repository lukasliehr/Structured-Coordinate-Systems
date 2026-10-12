import Lean_Code.SchauderTranslates.Lp.HaarCoordinates
import Lean_Code.SchauderTranslates.Lp.IndexedCoordinateConvergence

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haarAtom_eq_norm_smul_normalized (i : HaarIndex) :
    haarAtom p i = (‖haarAtom p i‖ : ℂ) • haarNormalizedAtom p i := by
  have hn : (‖haarAtom p i‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (haarAtom_ne_zero p i))
  rw [haarNormalizedAtom, smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem haar_normalized_span_eq :
    Submodule.span ℂ (Set.range (haarNormalizedAtom p)) = haarAtomSpan p := by
  apply Submodule.span_eq_span
  · rintro _ ⟨i, rfl⟩
    exact (haarAtomSpan p).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [haarAtom_eq_norm_smul_normalized p i]
    exact (Submodule.span ℂ (Set.range (haarNormalizedAtom p))).smul_mem _
      (Submodule.subset_span ⟨i, rfl⟩)

theorem haar_normalized_finite_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (t : Finset HaarIndex) (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) (f : HaarLp p) :
    ‖∑ i ∈ t, (w i * haarNormalizedCoordinate p q i f) • haarNormalizedAtom p i‖ ≤
      haarStrongConstant q.toReal * ‖f‖ := by
  have he : ∑ i ∈ t, (w i * haarNormalizedCoordinate p q i f) • haarNormalizedAtom p i =
      haarNormalizedMultiplier p q t w f := by
    simp [haarNormalizedMultiplier, smul_smul]
  rw [he, haarNormalizedMultiplier_eq]
  exact haar_dual_multiplier_bound hp2 hpfin t w hw f

theorem haar_normalized_finset_tendsto (hp2 : 2 < p) (hpfin : p ≠ ∞) (f : HaarLp p) :
    Tendsto (fun t : Finset HaarIndex =>
      ∑ i ∈ t, haarNormalizedCoordinate p q i f • haarNormalizedAtom p i) atTop (𝓝 f) := by
  classical
  refine indexed_coordinate_finset_tendsto (haarNormalizedAtom p) (haarNormalizedCoordinate p q)
    (haarNormalizedCoordinate_atom p q) (K := haarStrongConstant q.toReal) ?_ ?_ ?_ f
  · rw [haar_normalized_span_eq]
    exact haar_dense_span hpfin
  · exact zero_le_one.trans (haarStrongConstant_ge_one hp2 hpfin)
  · intro t x
    simpa only [one_mul] using haar_normalized_finite_bound p q hp2 hpfin t (fun _ => 1)
      (by simp) x

end SchauderTranslates.LpConstruction
