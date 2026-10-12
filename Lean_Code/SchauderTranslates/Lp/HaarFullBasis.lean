import Lean_Code.SchauderTranslates.Lp.HaarFullConvergence
import Lean_Code.SchauderTranslates.Lp.RootCoefficients

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

instance haarIndex_infinite : Infinite HaarIndex :=
  Infinite.of_injective (fun n : ℕ => (some ⟨n, ⟨0, by positivity⟩⟩ : HaarIndex))
    (fun _ _ h => congrArg Sigma.fst (Option.some.inj h))

def haarOrdering : ℕ ≃ HaarIndex := Classical.choice inferInstance

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

include q in
theorem haar_normalized_ordered_basis (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (e : ℕ ≃ HaarIndex) :
    Construction.OrderedSchauderBasis (fun n => haarNormalizedAtom p (e n)) := by
  classical
  refine schauder_of_continuous_coordinates (fun n => haarNormalizedAtom p (e n))
    (fun n => haarNormalizedCoordinate p q (e n)) ?_ ?_
  · intro n m
    simpa only [e.injective.eq_iff] using haarNormalizedCoordinate_atom p q (e n) (e m)
  · intro f
    have ht := (haar_normalized_finset_tendsto p q hp2 hpfin f).comp
      ((tendsto_finset_image_atTop_atTop e.apply_symm_apply).comp tendsto_finset_range)
    have he : (fun n : ℕ => ∑ j ∈ Finset.range n,
        haarNormalizedCoordinate p q (e j) f • haarNormalizedAtom p (e j)) =
        (fun n : ℕ => ∑ i ∈ (Finset.range n).image e,
          haarNormalizedCoordinate p q i f • haarNormalizedAtom p i) := by
      funext n
      symm
      apply Finset.sum_image
      exact e.injective.injOn
    rw [he]
    exact ht

theorem haar_normalized_finite_synthesis_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (t : Finset HaarIndex) (c w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) :
    ‖∑ i ∈ t, (w i * c i) • haarNormalizedAtom p i‖ ≤
      haarStrongConstant q.toReal * ‖∑ i ∈ t, c i • haarNormalizedAtom p i‖ := by
  classical
  have hc (i : HaarIndex) (hi : i ∈ t) :
      haarNormalizedCoordinate p q i (∑ j ∈ t, c j • haarNormalizedAtom p j) = c i := by
    simp [map_sum, map_smul, haarNormalizedCoordinate_atom, smul_eq_mul, hi]
  have hb := haar_normalized_finite_bound p q hp2 hpfin t w hw
    (∑ i ∈ t, c i • haarNormalizedAtom p i)
  have he : (∑ i ∈ t, (w i * haarNormalizedCoordinate p q i
        (∑ j ∈ t, c j • haarNormalizedAtom p j)) • haarNormalizedAtom p i) =
      ∑ i ∈ t, (w i * c i) • haarNormalizedAtom p i :=
    Finset.sum_congr rfl (fun i hi => by rw [hc i hi])
  rwa [he] at hb

theorem haar_normalized_finite_multiplier_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (e : ℕ ≃ HaarIndex) :
    FiniteMultiplierBound (fun n => haarNormalizedAtom p (e n)) (haarStrongConstant q.toReal) := by
  classical
  intro n c a ha
  have hb := haar_normalized_finite_synthesis_bound p q hp2 hpfin ((Finset.range n).image e)
    (fun i => c (e.symm i)) (fun i => a (e.symm i)) (fun i _ => ha _)
  simpa only [Finset.sum_image e.injective.injOn, e.symm_apply_apply] using hb

/-- The full normalized Haar system has an ordered basis for every
enumeration, a bound for all finite coordinate multipliers, and convergence
over arbitrary finite subsets. -/
theorem haar_full_basis (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    (∀ i, ‖haarNormalizedAtom p i‖ = 1) ∧
    (∀ e : ℕ ≃ HaarIndex,
      Construction.OrderedSchauderBasis (fun n => haarNormalizedAtom p (e n)) ∧
      FiniteMultiplierBound (fun n => haarNormalizedAtom p (e n)) (haarStrongConstant q.toReal)) ∧
    (∀ f : HaarLp p, Tendsto (fun t : Finset HaarIndex =>
      ∑ i ∈ t, haarNormalizedCoordinate p q i f • haarNormalizedAtom p i) atTop (𝓝 f)) :=
  ⟨haarNormalizedAtom_norm p, fun e => ⟨haar_normalized_ordered_basis p q hp2 hpfin e,
      haar_normalized_finite_multiplier_bound p q hp2 hpfin e⟩,
    haar_normalized_finset_tendsto p q hp2 hpfin⟩

end SchauderTranslates.LpConstruction
