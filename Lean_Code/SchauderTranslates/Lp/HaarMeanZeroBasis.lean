import Lean_Code.SchauderTranslates.Lp.HaarMeanZeroConvergence

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haar_meanZero_ordered_basis (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (e : ℕ ≃ HaarMeanZeroIndex) :
    Construction.OrderedSchauderBasis (fun n => haarMeanZeroAtom p q (e n)) := by
  classical
  refine schauder_of_continuous_coordinates (fun n => haarMeanZeroAtom p q (e n))
    (fun n => haarMeanZeroCoordinate p q (e n)) ?_ ?_
  · intro n m
    simpa only [e.injective.eq_iff] using haarMeanZeroCoordinate_atom p q (e n) (e m)
  · intro f
    have ht := (haar_meanZero_finset_tendsto p q hp2 hpfin f).comp
      ((tendsto_finset_image_atTop_atTop e.apply_symm_apply).comp tendsto_finset_range)
    have he : (fun n : ℕ => ∑ j ∈ Finset.range n,
        haarMeanZeroCoordinate p q (e j) f • haarMeanZeroAtom p q (e j)) =
        (fun n : ℕ => ∑ i ∈ (Finset.range n).image e,
          haarMeanZeroCoordinate p q i f • haarMeanZeroAtom p q i) := by
      funext n
      symm
      apply Finset.sum_image
      exact e.injective.injOn
    rw [he]
    exact ht

theorem haar_meanZero_finite_synthesis_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (t : Finset HaarMeanZeroIndex) (c w : HaarMeanZeroIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) :
    ‖∑ i ∈ t, (w i * c i) • haarMeanZeroAtom p q i‖ ≤
      haarStrongConstant q.toReal * ‖∑ i ∈ t, c i • haarMeanZeroAtom p q i‖ := by
  classical
  have hc (i : HaarMeanZeroIndex) (hi : i ∈ t) :
      haarMeanZeroCoordinate p q i (∑ j ∈ t, c j • haarMeanZeroAtom p q j) = c i := by
    simp [map_sum, map_smul, haarMeanZeroCoordinate_atom, smul_eq_mul, hi]
  have hb := haar_meanZero_finite_bound p q hp2 hpfin t w hw
    (∑ i ∈ t, c i • haarMeanZeroAtom p q i)
  have he : (∑ i ∈ t, (w i * haarMeanZeroCoordinate p q i
        (∑ j ∈ t, c j • haarMeanZeroAtom p q j)) • haarMeanZeroAtom p q i) =
      ∑ i ∈ t, (w i * c i) • haarMeanZeroAtom p q i :=
    Finset.sum_congr rfl (fun i hi => by rw [hc i hi])
  rwa [he] at hb

theorem haar_meanZero_finite_multiplier_bound (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (e : ℕ ≃ HaarMeanZeroIndex) :
    FiniteMultiplierBound (fun n => haarMeanZeroAtom p q (e n)) (haarStrongConstant q.toReal) := by
  classical
  intro n c a ha
  have hb := haar_meanZero_finite_synthesis_bound p q hp2 hpfin ((Finset.range n).image e)
    (fun i => c (e.symm i)) (fun i => a (e.symm i)) (fun i _ => ha _)
  simpa only [Finset.sum_image e.injective.injOn, e.symm_apply_apply] using hb

/-- The normalized system with the constant removed is an unconditional
ordered basis of the actual kernel of the continuous integral. -/
theorem haar_meanZero_basis (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    (∀ i, ‖haarMeanZeroAtom p q i‖ = 1) ∧
    (∀ e : ℕ ≃ HaarMeanZeroIndex,
      Construction.OrderedSchauderBasis (fun n => haarMeanZeroAtom p q (e n)) ∧
      FiniteMultiplierBound (fun n => haarMeanZeroAtom p q (e n)) (haarStrongConstant q.toReal)) ∧
    (∀ f : haarMeanZero p q, Tendsto (fun t : Finset HaarMeanZeroIndex =>
      ∑ i ∈ t, haarMeanZeroCoordinate p q i f • haarMeanZeroAtom p q i) atTop (𝓝 f)) :=
  ⟨haarMeanZeroAtom_norm p q, fun e => ⟨haar_meanZero_ordered_basis p q hp2 hpfin e,
      haar_meanZero_finite_multiplier_bound p q hp2 hpfin e⟩,
    haar_meanZero_finset_tendsto p q hp2 hpfin⟩

end SchauderTranslates.LpConstruction
