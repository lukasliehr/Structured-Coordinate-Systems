import Lean_Code.SchauderTranslates.TagLift
import Lean_Code.SchauderTranslates.LineTransferBasics

/-!
# The normalized slow law and the residual (setup of `extend:product`)

The old weight is normalized to a probability on the whole line. Raw squared norms of
bounded representatives are its squared L² norms times the total mass `∫ w`. The old
prefix bound passes to the normalized law, and the residual of the target is an explicit
finite character sum orthogonal to all old characters, whose squared norm times `∫ w`
is exactly `distanceSq`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

theorem weight_integral_pos (w : Weight) : 0 < ∫ s, w.density s := by
  have hnn : 0 ≤ᵐ[volume] w.density := w.positive.mono (fun _ h => h.le)
  rw [integral_pos_iff_support_of_nonneg_ae hnn w.integrable]
  have hs : Function.support w.density =ᵐ[volume] (Set.univ : Set ℝ) := by
    filter_upwards [w.positive] with t ht
    change (t ∈ Function.support w.density) = (t ∈ Set.univ)
    simp [Function.mem_support, ht.ne']
  rw [measure_congr hs]
  simp

/-- The normalized slow weight `w / ∫ w`. -/
def normalizedWeight (w : Weight) : Weight where
  density t := w.density t / ∫ s, w.density s
  measurable := w.measurable.div_const _
  integrable := w.integrable.div_const _
  positive := by
    filter_upwards [w.positive] with t ht
    exact div_pos ht (weight_integral_pos w)

/-- The normalized slow law. -/
abbrev lineLaw (w : Weight) : Measure ℝ := (normalizedWeight w).measure

theorem lineLaw_integral (w : Weight) (f : ℝ → ℂ) :
    (∫ t, f t ∂lineLaw w) = ((∫ s, w.density s : ℝ) : ℂ)⁻¹ * ∫ t, (w.density t : ℂ) * f t := by
  rw [LineTransfer.integral_weight_measure, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [normalizedWeight]
  push_cast
  ring

instance lineLaw_probability (w : Weight) : IsProbabilityMeasure (lineLaw w) := by
  constructor
  have hZ := weight_integral_pos w
  have hnn : 0 ≤ᵐ[volume] (normalizedWeight w).density :=
    (normalizedWeight w).positive.mono (fun _ h => h.le)
  simp only [lineLaw, Weight.measure]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (normalizedWeight w).integrable hnn]
  have h1 : (∫ t, (normalizedWeight w).density t) = 1 := by
    simp only [normalizedWeight]
    rw [integral_div, div_self hZ.ne']
  rw [h1, ENNReal.ofReal_one]

/-- Raw squared norms are squared normalized norms times the total mass. -/
theorem normSq_eq_mass_mul (w : Weight) (g : BoundedMeasurableComplex ℝ) :
    normSq w g = (∫ s, w.density s) * ‖g.toL2 (lineLaw w)‖ ^ 2 := by
  have hZ := weight_integral_pos w
  have hi := BoundedMeasurableComplex.inner_toL2 (lineLaw w) g g
  rw [lineLaw_integral] at hi
  have hn : (inner ℂ (g.toL2 (lineLaw w)) (g.toL2 (lineLaw w))).re =
      ‖g.toL2 (lineLaw w)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hi] at hn
  have hreal : (∫ t, (w.density t : ℂ) * (star (g t) * g t)) =
      ((∫ t, ‖g t‖ ^ 2 * w.density t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  rw [hreal, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re] at hn
  rw [normSq, ← hn]
  field_simp

/-- The bounded representative of a finite character sum. -/
def lineSum {ι : Type*} [Fintype ι] (lam : ι → ℝ) (c : ι → ℂ) : BoundedMeasurableComplex ℝ :=
  BoundedMeasurableComplex.linearCombination (fun i => lineCharacter (lam i)) c

theorem lineSum_apply {ι : Type*} [Fintype ι] (lam : ι → ℝ) (c : ι → ℂ) (t : ℝ) :
    lineSum lam c t = ∑ i, c i * character (lam i) t := rfl

theorem lineSum_toL2 {ι : Type*} [Fintype ι] (lam : ι → ℝ) (c : ι → ℂ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] :
    (lineSum lam c).toL2 μ = ∑ i, c i • (lineCharacter (lam i)).toL2 μ :=
  BoundedMeasurableComplex.toL2_linearCombination _ _ _

theorem normSq_synthesis_eq (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) :
    normSq w (synthesis μ c) =
      (∫ s, w.density s) * ‖∑ i, c i • (lineCharacter (μ i)).toL2 (lineLaw w)‖ ^ 2 := by
  rw [← lineSum_toL2, ← normSq_eq_mass_mul]
  rfl

/-- The old prefix bound in the normalized law. -/
theorem prefixBound_lineLaw (w : Weight) {d : ℕ} (μ : Fin d → ℝ) {K : ℝ}
    (h : PrefixBound w μ K) :
    FinitePrefixSqBound (fun i => (lineCharacter (μ i)).toL2 (lineLaw w)) (K ^ 2) := by
  intro k c
  have hZ := weight_integral_pos w
  have hk := h k c
  have hcut : (fun t => ∑ i : Fin d, if i.val < k then c i * character (μ i) t else 0) =
      synthesis μ (fun i => if i.val < k then c i else 0) := by
    funext t
    simp only [synthesis]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hcut, normSq_synthesis_eq, normSq_synthesis_eq] at hk
  have hsum : (∑ i, if i.val < k then c i • (lineCharacter (μ i)).toL2 (lineLaw w) else 0) =
      ∑ i, (if i.val < k then c i else 0) • (lineCharacter (μ i)).toL2 (lineLaw w) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hsum]
  nlinarith

/-- The target residual: an explicit character sum orthogonal to all old characters, with
squared norm `distanceSq / ∫ w`, differing from the target by an old combination. -/
theorem residual_exists (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ) :
    ∃ c : Fin (d + 1) → ℂ, c 0 = 1 ∧
      (∀ i, inner ℂ ((lineCharacter (μ i)).toL2 (lineLaw w))
        ((lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w)) = 0) ∧
      (lineCharacter ξ).toL2 (lineLaw w) - (lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) ∈
        Submodule.span ℂ (Set.range fun i => (lineCharacter (μ i)).toL2 (lineLaw w)) ∧
      (∫ s, w.density s) * ‖(lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w)‖ ^ 2 =
        distanceSq w μ ξ := by
  classical
  set ρ := lineLaw w
  set e : Fin d → Lp ℂ 2 ρ := fun i => (lineCharacter (μ i)).toL2 ρ with he
  set V := Submodule.span ℂ (Set.range e)
  have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set f := (lineCharacter ξ).toL2 ρ
  have hp : V.starProjection f ∈ V := by
    rw [Submodule.starProjection_apply]
    exact (V.orthogonalProjectionOnto f).2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hp
  set c : Fin (d + 1) → ℂ := Fin.cons 1 (fun i => -a i) with hc
  have hr : (lineSum (Fin.cons ξ μ) c).toL2 ρ = f - V.starProjection f := by
    rw [lineSum_toL2, Fin.sum_univ_succ, ← ha]
    simp only [hc, Fin.cons_zero, Fin.cons_succ, one_smul, neg_smul, Finset.sum_neg_distrib, he]
    abel
  have horth : f - V.starProjection f ∈ Vᗮ := by
    intro y hy
    rw [inner_sub_right, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hy, sub_self]
  refine ⟨c, by simp [hc], ?_, ?_, ?_⟩
  · intro i
    rw [hr]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i))
      horth
  · rw [hr, sub_sub_cancel]
    exact hp
  · have hZ := weight_integral_pos w
    have hval (b : Fin d → ℂ) : normSq w (fun t => character ξ t - synthesis μ b t) =
        (∫ s, w.density s) * ‖f - ∑ i, b i • e i‖ ^ 2 := by
      have h1 := normSq_eq_mass_mul w ((lineCharacter ξ).sub (lineSum μ b))
      rw [BoundedMeasurableComplex.toL2_sub, lineSum_toL2] at h1
      exact h1
    have hpy (b : Fin d → ℂ) : ‖f - V.starProjection f‖ ^ 2 ≤ ‖f - ∑ i, b i • e i‖ ^ 2 := by
      have hmem : V.starProjection f - ∑ i, b i • e i ∈ V :=
        V.sub_mem hp (V.sum_mem fun i _ => V.smul_mem _
          (Submodule.subset_span (Set.mem_range_self i)))
      have hsplit : f - ∑ i, b i • e i =
          (f - V.starProjection f) + (V.starProjection f - ∑ i, b i • e i) := by abel
      have h0 : inner ℂ (f - V.starProjection f) (V.starProjection f - ∑ i, b i • e i) = 0 :=
        Submodule.inner_left_of_mem_orthogonal hmem horth
      rw [hsplit, @norm_add_sq ℂ, h0]
      simp only [map_zero, mul_zero, add_zero]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hleast : IsLeast (Set.range fun b : Fin d → ℂ =>
        normSq w (fun t => character ξ t - synthesis μ b t))
        ((∫ s, w.density s) * ‖f - V.starProjection f‖ ^ 2) := by
      refine ⟨⟨a, ?_⟩, ?_⟩
      · dsimp only
        rw [hval, ha]
      · rintro y ⟨b, rfl⟩
        dsimp only
        rw [hval]
        exact mul_le_mul_of_nonneg_left (hpy b) hZ.le
    rw [hr, distanceSq, hleast.csInf_eq]

end SchauderTranslates
