import Lean_Code.PositiveTranslates.StageMachine

/-!
# Non-negative compact step functions are dense in the non-negative part of `Lᵖ`

`exists_nonneg_compactStep_near`: for a non-negative `g ∈ Lᵖ(ℝ)` (`p < ∞`) and `ε > 0`
there is a non-negative compactly supported step function `v` with `‖v - g‖ ≤ ε`.

Proof: approximate the real part of `g` by a continuous compactly supported function `w`
(Mathlib), replace `w` by its positive part (this does not increase the distance to a
non-negative function), and sample the positive part at the left endpoints of a fine
uniform partition.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞}

/-! ### Left-endpoint sampling on a uniform partition -/

/-- The left-endpoint sample of `u` on the first `m` cells of the partition with first point
`c` and mesh `δ`, as a function. -/
def sampleValue (u : ℝ → ℝ) (c δ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m,
    u (c + k * δ) * (Ico (c + k * δ) (c + (k + 1) * δ)).indicator (fun _ => (1 : ℝ)) x

/-- The left-endpoint sample as a compact step function in `Lᵖ`. -/
def sampleLp (p : ℝ≥0∞) (u : ℝ → ℝ) (c δ : ℝ) (m : ℕ) : LebesgueLp p :=
  ∑ k ∈ Finset.range m, u (c + k * δ) • intervalAtom p (c + k * δ, c + (k + 1) * δ)

theorem sampleLp_isCompactStep (u : ℝ → ℝ) (c δ : ℝ) (m : ℕ) :
    IsCompactStep p (sampleLp p u c δ m) :=
  IsCompactStep.finset_sum _ _ fun _ _ => (intervalAtom_isCompactStep p _).smul _

theorem sampleLp_ae (u : ℝ → ℝ) (c δ : ℝ) (m : ℕ) :
    (sampleLp p u c δ m : ℝ → ℂ) =ᵐ[volume] fun x => (sampleValue u c δ m x : ℂ) := by
  classical
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k ∈ Finset.range m,
      (u (c + k * δ) • intervalAtom p (c + k * δ, c + (k + 1) * δ) : LebesgueLp p) x =
        ((u (c + k * δ) *
          (Ico (c + k * δ) (c + (k + 1) * δ)).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
    simp only [Filter.eventually_all_finset]
    intro k _
    filter_upwards [intervalAtom_ae p (c + k * δ, c + (k + 1) * δ),
      Lp.coeFn_smul (u (c + k * δ)) (intervalAtom p (c + k * δ, c + (k + 1) * δ))] with x hi hs
    rw [hs, Pi.smul_apply, hi, Complex.real_smul]
    by_cases hx : x ∈ Ico (c + k * δ) (c + (k + 1) * δ) <;> simp [hx]
  filter_upwards [hall, Lp.coeFn_fun_finsetSum (Finset.range m)
    (fun k : ℕ => (u (c + k * δ) • intervalAtom p (c + k * δ, c + (k + 1) * δ) : LebesgueLp p))]
    with x hall hx
  rw [sampleLp, hx, sampleValue, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun k hk => hall k hk

theorem sampleValue_nonneg {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (c δ : ℝ) (m : ℕ) (x : ℝ) :
    0 ≤ sampleValue u c δ m x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hu _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- If `u` oscillates by at most `η` between a point of a cell and its left endpoint, the
sample is within `η` of `u` on the union of the cells, and vanishes outside. -/
theorem abs_sampleValue_sub_le {u : ℝ → ℝ} {c δ η : ℝ} (hδ : 0 ≤ δ) (m : ℕ)
    (hosc : ∀ k < m, ∀ x ∈ Ico (c + k * δ) (c + (k + 1) * δ), |u (c + k * δ) - u x| ≤ η)
    (x : ℝ) :
    |sampleValue u c δ m x - (Ico c (c + m * δ)).indicator u x| ≤
      (Ico c (c + m * δ)).indicator (fun _ => η) x := by
  induction m with
  | zero => simp [sampleValue]
  | succ m ih =>
    have ih' := ih fun k hk => hosc k (Nat.lt_succ_of_lt hk)
    have hsucc : sampleValue u c δ (m + 1) x = sampleValue u c δ m x +
        u (c + m * δ) * (Ico (c + m * δ) (c + (m + 1) * δ)).indicator (fun _ => (1 : ℝ)) x := by
      simp [sampleValue, Finset.sum_range_succ]
    have hmδ : 0 ≤ (m : ℝ) * δ := mul_nonneg (Nat.cast_nonneg m) hδ
    rw [hsucc]
    push_cast
    by_cases hx : x ∈ Ico (c + m * δ) (c + (m + 1) * δ)
    · have hxJ : x ∉ Ico c (c + m * δ) := fun h => absurd h.2 (not_lt.mpr hx.1)
      have hxJ' : x ∈ Ico c (c + (m + 1) * δ) := ⟨by linarith [hx.1], hx.2⟩
      rw [Set.indicator_of_notMem hxJ, Set.indicator_of_notMem hxJ, sub_zero] at ih'
      have h0 : sampleValue u c δ m x = 0 := abs_eq_zero.mp (le_antisymm ih' (abs_nonneg _))
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxJ', Set.indicator_of_mem hxJ', h0,
        zero_add, mul_one]
      exact hosc m (Nat.lt_succ_self m) x hx
    · have hiff : x ∈ Ico c (c + (m + 1) * δ) ↔ x ∈ Ico c (c + m * δ) := by
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          by_contra hlt
          exact hx ⟨not_lt.mp hlt, h.2⟩
        · intro h
          exact ⟨h.1, by nlinarith [h.2]⟩
      rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      by_cases hxJ : x ∈ Ico c (c + m * δ)
      · rw [Set.indicator_of_mem (hiff.mpr hxJ), Set.indicator_of_mem (hiff.mpr hxJ)]
        rw [Set.indicator_of_mem hxJ, Set.indicator_of_mem hxJ] at ih'
        exact ih'
      · rw [Set.indicator_of_notMem (mt hiff.mp hxJ), Set.indicator_of_notMem (mt hiff.mp hxJ)]
        rw [Set.indicator_of_notMem hxJ, Set.indicator_of_notMem hxJ] at ih'
        exact ih'

/-! ### Continuous compactly supported non-negative functions -/

variable [Fact (1 ≤ p)]

theorem exists_nonneg_step_near_continuous (hp : p ≠ ∞) {u : ℝ → ℝ} (hu : Continuous u)
    (hc : HasCompactSupport u) (hu0 : ∀ x, 0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : LebesgueLp p, IsCompactStep p v ∧ IsNonneg v ∧
      eLpNorm (fun x => v x - (u x : ℂ)) p volume ≤ ENNReal.ofReal ε := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- a bounded interval containing the support
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R : ℕ := ⌈r⌉₊ + 1 with hRdef
  have hRr : r < (R : ℝ) := by
    have := Nat.le_ceil r
    rw [hRdef]
    push_cast
    linarith
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hRdef]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈r⌉₊]
  have hzero : ∀ x : ℝ, x ∉ Ico (-(R : ℝ)) R → u x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have hxr := hr hxs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxr
    exact hx ⟨by linarith [(abs_le.mp hxr).1], by linarith [(abs_le.mp hxr).2]⟩
  -- the oscillation budget
  set W : ℝ := (2 * (R : ℝ)) ^ (1 / p.toReal) with hW
  have hW0 : 0 < W := by positivity
  set η : ℝ := ε / W with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ', hδ', huc⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hu) η hη0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ'
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ0 : 0 < δ := by positivity
  set m : ℕ := 2 * R * (n + 1) with hm
  have hmδ : (-(R : ℝ)) + (m : ℝ) * δ = R := by
    rw [hm, hδdef]
    push_cast
    field_simp
    ring
  have hosc : ∀ k < m, ∀ x ∈ Ico (-(R : ℝ) + k * δ) (-(R : ℝ) + (k + 1) * δ),
      |u (-(R : ℝ) + k * δ) - u x| ≤ η := by
    intro k _ x hx
    have hd : dist (-(R : ℝ) + k * δ) x < δ' := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
      have : x - (-(R : ℝ) + k * δ) < δ := by nlinarith [hx.2]
      linarith
    have := huc hd
    rw [Real.dist_eq] at this
    exact this.le
  have hpt : ∀ x, |sampleValue u (-(R : ℝ)) δ m x - u x| ≤
      (Ico (-(R : ℝ)) R).indicator (fun _ => η) x := by
    intro x
    have h := abs_sampleValue_sub_le hδ0.le m hosc x
    rw [hmδ] at h
    by_cases hx : x ∈ Ico (-(R : ℝ)) R
    · rwa [Set.indicator_of_mem hx] at h
    · rwa [Set.indicator_of_notMem hx, ← hzero x hx] at h
  refine ⟨sampleLp p u (-(R : ℝ)) δ m, sampleLp_isCompactStep _ _ _ _, ?_, ?_⟩
  · filter_upwards [sampleLp_ae (p := p) u (-(R : ℝ)) δ m] with x hx
    rw [hx]
    exact Complex.zero_le_real.mpr (sampleValue_nonneg hu0 _ _ _ _)
  · have hae : ∀ᵐ x ∂(volume : Measure ℝ),
        ‖sampleLp p u (-(R : ℝ)) δ m x - (u x : ℂ)‖ ≤
          (Ico (-(R : ℝ)) R).indicator (fun _ => η) x := by
      filter_upwards [sampleLp_ae (p := p) u (-(R : ℝ)) δ m] with x hx
      rw [hx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hpt x
    refine (eLpNorm_mono_ae_real hae).trans ?_
    rw [eLpNorm_indicator_const measurableSet_Ico hp0 hp, Real.volume_Ico,
      Real.enorm_eq_ofReal hη0.le, ENNReal.ofReal_rpow_of_nonneg (by linarith) (by positivity),
      ← ENNReal.ofReal_mul hη0.le]
    apply ENNReal.ofReal_le_ofReal
    have : (R : ℝ) - -(R : ℝ) = 2 * R := by ring
    rw [this, ← hW, hη, div_mul_cancel₀ _ hW0.ne']

/-! ### The density statement -/

/-- **Density of non-negative compact step functions.** -/
theorem exists_nonneg_compactStep_near (hp : p ≠ ∞) (g : LebesgueLp p) (hg : IsNonneg g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : LebesgueLp p, IsCompactStep p v ∧ IsNonneg v ∧ ‖v - g‖ ≤ ε := by
  set f : ℝ → ℝ := fun x => (g x).re with hf
  have hfmem : MemLp f p volume := (Lp.memLp g).re
  have hgf : ∀ᵐ x ∂(volume : Measure ℝ), g x = (f x : ℂ) ∧ 0 ≤ f x := by
    filter_upwards [hg] with x hx
    have h := Complex.nonneg_iff.mp hx
    exact ⟨Complex.ext (by simp [hf]) (by simpa using h.2.symm), h.1⟩
  obtain ⟨w, hwc, hwε, hwcont, -⟩ := hfmem.exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε)
  set u : ℝ → ℝ := fun x => max (w x) 0 with hu
  have hucont : Continuous u := hwcont.max continuous_const
  have huc : HasCompactSupport u := hwc.comp_left (g := fun y : ℝ => max y 0) (by simp)
  obtain ⟨v, hv1, hv2, hv3⟩ := exists_nonneg_step_near_continuous (p := p) hp hucont huc
    (fun x => le_max_right _ _) (half_pos hε)
  refine ⟨v, hv1, hv2, ?_⟩
  rw [Lp.norm_def]
  apply ENNReal.toReal_le_of_le_ofReal hε.le
  have h2 : eLpNorm (fun x => (u x : ℂ) - g x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    refine le_trans (eLpNorm_mono_ae ?_) hwε
    filter_upwards [hgf] with x hx
    rw [hx.1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Pi.sub_apply,
      Real.norm_eq_abs]
    simp only [hu]
    rcases le_total 0 (w x) with hw | hw
    · rw [max_eq_left hw, abs_sub_comm]
    · rw [max_eq_right hw, zero_sub, abs_neg, abs_of_nonneg hx.2]
      exact (le_abs_self _).trans' (by linarith)
  calc
    eLpNorm (⇑(v - g)) p volume = eLpNorm (fun x => v x - g x) p volume :=
      eLpNorm_congr_ae (Lp.coeFn_sub v g)
    _ = eLpNorm ((fun x => v x - (u x : ℂ)) + fun x => (u x : ℂ) - g x) p volume := by
      congr 1
      funext x
      simp
    _ ≤ eLpNorm (fun x => v x - (u x : ℂ)) p volume +
          eLpNorm (fun x => (u x : ℂ) - g x) p volume :=
      eLpNorm_add_le
        ((Lp.aestronglyMeasurable v).sub
          (Complex.continuous_ofReal.comp hucont).aestronglyMeasurable)
        ((Complex.continuous_ofReal.comp hucont).aestronglyMeasurable.sub
          (Lp.aestronglyMeasurable g)) Fact.out
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hv3 h2
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

end StructuredBases.PositiveTranslates
