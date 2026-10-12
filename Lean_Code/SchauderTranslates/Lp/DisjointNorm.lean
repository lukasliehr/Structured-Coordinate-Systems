import Lean_Code.SchauderTranslates.Lp.Contracts

noncomputable section
open MeasureTheory
open scoped ENNReal Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {p : ℝ≥0∞}

theorem integral_norm_rpow (f : Lp E p μ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    (∫ x, ‖f x‖ ^ p.toReal ∂μ) = ‖f‖ ^ p.toReal := by
  have hnorm : ‖f‖ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
    rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable f)]
    exact lpNorm_eq_integral_norm_rpow_toReal hp0 hpfin (Lp.aestronglyMeasurable f)
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hnorm, Real.rpow_inv_rpow hnonneg (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩)]

theorem integrable_norm_rpow (f : Lp E p μ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    Integrable (fun x => ‖f x‖ ^ p.toReal) μ :=
  (memLp_one_iff_integrable).mp ((Lp.memLp f).norm_rpow hp0 hpfin)

/-- Exact pth-power norm additivity for a.e. disjoint vectors. This is the
norm identity used in every packet and every private-coordinate block. -/
theorem norm_add_rpow_of_ae_disjoint [Fact (1 ≤ p)]
    (f g : Lp E p μ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hdis : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    ‖f + g‖ ^ p.toReal = ‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal := by
  have hpR : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩
  rw [← integral_norm_rpow (f + g) hp0 hpfin,
    ← integral_norm_rpow f hp0 hpfin, ← integral_norm_rpow g hp0 hpfin,
    ← integral_add (integrable_norm_rpow f hp0 hpfin) (integrable_norm_rpow g hp0 hpfin)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g, hdis] with x ha hd
  rw [ha]
  rcases hd with hf | hg
  · simp [hf, hpR]
  · simp [hg, hpR]

def SupportedOn (f : Lp E p μ) (s : Set α) : Prop :=
  ∀ᵐ x ∂μ, x ∉ s → f x = 0

theorem SupportedOn.mono {f : Lp E p μ} {s t : Set α}
    (hf : SupportedOn f s) (hst : s ⊆ t) : SupportedOn f t :=
  Filter.Eventually.mono hf (fun _ hx hnot => hx (fun hin => hnot (hst hin)))

theorem SupportedOn.add {f g : Lp E p μ} {s : Set α}
    (hf : SupportedOn f s) (hg : SupportedOn g s) : SupportedOn (f + g) s := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx ha
  intro hout
  rw [ha]
  change f x + g x = 0
  rw [hfx hout, hgx hout, add_zero]

theorem SupportedOn.real_smul [NormedSpace ℝ E] {f : Lp E p μ} {s : Set α}
    (hf : SupportedOn f s) (a : ℝ) : SupportedOn (a • f) s := by
  filter_upwards [hf, Lp.coeFn_smul a f] with x hfx ha
  intro hout
  rw [ha]
  change a • f x = 0
  rw [hfx hout, smul_zero]

theorem SupportedOn.finset_sum {ι : Type*} (s : Finset ι) (f : ι → Lp E p μ)
    {A : Set α} (hf : ∀ i ∈ s, SupportedOn (f i) A) : SupportedOn (∑ i ∈ s, f i) A := by
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, x ∉ A → f i x = 0 := by
    simpa only [Filter.eventually_all_finset, SupportedOn] using hf
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s f] with x hx hsum
  intro hout
  rw [hsum]
  exact Finset.sum_eq_zero (fun i hi => hx i hi hout)

theorem SupportedOn.ae_disjoint {f g : Lp E p μ} {s t : Set α}
    (hf : SupportedOn f s) (hg : SupportedOn g t) (hst : Disjoint s t) :
    ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0 := by
  filter_upwards [hf, hg] with x hfx hgx
  by_cases hx : x ∈ s
  · exact Or.inr (hgx (fun hxt => Set.disjoint_left.mp hst hx hxt))
  · exact Or.inl (hfx hx)

theorem ae_disjoint_finset_sum {ι : Type*} (s : Finset ι)
    (f : Lp E p μ) (g : ι → Lp E p μ)
    (hdis : ∀ i ∈ s, ∀ᵐ x ∂μ, f x = 0 ∨ g i x = 0) :
    ∀ᵐ x ∂μ, f x = 0 ∨ (∑ i ∈ s, g i) x = 0 := by
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, f x = 0 ∨ g i x = 0 := by
    simpa only [Filter.eventually_all_finset] using hdis
  filter_upwards [hall, Lp.coeFn_fun_finsetSum s g] with x hx hsum
  by_cases hf : f x = 0
  · exact Or.inl hf
  · refine Or.inr ?_
    rw [hsum]
    exact Finset.sum_eq_zero (fun i hi => (hx i hi).resolve_left hf)

theorem ae_disjoint_real_smul_right [NormedSpace ℝ E]
    (f g : Lp E p μ) (a : ℝ) (hdis : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    ∀ᵐ x ∂μ, f x = 0 ∨ (a • g) x = 0 := by
  filter_upwards [hdis, Lp.coeFn_smul a g] with x hx ha
  rcases hx with hf | hg
  · exact Or.inl hf
  · right
    rw [ha]
    change a • g x = 0
    rw [hg, smul_zero]

theorem norm_finset_sum_rpow [Fact (1 ≤ p)] {ι : Type*}
    (s : Finset ι) (f : ι → Lp E p μ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0) :
    ‖∑ i ∈ s, f i‖ ^ p.toReal = ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  classical
  revert hdis
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp [ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩]
  | @insert i s hi ih =>
    intro hdis
    have hpast : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → ∀ᵐ x ∂μ, f j x = 0 ∨ f k x = 0 :=
      fun j hj k hk => hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have hfresh : ∀ j ∈ s, ∀ᵐ x ∂μ, f i x = 0 ∨ f j x = 0 := by
      intro j hj
      exact hdis i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun he => hi (he ▸ hj))
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin (ae_disjoint_finset_sum s (f i) f hfresh),
      ih hpast]

theorem norm_real_smul_rpow [NormedSpace ℝ E] [Fact (1 ≤ p)]
    (a : ℝ) (f : Lp E p μ) :
    ‖a • f‖ ^ p.toReal = |a| ^ p.toReal * ‖f‖ ^ p.toReal := by
  rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]

theorem translate_supported_interval {p : ℝ≥0∞} {R : ℝ}
    {f : LebesgueLp p} (hf : SupportedOn f (Set.Icc (-R) R)) (a : ℝ) :
    SupportedOn (translate p a f) (Set.Icc (a - R) (a + R)) := by
  have hcomp := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae hf
  filter_upwards [translate_ae p a f, hcomp] with x hx hfx
  intro hout
  rw [hx]
  apply hfx
  intro hin
  apply hout
  exact ⟨by linarith [hin.1], by linarith [hin.2]⟩

end SchauderTranslates.LpConstruction
