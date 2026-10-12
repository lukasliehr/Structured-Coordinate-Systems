import Lean_Code.PositiveTranslates.Analytic.Limit
import Lean_Code.Basis.Perturbation
import Lean_Code.SchauderTranslates.Lp.LpMeasurableEquiv

/-!
# A non-negative entire generator whose translates form a Schauder basis (`p > 2`)

The analytic half of the paper's Theorem `thm:translate-properties`(iii).

* `exists_nonneg_entire_translate_basis_of_machine`: given a stage machine `M` over a
  parameter set `Γ ∋ 0` (the reference construction), there are a non-negative function
  `f ∈ Lᵖ(ℝ)` extending to an entire function and pairwise distinct parameters
  `λ_n ∈ Γ` such that the translates `f(· - λ_n)` form a Schauder basis of `Lᵖ(ℝ)`.
  The quantitative form `exists_nonneg_entire_translate_basis_of_machine_with_constant`
  also bounds the basis constant by `M.K (1 + ρ) / (1 - ρ)` for any prescribed
  `0 < ρ < 1`.
* `exists_nonneg_entire_translate_basis`: if stage machines exist for every set `Γ ∋ 0`
  that is unbounded above, the same holds with parameters in an arbitrary unbounded set
  `S ⊆ ℝ`. The variant `exists_nonneg_entire_translate_basis_of_nonneg_machines` only
  needs machines over parameter sets `Γ ⊆ [0, ∞)`, as in the paper.

The proof follows the paper: an analytic run (`exists_analytic_run`), the limit generator
(`exists_entire_limit`), the total error estimate (`MachineRun.summable_translate_error`)
and the small perturbation principle
(`StructuredBases.exists_schauderBasis_of_summable_perturbation`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-- **The analytic half, quantitative form.** A stage machine over `Γ ∋ 0` yields a
non-negative generator with an entire extension whose translates by distinct parameters
from `Γ` form a Schauder basis of `Lᵖ(ℝ)`, `2 < p < ∞`. For every `0 < ρ < 1` the basis
constant can be made at most `K (1 + ρ) / (1 - ρ)`, where `K = M.K` bounds the basis
constants of the reference bases of the machine. -/
theorem exists_nonneg_entire_translate_basis_of_machine_with_constant
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞) (Γ : Set ℝ) (h0 : (0 : ℝ) ∈ Γ)
    (M : StageMachine p Γ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ Γ) ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
        ∀ N, ‖b.proj N‖ ≤ M.K * (1 + ρ) / (1 - ρ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  -- the constants
  set K : ℝ := max M.K 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  set κ : ℝ := min (1 / 100) (ρ / (24 * K)) with hκdef
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ' : κ ≤ 1 / 100 := min_le_left _ _
  have hκρ : 24 * K * κ ≤ ρ := by
    have h := min_le_right (1 / 100 : ℝ) (ρ / (24 * K))
    rw [← hκdef, le_div_iff₀ (by positivity)] at h
    linarith
  -- the analytic run and the reference basis
  obtain ⟨S, N, v, Λ₀, G, g, hS0, hSnext, hNmin, hvadm, hGdiff, hGpos, hgG, hgnorm, hGinc,
    hgL, hgV⟩ := exists_analytic_run hp hp' M hκ hκ'
  let R : MachineRun M := ⟨S, N, v, Λ₀, hS0, hSnext, hNmin, hvadm⟩
  obtain ⟨B, hB, hBK⟩ := M.basis_of_run S N v Λ₀ hS0 hSnext hNmin hvadm
  -- the limit in `Lᵖ`
  have hcauchy : CauchySeq g := by
    refine cauchySeq_of_le_geometric (1 / 2) (3 / 2 * κ) (by norm_num) fun t => ?_
    rw [dist_comm, dist_eq_norm]
    have h2 : (1 : ℝ) ≤ ((M.births (S t)).length : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (M.births (S t)).length]
    exact (le_mul_of_one_le_left (norm_nonneg _) h2).trans (hgL t)
  obtain ⟨glim, hglim⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the entire limit
  obtain ⟨Glim, hGlimdiff, hGlimpos, hglimG⟩ := exists_entire_limit hGdiff hGpos hgG hGinc hglim
  -- the total error
  have hg0 : ‖g 0 - intervalAtom p (0, 1)‖ ≤ κ := by
    have h := hgnorm 0
    norm_num at h
    exact h
  obtain ⟨hsum, htsum⟩ := R.summable_translate_error hκ.le hg0 hgL hgV hglim
  have hBeq : ∀ m, B m = (R.birth m).2 := R.basis_eq hB
  have hlower : ∀ m, (1 / 2 : ℝ) ≤ ‖B m‖ := fun m => by
    rw [hBeq]
    exact R.half_le_norm_birth hp' m
  have hBK' : ∀ n, ‖B.proj n‖ ≤ K := fun n => (hBK n).trans (le_max_left _ _)
  have hs : Summable fun m => ‖translate p (R.birth m).1 glim - B m‖ := by
    simpa only [hBeq] using hsum
  have htsum' : ∑' m, ‖translate p (R.birth m).1 glim - B m‖ ≤ 6 * κ := by
    simpa only [hBeq] using htsum
  have hlt : ∑' m, ‖translate p (R.birth m).1 glim - B m‖ < 1 / 2 / (2 * K) := by
    refine htsum'.trans_lt ?_
    rw [div_div, lt_div_iff₀ (by positivity)]
    linarith
  -- the perturbed basis
  obtain ⟨b', hb', hproj⟩ := exists_schauderBasis_of_summable_perturbation B (by norm_num)
    hlower hBK' (fun m => translate p (R.birth m).1 glim) hs hlt
  -- the generator
  set f : ℝ → ℝ := fun x => (Glim x).re with hf
  have hfG : ∀ x : ℝ, Glim x = (f x : ℂ) := fun x => by
    have h := Complex.nonneg_iff.mp (hGlimpos x)
    exact Complex.ext (by simp [hf]) (by simpa using h.2.symm)
  have hgf : (glim : ℝ → ℂ) =ᵐ[volume] fun x => (f x : ℂ) := by
    filter_upwards [hglimG] with x hx
    rw [hx, hfG]
  refine ⟨f, fun m => (R.birth m).1, ?_, fun x => (Complex.nonneg_iff.mp (hGlimpos x)).1, ?_,
    ⟨Glim, hGlimdiff, hfG⟩, R.birth_fst_injective, fun n => R.birth_fst_mem h0 n, b',
    fun n => ?_, fun n => ?_⟩
  · -- `f ∈ Lᵖ`
    have h1 : MemLp (fun x : ℝ => (f x : ℂ)) p volume := (Lp.memLp glim).ae_eq hgf
    simpa using h1.re
  · -- `f` is not the zero class
    intro hzero
    have hglim0 : glim = 0 := by
      apply Lp.ext
      filter_upwards [hgf, hzero, Lp.coeFn_zero ℂ p (volume : Measure ℝ)] with x h1 h2 h3
      rw [h1, h3, h2]
      simp
    have hlim : ‖glim - intervalAtom p (0, 1)‖ ≤ 4 * κ := by
      refine le_of_tendsto' ((hglim.sub_const _).norm) (fun t => (hgnorm t).trans ?_)
      have : 0 ≤ κ * (3 * (1 / 2 : ℝ) ^ t) := by positivity
      linarith
    rw [hglim0, zero_sub, norm_neg, initial_generator_unit p hp0 hp'] at hlim
    linarith
  · -- the basis vectors are the translates of `f`
    rw [hb']
    have h1 := translate_ae p (R.birth n).1 glim
    have h2 := (measurePreserving_sub_right volume (R.birth n).1).quasiMeasurePreserving.ae hgf
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  · -- the basis constant
    have hMK : 1 ≤ M.K := (one_le_norm_proj B one_pos).trans (hBK 1)
    have hKM : M.K = K := (max_eq_left hMK).symm
    rw [hKM]
    refine (hproj n).trans ?_
    set s : ℝ := ∑' m, ‖translate p (R.birth m).1 glim - B m‖ with hsdef
    have hs0 : 0 ≤ s := tsum_nonneg fun _ => norm_nonneg _
    have hρle : 2 * K * s / (1 / 2) ≤ ρ := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    have hρ0' : 0 ≤ 2 * K * s / (1 / 2) := by positivity
    apply div_le_div₀
    · exact mul_nonneg (by linarith) (by linarith)
    · exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    · linarith
    · linarith

/-- **The analytic half.** A stage machine over `Γ ∋ 0` yields a non-negative generator
with an entire extension whose translates by distinct parameters from `Γ` form a Schauder
basis of `Lᵖ(ℝ)`, `2 < p < ∞`. -/
theorem exists_nonneg_entire_translate_basis_of_machine
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞) (Γ : Set ℝ) (h0 : (0 : ℝ) ∈ Γ)
    (M : StageMachine p Γ) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ Γ) ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ) := by
  obtain ⟨f, lam, hf, hpos, hne, hF, hinj, hmem, b, hb, -⟩ :=
    exists_nonneg_entire_translate_basis_of_machine_with_constant p hp hp' Γ h0 M
      (ρ := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨f, lam, hf, hpos, hne, hF, hinj, hmem, b, hb⟩

/-- The statement for sets that are unbounded above: translate the parameter set to
`Γ = {0} ∪ {s - b₀ : s ∈ S, s > b₀} ⊆ [0, ∞)` with `b₀ ∈ S`, and translate the generator
back. -/
theorem exists_nonneg_entire_translate_basis_of_unbounded_above
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (hM : ∀ Γ : Set ℝ, (0 : ℝ) ∈ Γ → Γ ⊆ Set.Ici 0 → (∀ x : ℝ, ∃ γ ∈ Γ, x < γ) →
      Nonempty (StageMachine p Γ))
    (S : Set ℝ) (hS : ∀ x : ℝ, ∃ s ∈ S, x < s) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ) := by
  obtain ⟨b₀, hb₀, -⟩ := hS 0
  -- `Γ = (S - b₀) ∩ [0, ∞)` contains `0` and is unbounded above
  set Γ : Set ℝ := {γ | 0 ≤ γ ∧ γ + b₀ ∈ S} with hΓ
  have h0 : (0 : ℝ) ∈ Γ := by
    refine ⟨le_rfl, ?_⟩
    rwa [zero_add]
  have hΓ0 : Γ ⊆ Set.Ici 0 := fun γ hγ => hγ.1
  have hunb : ∀ x : ℝ, ∃ γ ∈ Γ, x < γ := by
    intro x
    obtain ⟨s, hs, hxs⟩ := hS (max x 0 + b₀)
    have h1 : max x 0 < s - b₀ := by linarith
    refine ⟨s - b₀, ⟨(le_max_right x 0).trans h1.le, ?_⟩, (le_max_left x 0).trans_lt h1⟩
    rwa [sub_add_cancel]
  obtain ⟨M⟩ := hM Γ h0 hΓ0 hunb
  obtain ⟨f, lam, hf, hpos, hne, ⟨F, hF, hFf⟩, hinj, hmem, b, hb⟩ :=
    exists_nonneg_entire_translate_basis_of_machine p hp hp' Γ h0 M
  refine ⟨fun x => f (x + b₀), fun n => lam n + b₀, ?_, fun x => hpos _, ?_,
    ⟨fun z => F (z + b₀), hF.comp (differentiable_id.add_const _), fun x => ?_⟩,
    fun m n h => hinj (add_right_cancel h), fun n => (hmem n).2, b, fun n => ?_⟩
  · exact hf.comp_measurePreserving (measurePreserving_add_right volume b₀)
  · intro hzero
    apply hne
    have h := (measurePreserving_sub_right volume b₀).quasiMeasurePreserving.ae hzero
    filter_upwards [h] with x hx
    simpa using hx
  · show F ((x : ℂ) + b₀) = ((f (x + b₀) : ℝ) : ℂ)
    rw [← Complex.ofReal_add]
    exact hFf _
  · filter_upwards [hb n] with x hx
    rw [hx]
    show ((f (x - lam n) : ℝ) : ℂ) = ((f (x - (lam n + b₀) + b₀) : ℝ) : ℂ)
    congr 2
    ring

/-- **A non-negative entire generator with parameters in a prescribed unbounded set**,
assuming only stage machines over parameter sets `Γ ⊆ [0, ∞)` containing `0` and unbounded
above (the situation of the paper). If `S` is unbounded above, the parameter set is
shifted to contain `0`; otherwise `S` is reflected first. -/
theorem exists_nonneg_entire_translate_basis_of_nonneg_machines
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (hM : ∀ Γ : Set ℝ, (0 : ℝ) ∈ Γ → Γ ⊆ Set.Ici 0 → (∀ x : ℝ, ∃ γ ∈ Γ, x < γ) →
      Nonempty (StageMachine p Γ))
    (S : Set ℝ) (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ) := by
  by_cases hA : BddAbove S
  · -- `S` is unbounded below: reflect
    have hB : ¬ BddBelow S := fun hB => hS (isBounded_iff_bddBelow_bddAbove.mpr ⟨hB, hA⟩)
    have hbelow : ∀ x : ℝ, ∃ s ∈ S, s < x := not_bddBelow_iff.mp hB
    set S' : Set ℝ := {s | -s ∈ S} with hS'
    have hS'unb : ∀ x : ℝ, ∃ s ∈ S', x < s := by
      intro x
      obtain ⟨s, hs, hsx⟩ := hbelow (-x)
      refine ⟨-s, ?_, by linarith⟩
      show - -s ∈ S
      rwa [neg_neg]
    obtain ⟨f, lam, hf, hpos, hne, ⟨F, hF, hFf⟩, hinj, hmem, b, hb⟩ :=
      exists_nonneg_entire_translate_basis_of_unbounded_above p hp hp' hM S' hS'unb
    have hneg : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      Measure.measurePreserving_neg volume
    -- the reflection `g ↦ g(-·)` is a linear isometry of `Lᵖ(ℝ)` onto itself
    let Refl : Lp ℂ p (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ p (volume : Measure ℝ) :=
      lpMeasurePreservingEquiv p volume volume (MeasurableEquiv.neg ℝ) hneg
    refine ⟨fun x => f (-x), fun n => -lam n, ?_, fun x => hpos _, ?_,
      ⟨fun z => F (-z), hF.comp differentiable_neg, fun x => ?_⟩,
      fun m n h => hinj (neg_injective h), hmem,
      transport b Refl.toContinuousLinearEquiv, fun n => ?_⟩
    · exact hf.comp_measurePreserving hneg
    · intro hzero
      apply hne
      have h := hneg.quasiMeasurePreserving.ae hzero
      filter_upwards [h] with x hx
      simpa using hx
    · show F (-(x : ℂ)) = ((f (-x) : ℝ) : ℂ)
      rw [← Complex.ofReal_neg]
      exact hFf _
    · have h1 : (Refl (b n) : ℝ → ℂ) =ᵐ[volume] fun x => b n (-x) :=
        lpMeasurePreservingEquiv_ae p volume volume (MeasurableEquiv.neg ℝ) hneg (b n)
      have h2 := hneg.quasiMeasurePreserving.ae (hb n)
      rw [transport_apply]
      filter_upwards [h1, h2] with x hx1 hx2
      show (Refl (b n) : ℝ → ℂ) x = ((f (-(x - -lam n)) : ℝ) : ℂ)
      rw [hx1, hx2]
      congr 2
      ring
  · exact exists_nonneg_entire_translate_basis_of_unbounded_above p hp hp' hM S
      (not_bddAbove_iff.mp hA)

/-- **A non-negative entire generator with parameters in a prescribed unbounded set.**
Assume that the reference construction is available as a stage machine over every
parameter set `Γ ∋ 0` that is unbounded above. Then for every unbounded `S ⊆ ℝ` and
`2 < p < ∞` there are a non-negative `f ∈ Lᵖ(ℝ)` extending to an entire function and
pairwise distinct `λ_n ∈ S` such that the translates `f(· - λ_n)` form a Schauder basis of
`Lᵖ(ℝ)`. -/
theorem exists_nonneg_entire_translate_basis
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (hM : ∀ Γ : Set ℝ, (0 : ℝ) ∈ Γ → (∀ x : ℝ, ∃ γ ∈ Γ, x < γ) → Nonempty (StageMachine p Γ))
    (S : Set ℝ) (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p volume ∧ (∀ x, 0 ≤ f x) ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      ∃ b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)),
        ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ) :=
  exists_nonneg_entire_translate_basis_of_nonneg_machines p hp hp'
    (fun Γ h0 _ hunb => hM Γ h0 hunb) S hS

end StructuredBases.PositiveTranslates
