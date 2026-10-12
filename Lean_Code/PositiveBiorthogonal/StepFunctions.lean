import Lean_Code.PositiveBiorthogonal.BasicLp

/-! Closure and integrability of the exact interval-step-function class. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

theorem step_add {f g : L 𝕜 p} (hf : CompactlySupportedStep f) (hg : CompactlySupportedStep g) :
    CompactlySupportedStep (f + g) := by
  obtain ⟨m, l, r, c, hc⟩ := hf
  obtain ⟨n, l', r', c', hc'⟩ := hg
  refine ⟨m + n, Fin.addCases l l', Fin.addCases r r', Fin.addCases c c', ?_⟩
  filter_upwards [hc, hc', Lp.coeFn_add f g] with x hx hy ha
  rw [ha, Pi.add_apply, hx, hy, Fin.sum_univ_add]
  simp

theorem step_neg {f : L 𝕜 p} (hf : CompactlySupportedStep f) : CompactlySupportedStep (-f) := by
  simpa only [neg_one_smul] using step_smul hf (-1 : 𝕜)

theorem step_sub {f g : L 𝕜 p} (hf : CompactlySupportedStep f) (hg : CompactlySupportedStep g) :
    CompactlySupportedStep (f - g) := by
  simpa only [sub_eq_add_neg] using step_add hf (step_neg hg)

theorem step_finset_sum {ι : Type*} (s : Finset ι) (f : ι → L 𝕜 p)
    (hf : ∀ i ∈ s, CompactlySupportedStep (f i)) : CompactlySupportedStep (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (step_zero (𝕜 := 𝕜) (p := p))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact step_add (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem integral_lp_smul (a : 𝕜) (f : L 𝕜 p) :
    (∫ x : ℝ, (a • f) x) = a * ∫ x : ℝ, f x := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul a f] with x hx
  simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem integrable_lp_smul (a : 𝕜) (f : L 𝕜 p) (hf : Integrable f volume) :
    Integrable (a • f : L 𝕜 p) volume := by
  apply (hf.const_mul a).congr
  filter_upwards [Lp.coeFn_smul a f] with x hx
  simpa only [Pi.smul_apply, smul_eq_mul] using hx.symm

theorem integral_lp_sub (f g : L 𝕜 p) (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x : ℝ, (f - g) x) = (∫ x : ℝ, f x) - ∫ x : ℝ, g x := by
  rw [← integral_sub hf hg]
  apply integral_congr_ae
  exact Lp.coeFn_sub f g

end PositiveBiorthogonal
