import Lean_Code.SchauderTranslates.Lp.BranchDensity

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem finite_lp_functional_bound {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (s : Finset ι) (c : ι → ℂ) (z : lp (fun _ : ι => ℂ) p) :
    ‖∑ i ∈ s, c i * z i‖ ≤
      (∑ i ∈ s, ‖c i‖ ^ Real.conjExponent p.toReal) ^ (1 / Real.conjExponent p.toReal) * ‖z‖ := by
  have hconj := Real.HolderConjugate.conjExponent hp
  have hpow : (∑ i ∈ s, ‖z i‖ ^ p.toReal) ^ (1 / p.toReal) ≤ ‖z‖ := by
    calc
      _ ≤ (‖z‖ ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
          (lp.sum_rpow_le_norm_rpow hconj.pos z s) (by positivity)
      _ = ‖z‖ := by rw [one_div, Real.rpow_rpow_inv (norm_nonneg _) hconj.ne_zero]
  calc
    _ ≤ ∑ i ∈ s, ‖c i * z i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖c i‖ * ‖z i‖ := by simp_rw [norm_mul]
    _ ≤ (∑ i ∈ s, ‖c i‖ ^ Real.conjExponent p.toReal) ^ (1 / Real.conjExponent p.toReal) *
        (∑ i ∈ s, ‖z i‖ ^ p.toReal) ^ (1 / p.toReal) :=
      Real.inner_le_Lp_mul_Lq_of_nonneg s hconj.symm (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)

theorem layer_dual_power {P : ℝ} (hP : 1 < P) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * layerDualScale P N ^ Real.conjExponent P = 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hN)
  rw [layerDualScale, ← Real.rpow_mul hn.le]
  have he : -(P - 1) / P * Real.conjExponent P = -1 := by
    unfold Real.conjExponent
    field_simp [ne_of_gt (show 0 < P from by linarith),
      ne_of_gt (show 0 < P - 1 from by linarith)]
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hn)]

theorem branchMean_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) (z : BranchSpace p N) :
    ‖branchMean p N n z‖ ≤ ‖z‖ := by
  let s : Finset (BranchIndex N) := Finset.univ.image (fun i : Fin (N n) => some ⟨n, i⟩)
  have hinj : Function.Injective (fun i : Fin (N n) => (some ⟨n, i⟩ : BranchIndex N)) := by
    intro i j hij
    simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hij
  have hsum : branchMean p N n z =
      ∑ k ∈ s, (layerDualScale p.toReal (N n) : ℂ) * z k := by
    dsimp [s]
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simp [Finset.mul_sum]
  have hscale : (∑ _k ∈ s, ‖(layerDualScale p.toReal (N n) : ℂ)‖ ^
      Real.conjExponent p.toReal) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (layer_scale_pos p.toReal (hN n)).2]
    simpa [s, Finset.card_image_of_injective _ hinj] using layer_dual_power hp (hN n)
  rw [hsum]
  simpa only [hscale, Real.one_rpow, one_mul] using
    finite_lp_functional_bound hp s (fun _ => (layerDualScale p.toReal (N n) : ℂ)) z

theorem branchMean_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) : ‖branchMean p N n‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by simpa using branchMean_bound hp N hN n z)
  · have hbound := (branchMean p N n).le_opNorm (branchMeanVector p N n)
    simpa [branchMean_meanVector (by linarith : 0 < p.toReal) N hN,
      branchMeanVector_norm (by linarith : 0 < p.toReal) N hN] using hbound

end SchauderTranslates.LpConstruction
