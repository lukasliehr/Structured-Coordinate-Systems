import Lean_Code.SchauderTranslates.InformationCentering
import Lean_Code.SchauderTranslates.CenteredProjection

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction and quotient for an initial carrier block, stated directly in
terms of the actual centered vectors. The initial coefficients are freely
chosen; no orthonormality or condition-number hypothesis is imposed. -/
theorem centered_extension_bound (u : ι → H) (v m : κ → H)
    (hm : ∀ i, m i ∈ atomSpan u)
    (hr : ∀ i, v i - m i ∈ (atomSpan u)ᗮ)
    (δ : κ → ℂ) (K : ℝ)
    (hbound : ∀ (a : ι → ℂ) (c : κ → ℂ),
      ‖finiteSynthesis u a + finiteSynthesis v (fun i => δ i * c i)‖ ^ 2 ≤
        K ^ 2 * ‖finiteSynthesis u a + finiteSynthesis v c‖ ^ 2) (c : κ → ℂ) :
    ‖finiteSynthesis (fun i => v i - m i) (fun i => δ i * c i)‖ ^ 2 ≤
      K ^ 2 * ‖finiteSynthesis (fun i => v i - m i) c‖ ^ 2 := by
  classical
  let F := atomSpan u
  have hmean : -finiteSynthesis m c ∈ F :=
    F.neg_mem (Submodule.sum_mem _ (fun i _ => F.smul_mem _ (hm i)))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmean
  have ha' : finiteSynthesis u a = -finiteSynthesis m c := ha
  have hproj (i : κ) : Fᗮ.starProjection (v i) = v i - m i := by
    have he : v i = (v i - m i) + m i := by abel
    conv_lhs => rw [he]
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hr i),
      F.starProjection_orthogonal_apply_eq_zero (hm i), add_zero]
  have hpu : Fᗮ.starProjection (finiteSynthesis u a) = 0 :=
    F.starProjection_orthogonal_apply_eq_zero
      (Submodule.sum_mem _ (fun i _ => F.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))))
  have hleft : Fᗮ.starProjection (finiteSynthesis u a + finiteSynthesis v (fun i => δ i * c i)) =
      finiteSynthesis (fun i => v i - m i) (fun i => δ i * c i) := by
    rw [map_add, hpu, zero_add]
    simp only [finiteSynthesis, map_sum, map_smul, hproj]
  have hright : finiteSynthesis u a + finiteSynthesis v c = finiteSynthesis (fun i => v i - m i) c := by
    rw [ha']
    simp only [finiteSynthesis, smul_sub, Finset.sum_sub_distrib]
    abel
  have hnorm := Fᗮ.norm_starProjection_apply_le
    (finiteSynthesis u a + finiteSynthesis v (fun i => δ i * c i))
  rw [hleft] at hnorm
  have hh := hbound a c
  rw [hright] at hh
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hh

end SchauderTranslates
