import Lean_Code.SchauderTranslates.Lp.ForestNorm

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (N : ℕ → ℕ → ℕ)

/-- Synthesis into disjoint private branches preserves the ℓᵖ bound on the
scalar root coefficients; no root synthesis estimate is used here. -/
theorem forest_root_private_diagonal_bound (s : Finset ℕ)
    (t : lp (fun _ : ℕ => ℂ) p) (z : ∀ j, BranchSpace p (N j))
    (hz : ∀ j, z j none = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j ∈ s, ‖z j‖ ≤ C * ‖t j‖) :
    ‖∑ j ∈ s, forestInsert hp N j (z j)‖ ≤ C * ‖t‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hC (norm_nonneg t)) hp).mp
  calc
    _ = ∑ j ∈ s, ‖z j‖ ^ p.toReal := forest_insert_sum_power hp N s z hz
    _ ≤ ∑ j ∈ s, (C * ‖t j‖) ^ p.toReal :=
      Finset.sum_le_sum (fun j hj => Real.rpow_le_rpow (norm_nonneg _) (hbound j hj) hp.le)
    _ = C ^ p.toReal * ∑ j ∈ s, ‖t j‖ ^ p.toReal := by
      simp_rw [Real.mul_rpow hC (norm_nonneg (t _))]
      rw [Finset.mul_sum]
    _ ≤ C ^ p.toReal * ‖t‖ ^ p.toReal :=
      mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp t s) (Real.rpow_nonneg hC _)
    _ = (C * ‖t‖) ^ p.toReal := (Real.mul_rpow hC (norm_nonneg t)).symm

/-- A diagonal bound on all private branches also bounds the initial
coordinate, provided the common constant is at least one. -/
theorem forest_private_diagonal_bound (s : Finset ℕ)
    (y : ForestPrivateSpace p N) (z : ∀ j, BranchSpace p (N j))
    (hz : ∀ j, z j none = 0) {C : ℝ} (hC : 1 ≤ C)
    (hbound : ∀ j ∈ s, ‖z j‖ ≤ C * ‖forestExtract hp N j y‖) :
    ‖y none • forestInitial p N + ∑ j ∈ s, forestInsert hp N j (z j)‖ ≤ C * ‖y‖ := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCp : 1 ≤ C ^ p.toReal := Real.one_le_rpow hC hp.le
  have hsum : (∑ j ∈ s, ‖z j‖ ^ p.toReal) ≤
      C ^ p.toReal * ∑ j ∈ s, ‖forestExtract hp N j y‖ ^ p.toReal := by
    calc
      _ ≤ ∑ j ∈ s, (C * ‖forestExtract hp N j y‖) ^ p.toReal :=
        Finset.sum_le_sum (fun j hj => Real.rpow_le_rpow (norm_nonneg _) (hbound j hj) hp.le)
      _ = _ := by
        simp_rw [Real.mul_rpow hC0 (norm_nonneg (forestExtract hp N _ y))]
        rw [Finset.mul_sum]
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg y)) hp).mp
  calc
    _ = ‖y none‖ ^ p.toReal + ∑ j ∈ s, ‖z j‖ ^ p.toReal :=
      forest_initial_insert_sum_power hp N s _ z hz
    _ ≤ C ^ p.toReal * ‖y none‖ ^ p.toReal +
        C ^ p.toReal * ∑ j ∈ s, ‖forestExtract hp N j y‖ ^ p.toReal :=
      add_le_add (by simpa using mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg (norm_nonneg (y none)) _)) hsum
    _ = C ^ p.toReal * (‖y none‖ ^ p.toReal +
        ∑ j ∈ s, ‖forestExtract hp N j y‖ ^ p.toReal) := by ring
    _ ≤ C ^ p.toReal * ‖y‖ ^ p.toReal := mul_le_mul_of_nonneg_left
      (forest_initial_extract_sum_power_le hp N s y) (Real.rpow_nonneg hC0 _)
    _ = (C * ‖y‖) ^ p.toReal := (Real.mul_rpow hC0 (norm_nonneg y)).symm

end SchauderTranslates.LpConstruction
