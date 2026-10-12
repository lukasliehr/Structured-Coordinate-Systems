import Lean_Code.SchauderTranslates.Lp.BranchPast

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def branchRootProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) :
    BranchSpace p N →L[ℂ] BranchSpace p N := (lp.evalCLM ℂ _ p none).smulRight (branchRoot p N)

def branchPrivateProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) :
    BranchSpace p N →L[ℂ] BranchSpace p N := 1 - branchRootProjection p N

@[simp] theorem branchRootProjection_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : branchRootProjection p N z = z none • branchRoot p N := rfl

@[simp] theorem branchPrivateProjection_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : branchPrivateProjection p N z = z - z none • branchRoot p N := rfl

@[simp] theorem branchPrivateProjection_none {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : branchPrivateProjection p N z none = 0 := by simp [lp.coeFn_smul]

@[simp] theorem branchPrivateProjection_private {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) (n : ℕ) (i : Fin (N n)) :
    branchPrivateProjection p N z (some ⟨n, i⟩) = z (some ⟨n, i⟩) := by simp [lp.coeFn_smul]

theorem branchPrivateProjection_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : ‖branchPrivateProjection p N z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro k
  rcases k with _ | ⟨n, i⟩
  · simp
  · simp

theorem branchRootProjection_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : ‖branchRootProjection p N z‖ ≤ ‖z‖ := by
  rw [branchRootProjection_apply, norm_smul, branchRoot_norm, mul_one]
  exact lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' z none

theorem branchPrivateProjection_residual_bound {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) :
    ‖branchPrivateProjection p N (branchResidual p N n)‖ ≤ 1 :=
  (branchPrivateProjection_bound N _).trans_eq (branchResidual_norm hp N hN n)

@[simp] theorem branchLayer_none {p : ℝ≥0∞} (N : ℕ → ℕ)
    (n : ℕ) (y : Fin (N n) → ℂ) : branchLayer p N n y none = 0 := by
  simp [branchLayer, lp.coeFn_sum, lp.coeFn_smul]

@[simp] theorem branchLayer_same {p : ℝ≥0∞} (N : ℕ → ℕ)
    (n : ℕ) (y : Fin (N n) → ℂ) (i : Fin (N n)) :
    branchLayer p N n y (some ⟨n, i⟩) = y i := by
  simp [branchLayer, lp.coeFn_sum, lp.coeFn_smul, smul_eq_mul]

theorem branchLayer_other {p : ℝ≥0∞} (N : ℕ → ℕ)
    {n k : ℕ} (hkn : k ≠ n) (y : Fin (N n) → ℂ) (i : Fin (N k)) :
    branchLayer p N n y (some ⟨k, i⟩) = 0 := by
  simp [branchLayer, lp.coeFn_sum, lp.coeFn_smul, branchUnit_other p N hkn]

def branchSubsetVector (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (s : Finset (Fin (N n)))
    (y : Fin (N n) → ℂ) : BranchSpace p N := ∑ i ∈ s, y i • branchUnit p N n i

@[simp] theorem branchSubsetVector_none {p : ℝ≥0∞} (N : ℕ → ℕ)
    (n : ℕ) (s : Finset (Fin (N n))) (y : Fin (N n) → ℂ) :
    branchSubsetVector p N n s y none = 0 := by simp [branchSubsetVector, lp.coeFn_sum, lp.coeFn_smul]

@[simp] theorem branchSubsetVector_same {p : ℝ≥0∞} (N : ℕ → ℕ)
    (n : ℕ) (s : Finset (Fin (N n))) (y : Fin (N n) → ℂ) (i : Fin (N n)) :
    branchSubsetVector p N n s y (some ⟨n, i⟩) = if i ∈ s then y i else 0 := by
  simp [branchSubsetVector, lp.coeFn_sum, lp.coeFn_smul, smul_eq_mul]

theorem branchSubsetVector_other {p : ℝ≥0∞} (N : ℕ → ℕ)
    {n k : ℕ} (hkn : k ≠ n) (s : Finset (Fin (N n))) (y : Fin (N n) → ℂ) (i : Fin (N k)) :
    branchSubsetVector p N n s y (some ⟨k, i⟩) = 0 := by
  simp [branchSubsetVector, lp.coeFn_sum, lp.coeFn_smul, branchUnit_other p N hkn]

theorem branchSubsetVector_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (s : Finset (Fin (N n))) (z : BranchSpace p N) :
    ‖branchSubsetVector p N n s (fun i => z (some ⟨n, i⟩))‖ ≤ ‖z‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro k
  rcases k with _ | ⟨l, i⟩
  · simp
  · by_cases he : l = n
    · subst l; simp only [branchSubsetVector_same]; split_ifs <;> simp
    · simp [branchSubsetVector_other N he]

theorem branch_subset_meanVector_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) (s : Finset (Fin (N n))) :
    ‖branchSubsetVector p N n s (fun _ => (layerPrimalScale p.toReal (N n) : ℂ))‖ ≤ 1 := by
  simpa only [branchMeanVector_same, branchMeanVector_norm hp N hN] using
    branchSubsetVector_bound N n s (branchMeanVector p N n)

end SchauderTranslates.LpConstruction
