import Lean_Code.SchauderTranslates.Lp.BranchHolder

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : 0 < p.toReal) (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n)

def branchCompletedPrefix (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) (n : ℕ) :
    BranchSpace p N →L[ℂ] BranchSpace p N :=
  ∑ l ∈ Finset.range n, ∑ i, (branchCoordinate p N l i).smulRight (branchAtom p N l i)

def branchCutPrefix (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) (n : ℕ)
    (s : Finset (Fin (N n))) : BranchSpace p N →L[ℂ] BranchSpace p N :=
  branchCompletedPrefix p N n + ∑ i ∈ s, (branchCoordinate p N n i).smulRight (branchAtom p N n i)

def branchCutScalar (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) (n : ℕ)
    (s : Finset (Fin (N n))) : BranchSpace p N →L[ℂ] ℂ :=
  (layerDualScale p.toReal (N n) : ℂ) • ∑ i ∈ s, branchCoordinate p N n i

@[simp] theorem branchCompletedPrefix_apply (n : ℕ) (z : BranchSpace p N) :
    branchCompletedPrefix p N n z = ∑ l ∈ Finset.range n,
      ∑ i, branchCoordinate p N l i z • branchAtom p N l i := by
  simp [branchCompletedPrefix]

@[simp] theorem branchCutPrefix_apply (n : ℕ) (s : Finset (Fin (N n))) (z : BranchSpace p N) :
    branchCutPrefix p N n s z = branchCompletedPrefix p N n z +
      ∑ i ∈ s, branchCoordinate p N n i z • branchAtom p N n i := by simp [branchCutPrefix]

@[simp] theorem branchCutScalar_apply (n : ℕ) (s : Finset (Fin (N n))) (z : BranchSpace p N) :
    branchCutScalar p N n s z = (layerDualScale p.toReal (N n) : ℂ) *
      ∑ i ∈ s, branchCoordinate p N n i z := by simp [branchCutScalar]

include hp hN in
theorem branch_completed_prefix_formula (n : ℕ) (z : BranchSpace p N) :
    branchCompletedPrefix p N n z = z none • branchRoot p N +
      (∑ l ∈ Finset.range n, branchLayer p N l (fun i => z (some ⟨l, i⟩))) -
        branchScalar p N n z • branchResidual p N n := by
  induction n with
  | zero => simp [branchResidual]
  | succ n ih =>
    have he := branch_elimination_identity hp N hN n z
    simp only [branchCompletedPrefix_apply, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    rw [eq_sub_of_add_eq he.symm]
    abel

theorem branch_subset_synthesis (n : ℕ) (s : Finset (Fin (N n))) (c : Fin (N n) → ℂ) :
    (∑ i ∈ s, c i • branchAtom p N n i) =
      (∑ i ∈ s, c i • branchUnit p N n i) +
        ((layerDualScale p.toReal (N n) : ℂ) * ∑ i ∈ s, c i) • branchResidual p N n := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum, Finset.sum_apply, branchAtom,
    lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  congr 1
  ring

include hp hN in
/-- Exact formula for a cut inside any branch layer, including empty and full cuts. -/
theorem branch_cut_formula (n : ℕ) (s : Finset (Fin (N n))) (z : BranchSpace p N) :
    branchCutPrefix p N n s z = z none • branchRoot p N +
      (∑ l ∈ Finset.range n, branchLayer p N l (fun i => z (some ⟨l, i⟩))) +
      (∑ i ∈ s, branchCoordinate p N n i z • branchUnit p N n i) -
        (branchScalar p N n z - branchCutScalar p N n s z) • branchResidual p N n := by
  rw [branchCutPrefix_apply, branch_completed_prefix_formula hp N hN,
    branch_subset_synthesis, branchCutScalar_apply, sub_smul]
  abel

end SchauderTranslates.LpConstruction
