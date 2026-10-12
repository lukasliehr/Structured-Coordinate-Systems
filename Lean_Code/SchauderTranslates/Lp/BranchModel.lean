import Lean_Code.SchauderTranslates.Lp.BranchScalars

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- The root and the private coordinates, equipped with the genuine ℓᵖ norm. -/
abbrev BranchIndex (N : ℕ → ℕ) := Option (Σ n, Fin (N n))
abbrev BranchSpace (p : ℝ≥0∞) (N : ℕ → ℕ) := lp (fun _ : BranchIndex N => ℂ) p

def branchRoot (p : ℝ≥0∞) (N : ℕ → ℕ) : BranchSpace p N := lp.single p none 1
def branchUnit (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i : Fin (N n)) : BranchSpace p N :=
  lp.single p (some ⟨n, i⟩) 1

def branchLayer (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (y : Fin (N n) → ℂ) : BranchSpace p N :=
  ∑ i, y i • branchUnit p N n i

def branchMeanVector (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) : BranchSpace p N :=
  layerPrimalScale p.toReal (N n) • ∑ i, branchUnit p N n i

def branchResidual (p : ℝ≥0∞) (N : ℕ → ℕ) : ℕ → BranchSpace p N
  | 0 => branchRoot p N
  | n + 1 => branchBeta p.toReal • (branchResidual p N n - branchMeanVector p N n)

def branchAtom (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i : Fin (N n)) : BranchSpace p N :=
  branchUnit p N n i + layerDualScale p.toReal (N n) • branchResidual p N n

def branchMean (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) (n : ℕ) :
    BranchSpace p N →L[ℂ] ℂ :=
  (layerDualScale p.toReal (N n) : ℂ) • ∑ i, lp.evalCLM ℂ _ p (some ⟨n, i⟩)

def branchScalar (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) :
    ℕ → (BranchSpace p N →L[ℂ] ℂ)
  | 0 => lp.evalCLM ℂ _ p none
  | n + 1 => (branchRatio p.toReal : ℂ) • (branchScalar p N n - branchMean p N n)

def branchCoordinate (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (i : Fin (N n)) : BranchSpace p N →L[ℂ] ℂ :=
  lp.evalCLM ℂ _ p (some ⟨n, i⟩) +
    (layerPrimalScale p.toReal (N n) / 2 : ℂ) • (branchScalar p N n - branchMean p N n)

@[simp] theorem branchRoot_none (p : ℝ≥0∞) (N : ℕ → ℕ) : branchRoot p N none = 1 := by
  simp [branchRoot]

@[simp] theorem branchRoot_private (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i : Fin (N n)) :
    branchRoot p N (some ⟨n, i⟩) = 0 := by simp [branchRoot, Pi.single_apply]

@[simp] theorem branchUnit_none (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i : Fin (N n)) :
    branchUnit p N n i none = 0 := by simp [branchUnit, Pi.single_apply]

@[simp] theorem branchUnit_same (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i j : Fin (N n)) :
    branchUnit p N n i (some ⟨n, j⟩) = if j = i then 1 else 0 := by
  simp [branchUnit, Pi.single_apply, Sigma.mk.inj_iff]

theorem branchUnit_other (p : ℝ≥0∞) (N : ℕ → ℕ) {n k : ℕ} (hkn : k ≠ n)
    (i : Fin (N n)) (j : Fin (N k)) : branchUnit p N n i (some ⟨k, j⟩) = 0 := by
  simp [branchUnit, Pi.single_apply, Sigma.mk.inj_iff, hkn]

@[simp] theorem branchMeanVector_none (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) :
    branchMeanVector p N n none = 0 := by
  simp [branchMeanVector, lp.coeFn_smul, lp.coeFn_sum]

@[simp] theorem branchMeanVector_same (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) (i : Fin (N n)) :
    branchMeanVector p N n (some ⟨n, i⟩) = (layerPrimalScale p.toReal (N n) : ℂ) := by
  simp [branchMeanVector, lp.coeFn_smul, lp.coeFn_sum]

theorem branchMeanVector_other (p : ℝ≥0∞) (N : ℕ → ℕ) {n k : ℕ} (hkn : k ≠ n)
    (j : Fin (N k)) : branchMeanVector p N n (some ⟨k, j⟩) = 0 := by
  simp [branchMeanVector, lp.coeFn_smul, lp.coeFn_sum, branchUnit_other p N hkn]

@[simp] theorem branchMean_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (z : BranchSpace p N) :
    branchMean p N n z = (layerDualScale p.toReal (N n) : ℂ) * ∑ i, z (some ⟨n, i⟩) := by
  simp [branchMean, lp.evalCLM, lp.evalₗ, smul_eq_mul]

@[simp] theorem branchScalar_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (z : BranchSpace p N) : branchScalar p N 0 z = z none := rfl

@[simp] theorem branchScalar_succ (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (z : BranchSpace p N) :
    branchScalar p N (n + 1) z =
      (branchRatio p.toReal : ℂ) * (branchScalar p N n z - branchMean p N n z) := rfl

@[simp] theorem branchCoordinate_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (i : Fin (N n)) (z : BranchSpace p N) :
    branchCoordinate p N n i z = z (some ⟨n, i⟩) +
      (layerPrimalScale p.toReal (N n) / 2 : ℂ) * (branchScalar p N n z - branchMean p N n z) := rfl

@[simp] theorem branchMean_unit_same (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (i : Fin (N n)) :
    branchMean p N n (branchUnit p N n i) = (layerDualScale p.toReal (N n) : ℂ) := by simp

theorem branchMean_unit_other (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ) {n k : ℕ}
    (hnk : n ≠ k) (i : Fin (N k)) : branchMean p N n (branchUnit p N k i) = 0 := by
  simp [branchUnit_other p N hnk]

theorem branchResidual_private_future (p : ℝ≥0∞) (N : ℕ → ℕ) {k n : ℕ}
    (hkn : k ≤ n) (i : Fin (N n)) : branchResidual p N k (some ⟨n, i⟩) = 0 := by
  induction k with
  | zero => simp [branchResidual]
  | succ k ih =>
    have hnk : n ≠ k := by omega
    simp [branchResidual, lp.coeFn_smul, lp.coeFn_sub,
      ih (by omega), branchMeanVector_other p N hnk]

theorem branchResidual_none (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) :
    branchResidual p N n none = (branchBeta p.toReal : ℂ) ^ n := by
  induction n with
  | zero => simp [branchResidual]
  | succ n ih => simp [branchResidual, lp.coeFn_smul, lp.coeFn_sub, ih, pow_succ, mul_comm]

theorem branchMean_residual_future (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ → ℕ)
    {k n : ℕ} (hkn : k ≤ n) : branchMean p N n (branchResidual p N k) = 0 := by
  simp [branchResidual_private_future p N hkn]

end SchauderTranslates.LpConstruction
