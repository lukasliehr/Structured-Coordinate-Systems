module

public import Lean_Code.PositiveBiorthogonal.FiniteInverse
public import Lean_Code.PositiveBiorthogonal.BasisCriterion
public import Lean_Code.PositiveBiorthogonal.PairingNorms
public import Lean_Code.PositiveBiorthogonal.BasicLp
public import Lean_Code.PositiveBiorthogonal.SupportObstruction
public import Lean_Code.PositiveBiorthogonal.DualExpansion
public import Lean_Code.PositiveBiorthogonal.Existence
public import Lean_Code.PositiveBiorthogonal.CoefficientObstruction
public import Lean_Code.PositiveBiorthogonal.VectorObstruction
public import Lean_Code.PositiveBiorthogonal.FinitePolynomial
public import Lean_Code.PositiveBiorthogonal.FiniteKernel
public import Lean_Code.PositiveBiorthogonal.Auxiliary
public import Lean_Code.PositiveBiorthogonal.EndpointAuxiliary
public import Lean_Code.PositiveBiorthogonal.ToeplitzProjections
public import Lean_Code.PositiveBiorthogonal.AuxiliaryExistence
public import Lean_Code.PositiveBiorthogonal.Partitions
public import Lean_Code.PositiveBiorthogonal.Averaging
public import Lean_Code.PositiveBiorthogonal.PartitionRefinement
public import Lean_Code.PositiveBiorthogonal.RefinementTrace
public import Lean_Code.PositiveBiorthogonal.Schedule
public import Lean_Code.PositiveBiorthogonal.UnitExtraction
public import Lean_Code.PositiveBiorthogonal.LocalPositive
public import Lean_Code.PositiveBiorthogonal.Flatten
public import Lean_Code.PositiveBiorthogonal.CellSpans
public import Lean_Code.PositiveBiorthogonal.IntervalDensity
public import Lean_Code.PositiveBiorthogonal.FinalExistence

@[expose] public section

namespace PositiveBiorthogonal

theorem isGLB_one_of_approach {S : Set ℝ} (hlower : ∀ k ∈ S, 1 ≤ k)
    (happroach : ∀ ε : ℝ, 0 < ε → ∃ k ∈ S, k < 1 + ε) : IsGLB S 1 := by
  refine ⟨hlower, ?_⟩
  intro x hx
  by_contra! hgt
  obtain ⟨k, hk, hclose⟩ := happroach (x - 1) (sub_pos.mpr hgt)
  have hlow := hx hk
  linarith

end PositiveBiorthogonal
