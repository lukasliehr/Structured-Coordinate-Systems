import Lean_Code.PositiveBiorthogonal.FiniteInverse
import Lean_Code.PositiveBiorthogonal.BasisCriterion
import Lean_Code.PositiveBiorthogonal.PairingNorms
import Lean_Code.PositiveBiorthogonal.BasicLp
import Lean_Code.PositiveBiorthogonal.SupportObstruction
import Lean_Code.PositiveBiorthogonal.DualExpansion
import Lean_Code.PositiveBiorthogonal.Existence
import Lean_Code.PositiveBiorthogonal.CoefficientObstruction
import Lean_Code.PositiveBiorthogonal.VectorObstruction
import Lean_Code.PositiveBiorthogonal.FinitePolynomial
import Lean_Code.PositiveBiorthogonal.FiniteKernel
import Lean_Code.PositiveBiorthogonal.Auxiliary
import Lean_Code.PositiveBiorthogonal.EndpointAuxiliary
import Lean_Code.PositiveBiorthogonal.ToeplitzProjections
import Lean_Code.PositiveBiorthogonal.AuxiliaryExistence
import Lean_Code.PositiveBiorthogonal.Partitions
import Lean_Code.PositiveBiorthogonal.Averaging
import Lean_Code.PositiveBiorthogonal.PartitionRefinement
import Lean_Code.PositiveBiorthogonal.RefinementTrace
import Lean_Code.PositiveBiorthogonal.Schedule
import Lean_Code.PositiveBiorthogonal.UnitExtraction
import Lean_Code.PositiveBiorthogonal.LocalPositive
import Lean_Code.PositiveBiorthogonal.Flatten
import Lean_Code.PositiveBiorthogonal.CellSpans
import Lean_Code.PositiveBiorthogonal.IntervalDensity
import Lean_Code.PositiveBiorthogonal.FinalExistence

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

/-! Closed construction and obstruction branches are assembled in the public Showcase. -/
