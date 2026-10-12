import Lean_Code.PositiveBiorthogonal.FiniteKernel

/-! The exact finite auxiliary-family data. Existence is a separate proof obligation. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped ENNReal Topology BigOperators ComplexOrder

namespace PositiveBiorthogonal

/-- Source `def:auxiliary`, with every finite space carrying its stated exponent.
The zero-dimensional member is allowed and is excluded from the finite requirements.
No existence of this structure is assumed. -/
structure AuxiliaryFamily (𝕜 : Type*) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (δ : ℝ) where
  M : ℝ
  M_ge_one : 1 ≤ M
  d : ∀ N : ℕ, Fin (2 * N) → FiniteLp 𝕜 p (2 * N)
  s : ∀ N : ℕ, Fin (2 * N) → FiniteLp 𝕜 q (2 * N)
  z : ∀ N : ℕ, FiniteLp 𝕜 p (2 * N)
  biorthogonal : ∀ N : ℕ, 0 < N → ∀ i j : Fin (2 * N),
    finitePairing (d N i) (s N j) = if i = j then 1 else 0
  primal_span : ∀ N : ℕ, 0 < N → Submodule.span 𝕜 (Set.range (d N)) = ⊤
  dual_span : ∀ N : ℕ, 0 < N → Submodule.span 𝕜 (Set.range (s N)) = ⊤
  s_nonneg : ∀ N : ℕ, 0 < N → ∀ j i : Fin (2 * N), 0 ≤ s N j i
  s_norm_le : ∀ N : ℕ, 0 < N → ∀ j : Fin (2 * N), ‖s N j‖ ≤ M
  projection_bound : ∀ N : ℕ, 0 < N → ∀ h : ℕ, h ≤ 2 * N →
    ‖finiteRankProjection (d N) (s N) h‖ ≤ 1 + δ
  z_nonneg : ∀ N : ℕ, 0 < N → ∀ i : Fin (2 * N), 0 ≤ z N i
  z_pairing : ∀ N : ℕ, 0 < N → ∀ j : Fin (2 * N), j.val < N →
    1 ≤ finitePairing (z N) (s N j)
  small_correction : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / p.toReal)) * ‖z N‖) atTop (𝓝 0)

end PositiveBiorthogonal
