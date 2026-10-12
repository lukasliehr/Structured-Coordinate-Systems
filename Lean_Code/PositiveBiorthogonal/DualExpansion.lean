import Lean_Code.PositiveBiorthogonal.PairingNorms
import Lean_Code.PositiveBiorthogonal.BasisCriterion

/-! The weak dual series is a consequence of any represented basis expansion. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def dualProjection (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q) (N : ℕ) :
    L 𝕜 q →L[𝕜] L 𝕜 q :=
  ∑ n ∈ Finset.range N, (pairingCLM (B.b n)).smulRight (γ n)

@[simp] theorem dualProjection_apply (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (N : ℕ) (g : L 𝕜 q) :
    dualProjection B γ N g = ∑ n ∈ Finset.range N, pairing (B.b n) g • γ n := by
  simp [dualProjection]

theorem pairing_projection (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (N : ℕ) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing (P B N f) g =
      ∑ n ∈ Finset.range N, pairing (B.b n) g * pairing f (γ n) := by
  rw [← representedFunctional_apply g (P B N f)]
  unfold Represents at hγ
  simp [StatementAudit.P_apply, map_sum, map_smul, hγ, mul_comm]

theorem dual_projection_paired (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (N : ℕ) (f : L 𝕜 p) (g : L 𝕜 q) :
    pairing f (dualProjection B γ N g) = pairing (P B N f) g := by
  have hpq : 1 / p + 1 / q = 1 := by
    simpa only [one_div] using ENNReal.HolderConjugate.inv_add_inv_eq_one p q
  rw [dualProjection_apply, StatementAudit.dual_test_identity hpq,
    pairing_projection B γ hγ]

theorem dual_weak (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (g : L 𝕜 q) (f : L 𝕜 p) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, pairing (B.b n) g * pairing f (γ n))
      atTop (𝓝 (pairing f g)) := by
  have h := (pairing_continuous_left g).tendsto f |>.comp
    (StatementAudit.partial_projections_converge B f)
  simpa only [Function.comp_def, pairing_projection B γ hγ] using h

theorem dualProjection_norm (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ) (N : ℕ) :
    ‖dualProjection B γ N‖ = ‖P B N‖ := by
  exact (paired_operator_norm_eq (P B N) (dualProjection B γ N)
    (fun f g => (dual_projection_paired B γ hγ N f g).symm)).symm

/-- The construction's coefficient-density obligation is sufficient to produce
the dual norm basis, with exactly the original coefficient sequence. -/
def dualBasisOfDense (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ)
    (hdense : Dense (Submodule.span 𝕜 (Set.range γ) : Set (L 𝕜 q))) :
    SchauderBasis 𝕜 q :=
  basisOfDenseSpan γ (fun n => pairingCLM (B.b n))
    (fun n l => by
      simpa only [pairingCLM_apply, eq_comm] using
        represented_pairing_biorthogonal B γ hγ l n)
    hdense (K B) (fun N => by
      change ‖dualProjection B γ N‖ ≤ K B
      rw [dualProjection_norm B γ hγ]
      exact projection_le_K B N)

@[simp] theorem dualBasisOfDense_vector (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ)
    (hdense : Dense (Submodule.span 𝕜 (Set.range γ) : Set (L 𝕜 q))) (n : ℕ) :
    (dualBasisOfDense B γ hγ hdense).b n = γ n := rfl

@[simp] theorem dualBasisOfDense_coeff (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ)
    (hdense : Dense (Submodule.span 𝕜 (Set.range γ) : Set (L 𝕜 q))) (n : ℕ) (g : L 𝕜 q) :
    (dualBasisOfDense B γ hγ hdense).coeff n g = pairing (B.b n) g :=
  pairingCLM_apply (B.b n) g

theorem dualBasisOfDense_constant (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ)
    (hdense : Dense (Submodule.span 𝕜 (Set.range γ) : Set (L 𝕜 q))) :
    K (dualBasisOfDense B γ hγ hdense) = K B := by
  unfold K
  congr 1
  funext N
  exact dualProjection_norm B γ hγ N

theorem dualBasisOfDense_positive (B : SchauderBasis 𝕜 p)
    (γ : ℕ → L 𝕜 q) (hγ : Represents B γ)
    (hdense : Dense (Submodule.span 𝕜 (Set.range γ) : Set (L 𝕜 q)))
    (hpos : ∀ n, Nonnegative (γ n)) :
    PositiveBasis (dualBasisOfDense B γ hγ hdense) := hpos

end PositiveBiorthogonal
