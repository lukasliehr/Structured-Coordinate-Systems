import Lean_Code.PositiveBiorthogonal.MainTheorem

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder
namespace PositiveBiorthogonal
local notation "⟨" f ", " g "⟩" => pairing f g

/-!
## The main result, separated into six statements

`Fact (1 ≤ p)` and `Fact (1 ≤ q)` supply the normed-space instances for Lᵖ and
Lᑫ. The conjugacy equation includes q = ∞ when p = 1, since 1 / ∞ = 0.
`eLpNorm (γ n) ∞ volume = 1` is exactly ‖γ_n‖_∞ = 1.
All six statements hold over either scalar field.
-/

/-- Existence and dual expansion for the same basis and coefficient functions.
The coefficients are normalized, nonnegative, compactly supported step
functions, and the basis constant is less than 1 + ε.
The scalar partial-sum limit tested against every f ∈ Lᵖ states convergence
in σ(Lᑫ,Lᵖ); at p = 1 this is weak-star convergence. For p > 1 the second
Schauder basis supplies norm convergence of the same dual series.
-/
theorem exists_almost_monotone_basis_with_positive_biorthogonal
    (𝕜 : Type*) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p < ∞) (hpq : 1 / p + 1 / q = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q),
      (∀ n, CompactlySupportedStep (γ n)) ∧
      (∀ n, ∀ᵐ x : ℝ, 0 ≤ γ n x ∧ γ n x ≤ 1) ∧
      (∀ n, eLpNorm (γ n) ∞ volume = 1) ∧
      Represents B γ ∧
      (∀ n l, ⟨B.b n, γ l⟩ = if n = l then 1 else 0) ∧
      (∀ f : L 𝕜 p,
        Tendsto (fun N => ∑ n ∈ Finset.range N, ⟨f, γ n⟩ • B.b n) atTop (𝓝 f)) ∧
      K B < 1 + ε ∧
      (∀ (g : L 𝕜 q) (f : L 𝕜 p),
        Tendsto (fun N => ∑ n ∈ Finset.range N, ⟨B.b n, g⟩ * ⟨f, γ n⟩)
          atTop (𝓝 ⟨f, g⟩)) ∧
      (1 < p → ∃ Γ : SchauderBasis 𝕜 q,
        (∀ n, Γ.b n = γ n) ∧
        (∀ n (g : L 𝕜 q), Γ.coeff n g = ⟨B.b n, g⟩) ∧
        PositiveBasis Γ ∧ K Γ = K B) := by
  let := StatementAudit.conjugate_instance hpq
  exact almost_monotone_existence hp.ne ε hε

/-- For 1 ≤ p < ∞, a basis with positive biorthogonal functionals cannot
have a contractive first coordinate projection. -/
theorem first_projection_not_contractive_of_positive_biorthogonal
    (𝕜 : Type*) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p < ∞) (hpq : 1 / p + 1 / q = 1)
    (B : SchauderBasis 𝕜 p) (hB : HasPositiveBiorthogonal q B) :
    1 < ‖P B 1‖ := by
  let := StatementAudit.conjugate_instance hpq
  obtain ⟨γ, hγ, hpos⟩ := hB
  exact coefficient_first_projection_strict hp.ne B γ hγ hpos

/-- For 1 ≤ p < ∞, the sharp infimum of basis constants for bases with
positive biorthogonal functionals is one and is not attained.
`IsGLB S 1` means that 1 is the greatest lower bound of S. -/
theorem sharp_infimum_positive_biorthogonal
    (𝕜 : Type*) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p < ∞) (hpq : 1 / p + 1 / q = 1) :
    IsGLB (biorthogonalConstants 𝕜 p q) 1 ∧
      1 ∉ biorthogonalConstants 𝕜 p q := by
  constructor
  · apply isGLB_one_of_approach
    · rintro k ⟨B, _, rfl⟩
      exact StatementAudit.K_ge_one B
    · intro ε hε
      let := StatementAudit.conjugate_instance hpq
      let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
      obtain ⟨B, γ, _, hpos, _, hrep, _, _, hK, _, _⟩ :=
        exists_almost_monotone_basis_with_positive_biorthogonal 𝕜 p q hp hpq ε hε
      exact ⟨K B, ⟨B, ⟨γ, hrep, fun n => (hpos n).mono fun _ hx => hx.1⟩, rfl⟩, hK⟩
  · rintro ⟨B, hB, hK⟩
    have hstrict := first_projection_not_contractive_of_positive_biorthogonal 𝕜 p q hp hpq B hB
    have hle := projection_le_K B 1
    rw [hK] at hle
    exact hstrict.not_ge hle

/-- For 1 < p < ∞, positive Schauder bases consisting of compactly supported
step functions can have basis constant arbitrarily close to one. -/
theorem exists_almost_monotone_positive_basis
    (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : SchauderBasis 𝕜 p,
      PositiveBasis B ∧ (∀ n, CompactlySupportedStep (B.b n)) ∧ K B < 1 + ε := by
  obtain ⟨q, hpq⟩ := StatementAudit.conjugate_exists hp₁.le
  let := StatementAudit.conjugate_instance hpq
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q < ∞ := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp₁
  have hq₁ : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp
  obtain ⟨B, γ, hstep, _, _, _, _, _, hK, _, hdual⟩ :=
    exists_almost_monotone_basis_with_positive_biorthogonal 𝕜 q p hq
      (by simpa only [add_comm] using hpq) ε hε
  obtain ⟨Γ, hvec, _, hpos, hconst⟩ := hdual hq₁
  refine ⟨Γ, hpos, ?_, ?_⟩
  · intro n
    rw [hvec n]
    exact hstep n
  · rw [hconst]
    exact hK

/-- For 1 < p < ∞, a positive Schauder basis cannot have a contractive
first coordinate projection. -/
theorem first_projection_not_contractive_of_positive_basis
    (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p < ∞)
    (B : SchauderBasis 𝕜 p) (hB : PositiveBasis B) :
    1 < ‖P B 1‖ := by
  exact positive_first_projection_strict hp₁ hp.ne B hB

/-- For 1 < p < ∞, the sharp infimum of basis constants for positive
Schauder bases is one and is not attained. -/
theorem sharp_infimum_positive_bases
    (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p < ∞) :
    IsGLB (positiveConstants 𝕜 p) 1 ∧ 1 ∉ positiveConstants 𝕜 p := by
  constructor
  · apply isGLB_one_of_approach
    · rintro k ⟨B, _, rfl⟩
      exact StatementAudit.K_ge_one B
    · intro ε hε
      obtain ⟨B, hB, _, hK⟩ := exists_almost_monotone_positive_basis 𝕜 p hp₁ hp ε hε
      exact ⟨K B, ⟨B, hB, rfl⟩, hK⟩
  · rintro ⟨B, hB, hK⟩
    have hstrict := first_projection_not_contractive_of_positive_basis 𝕜 p hp₁ hp B hB
    have hle := projection_le_K B 1
    rw [hK] at hle
    exact hstrict.not_ge hle

end PositiveBiorthogonal
