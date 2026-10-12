import Lean_Code.PositiveBiorthogonal.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Order.LiminfLimsup

/-!
Semantic checks ported from audit/StatementChecks.lean to the shared definitions.
The historical admitted reference is never imported.
These lemmas check interpretation; they do not prove any of the six main results.
No theorem with an admitted proof is used in the lemmas below.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder
open PositiveBiorthogonal

namespace StatementAudit

theorem conjugate_instance {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1) :
    ENNReal.HolderConjugate p q := by
  constructor
  simpa using hpq

theorem conjugate_range {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1) :
    1 ≤ p ∧ 1 ≤ q ∧ (q = ∞ ↔ p = 1) ∧ (q < ∞ ↔ 1 < p) := by
  let := conjugate_instance hpq
  exact ⟨ENNReal.HolderConjugate.one_le p q,
    ENNReal.HolderConjugate.one_le q p,
    ENNReal.HolderConjugate.eq_top_iff_eq_one q p,
    ENNReal.HolderConjugate.lt_top_iff_one_lt q p⟩

theorem conjugate_unique {p q r : ℝ≥0∞}
    (hpq : 1 / p + 1 / q = 1) (hpr : 1 / p + 1 / r = 1) : q = r := by
  let := conjugate_instance hpq
  let := conjugate_instance hpr
  exact ENNReal.HolderConjugate.unique p q r

theorem conjugate_exists {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∃ q : ℝ≥0∞, 1 / p + 1 / q = 1 := by
  refine ⟨(1 - p⁻¹)⁻¹, ?_⟩
  simp only [one_div, inv_inv]
  have hi : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv.mpr hp)
  exact add_tsub_cancel_of_le hi

theorem positivity_means_real_nonnegative {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} (f : L 𝕜 p) :
    Nonnegative f ↔ ∀ᵐ x : ℝ, 0 ≤ RCLike.re (f x) ∧ RCLike.im (f x) = 0 := by
  change (∀ᵐ x : ℝ, 0 ≤ f x) ↔ _
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    RCLike.nonneg_iff (z := f x))

theorem normalization_is_essential_supremum {𝕜 : Type*} [RCLike 𝕜]
    {q : ℝ≥0∞} (g : L 𝕜 q) :
    eLpNorm g ∞ volume = essSup (fun x : ℝ => ‖g x‖ₑ) volume := by
  rfl

theorem pairing_is_integrable {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1) (f : L 𝕜 p) (g : L 𝕜 q) :
    Integrable (fun x : ℝ => f x * g x) volume := by
  let := conjugate_instance hpq
  exact (Lp.memLp f).integrable_mul (Lp.memLp g)

theorem pairing_add_right {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1)
    (f : L 𝕜 p) (g h : L 𝕜 q) :
    pairing f (g + h) = pairing f g + pairing f h := by
  unfold pairing
  calc
    (∫ x : ℝ, f x * (g + h) x) = ∫ x : ℝ, f x * g x + f x * h x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add g h] with x hx
      simp only [hx, Pi.add_apply, mul_add]
    _ = _ := integral_add (pairing_is_integrable hpq f g) (pairing_is_integrable hpq f h)

theorem pairing_smul_right {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (f : L 𝕜 p) (g : L 𝕜 q) (c : 𝕜) :
    pairing f (c • g) = c * pairing f g := by
  unfold pairing
  calc
    (∫ x : ℝ, f x * (c • g) x) = ∫ x : ℝ, c * (f x * g x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c g] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    _ = _ := integral_const_mul c _

theorem pairing_zero_right {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (f : L 𝕜 p) : pairing f (0 : L 𝕜 q) = 0 := by
  unfold pairing
  calc
    (∫ x : ℝ, f x * (0 : L 𝕜 q) x) = ∫ _ : ℝ, (0 : 𝕜) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero 𝕜 q (volume : Measure ℝ)] with x hx
      simp only [hx, Pi.zero_apply, mul_zero]
    _ = 0 := integral_zero _ _

theorem dual_test_identity {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1)
    (b : ℕ → L 𝕜 p) (γ : ℕ → L 𝕜 q)
    (g : L 𝕜 q) (f : L 𝕜 p) (N : ℕ) :
    pairing f (∑ n ∈ Finset.range N, pairing (b n) g • γ n) =
      ∑ n ∈ Finset.range N, pairing (b n) g * pairing f (γ n) := by
  induction N with
  | zero => simp [pairing_zero_right]
  | succ N ih =>
      simp only [Finset.sum_range_succ, pairing_add_right hpq,
        pairing_smul_right, ih]

/-- The mathematical definition of σ(Lᑫ,Lᵖ): the topology induced by all
pairings with elements of Lᵖ, into the product of copies of the scalar field. -/
@[instance_reducible]
def sigmaTopology (𝕜 : Type*) [RCLike 𝕜] (p q : ℝ≥0∞) :
    TopologicalSpace (L 𝕜 q) :=
  TopologicalSpace.induced (fun g : L 𝕜 q => fun f : L 𝕜 p => pairing f g)
    inferInstance

theorem scalar_test_iff_sigma_convergence {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} (hpq : 1 / p + 1 / q = 1)
    (b : ℕ → L 𝕜 p) (γ : ℕ → L 𝕜 q) (g : L 𝕜 q) :
    (∀ f : L 𝕜 p,
      Tendsto (fun N => ∑ n ∈ Finset.range N, pairing (b n) g * pairing f (γ n))
        atTop (𝓝 (pairing f g))) ↔
    Tendsto (fun N => ∑ n ∈ Finset.range N, pairing (b n) g • γ n)
      atTop (@nhds _ (sigmaTopology 𝕜 p q) g) := by
  rw [sigmaTopology, nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  simp only [Function.comp_apply, dual_test_identity hpq]

theorem P_apply {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) (N : ℕ) (f : L 𝕜 p) :
    P B N f = ∑ n ∈ Finset.range N, B.coeff n f • B.b n := by
  simp [P]

theorem P_zero {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) : P B 0 = 0 := by
  simp [P]

theorem P_one {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) (f : L 𝕜 p) :
    P B 1 f = B.coeff 0 f • B.b 0 := by
  simp [P_apply]

theorem basis_vector_ne_zero {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p) (n : ℕ) : B.b n ≠ 0 := by
  intro h
  have hbi := B.biorthogonal n n
  simp [h] at hbi

theorem partial_projections_converge {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p) (f : L 𝕜 p) :
    Tendsto (fun N => P B N f) atTop (𝓝 f) := by
  simpa only [P_apply] using B.expansion f

theorem projection_norms_bounded {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p) :
    BddAbove (Set.range fun N => ‖P B N‖) := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := P B) (fun f => by
    obtain ⟨C, hC⟩ := (partial_projections_converge B f).norm.bddAbove_range
    exact ⟨C, fun N => hC (Set.mem_range_self N)⟩)
  exact ⟨C, by rintro _ ⟨N, rfl⟩; exact hC N⟩

theorem K_is_supremum {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p) :
    IsLUB (Set.range fun N => ‖P B N‖) (K B) := by
  exact isLUB_ciSup (projection_norms_bounded B)

theorem K_ge_one {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p) : 1 ≤ K B := by
  have hfix : P B 1 (B.b 0) = B.b 0 := by
    simp [P_one, B.biorthogonal]
  have hnorm := (P B 1).le_opNorm (B.b 0)
  rw [hfix] at hnorm
  have hpos : 0 < ‖B.b 0‖ := norm_pos_iff.mpr (basis_vector_ne_zero B 0)
  have hone : 1 ≤ ‖P B 1‖ := by nlinarith
  exact hone.trans (le_ciSup (projection_norms_bounded B) 1)

theorem coefficient_of_convergent_series {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : SchauderBasis 𝕜 p)
    (a : ℕ → 𝕜) (f : L 𝕜 p)
    (ha : Tendsto (fun N => ∑ n ∈ Finset.range N, a n • B.b n) atTop (𝓝 f))
    (j : ℕ) : a j = B.coeff j f := by
  have ht := (B.coeff j).continuous.tendsto f |>.comp ha
  have he : (fun N => B.coeff j (∑ n ∈ Finset.range N, a n • B.b n))
      =ᶠ[atTop] (fun _ => a j) := by
    filter_upwards [eventually_gt_atTop j] with N hN
    simp [map_sum, B.biorthogonal, Finset.mem_range.mpr hN]
  exact tendsto_nhds_unique tendsto_const_nhds (ht.congr' he)

theorem dual_basis_supplies_same_norm_series {𝕜 : Type*} [RCLike 𝕜]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q) (Γ : SchauderBasis 𝕜 q)
    (hvec : ∀ n, Γ.b n = γ n)
    (hcoeff : ∀ n (g : L 𝕜 q), Γ.coeff n g = pairing (B.b n) g)
    (g : L 𝕜 q) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, pairing (B.b n) g • γ n)
      atTop (𝓝 g) := by
  simpa only [hvec, hcoeff] using Γ.expansion g

end StatementAudit

