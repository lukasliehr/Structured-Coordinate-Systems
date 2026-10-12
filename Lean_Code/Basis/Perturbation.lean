import Lean_Code.Basis.Criterion
import Lean_Code.Basis.Transport

/-!
# Transport and small perturbations of Schauder bases

Everything here is stated for Mathlib's `SchauderBasis 𝕜 X`.

* (`StructuredBases.transport`, the image of a Schauder basis under a continuous linear
  equivalence, is defined in `Lean_Code/Basis/Transport.lean`.)
* `StructuredBases.norm_coord_le`: if all partial sum projections have norm at most `K`
  and all basis vectors have norm at least `c > 0`, the coordinate functionals have norm
  at most `2K/c`.
* `StructuredBases.exists_schauderBasis_of_summable_perturbation`: the classical small
  perturbation principle. If `∑ ‖a n - b n‖ < c / (2K)`, then `a` is a Schauder basis, and
  its basis constant is at most `K (1 + ρ) / (1 - ρ)` with `ρ = 2K ∑ ‖a n - b n‖ / c`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators NNReal

namespace StructuredBases

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Transport along a linear isometric equivalence -/

/-- Transport along a linear isometric equivalence does not change the norms of the
partial sum projections. -/
theorem norm_transport_proj_le_of_isometry (b : SchauderBasis 𝕜 X) (U : X ≃ₗᵢ[𝕜] Y)
    {K : ℝ} (hK : ∀ N, ‖b.proj N‖ ≤ K) (N : ℕ) :
    ‖(transport b U.toContinuousLinearEquiv).proj N‖ ≤ K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun y => ?_
  rw [transport_proj_apply]
  calc
    ‖U.toContinuousLinearEquiv (b.proj N (U.toContinuousLinearEquiv.symm y))‖
        = ‖b.proj N (U.toContinuousLinearEquiv.symm y)‖ := U.norm_map _
    _ ≤ ‖b.proj N‖ * ‖U.toContinuousLinearEquiv.symm y‖ := (b.proj N).le_opNorm _
    _ = ‖b.proj N‖ * ‖y‖ := by
      congr 1
      exact U.symm.norm_map y
    _ ≤ K * ‖y‖ := mul_le_mul_of_nonneg_right (hK N) (norm_nonneg _)

/-! ### The coordinate bound -/

/-- Coordinates of a Schauder basis with basis constant `≤ K` whose vectors have norm at
least `c`. -/
theorem norm_coord_le (b : SchauderBasis 𝕜 X) {K c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, c ≤ ‖b n‖) (hK : ∀ N, ‖b.proj N‖ ≤ K) (n : ℕ) :
    ‖b.coord n‖ ≤ 2 * K / c := by
  have hb : ‖b.coord n‖ * ‖b n‖ ≤ 2 * K := by
    calc
      ‖b.coord n‖ * ‖b n‖ = ‖(b.coord n).smulRight (b n)‖ :=
        (ContinuousLinearMap.norm_smulRight_apply _ _).symm
      _ = ‖b.proj (n + 1) - b.proj n‖ := by rw [proj_succ_sub]
      _ ≤ ‖b.proj (n + 1)‖ + ‖b.proj n‖ := norm_sub_le _ _
      _ ≤ K + K := add_le_add (hK _) (hK _)
      _ = 2 * K := by ring
  exact (le_div_iff₀ hc).mpr
    ((mul_le_mul_of_nonneg_left (hlower n) (norm_nonneg _)).trans hb)

/-! ### Small perturbations -/

/-- **Small perturbation principle.** Let `b` be a Schauder basis of a Banach space with
`‖b.proj N‖ ≤ K` for all `N` and `‖b n‖ ≥ c > 0` for all `n`. Every sequence `a` with
`∑ ‖a n - b n‖ < c / (2K)` is a Schauder basis, with basis constant at most
`K (1 + ρ) / (1 - ρ)`, `ρ = 2K ∑ ‖a n - b n‖ / c`. -/
theorem exists_schauderBasis_of_summable_perturbation [CompleteSpace X]
    (b : SchauderBasis 𝕜 X) {K c : ℝ} (hc : 0 < c) (hlower : ∀ n, c ≤ ‖b n‖)
    (hK : ∀ N, ‖b.proj N‖ ≤ K) (a : ℕ → X)
    (hs : Summable fun n => ‖a n - b n‖) (hlt : ∑' n, ‖a n - b n‖ < c / (2 * K)) :
    ∃ b' : SchauderBasis 𝕜 X, ⇑b' = a ∧ ∀ N, ‖b'.proj N‖ ≤
      K * (1 + 2 * K * (∑' n, ‖a n - b n‖) / c) / (1 - 2 * K * (∑' n, ‖a n - b n‖) / c) := by
  classical
  have hK1 : 1 ≤ K := (one_le_norm_proj b one_pos).trans (hK 1)
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  set s := ∑' n, ‖a n - b n‖ with hs_def
  have hs0 : 0 ≤ s := tsum_nonneg fun _ => norm_nonneg _
  set ρ := 2 * K * s / c with hρ_def
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ_def, div_lt_one hc]
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp hlt
    linarith
  let T : ℕ → X →L[𝕜] X := fun n => (b.coord n).smulRight (a n - b n)
  have hnorm (n : ℕ) : ‖T n‖ = ‖b.coord n‖ * ‖a n - b n‖ :=
    ContinuousLinearMap.norm_smulRight_apply _ _
  have hbound (n : ℕ) : ‖T n‖ ≤ (2 * K / c) * ‖a n - b n‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (norm_coord_le b hc hlower hK n) (norm_nonneg _)
  have hmajor : Summable fun n => (2 * K / c) * ‖a n - b n‖ := hs.mul_left _
  have hsT : Summable fun n => ‖T n‖ :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hsum : Summable T := hsT.of_norm
  let E : X →L[𝕜] X := ∑' n, T n
  have hE : ‖E‖ ≤ ρ := by
    calc
      ‖E‖ ≤ ∑' n, ‖T n‖ := norm_tsum_le_tsum_norm hsT
      _ ≤ ∑' n, (2 * K / c) * ‖a n - b n‖ := hsT.tsum_le_tsum hbound hmajor
      _ = (2 * K / c) * s := tsum_mul_left
      _ = ρ := by rw [hρ_def]; ring
  have hE1 : ‖E‖ < 1 := hE.trans_lt hρ1
  have hu : IsUnit (1 + E) := by
    simpa using (isUnit_one_sub_of_norm_lt_one (x := -E) (by simpa using hE1))
  let U : X ≃L[𝕜] X := ContinuousLinearEquiv.unitsEquiv 𝕜 X hu.unit
  have hU (z : X) : U z = z + E z := by
    change (hu.unit : X →L[𝕜] X) z = z + E z
    rw [hu.unit_spec]
    rfl
  have hEb (m : ℕ) : E (b m) = a m - b m := by
    have hmap := (ContinuousLinearMap.apply 𝕜 X (b m)).map_tsum hsum
    change (∑' n, T n) (b m) = ∑' n, T n (b m) at hmap
    change (∑' n, T n) (b m) = a m - b m
    rw [hmap]
    have hterm (n : ℕ) : T n (b m) = if n = m then a m - b m else 0 := by
      simp only [T, ContinuousLinearMap.smulRight_apply, coord_apply_basis]
      split <;> simp_all
    simp only [hterm]
    exact tsum_ite_eq m (fun _ => a m - b m)
  have hatom (m : ℕ) : U (b m) = a m := by
    rw [hU, hEb]
    abel
  have hUle (z : X) : ‖U z‖ ≤ (1 + ρ) * ‖z‖ := by
    rw [hU]
    calc
      ‖z + E z‖ ≤ ‖z‖ + ‖E z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ρ * ‖z‖ :=
        add_le_add le_rfl ((E.le_opNorm z).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _)))
      _ = (1 + ρ) * ‖z‖ := by ring
  have hUge (z : X) : (1 - ρ) * ‖z‖ ≤ ‖U z‖ := by
    rw [hU]
    have h1 : ‖z‖ - ‖E z‖ ≤ ‖z + E z‖ := by
      have := norm_sub_norm_le z (-(E z))
      simpa [sub_neg_eq_add] using this
    have h2 : ‖E z‖ ≤ ρ * ‖z‖ :=
      (E.le_opNorm z).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
    linarith
  have hρpos : 0 < 1 - ρ := by linarith
  refine ⟨transport b U, funext hatom, fun N => ?_⟩
  have hbound0 : 0 ≤ K * (1 + ρ) / (1 - ρ) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hbound0 fun y => ?_
  rw [transport_proj_apply]
  have hsymm : ‖U.symm y‖ ≤ ‖y‖ / (1 - ρ) := by
    rw [le_div_iff₀ hρpos]
    have := hUge (U.symm y)
    rw [U.apply_symm_apply] at this
    linarith
  calc
    ‖U (b.proj N (U.symm y))‖ ≤ (1 + ρ) * ‖b.proj N (U.symm y)‖ := hUle _
    _ ≤ (1 + ρ) * (K * ‖U.symm y‖) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact ((b.proj N).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK N) (norm_nonneg _))
    _ ≤ (1 + ρ) * (K * (‖y‖ / (1 - ρ))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hsymm hKpos.le
    _ = K * (1 + ρ) / (1 - ρ) * ‖y‖ := by ring

end StructuredBases
