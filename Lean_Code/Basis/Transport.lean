import Lean_Code.Basis.Criterion

/-!
# Transport and rescaling of Schauder bases

Generic constructions for Mathlib's `SchauderBasis 𝕜 X`.

* `StructuredBases.transport`: the image of a Schauder basis under a continuous linear
  equivalence `e : X ≃L[𝕜] Y`. Its vectors are `e (b n)`, its coordinates are
  `b.coord n ∘ e.symm` and its partial sum projections are `e ∘ b.proj N ∘ e.symm`
  (`transport_proj`).
* `StructuredBases.norm_transport_proj`: a linear isometric equivalence does not change
  the norms of the partial sum projections, hence not the basis constant
  (`nnnormProjBound_transport`).
* `StructuredBases.rescale`: multiplying the basis vectors by nonzero scalars gives a
  Schauder basis with the same partial sum projections (`rescale_proj`).
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace StructuredBases

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Transport along a continuous linear equivalence -/

section Transport

/-- The image of a Schauder basis under a continuous linear equivalence. -/
def transport (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Y) : SchauderBasis 𝕜 Y :=
  ofCoord (fun n => e (b n)) (fun n => (b.coord n).comp (e.symm : Y →L[𝕜] X))
    (fun n m => by simp [coord_apply_basis])
    (fun y => by
      have h := (e.continuous.tendsto (e.symm y)).comp (tendsto_expansion b (e.symm y))
      simpa [Function.comp_def, map_sum] using h)

variable (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Y)

@[simp] theorem transport_apply (n : ℕ) : transport b e n = e (b n) := rfl

theorem transport_coe : ⇑(transport b e) = fun n => e (b n) := rfl

theorem transport_coe' : ⇑(transport b e) = e ∘ b := rfl

@[simp] theorem transport_coord (n : ℕ) :
    (transport b e).coord n = (b.coord n).comp (e.symm : Y →L[𝕜] X) := rfl

theorem transport_coord_apply (n : ℕ) (y : Y) :
    (transport b e).coord n y = b.coord n (e.symm y) := rfl

/-- The partial sum projections of the transported basis are conjugates of the original
ones. -/
theorem transport_proj_apply (N : ℕ) (y : Y) :
    (transport b e).proj N y = e (b.proj N (e.symm y)) := by
  simp [map_sum]

theorem transport_proj (N : ℕ) :
    (transport b e).proj N =
      (e : X →L[𝕜] Y).comp ((b.proj N).comp (e.symm : Y →L[𝕜] X)) := by
  ext y
  simp [map_sum]

theorem transport_proj_apply_apply (N : ℕ) (x : X) :
    (transport b e).proj N (e x) = e (b.proj N x) := by
  rw [transport_proj_apply, e.symm_apply_apply]

/-- Transporting back and forth returns the original basis. -/
theorem transport_transport_symm : transport (transport b e) e.symm = b := by
  ext n
  · simp
  · simp

theorem norm_transport_proj_le (N : ℕ) :
    ‖(transport b e).proj N‖ ≤
      ‖(e : X →L[𝕜] Y)‖ * (‖b.proj N‖ * ‖(e.symm : Y →L[𝕜] X)‖) := by
  rw [transport_proj]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

/-- A uniform bound for the transported projections. -/
theorem norm_transport_proj_le_of_le {C : ℝ} (hC : ∀ N, ‖b.proj N‖ ≤ C) (N : ℕ) :
    ‖(transport b e).proj N‖ ≤
      ‖(e : X →L[𝕜] Y)‖ * (C * ‖(e.symm : Y →L[𝕜] X)‖) :=
  (norm_transport_proj_le b e N).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC N) (norm_nonneg _))
      (norm_nonneg _))

end Transport

/-! ### Transport along a linear isometric equivalence -/

section Isometry

variable (b : SchauderBasis 𝕜 X) (e : X ≃ₗᵢ[𝕜] Y)

theorem norm_transport_isometry_proj_le (N : ℕ) :
    ‖(transport b e.toContinuousLinearEquiv).proj N‖ ≤ ‖b.proj N‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  rw [transport_proj_apply]
  calc
    ‖e.toContinuousLinearEquiv (b.proj N (e.toContinuousLinearEquiv.symm y))‖ =
        ‖b.proj N (e.toContinuousLinearEquiv.symm y)‖ := e.norm_map _
    _ ≤ ‖b.proj N‖ * ‖e.toContinuousLinearEquiv.symm y‖ := (b.proj N).le_opNorm _
    _ = ‖b.proj N‖ * ‖y‖ := by
      congr 1
      exact e.symm.norm_map y

theorem le_norm_transport_isometry_proj (N : ℕ) :
    ‖b.proj N‖ ≤ ‖(transport b e.toContinuousLinearEquiv).proj N‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  calc
    ‖b.proj N x‖ = ‖e.toContinuousLinearEquiv (b.proj N x)‖ := (e.norm_map _).symm
    _ = ‖(transport b e.toContinuousLinearEquiv).proj N (e.toContinuousLinearEquiv x)‖ := by
      rw [transport_proj_apply_apply]
    _ ≤ ‖(transport b e.toContinuousLinearEquiv).proj N‖ * ‖e.toContinuousLinearEquiv x‖ :=
      ((transport b e.toContinuousLinearEquiv).proj N).le_opNorm _
    _ = ‖(transport b e.toContinuousLinearEquiv).proj N‖ * ‖x‖ := by
      congr 1
      exact e.norm_map x

/-- A linear isometric equivalence preserves the norms of the partial sum projections. -/
theorem norm_transport_proj (N : ℕ) :
    ‖(transport b e.toContinuousLinearEquiv).proj N‖ = ‖b.proj N‖ :=
  le_antisymm (norm_transport_isometry_proj_le b e N) (le_norm_transport_isometry_proj b e N)

/-- A linear isometric equivalence preserves the basis constant. -/
theorem nnnormProjBound_transport :
    (transport b e.toContinuousLinearEquiv).nnnormProjBound = b.nnnormProjBound := by
  unfold SchauderBasis.nnnormProjBound
  exact iSup_congr fun N => NNReal.eq (norm_transport_proj b e N)

/-- Existence form: the image of a Schauder basis under a linear isometric equivalence is
a Schauder basis with the same projection norms. -/
theorem exists_schauderBasis_of_isometryEquiv :
    ∃ b' : SchauderBasis 𝕜 Y, (∀ n, b' n = e (b n)) ∧
      (∀ n y, b'.coord n y = b.coord n (e.symm y)) ∧
      (∀ N y, b'.proj N y = e (b.proj N (e.symm y))) ∧ ∀ N, ‖b'.proj N‖ = ‖b.proj N‖ :=
  ⟨transport b e.toContinuousLinearEquiv, fun _ => rfl, fun _ _ => rfl,
    fun N y => transport_proj_apply b e.toContinuousLinearEquiv N y,
    fun N => norm_transport_proj b e N⟩

end Isometry

/-! ### Rescaling the basis vectors -/

section Rescale

/-- Multiplying the vectors of a Schauder basis by nonzero scalars. -/
def rescale (b : SchauderBasis 𝕜 X) (d : ℕ → 𝕜) (hd : ∀ n, d n ≠ 0) : SchauderBasis 𝕜 X :=
  ofCoord (fun n => d n • b n) (fun n => (d n)⁻¹ • b.coord n)
    (fun n m => by
      by_cases h : n = m
      · subst h
        simp [coord_apply_basis, hd n]
      · simp [coord_apply_basis, h])
    (fun x => by
      have h := tendsto_expansion b x
      refine h.congr fun N => Finset.sum_congr rfl fun n _ => ?_
      change b.coord n x • b n = ((d n)⁻¹ * b.coord n x) • d n • b n
      rw [smul_smul, mul_comm (d n)⁻¹, mul_assoc, inv_mul_cancel₀ (hd n), mul_one])

variable (b : SchauderBasis 𝕜 X) (d : ℕ → 𝕜) (hd : ∀ n, d n ≠ 0)

@[simp] theorem rescale_apply (n : ℕ) : rescale b d hd n = d n • b n := rfl

theorem rescale_coe : ⇑(rescale b d hd) = fun n => d n • b n := rfl

@[simp] theorem rescale_coord (n : ℕ) : (rescale b d hd).coord n = (d n)⁻¹ • b.coord n := rfl

theorem rescale_coord_apply (n : ℕ) (x : X) :
    (rescale b d hd).coord n x = (d n)⁻¹ * b.coord n x := rfl

/-- Rescaling the basis vectors does not change the partial sum projections. -/
theorem rescale_proj (N : ℕ) : (rescale b d hd).proj N = b.proj N := by
  ext x
  rw [SchauderBasis.proj_apply, SchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  change ((d n)⁻¹ * b.coord n x) • d n • b n = b.coord n x • b n
  rw [smul_smul, mul_comm (d n)⁻¹, mul_assoc, inv_mul_cancel₀ (hd n), mul_one]

theorem norm_rescale_proj (N : ℕ) : ‖(rescale b d hd).proj N‖ = ‖b.proj N‖ := by
  rw [rescale_proj]

/-- Rescaling the basis vectors does not change the basis constant. -/
theorem nnnormProjBound_rescale :
    (rescale b d hd).nnnormProjBound = b.nnnormProjBound := by
  unfold SchauderBasis.nnnormProjBound
  simp only [rescale_proj]

/-- Existence form of `rescale`. -/
theorem exists_schauderBasis_rescale (b : SchauderBasis 𝕜 X) (d : ℕ → 𝕜)
    (hd : ∀ n, d n ≠ 0) :
    ∃ b' : SchauderBasis 𝕜 X, (∀ n, b' n = d n • b n) ∧
      (∀ n x, b'.coord n x = (d n)⁻¹ * b.coord n x) ∧ ∀ N, b'.proj N = b.proj N :=
  ⟨rescale b d hd, fun _ => rfl, fun _ _ => rfl, rescale_proj b d hd⟩

end Rescale

end StructuredBases
