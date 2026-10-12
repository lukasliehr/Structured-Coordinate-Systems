import Lean_Code.PositiveBiorthogonal.Interpretation

/-! `lem:basis-criterion`: dense biorthogonal systems and genuine basis constants. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PositiveBiorthogonal

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def initialProjection (v : ℕ → L 𝕜 p) (c : ℕ → L 𝕜 p →L[𝕜] 𝕜)
    (N : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  ∑ n ∈ Finset.range N, (c n).smulRight (v n)

@[simp] theorem initialProjection_apply (v : ℕ → L 𝕜 p)
    (c : ℕ → L 𝕜 p →L[𝕜] 𝕜) (N : ℕ) (f : L 𝕜 p) :
    initialProjection v c N f = ∑ n ∈ Finset.range N, c n f • v n := by
  simp [initialProjection]

theorem initialProjection_eventually_eq (v : ℕ → L 𝕜 p)
    (c : ℕ → L 𝕜 p →L[𝕜] 𝕜)
    (hbi : ∀ n l, c l (v n) = if n = l then 1 else 0)
    {f : L 𝕜 p} (hf : f ∈ Submodule.span 𝕜 (Set.range v)) :
    ∀ᶠ N in atTop, initialProjection v c N f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      filter_upwards [eventually_gt_atTop n] with N hN
      simp [initialProjection_apply, hbi, Finset.mem_range.mpr hN]
  | zero => exact Eventually.of_forall fun N => map_zero _
  | add x y _ _ hx hy =>
      filter_upwards [hx, hy] with N hxN hyN
      simp [map_add, hxN, hyN]
  | smul a x _ hx =>
      filter_upwards [hx] with N hxN
      simp [map_smul, hxN]

theorem basisCriterion_expansion (v : ℕ → L 𝕜 p)
    (c : ℕ → L 𝕜 p →L[𝕜] 𝕜)
    (hbi : ∀ n l, c l (v n) = if n = l then 1 else 0)
    (hdense : Dense (Submodule.span 𝕜 (Set.range v) : Set (L 𝕜 p)))
    (C : ℝ) (hC : ∀ N, ‖initialProjection v c N‖ ≤ C) (f : L 𝕜 p) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, c n f • v n) atTop (𝓝 f) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hCp : 0 < C + 1 := by linarith
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨h, hh, hdist⟩ := hdense.exists_dist_lt f (div_pos hε hCp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (initialProjection_eventually_eq v c hbi hh)
  refine ⟨N, fun n hn => ?_⟩
  have heq : initialProjection v c n f - f =
      initialProjection v c n (f - h) + (h - f) := by
    rw [map_sub, hN n hn]
    abel
  rw [← initialProjection_apply, dist_eq_norm, heq]
  calc
    ‖initialProjection v c n (f - h) + (h - f)‖ ≤
        ‖initialProjection v c n (f - h)‖ + ‖h - f‖ := norm_add_le _ _
    _ ≤ C * ‖f - h‖ + ‖h - f‖ := by
      gcongr
      exact ((initialProjection v c n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    _ = (C + 1) * dist f h := by rw [norm_sub_rev h f, dist_eq_norm]; ring
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hCp).mp hdist

def basisOfDenseSpan (v : ℕ → L 𝕜 p) (c : ℕ → L 𝕜 p →L[𝕜] 𝕜)
    (hbi : ∀ n l, c l (v n) = if n = l then 1 else 0)
    (hdense : Dense (Submodule.span 𝕜 (Set.range v) : Set (L 𝕜 p)))
    (C : ℝ) (hC : ∀ N, ‖initialProjection v c N‖ ≤ C) : SchauderBasis 𝕜 p where
  b := v
  coeff := c
  biorthogonal := hbi
  expansion := basisCriterion_expansion v c hbi hdense C hC

theorem one_le_firstProjection (B : SchauderBasis 𝕜 p) : 1 ≤ ‖P B 1‖ := by
  have hfix : P B 1 (B.b 0) = B.b 0 := by
    simp [StatementAudit.P_one, B.biorthogonal]
  have hnorm := (P B 1).le_opNorm (B.b 0)
  rw [hfix] at hnorm
  have hpos := norm_pos_iff.mpr (StatementAudit.basis_vector_ne_zero B 0)
  nlinarith

theorem projection_le_K (B : SchauderBasis 𝕜 p) (N : ℕ) : ‖P B N‖ ≤ K B :=
  le_ciSup (StatementAudit.projection_norms_bounded B) N

theorem K_le_of_projection_bound (B : SchauderBasis 𝕜 p) (C : ℝ)
    (hC : ∀ N, ‖P B N‖ ≤ C) : K B ≤ C :=
  ciSup_le hC

theorem one_lt_K_of_firstProjection (B : SchauderBasis 𝕜 p)
    (hB : 1 < ‖P B 1‖) : 1 < K B :=
  hB.trans_le (projection_le_K B 1)

end PositiveBiorthogonal
