import Lean_Code.SchauderTranslates.ProductPoly
import Lean_Code.SchauderTranslates.Sharp.SelectivePrefixSharp

/-!
# The sharp finite extension in the normalized product law

Sharp counterpart of `ProductModel.lean` (paper: `h2:eq:tagcapture`, `h2:eq:new-constant`,
`h2:eq:angle-comparison`, `h2:eq:product-error`). The tag stage `TagSetup.Valid` is reused
unchanged. The engine stage has a new validity predicate `ValidSharp`, since the old
`EngineSetup.Valid` fixes the per-replica strength `n j ∈ [1/10, 11/100]`, whereas here it
is of size `u`.

* `replica_witness_sharp`: with total strength `n j · N α² ≥ u` and `N α² ≥ 1` the common
  multiple of the engine witnesses captures the fraction `c_* = u / (1 + 2u)` of the residual.
* `EngineSetup.fast_prefix_sharp`: the sharp centered prefix bound of every engine.
* `EngineSetup.model_main_sharp`: independence, prefix bound
  `(1+ρ)/(1−ρ) · max(K², (1+λ) Q_c)` and squared error `≤ (1 − c_*) ‖r‖²`.
* The raw kernel is a mixed trigonometric polynomial under `ValidSharp`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction ProductEngines

section Witness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The replica witness with sharp bookkeeping (paper `h2:eq:tagcapture`): if the engines
of each replica realize `j • e_i` at centered cost `j`, a common real multiple of the
witnesses captures the fraction `u / (1 + 2u)` of `r` as soon as `u ≤ n j · N α²` and
`1 ≤ N α²`. -/
theorem replica_witness_sharp {N n q : ℕ} (e : Fin N → H) {α F j u : ℝ}
    (hα1 : α ^ 2 ≤ 1)
    (he1 : ∀ i, ‖e i‖ = 1) (he2 : ∀ i i', i ≠ i' → ⟪e i, e i'⟫_ℂ = ((α ^ 2 : ℝ) : ℂ))
    (r : H) (hr : ‖r‖ = F) (her : ∀ i, ⟪e i, r⟫_ℂ = ((α * F : ℝ) : ℂ))
    (T R : Fin (N * n) → Fin q → H)
    (hwit : ∀ c, ∃ b : Fin q → ℂ, ∑ p, b p • T c p = (j : ℂ) • e (finProdFinEquiv.symm c).1 ∧
      ‖∑ p, b p • R c p‖ ^ 2 = j)
    (hu : 0 < u) (hQ0 : 0 ≤ (n : ℝ) * j) (hβ : 1 ≤ (N : ℝ) * α ^ 2)
    (hQ : u ≤ n * j * (N * α ^ 2)) :
    ∃ b : Fin (N * n) → Fin q → ℂ,
      ‖r - ∑ c, ∑ p, b c p • T c p‖ ^ 2 + ∑ c, ‖∑ p, b c p • R c p‖ ^ 2 ≤
        (1 - u / (1 + 2 * u)) * F ^ 2 := by
  choose w hwT hwR using hwit
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = α * F / (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) := ⟨_, rfl⟩
  refine ⟨fun c p => (L : ℂ) * w c p, ?_⟩
  have hT1 : ∀ c, ∑ p, ((L : ℂ) * w c p) • T c p =
      ((L * j : ℝ) : ℂ) • e (finProdFinEquiv.symm c).1 := by
    intro c
    simp only [mul_smul, ← Finset.smul_sum, hwT c]
    rw [smul_smul, ← Complex.ofReal_mul]
  have hcount : ∑ c : Fin (N * n), e (finProdFinEquiv.symm c).1 = (n : ℂ) • ∑ i, e i := by
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun x : Fin N × Fin n => e x.1),
      Fintype.sum_prod_type, Finset.smul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hTsum : ∑ c, ∑ p, ((L : ℂ) * w c p) • T c p = ((L * j * n : ℝ) : ℂ) • ∑ i, e i := by
    simp only [hT1, ← Finset.smul_sum, hcount, smul_smul]
    push_cast
    rfl
  have hRsum : ∑ c, ‖∑ p, ((L : ℂ) * w c p) • R c p‖ ^ 2 = N * n * (L ^ 2 * j) := by
    have h1 : ∀ c, ‖∑ p, ((L : ℂ) * w c p) • R c p‖ ^ 2 = L ^ 2 * j := by
      intro c
      simp only [mul_smul, ← Finset.smul_sum, norm_smul, mul_pow, hwR c, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hss : ‖∑ i, e i‖ ^ 2 = (1 - α ^ 2) * N + α ^ 2 * N ^ 2 := by
    have h := equiangular_norm_sq_sum e he1 he2 (fun _ => 1)
    simp only [one_smul, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.norm_natCast] at h
    rw [h]
  have hrs : ⟪r, ∑ i, e i⟫_ℂ = ((N * (α * F) : ℝ) : ℂ) := by
    have h1 : ∀ i, ⟪r, e i⟫_ℂ = ((α * F : ℝ) : ℂ) := fun i => by
      rw [← inner_conj_symm, her, Complex.conj_ofReal]
    simp only [inner_sum, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hV : ‖r - ((L * j * n : ℝ) : ℂ) • ∑ i, e i‖ ^ 2 =
      F ^ 2 - 2 * ((L * j * n) * (N * (α * F))) +
        (L * j * n) ^ 2 * ((1 - α ^ 2) * N + α ^ 2 * N ^ 2) := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hrs, hr, norm_smul, mul_pow, hss,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_mul,
      RCLike.re_to_complex, Complex.ofReal_re]
  rw [hTsum, hRsum, hV]
  -- the scalar optimization: the value is `F ^ 2 * (1 - X / D)` with `u D ≤ (1 + 2u) X`
  have h1α : 0 ≤ 1 - α ^ 2 := by linarith
  have hD : 0 < 1 + n * j * (1 - α ^ 2 + N * α ^ 2) := by
    have : 0 ≤ (n : ℝ) * j * (1 - α ^ 2 + N * α ^ 2) :=
      mul_nonneg hQ0 (by linarith)
    linarith
  have hLD : L * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) = α * F := by
    rw [hL, div_mul_cancel₀ _ hD.ne']
  have hval : F ^ 2 - 2 * ((L * j * n) * (N * (α * F))) +
      (L * j * n) ^ 2 * ((1 - α ^ 2) * N + α ^ 2 * N ^ 2) + N * n * (L ^ 2 * j) =
      F ^ 2 - L * (n * j * N * α * F) := by
    linear_combination (L * j * n * N) * hLD
  rw [hval]
  have h2u : 0 < 1 + 2 * u := by linarith
  -- `u * D ≤ (1 + 2u) * (n j N α²)`
  have key : u * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) ≤
      (1 + 2 * u) * (n * j * (N * α ^ 2)) := by
    have hA : (n : ℝ) * j * (1 - α ^ 2) ≤ n * j * (N * α ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg α]) hQ0
    have hB : u * ((n : ℝ) * j * (1 - α ^ 2)) ≤ u * (n * j * (N * α ^ 2)) :=
      mul_le_mul_of_nonneg_left hA hu.le
    nlinarith
  have h3 : u / (1 + 2 * u) * F ^ 2 * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) ≤
      L * (n * j * N * α * F) * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) := by
    have e1 : L * (n * j * N * α * F) * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) =
        F ^ 2 * (n * j * (N * α ^ 2)) := by
      calc L * (n * j * N * α * F) * (1 + n * j * (1 - α ^ 2 + N * α ^ 2))
          = (L * (1 + n * j * (1 - α ^ 2 + N * α ^ 2))) * (n * j * N * α * F) := by ring
        _ = F ^ 2 * (n * j * (N * α ^ 2)) := by rw [hLD]; ring
    rw [e1]
    have e2 : u / (1 + 2 * u) * F ^ 2 * (1 + n * j * (1 - α ^ 2 + N * α ^ 2)) =
        F ^ 2 * (u * (1 + n * j * (1 - α ^ 2 + N * α ^ 2))) / (1 + 2 * u) := by
      field_simp
    rw [e2, div_le_iff₀ h2u]
    have := mul_le_mul_of_nonneg_left key (sq_nonneg F)
    nlinarith
  have h4 := le_of_mul_le_mul_right h3 hD
  linarith

end Witness

end SchauderTranslates.Sharp

namespace SchauderTranslates
open Construction ProductEngines Sharp

namespace EngineSetup
variable {T : TagSetup} (E : EngineSetup T)

/-- Validity of the engine stage in the sharp regime: only the structural facts. All
numerical bounds are separate hypotheses of the theorems below. -/
structure ValidSharp : Prop where
  e_eq : ∀ c, (E.a c).e = T.lift (E.rep c)
  info : ∀ c, HasSelectiveInformation T.ρS E.a E.φ c E.cE E.jE
  cE_nonneg : 0 ≤ E.cE
  jE_pos : 0 < E.jE
  eng_poly : ∀ c, (E.a c).scalar.IsPolynomial

variable {E}

theorem slowLift_e_sharp (hE : E.ValidSharp) (c : Fin (T.N * E.n)) :
    (FiberKernel.piKernel (kernels E.a)).slowLift T.ρS ((E.a c).e.toL2 T.ρS) =
      E.Ev (E.rep c) := by
  rw [EngineSetup.Ev, slowVec_eq_slowLift, hE.e_eq]

theorem e_norm_sharp (hT : T.Valid) (hE : E.ValidSharp) (c : Fin (T.N * E.n)) :
    ‖(E.a c).e.toL2 T.ρS‖ = 1 := by
  rw [hE.e_eq]
  exact T.lift_norm hT _

theorem info_nonneg_sharp (hE : E.ValidSharp) (c : Fin (T.N * E.n)) (v : E.Hil) :
    0 ≤ E.info c v := by
  have := hE.cE_nonneg
  have := hE.jE_pos.le
  unfold EngineSetup.info
  positivity

theorem info_bound_sharp (hT : T.Valid) (hE : E.ValidSharp) (c : Fin (T.N * E.n)) (v : E.Hil)
    (b : Fin E.q → ℂ) (hv : v ∈ E.Sl) :
    ‖inner ℂ v (∑ p, b p • E.Tp c p)‖ ^ 2 ≤ E.info c v * ‖∑ p, b p • E.Rp c p‖ ^ 2 := by
  have h := engine_information_bound T.ρS E.a E.φ c hE.cE_nonneg hE.jE_pos.le
    (T.carrier_independent (E.rep c)) (e_norm_sharp hT hE c) (hE.info c) v hv b
  rw [slowLift_e_sharp hE] at h
  exact h

theorem info_total_sharp (hT : T.Valid) (hE : E.ValidSharp) (v : E.Hil) :
    ∑ c, E.info c v ≤
      ((T.N * E.n : ℕ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2)) * ‖v‖ ^ 2 := by
  have hb := equiangular_bessel_of_pos E.Ev (EngineSetup.Ev_norm hT)
    (fun i i' h => EngineSetup.Ev_inner_ne hT h) hT.N_pos v
  have hs : ∑ c, ‖inner ℂ (E.Ev (E.rep c)) v‖ ^ 2 = E.n * ∑ i, ‖inner ℂ (E.Ev i) v‖ ^ 2 := by
    rw [EngineSetup.sum_rep (E := E) (fun i => ‖inner ℂ (E.Ev i) v‖ ^ 2), nsmul_eq_mul]
  simp only [EngineSetup.info, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
  have hj := hE.jE_pos.le
  have hn : (0 : ℝ) ≤ E.n := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hb (mul_nonneg hj hn)
  push_cast
  nlinarith

theorem info_angle_sharp (hT : T.Valid) (y : E.Hil)
    (hy : y ∈ Submodule.span ℂ (Set.range E.X)) :
    ∑ c, E.info c y = ((T.N * E.n : ℕ) * E.cE) * ‖y‖ ^ 2 := by
  simp only [EngineSetup.info, EngineSetup.Ev_inner_span hT _ y hy, norm_zero]
  simp
  ring

theorem witness_sharp (hT : T.Valid) (hE : E.ValidSharp) (c : Fin (T.N * E.n)) :
    ∃ b : Fin E.q → ℂ, ∑ p, b p • E.Tp c p = (E.jE : ℂ) • E.Ev (finProdFinEquiv.symm c).1 ∧
      ‖∑ p, b p • E.Rp c p‖ ^ 2 = E.jE := by
  obtain ⟨b, hb1, hb2⟩ := engine_witness T.ρS E.a E.φ c (T.carrier_independent (E.rep c))
    (e_norm_sharp hT hE c) (hE.info c)
  refine ⟨b, ?_, hb2⟩
  show ∑ p, b p • slowPart T.ρS E.a E.φ c p = _
  rw [hb1, slowLift_e_sharp hE]
  rfl

/-- The sharp centered prefix bound of every engine in the combined law. -/
theorem fast_prefix_sharp (hE : E.ValidSharp) {KV Ks C : ℝ} (hKV : 0 ≤ KV)
    (hcar : ∀ i, FinitePrefixSqBound (fun k => (T.carrier i k).toL2 T.ρS) (KV ^ 2))
    (hKs : 1 ≤ Ks) (haux : ∀ c, (E.a c).scalar.AugmentedPrefixSqBound (Ks ^ 2))
    (hC : 1 ≤ C)
    (hdiag : ∀ c (k : Fin E.ne),
      ((E.a c).scalar.rawGram⁻¹ (Sum.inr k) (Sum.inr k)).re ≤ C)
    (c : Fin (T.N * E.n)) :
    FinitePrefixSqBound (E.Rp c) (selectivePrefixSqSharp (Ks ^ 2) (C * max KV 1 ^ 2)) := by
  have h := selective_centered_prefix_sharp (E.a c) T.ρS (E.φ c) (T.carrier_independent _)
    (by rw [hE.e_eq]; exact T.lift_mem_span _) hKV (hcar _) hKs (haux c) hC (hdiag c)
  exact fastPart_prefix T.ρS E.a E.φ c h

/-- The main conclusions in the normalized product law, with sharp constants. -/
theorem model_main_sharp (hT : T.Valid) (hE : E.ValidSharp) (hμ : Function.Injective T.μ)
    {K : ℝ} (hK : 1 ≤ K) (hpre : PrefixBound T.w T.μ K)
    {ρs lam Qc u : ℝ} (hρ0 : 0 ≤ ρs) (hρ1 : ρs < 1)
    (hQc : 1 ≤ Qc) (hfast : ∀ c, FinitePrefixSqBound (E.Rp c) Qc)
    (hang : ((T.N * E.n : ℕ) : ℝ) * E.cE ≤ ρs ^ 2)
    (hlam : ((T.N * E.n : ℕ) : ℝ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤ lam)
    (hu : 0 < u) (hQ : u ≤ E.n * E.jE * (T.N * T.α ^ 2)) :
    LinearIndependent ℂ E.u ∧
      FinitePrefixSqBound E.u ((1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * Qc)) ∧
      ∃ b : Fin (T.d + T.N * E.n * E.q) → ℂ,
        ‖E.tgt - ∑ k, b k • E.u k‖ ^ 2 ≤ (1 - u / (1 + 2 * u)) * ‖T.resid‖ ^ 2 := by
  have hT' : ∀ c p, E.Tp c p ∈ E.Sl := fun c p => slowPart_mem _ _ _ _ _
  have hRS : ∀ c p, ∀ s ∈ E.Sl, inner ℂ s (E.Rp c p) = 0 :=
    fun c p s hs => fastPart_inner_slow _ _ _ _ _ s hs
  have hRR : ∀ c c' p p', c ≠ c' → inner ℂ (E.Rp c p) (E.Rp c' p') = 0 :=
    fun c c' p p' h => fastPart_inner_ne _ _ _ h _ _
  have hxS : ∀ i, E.X i ∈ E.Sl := fun i => EngineSetup.lineVec_mem _
  have hinfo : ∀ c v (b : Fin E.q → ℂ), v ∈ E.Sl →
      ‖inner ℂ v (∑ p, b p • E.Tp c p)‖ ^ 2 ≤ E.info c v * ‖∑ p, b p • E.Rp c p‖ ^ 2 :=
    fun c v b hv => info_bound_sharp hT hE c v b hv
  have hα : 0 < T.α := div_pos hT.resid_pos (Real.sqrt_pos.mpr (TagSetup.D_pos hT))
  have hα1 : T.α ≤ 1 := by
    have hD := TagSetup.D_pos hT
    rw [TagSetup.α, div_le_one (Real.sqrt_pos.mpr hD)]
    apply Real.le_sqrt_of_sq_le
    unfold TagSetup.D
    have := hT.gain_pos
    have : 0 ≤ (∑ j, ‖T.c j‖ ^ 2) / T.st.gain := by positivity
    linarith
  have hα2 : T.α ^ 2 ≤ 1 := by nlinarith
  have hlam0 : 0 ≤ lam := by
    have h1 := hE.cE_nonneg
    have h2 := hE.jE_pos.le
    have h3 : (0 : ℝ) ≤ 1 - T.α ^ 2 + T.N * T.α ^ 2 := by
      have hN : (1 : ℝ) ≤ T.N := by exact_mod_cast hT.N_pos
      nlinarith [sq_nonneg T.α]
    have h4 : (0 : ℝ) ≤ E.n := Nat.cast_nonneg _
    have h5 : (0 : ℝ) ≤ ((T.N * E.n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (mul_nonneg h4 h2) h3, mul_nonneg h5 h1]
  have htot : ∀ v ∈ E.Sl, ∑ c, E.info c v ≤ lam * ‖v‖ ^ 2 := by
    intro v _
    exact (info_total_sharp hT hE v).trans (mul_le_mul_of_nonneg_right hlam (sq_nonneg _))
  have hang' : ∀ y ∈ Submodule.span ℂ (Set.range E.X), ∑ c, E.info c y ≤ ρs ^ 2 * ‖y‖ ^ 2 := by
    intro y hy
    rw [info_angle_sharp hT y hy]
    exact mul_le_mul_of_nonneg_right hang (sq_nonneg _)
  have hsq : Real.sqrt Qc ^ 2 = Qc := Real.sq_sqrt (zero_le_one.trans hQc)
  have hsq1 : 1 ≤ Real.sqrt Qc := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hQc
  refine ⟨?_, ?_, ?_⟩
  · exact engine_concat_independent E.Sl E.X hxS (EngineSetup.X_independent hμ) E.Tp E.Rp hT'
      hRS hRR (fun c => fastPart_independent _ _ _ c (T.carrier_independent _)) E.info
      (info_nonneg_sharp hE) hinfo hρ0 hρ1 hang'
  · have h := engine_concat_prefix E.Sl E.X hxS hK (EngineSetup.X_prefix hpre) E.Tp E.Rp hT'
      hRS hRR hsq1 (fun c => by rw [hsq]; exact hfast c) E.info (info_nonneg_sharp hE) hinfo
      hlam0 hρ0 hρ1 htot hang'
    rw [hsq] at h
    exact h
  · have hQ0 : 0 ≤ (E.n : ℝ) * E.jE := mul_nonneg (Nat.cast_nonneg _) hE.jE_pos.le
    have hβ : 1 ≤ (T.N : ℝ) * T.α ^ 2 := by linarith [hT.N_big]
    obtain ⟨b, hb⟩ := replica_witness_sharp E.Ev hα2 (EngineSetup.Ev_norm hT)
      (fun i i' h => EngineSetup.Ev_inner_ne hT h) E.rP EngineSetup.rP_norm
      (EngineSetup.Ev_inner_rP hT) E.Tp E.Rp (witness_sharp hT hE) hu hQ0 hβ hQ
    obtain ⟨a, ha⟩ := engine_witness_residual E.Sl E.X E.Tp E.Rp hT' hRS hRR E.tgt E.rP
      (EngineSetup.lineVec_mem _) (EngineSetup.tgt_sub_rP_mem hT.diff) b
    refine ⟨a, ?_⟩
    rw [EngineSetup.u, ha]
    exact hb

/-! ### The raw kernel is a mixed trigonometric polynomial -/

theorem isFastPoly_auxDensity_sharp (hE : E.ValidSharp) (c : Fin (T.N * E.n)) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun _ y => ((E.a c).scalar.density (y.2 c).2 : ℂ)) := by
  obtain ⟨K, a, ha⟩ := hE.eng_poly c
  exact (isFastPoly_aux_poly c K a).congr (fun t y => (ha (y.2 c).2).symm)

theorem isFastPoly_seedFactor_sharp (hE : E.ValidSharp) (c : Fin (T.N * E.n)) (j : Fin E.L) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ)) := by
  have hz : IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun _ y => fourier (1 : ℤ) ((y.2 c).1 j)) :=
    (isFastPoly_seed c (Pi.single j 1)).congr (fun t y => mFourier_single_one j _)
  have hv : IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => ((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) := by
    apply IsFastPoly.const_mul
    rw [hE.e_eq]
    exact EngineSetup.isFastPoly_lift _
  have hexp : ∀ (t : ℝ) (y : E.Fast),
      (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ) =
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * (((E.a c).κ : ℂ) * (E.a c).e (t, y.1) *
          star (fourier (1 : ℤ) ((y.2 c).1 j))) +
        (1 / 2 : ℂ) * star (((E.a c).κ : ℂ) * (E.a c).e (t, y.1) *
          star (fourier (1 : ℤ) ((y.2 c).1 j))) := by
    intro t y
    simp only [seedFactor]
    push_cast
    rw [re_complex_eq]
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  apply IsFastPoly.add
  · apply IsFastPoly.add
    · exact isFastPoly_const_fast (1 / 2 : ℂ)
    · exact (hv.mul hz.star).const_mul _
  · exact (hv.mul hz.star).star.const_mul _

theorem isFastPoly_raw_sharp (hE : E.ValidSharp) (c : Fin (T.N * E.n)) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => ((E.a c).raw ((t, y.1), y.2 c) : ℂ)) := by
  have hexp : ∀ (t : ℝ) (y : E.Fast), ((E.a c).raw ((t, y.1), y.2 c) : ℂ) =
      ((E.a c).scalar.density (y.2 c).2 : ℂ) +
        (1 - ((E.a c).scalar.density (y.2 c).2 : ℂ)) *
          (((E.a c).m / (1 / 2 : ℝ) ^ E.L : ℝ) : ℂ) *
            ∏ j, (seedFactor (((E.a c).κ : ℂ) * (E.a c).e (t, y.1)) ((y.2 c).1 j) : ℂ) := by
    intro t y
    simp only [SelectiveKernelData.raw, seedKernel, seedProduct]
    push_cast
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  apply (isFastPoly_auxDensity_sharp hE c).add
  apply IsFastPoly.mul
  · apply IsFastPoly.mul
    · exact (isFastPoly_const_fast 1).add ((isFastPoly_auxDensity_sharp hE c).const_mul (-1))
        |>.congr (fun t y => by ring)
    · exact isFastPoly_const_fast _
  · exact IsFastPoly.prod _ (fun j _ => isFastPoly_seedFactor_sharp hE c j)

theorem isFastPoly_Wraw_sharp (hT : T.Valid) (hE : E.ValidSharp) :
    IsFastPoly (Mt := T.Mt) (dt := T.dt) (mE := T.N * E.n) (L := E.L) (de := E.de)
      (fun t y => (E.Wraw t y : ℂ)) := by
  have hexp : ∀ (t : ℝ) (y : E.Fast), (E.Wraw t y : ℂ) =
      (∏ b, (T.st.density (y.1 b) : ℂ)) * ∏ c, ((E.a c).raw ((t, y.1), y.2 c) : ℂ) := by
    intro t y
    simp only [EngineSetup.Wraw]
    push_cast
    ring
  apply IsFastPoly.congr _ (fun t y => (hexp t y).symm)
  exact (IsFastPoly.prod _ (fun b _ => EngineSetup.isFastPoly_tagDensity hT b)).mul
    (IsFastPoly.prod _ (fun c _ => isFastPoly_raw_sharp hE c))

theorem isMixedTrigPoly_Wflat_sharp (hT : T.Valid) (hE : E.ValidSharp) :
    IsMixedTrigPoly (fun t x => (E.Wflat t x : ℂ)) :=
  isFastPoly_Wraw_sharp hT hE

end EngineSetup

end SchauderTranslates
