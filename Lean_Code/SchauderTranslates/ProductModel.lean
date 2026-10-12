import Lean_Code.SchauderTranslates.ProductTags
import Lean_Code.SchauderTranslates.EngineAlgebra

/-!
# The finite extension in the normalized product law (blueprint `tag:angle`, `extend:product`)

Given the tag stage and selective engines attached to the replica lifts, the ordered list
"old characters, then all engine packets" in the actual combined weighted L² space is
independent, has the asserted prefix bound, and approximates the target with squared
error at most `(2/5) ‖r‖²`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

/-- The discrete choices of the engine stage. -/
structure EngineSetup (T : TagSetup) where
  L : ℕ
  de : ℕ
  ne : ℕ
  n : ℕ
  a : Fin (T.N * n) → SelectiveKernelData T.Slow L de ne
  cE : ℝ
  jE : ℝ

namespace EngineSetup
variable {T : TagSetup} (E : EngineSetup T)

/-- The replica served by engine `c`. -/
def rep (c : Fin (T.N * E.n)) : Fin T.N := (finProdFinEquiv.symm c).1

/-- The carrier list of engine `c`. -/
def φ (c : Fin (T.N * E.n)) : Fin ((T.d + 1) * T.nt) → BoundedMeasurableComplex T.Slow :=
  T.carrier (E.rep c)

abbrev q : ℕ := E.ne * ((T.d + 1) * T.nt + E.L)

/-- The combined weighted law. -/
abbrev P := law T.ρS E.a

abbrev Hil := Lp ℂ 2 E.P

/-- The slow space. -/
abbrev Sl : Submodule ℂ E.Hil := (FiberKernel.piKernel (kernels E.a)).slowSpace T.ρS

/-- Line functions in the combined law. -/
def lineVec (g : BoundedMeasurableComplex ℝ) : E.Hil :=
  slowVec T.ρS E.a (g.pullbackFst (Fin T.Mt → UnitAddTorus (Fin T.dt)))

/-- The old atoms. -/
def X (i : Fin T.d) : E.Hil := E.lineVec (lineCharacter (T.μ i))

/-- The target. -/
def tgt : E.Hil := E.lineVec (lineCharacter T.ξ)

/-- The residual. -/
def rP : E.Hil := E.lineVec (lineSum T.lam T.c)

/-- The replica lifts. -/
def Ev (i : Fin T.N) : E.Hil := slowVec T.ρS E.a (T.lift i)

/-- Slow and centered parts of the engine atoms. -/
def Tp (c : Fin (T.N * E.n)) (p : Fin E.q) : E.Hil := slowPart T.ρS E.a E.φ c p
def Rp (c : Fin (T.N * E.n)) (p : Fin E.q) : E.Hil := fastPart T.ρS E.a E.φ c p

/-- The ordered list: old characters, then all engine packets. -/
def u : Fin (T.d + T.N * E.n * E.q) → E.Hil := engineConcat E.X (fun c p => E.Tp c p + E.Rp c p)

/-- Validity of the engine stage. -/
structure Valid : Prop where
  e_eq : ∀ c, (E.a c).e = T.lift (E.rep c)
  info : ∀ c, HasSelectiveInformation T.ρS E.a E.φ c E.cE E.jE
  cE_nonneg : 0 ≤ E.cE
  jE_pos : 0 < E.jE
  aux : ∀ c, (E.a c).scalar.AugmentedPrefixSqBound 4
  diag : ∀ c k, ((E.a c).scalar.rawGram⁻¹ k k).re ≤ 2
  q1 : (1 / 10 : ℝ) ≤ E.n * E.jE
  q2 : (E.n : ℝ) * E.jE ≤ 11 / 100
  eng_poly : ∀ c, (E.a c).scalar.IsPolynomial

variable {E}

theorem lineVec_inner (g h : BoundedMeasurableComplex ℝ) :
    inner ℂ (E.lineVec g) (E.lineVec h) = inner ℂ (g.toL2 T.ρ) (h.toL2 T.ρ) := by
  rw [lineVec, lineVec, slowVec_inner, tag_slow_inner]

theorem lineVec_mem (g : BoundedMeasurableComplex ℝ) : E.lineVec g ∈ E.Sl :=
  slowVec_mem _ _ _

theorem Ev_mem (i : Fin T.N) : E.Ev i ∈ E.Sl := slowVec_mem _ _ _

theorem Ev_inner_lineVec (hT : T.Valid) (i : Fin T.N) (g : BoundedMeasurableComplex ℝ) :
    inner ℂ (E.Ev i) (E.lineVec g) =
      ((Real.sqrt T.D)⁻¹ : ℂ) * inner ℂ T.resid (g.toL2 T.ρ) := by
  rw [Ev, lineVec, slowVec_inner, ← inner_conj_symm, T.lift_slow_inner hT, map_mul,
    inner_conj_symm, map_inv₀, Complex.conj_ofReal]

theorem Ev_norm (hT : T.Valid) (i : Fin T.N) : ‖E.Ev i‖ = 1 := by
  rw [Ev, slowVec_eq_slowLift, LinearIsometry.norm_map, T.lift_norm hT]

theorem Ev_inner_ne (hT : T.Valid) {i i' : Fin T.N} (h : i ≠ i') :
    inner ℂ (E.Ev i) (E.Ev i') = ((T.α ^ 2 : ℝ) : ℂ) := by
  rw [Ev, Ev, slowVec_inner, T.lift_inner_ne hT h]

theorem lineSum_toL2_resid : (lineSum T.lam T.c).toL2 T.ρ = T.resid := rfl

theorem Ev_inner_X (hT : T.Valid) (i : Fin T.N) (l : Fin T.d) :
    inner ℂ (E.Ev i) (E.X l) = 0 := by
  rw [X, Ev_inner_lineVec hT, ← inner_conj_symm, hT.orth l, map_zero, mul_zero]

theorem Ev_inner_span (hT : T.Valid) (i : Fin T.N) (y : E.Hil)
    (hy : y ∈ Submodule.span ℂ (Set.range E.X)) : inner ℂ (E.Ev i) y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, rfl⟩ := hz
    exact Ev_inner_X hT i l
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem rP_norm : ‖E.rP‖ = ‖T.resid‖ := by
  have h := lineVec_inner (E := E) (lineSum T.lam T.c) (lineSum T.lam T.c)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, lineSum_toL2_resid] at h
  have h2 : ‖E.rP‖ ^ 2 = ‖T.resid‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem Ev_inner_rP (hT : T.Valid) (i : Fin T.N) :
    inner ℂ (E.Ev i) E.rP = ((T.α * ‖T.resid‖ : ℝ) : ℂ) := by
  have hD := TagSetup.D_pos hT
  rw [rP, Ev_inner_lineVec hT, lineSum_toL2_resid, inner_self_eq_norm_sq_to_K]
  rw [TagSetup.α]
  push_cast
  field_simp
  rfl

/-- The old atoms have the line Gram. -/
theorem X_inner (l l' : Fin T.d) :
    inner ℂ (E.X l) (E.X l') =
      inner ℂ ((lineCharacter (T.μ l)).toL2 T.ρ) ((lineCharacter (T.μ l')).toL2 T.ρ) :=
  lineVec_inner _ _

/-- The target minus the residual lies in the old span. -/
theorem tgt_sub_rP_mem
    (hdiff : (lineCharacter T.ξ).toL2 T.ρ - T.resid ∈
      Submodule.span ℂ (Set.range fun i => (lineCharacter (T.μ i)).toL2 T.ρ)) :
    E.tgt - E.rP ∈ Submodule.span ℂ (Set.range E.X) := by
  let lift1 := (tagKernel ℝ T.st T.Mt).slowLift T.ρ
  let lift2 := (FiberKernel.piKernel (kernels E.a)).slowLift T.ρS
  have hlin (g : BoundedMeasurableComplex ℝ) : E.lineVec g = lift2 (lift1 (g.toL2 T.ρ)) := by
    rw [lineVec, slowVec_eq_slowLift]
    congr 1
  have hmap : E.tgt - E.rP = (lift2.toLinearMap.comp lift1.toLinearMap)
      ((lineCharacter T.ξ).toL2 T.ρ - T.resid) := by
    rw [tgt, rP, hlin, hlin, map_sub]
    rfl
  rw [hmap]
  have hspan : Submodule.map (lift2.toLinearMap.comp lift1.toLinearMap)
      (Submodule.span ℂ (Set.range fun i => (lineCharacter (T.μ i)).toL2 T.ρ)) =
      Submodule.span ℂ (Set.range E.X) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
  rw [← hspan]
  exact Submodule.mem_map_of_mem hdiff

theorem X_independent (hμ : Function.Injective T.μ) : LinearIndependent ℂ E.X := by
  have hw : LinearIndependent ℂ (fun i => weightedCharacter (normalizedWeight T.w) (T.μ i)) :=
    characters_linearIndependent _ _ hμ
  have heq (i : Fin T.d) : weightedCharacter (normalizedWeight T.w) (T.μ i) =
      (lineCharacter (T.μ i)).toL2 T.ρ := by
    apply Lp.ext
    exact (weightedCharacter_ae _ _).trans ((lineCharacter (T.μ i)).toL2_ae T.ρ).symm
  simp only [heq] at hw
  have hg : Matrix.gram ℂ E.X =
      Matrix.gram ℂ (fun i => (lineCharacter (T.μ i)).toL2 T.ρ) := by
    ext l l'
    exact X_inner l l'
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [hg]
  exact Matrix.posDef_gram_iff_linearIndependent.mpr hw

theorem X_prefix {K : ℝ} (hpre : PrefixBound T.w T.μ K) : FinitePrefixSqBound E.X (K ^ 2) :=
  finitePrefixSqBound_of_inner_eq _ _ X_inner (prefixBound_lineLaw T.w T.μ hpre)

theorem slowLift_e (hE : E.Valid) (c : Fin (T.N * E.n)) :
    (FiberKernel.piKernel (kernels E.a)).slowLift T.ρS ((E.a c).e.toL2 T.ρS) = E.Ev (E.rep c) := by
  rw [Ev, slowVec_eq_slowLift, hE.e_eq]

theorem e_norm (hT : T.Valid) (hE : E.Valid) (c : Fin (T.N * E.n)) :
    ‖(E.a c).e.toL2 T.ρS‖ = 1 := by
  rw [hE.e_eq]
  exact T.lift_norm hT _

/-- The information quadratic bound of each engine in the combined law. -/
def info (c : Fin (T.N * E.n)) (v : E.Hil) : ℝ :=
  E.cE * ‖v‖ ^ 2 + E.jE * ‖inner ℂ (E.Ev (E.rep c)) v‖ ^ 2

theorem info_nonneg (hE : E.Valid) (c : Fin (T.N * E.n)) (v : E.Hil) : 0 ≤ E.info c v := by
  have := hE.cE_nonneg
  have := hE.jE_pos.le
  unfold info
  positivity

theorem info_bound (hT : T.Valid) (hE : E.Valid) (c : Fin (T.N * E.n)) (v : E.Hil)
    (b : Fin E.q → ℂ) (hv : v ∈ E.Sl) :
    ‖inner ℂ v (∑ p, b p • E.Tp c p)‖ ^ 2 ≤ E.info c v * ‖∑ p, b p • E.Rp c p‖ ^ 2 := by
  have h := engine_information_bound T.ρS E.a E.φ c hE.cE_nonneg hE.jE_pos.le
    (T.carrier_independent (E.rep c)) (e_norm hT hE c) (hE.info c) v hv b
  rw [slowLift_e hE] at h
  exact h

/-- Each replica is served by exactly `n` engines. -/
theorem sum_rep {M : Type*} [AddCommMonoid M] (g : Fin T.N → M) :
    ∑ c : Fin (T.N * E.n), g (E.rep c) = E.n • ∑ i, g i := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [rep, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.smul_sum]

theorem info_total (hT : T.Valid) (hE : E.Valid) (v : E.Hil) :
    ∑ c, E.info c v ≤
      ((T.N * E.n : ℕ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2)) * ‖v‖ ^ 2 := by
  have hb := equiangular_bessel_of_pos E.Ev (Ev_norm hT) (fun i i' h => Ev_inner_ne hT h)
    hT.N_pos v
  have hs : ∑ c, ‖inner ℂ (E.Ev (E.rep c)) v‖ ^ 2 = E.n * ∑ i, ‖inner ℂ (E.Ev i) v‖ ^ 2 := by
    rw [sum_rep (E := E) (fun i => ‖inner ℂ (E.Ev i) v‖ ^ 2), nsmul_eq_mul]
  simp only [info, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hs]
  have hj := hE.jE_pos.le
  have hn : (0 : ℝ) ≤ E.n := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hb (mul_nonneg hj hn)
  push_cast
  nlinarith

theorem info_angle (hT : T.Valid) (_hE : E.Valid) (y : E.Hil)
    (hy : y ∈ Submodule.span ℂ (Set.range E.X)) :
    ∑ c, E.info c y = ((T.N * E.n : ℕ) * E.cE) * ‖y‖ ^ 2 := by
  simp only [info, Ev_inner_span hT _ y hy, norm_zero]
  simp
  ring

theorem witness (hT : T.Valid) (hE : E.Valid) (c : Fin (T.N * E.n)) :
    ∃ b : Fin E.q → ℂ, ∑ p, b p • E.Tp c p = (E.jE : ℂ) • E.Ev (finProdFinEquiv.symm c).1 ∧
      ‖∑ p, b p • E.Rp c p‖ ^ 2 = E.jE := by
  obtain ⟨b, hb1, hb2⟩ := engine_witness T.ρS E.a E.φ c (T.carrier_independent (E.rep c))
    (e_norm hT hE c) (hE.info c)
  refine ⟨b, ?_, hb2⟩
  show ∑ p, b p • slowPart T.ρS E.a E.φ c p = _
  rw [hb1, slowLift_e hE]
  rfl

theorem sqrt_eight_prefix : selectivePrefixConstant (Real.sqrt 8) = 6 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hmax : max (Real.sqrt 8) 1 = Real.sqrt 8 := by
    apply max_eq_left
    rw [h8]
    nlinarith [Real.sqrt_nonneg 2, Real.one_lt_sqrt_two]
  unfold selectivePrefixConstant
  rw [hmax, h8]
  nlinarith

theorem fast_prefix (hT : T.Valid) (hE : E.Valid) (c : Fin (T.N * E.n)) :
    FinitePrefixSqBound (E.Rp c) (6 ^ 2) := by
  have hrow : FinitePrefixSqBound (fun i => (E.φ c i).toL2 T.ρS) (Real.sqrt 8 ^ 2) := by
    rw [Real.sq_sqrt (by norm_num)]
    exact T.carrier_prefix hT _
  have h := selective_centered_prefix (E.a c) T.ρS (E.φ c) (T.carrier_independent _)
    (by rw [hE.e_eq]; exact T.lift_mem_span _) (Real.sqrt_nonneg 8) hrow (hE.aux c) (hE.diag c)
  rw [sqrt_eight_prefix] at h
  exact fastPart_prefix T.ρS E.a E.φ c h

/-- The main conclusions in the normalized product law. -/
theorem model_main (hT : T.Valid) (hE : E.Valid) (hμ : Function.Injective T.μ)
    {K : ℝ} (hK : 1 ≤ K) (hpre : PrefixBound T.w T.μ K)
    {ρs lam : ℝ} (hρ0 : 0 ≤ ρs) (hρ1 : ρs < 1)
    (hang : ((T.N * E.n : ℕ) : ℝ) * E.cE ≤ ρs ^ 2)
    (hlam : ((T.N * E.n : ℕ) : ℝ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤ lam) :
    LinearIndependent ℂ E.u ∧
      FinitePrefixSqBound E.u ((1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * 6 ^ 2)) ∧
      ∃ b : Fin (T.d + T.N * E.n * E.q) → ℂ,
        ‖E.tgt - ∑ k, b k • E.u k‖ ^ 2 ≤ (2 / 5) * ‖T.resid‖ ^ 2 := by
  have hT' : ∀ c p, E.Tp c p ∈ E.Sl := fun c p => slowPart_mem _ _ _ _ _
  have hRS : ∀ c p, ∀ s ∈ E.Sl, inner ℂ s (E.Rp c p) = 0 :=
    fun c p s hs => fastPart_inner_slow _ _ _ _ _ s hs
  have hRR : ∀ c c' p p', c ≠ c' → inner ℂ (E.Rp c p) (E.Rp c' p') = 0 :=
    fun c c' p p' h => fastPart_inner_ne _ _ _ h _ _
  have hxS : ∀ i, E.X i ∈ E.Sl := fun i => lineVec_mem _
  have hinfo : ∀ c v (b : Fin E.q → ℂ), v ∈ E.Sl →
      ‖inner ℂ v (∑ p, b p • E.Tp c p)‖ ^ 2 ≤ E.info c v * ‖∑ p, b p • E.Rp c p‖ ^ 2 :=
    fun c v b hv => info_bound hT hE c v b hv
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
    exact (info_total hT hE v).trans (mul_le_mul_of_nonneg_right hlam (sq_nonneg _))
  have hang' : ∀ y ∈ Submodule.span ℂ (Set.range E.X), ∑ c, E.info c y ≤ ρs ^ 2 * ‖y‖ ^ 2 := by
    intro y hy
    rw [info_angle hT hE y hy]
    exact mul_le_mul_of_nonneg_right hang (sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · exact engine_concat_independent E.Sl E.X hxS (X_independent hμ) E.Tp E.Rp hT' hRS hRR
      (fun c => fastPart_independent _ _ _ c (T.carrier_independent _)) E.info
      (info_nonneg hE) hinfo hρ0 hρ1 hang'
  · exact engine_concat_prefix E.Sl E.X hxS hK (X_prefix hpre) E.Tp E.Rp hT' hRS hRR
      (by norm_num) (fast_prefix hT hE) E.info (info_nonneg hE) hinfo hlam0 hρ0 hρ1 htot hang'
  · have hα : 0 < T.α := div_pos hT.resid_pos (Real.sqrt_pos.mpr (TagSetup.D_pos hT))
    have hα1 : T.α ≤ 1 := by
      have hD := TagSetup.D_pos hT
      rw [TagSetup.α, div_le_one (Real.sqrt_pos.mpr hD)]
      apply Real.le_sqrt_of_sq_le
      unfold TagSetup.D
      have := hT.gain_pos
      have : 0 ≤ (∑ j, ‖T.c j‖ ^ 2) / T.st.gain := by positivity
      linarith
    obtain ⟨b, hb⟩ := replica_witness_bound E.Ev hα hα1 hT.resid_pos hE.jE_pos (Ev_norm hT)
      (fun i i' h => Ev_inner_ne hT h) E.rP rP_norm (Ev_inner_rP hT) E.Tp E.Rp hRR
      (witness hT hE) hE.q1 hE.q2 hT.N_big
    obtain ⟨a, ha⟩ := engine_witness_residual E.Sl E.X E.Tp E.Rp hT' hRS hRR E.tgt E.rP
      (lineVec_mem _) (tgt_sub_rP_mem hT.diff) b
    refine ⟨a, ?_⟩
    rw [u, ha]
    exact hb

end EngineSetup
end SchauderTranslates
