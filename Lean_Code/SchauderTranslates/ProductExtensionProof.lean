import Lean_Code.SchauderTranslates.ProductRaw
import Lean_Code.SchauderTranslates.ScalarTuning

/-!
# Blueprint `extend:product`: the finite extension on a product space

All discrete choices are made in the order required by the proof: the residual and the
tag gain `z` first, then `α` and the replica count `N`, then a tag block of gain exactly
`z` and small loss, the coupling parameter `κ`, and only then the selective engines and
their number of copies. The resulting kernel and atoms satisfy `ProductExtension`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

/-- Bernoulli-type loss bound for products of masses in `[0,1]`. -/
theorem one_sub_mul_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - x * y ≤ (1 - x) + (1 - y) := by nlinarith

theorem one_sub_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - x ^ k ≤ k * (1 - x) := by
  have h := one_add_le_pow_of_two_add_nonneg (a := x - 1) (by linarith) k
  have he : (1 + (x - 1)) = x := by ring
  rw [he] at h
  nlinarith

/-- The arithmetic of the prefix margin. -/
theorem prefix_margin {K τ ρs lam : ℝ} (hK : 1 ≤ K) (hτ : 0 < τ)
    (hρ0 : 0 ≤ ρs) (hρ3 : ρs ≤ 1 / 3) (hρτ : ρs ≤ τ / (4 * max K 12))
    (hlam : lam ≤ 3) :
    (1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * 6 ^ 2) < (max K 12 + τ) ^ 2 := by
  set K₁ := max K 12
  have hK₁ : 12 ≤ K₁ := le_max_right _ _
  have hKK : K ≤ K₁ := le_max_left _ _
  have hm : max (K ^ 2) ((1 + lam) * 6 ^ 2) ≤ K₁ ^ 2 := by
    apply max_le
    · exact pow_le_pow_left₀ (by linarith) hKK 2
    · nlinarith
  have hfrac : (1 + ρs) / (1 - ρs) ≤ 1 + 3 * ρs := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 ≤ max (K ^ 2) ((1 + lam) * 6 ^ 2) := le_max_of_le_left (sq_nonneg _)
  have h3 : 3 * ρs * K₁ ^ 2 ≤ (3 / 4) * τ * K₁ := by
    have h4 : ρs * (4 * K₁) ≤ τ := (le_div_iff₀ (by positivity)).mp hρτ
    nlinarith
  calc (1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * 6 ^ 2)
      ≤ (1 + 3 * ρs) * K₁ ^ 2 := by
        apply mul_le_mul hfrac hm hpos (by linarith)
    _ = K₁ ^ 2 + 3 * ρs * K₁ ^ 2 := by ring
    _ ≤ K₁ ^ 2 + (3 / 4) * τ * K₁ := by linarith
    _ < (K₁ + τ) ^ 2 := by nlinarith

/-- Blueprint `extend:product`. -/
theorem product_space_extension : ProductExtension := by
  intro w d μ K ξ δ τ hμ hK hpre hdist hδ hτ
  -- the residual of the target
  obtain ⟨c, hc0, horth, hdiff, hres⟩ := residual_exists w μ ξ
  have hZ : 0 < ∫ s, w.density s := weight_integral_pos w
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = ∫ s, w.density s := ⟨_, rfl⟩
  rw [← hZdef] at hZ hres
  obtain ⟨r, hrdef⟩ : ∃ r : Lp ℂ 2 (lineLaw w), r = (lineSum (Fin.cons ξ μ) c).toL2 (lineLaw w) :=
    ⟨_, rfl⟩
  rw [← hrdef] at hres
  have hFpos : 0 < ‖r‖ := by
    have h1 : 0 < Z * ‖r‖ ^ 2 := by rw [hres]; exact hdist
    have h2 : 0 < ‖r‖ ^ 2 := pos_of_mul_pos_right h1 hZ.le
    exact lt_of_le_of_ne (norm_nonneg r) (fun h => by rw [← h] at h2; simp at h2)
  -- the tag gain and the replica count
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = 1 / (1292 * ((d + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hJ : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
  have hz0 : 0 < z := by rw [hzdef]; positivity
  have hz1 : z < 1 / 646 := by
    rw [hzdef, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hzJ : ((d + 1 : ℕ) : ℝ) * z ≤ 1 := by
    rw [hzdef, mul_one_div, div_le_one (by positivity)]
    nlinarith
  have hcsum : 1 ≤ ∑ j, ‖c j‖ ^ 2 := by
    have h0 := Finset.single_le_sum (f := fun j => ‖c j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ 0)
    simp only [hc0, norm_one, one_pow] at h0
    exact h0
  obtain ⟨Dt, hDt⟩ : ∃ Dt : ℝ, Dt = ‖r‖ ^ 2 + (∑ j, ‖c j‖ ^ 2) / z := ⟨_, rfl⟩
  have hcz : 0 ≤ (∑ j, ‖c j‖ ^ 2) / z := by positivity
  have hDtpos : 0 < Dt := by rw [hDt]; positivity
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = ‖r‖ / Real.sqrt Dt := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hαdef]; exact div_pos hFpos (Real.sqrt_pos.mpr hDtpos)
  have hα1 : α ≤ 1 := by
    rw [hαdef, div_le_one (Real.sqrt_pos.mpr hDtpos)]
    apply Real.le_sqrt_of_sq_le
    rw [hDt]
    linarith
  have hα2 : 0 < α ^ 2 := by positivity
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈20 / α ^ 2⌉₊ := ⟨_, rfl⟩
  have hNge : 20 / α ^ 2 ≤ N := by rw [hNdef]; exact Nat.le_ceil _
  have hNlt : (N : ℝ) < 20 / α ^ 2 + 1 := by rw [hNdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNge
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hNbig : 20 ≤ (N : ℝ) * α ^ 2 := by
    have := mul_le_mul_of_nonneg_right hNge hα2.le
    rwa [div_mul_cancel₀ _ hα2.ne'] at this
  have hNsmall : (N : ℝ) * α ^ 2 ≤ 21 := by
    have := mul_le_mul_of_nonneg_right hNlt.le hα2.le
    rw [add_mul, div_mul_cancel₀ _ hα2.ne', one_mul] at this
    nlinarith
  -- the tag block of gain exactly `z`
  have hδt : 0 < δ / (4 * N * ((d + 1 : ℕ) : ℝ)) := by positivity
  obtain ⟨dt, nt, st, εt, Kt, hpoly, _, _, _, hεt0, hεtδ, hεt1, hmass, hgain, hKt0, hKt2,
    hcent, _⟩ := scalar_gain_tuning hz0 hz1 hδt
  let T : TagSetup := ⟨w, d, μ, ξ, c, dt, nt, st, N⟩
  have hTres : T.resid = r := by rw [hrdef]; rfl
  have hTD : T.D = Dt := by
    change ‖T.resid‖ ^ 2 + (∑ j, ‖c j‖ ^ 2) / st.gain = Dt
    rw [hTres, hgain, hDt]
  have hTα : T.α = α := by
    change ‖T.resid‖ / Real.sqrt T.D = α
    rw [hTres, hTD, hαdef]
  have hT : T.Valid := by
    refine ⟨hc0, horth, hdiff, ?_, ?_, hpoly, ?_, ⟨Kt ^ 2, sq_nonneg _, ?_, hcent⟩, hNpos, ?_⟩
    · rw [hTres]; exact hFpos
    · change 0 < st.gain
      rw [hgain]; exact hz0
    · change ((d + 1 : ℕ) : ℝ) * st.gain ≤ 1
      rw [hgain]; exact hzJ
    · nlinarith
    · change (20 : ℝ) ≤ (N : ℝ) * T.α ^ 2
      rw [hTα]; exact hNbig
  -- the coupling parameter
  have hκ0 : 0 < T.κ := TagSetup.κ_pos
  have hκ1 : T.κ < 1 := TagSetup.κ_lt_one
  -- the margins
  have hK₁pos : 0 < max K 12 := lt_of_lt_of_le (by norm_num) (le_max_right K 12)
  obtain ⟨ρs, hρsdef⟩ : ∃ ρs : ℝ, ρs = min (1 / 3) (τ / (4 * max K 12)) := ⟨_, rfl⟩
  have hρs0 : 0 < ρs := by rw [hρsdef]; exact lt_min (by norm_num) (by positivity)
  have hρs3 : ρs ≤ 1 / 3 := by rw [hρsdef]; exact min_le_left _ _
  have hρsτ : ρs ≤ τ / (4 * max K 12) := by rw [hρsdef]; exact min_le_right _ _
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (1 / 100) (min (ρs ^ 2 / N) (δ / N)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]; exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη100 : η ≤ 1 / 100 := by rw [hηdef]; exact min_le_left _ _
  have hηρ : η ≤ ρs ^ 2 / N := by rw [hηdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ / N := by rw [hηdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hNη : (N : ℝ) * η ≤ ρs ^ 2 := by
    have := mul_le_mul_of_nonneg_left hηρ hNr.le
    rwa [mul_div_cancel₀ _ hNr.ne'] at this
  have hNηδ : (N : ℝ) * η ≤ δ := by
    have := mul_le_mul_of_nonneg_left hηδ hNr.le
    rwa [mul_div_cancel₀ _ hNr.ne'] at this
  -- the selective engines
  obtain ⟨L, de, ne, se, m, cE, jE, hm0, hmL, hsepoly, hseaug, hsediag, hsel⟩ :=
    selective_blocks (ι := Fin ((d + 1) * nt)) T.ρS hκ0 hκ1 hη0
  have hN0 : (0 : ℕ) < N := hNpos
  let a₀ : SelectiveKernelData T.Slow L de ne :=
    ⟨se, T.lift ⟨0, hN0⟩, m, T.κ, hm0, hmL, TagSetup.coupling ⟨0, hN0⟩⟩
  obtain ⟨_, hjE0, hjEη, hcE0, hcEη, hloss⟩ := hsel a₀ (T.carrier ⟨0, hN0⟩) rfl rfl rfl
    (TagSetup.carrier_independent (T := T) ⟨0, hN0⟩) (TagSetup.lift_mem_span (T := T) ⟨0, hN0⟩)
    (TagSetup.lift_norm (T := T) hT ⟨0, hN0⟩)
  obtain ⟨ME, hMEdef⟩ : ∃ ME : ℝ, ME = a₀.mass := ⟨_, rfl⟩
  have hME0 : 0 ≤ ME := by rw [hMEdef]; exact a₀.mass_positive.le
  have hME1 : ME ≤ 1 := by rw [hMEdef]; exact a₀.mass_le_one
  have hMEloss : 1 - ME < η * jE := by rw [hMEdef]; exact hloss
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌈(1 / 10) / jE⌉₊ := ⟨_, rfl⟩
  have hnge : (1 / 10) / jE ≤ n := by rw [hndef]; exact Nat.le_ceil _
  have hnlt : (n : ℝ) < (1 / 10) / jE + 1 := by
    rw [hndef]; exact Nat.ceil_lt_add_one (by positivity)
  have hq1 : (1 / 10 : ℝ) ≤ n * jE := by
    have := mul_le_mul_of_nonneg_right hnge hjE0.le
    rwa [div_mul_cancel₀ _ hjE0.ne'] at this
  have hq2 : (n : ℝ) * jE ≤ 11 / 100 := by
    have := mul_le_mul_of_nonneg_right hnlt.le hjE0.le
    rw [add_mul, div_mul_cancel₀ _ hjE0.ne', one_mul] at this
    linarith [hjEη.trans_le hη100]
  let a : Fin (N * n) → SelectiveKernelData T.Slow L de ne := fun cc =>
    ⟨se, T.lift (finProdFinEquiv.symm cc).1, m, T.κ, hm0, hmL, TagSetup.coupling _⟩
  let E : EngineSetup T := ⟨L, de, ne, n, a, cE, jE⟩
  have hE : E.Valid := by
    refine ⟨fun cc => rfl, fun cc => ?_, hcE0, hjE0, fun cc => hseaug, fun cc => hsediag, hq1, hq2,
      fun cc => hsepoly⟩
    exact (hsel (a cc) (E.φ cc) rfl rfl rfl (TagSetup.carrier_independent (T := T) _)
      (TagSetup.lift_mem_span (T := T) _) (TagSetup.lift_norm (T := T) hT _)).1
  -- the model conclusions
  have hNn : (0 : ℝ) ≤ (N : ℝ) * n := by positivity
  have hang : ((T.N * E.n : ℕ) : ℝ) * E.cE ≤ ρs ^ 2 := by
    change ((N * n : ℕ) : ℝ) * cE ≤ ρs ^ 2
    push_cast
    have h1 : (N : ℝ) * n * cE ≤ (N : ℝ) * n * (η * jE) :=
      mul_le_mul_of_nonneg_left hcEη.le hNn
    have h2 : (N : ℝ) * n * (η * jE) = ((N : ℝ) * η) * ((n : ℝ) * jE) := by ring
    have h3 : ((N : ℝ) * η) * ((n : ℝ) * jE) ≤ ρs ^ 2 * 1 :=
      mul_le_mul hNη (by linarith only [hq2]) (by positivity) (sq_nonneg _)
    linarith only [h1, h2, h3]
  have hlam : ((T.N * E.n : ℕ) : ℝ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤
      ρs ^ 2 + 11 / 100 * 22 := by
    have hrest : (E.n : ℝ) * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤ 11 / 100 * 22 := by
      change (n : ℝ) * jE * (1 - T.α ^ 2 + N * T.α ^ 2) ≤ _
      rw [hTα]
      have h1 : 1 - α ^ 2 + N * α ^ 2 ≤ 22 := by linarith only [hNsmall, hα2]
      have hα2le : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
      have h0 : 0 ≤ 1 - α ^ 2 + N * α ^ 2 := by linarith only [hNbig, hα2le]
      have h2 := mul_le_mul hq2 h1 h0 (by norm_num : (0 : ℝ) ≤ 11 / 100)
      linarith only [h2]
    linarith only [hrest, hang]
  obtain ⟨hind, hprefix, b, hb⟩ := EngineSetup.model_main hT hE hμ hK hpre hρs0.le
    (by linarith only [hρs3]) hang hlam
  -- the output
  refine ⟨E.D, T.N * E.n * E.q, E.Wflat, E.M, E.newLam, E.newFreq,
    EngineSetup.isMixedTrigPoly_Wflat hT hE,
    fun t x => ⟨EngineSetup.Wraw_pos t _, EngineSetup.Wraw_le_one t _⟩,
    EngineSetup.integral_Wflat, ?_, EngineSetup.newFreq_ne_zero,
    fun k k' h => EngineSetup.newFreq_injective (congrArg Prod.snd h), ?_, ?_, ?_⟩
  · -- the loss
    have hM : E.M = st.mass ^ T.Mt * ME ^ (N * n) := by
      change st.mass ^ T.Mt * ∏ cc : Fin (N * n), (a cc).mass = _
      have hall : ∀ cc, (a cc).mass = ME := fun cc => by rw [hMEdef]; rfl
      simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hst0 : 0 ≤ st.mass := st.toTorusWeight.mass_pos.le
    have hst1 : st.mass ≤ 1 := st.toTorusWeight.mass_le_one
    have h1 := one_sub_mul_le (pow_nonneg hst0 T.Mt) (pow_le_one₀ hst0 hst1)
      (pow_nonneg hME0 (N * n)) (pow_le_one₀ hME0 hME1)
    have h2 := one_sub_pow_le hst0 hst1 T.Mt
    have h3 := one_sub_pow_le hME0 hME1 (N * n)
    have hMt : (T.Mt : ℝ) = N * ((d + 1 : ℕ) : ℝ) := by
      change ((N * (d + 1) : ℕ) : ℝ) = _
      push_cast; ring
    have h4 : (T.Mt : ℝ) * (1 - st.mass) ≤ δ / 4 := by
      rw [hmass, hMt]
      have h5 := hεtδ.le
      rw [le_div_iff₀ (by positivity)] at h5
      have h6 : (N : ℝ) * ((d + 1 : ℕ) : ℝ) * (1 - (1 - εt)) = N * ((d + 1 : ℕ) : ℝ) * εt := by
        ring
      rw [h6]
      have h7 : (N : ℝ) * ((d + 1 : ℕ) : ℝ) * εt ≤ δ / 4 := by
        have h8 : δ / (4 * N * ((d + 1 : ℕ) : ℝ)) * (4 * N * ((d + 1 : ℕ) : ℝ)) = δ := by
          field_simp
        nlinarith only [h5, h8, hεt0, hNr, hJ]
      exact h7
    have h5 : ((N * n : ℕ) : ℝ) * (1 - ME) ≤ (11 / 100) * δ := by
      push_cast
      have h6 : (N : ℝ) * n * (1 - ME) ≤ (N : ℝ) * n * (η * jE) :=
        mul_le_mul_of_nonneg_left hMEloss.le hNn
      have h7 : (N : ℝ) * n * (η * jE) = ((N : ℝ) * η) * ((n : ℝ) * jE) := by ring
      have h8 : ((N : ℝ) * η) * ((n : ℝ) * jE) ≤ δ * (11 / 100) :=
        mul_le_mul hNηδ hq2 (by positivity) hδ.le
      linarith only [h6, h7, h8]
    rw [hM]
    have h9 : (T.Mt : ℝ) * (1 - st.mass) = ((T.Mt : ℕ) : ℝ) * (1 - st.mass) := rfl
    linarith only [h1, h2, h3, h4, h5, hδ]
  · -- positive definiteness
    change (productGram T.w E.Wflat E.Λ E.κ).PosDef
    rw [EngineSetup.productGram_eq]
    have hc : (0 : ℂ) < (((∫ s, T.w.density s) * E.M : ℝ) : ℂ) := by
      exact_mod_cast mul_pos (weight_integral_pos T.w) EngineSetup.M_pos
    exact (Matrix.posDef_gram_iff_linearIndependent.mpr hind).smul hc
  · -- all prefixes
    intro j
    change (prefixGramDifference (max K 12 + τ) (cutMatrix j)
      (productGram T.w E.Wflat E.Λ E.κ)).PosDef
    rw [EngineSetup.productGram_eq]
    have hρ2 : ρs ^ 2 ≤ 1 / 9 := by nlinarith only [hρs0, hρs3]
    exact EngineSetup.prefix_posDef hind hprefix
      (prefix_margin hK hτ hρs0.le hρs3 hρsτ (by linarith only [hρ2]))
      (mul_pos (weight_integral_pos T.w) EngineSetup.M_pos) j
  · -- the residual error
    change E.M * (∫ t, T.w.density t) -
      gramCapture (productGram T.w E.Wflat E.Λ E.κ) (productSource T.w E.Wflat E.Λ E.κ T.ξ) < _
    have herr := EngineSetup.raw_error_le hind hb
    have hM1 := EngineSetup.M_le_one (E := E)
    have hM0 := EngineSetup.M_pos (E := E)
    have hZw : (∫ s, T.w.density s) = Z := hZdef.symm
    rw [hZw] at herr
    rw [hZw]
    have hres' : Z * ‖T.resid‖ ^ 2 = distanceSq w μ ξ := by rw [hTres]; exact hres
    have hfinal : (Z * E.M) * ((2 / 5) * ‖T.resid‖ ^ 2) = (2 / 5) * E.M * distanceSq w μ ξ := by
      rw [← hres']; ring
    have hlt : (2 / 5) * E.M * distanceSq w μ ξ < (1 / 2) * distanceSq w μ ξ := by
      nlinarith only [hM1, hM0, hdist]
    linarith only [herr, hfinal, hlt]

end SchauderTranslates
