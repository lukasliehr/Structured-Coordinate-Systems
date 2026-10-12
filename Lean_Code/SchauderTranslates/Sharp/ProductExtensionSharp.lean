import Lean_Code.SchauderTranslates.ProductRaw
import Lean_Code.SchauderTranslates.ProductExtensionProof
import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.SchauderTranslates.Sharp.SelectiveSupplySharp
import Lean_Code.SchauderTranslates.Sharp.ProductModelSharp
import Lean_Code.SchauderTranslates.Sharp.RealResidual
import Lean_Code.SchauderTranslates.Sharp.Evenness

/-!
# The sharp finite extension on a product space (paper: `h2:prop:extension`, product part)

Sharp counterpart of `ProductExtensionProof.lean`. For `0 < u ≤ 1/100` and the sharp
scalar contracts with excess `u`: for an even weight `w`, an ordered list of characters with
prefix constant `K` and a target at positive distance, there are a product kernel `W` on
`ℝ × 𝕋^D` (a finite mixed trigonometric polynomial with `0 < W ≤ 1`, constant conditional
mass `M > 1 - δ`, invariant under simultaneous inversion `(t, y) ↦ (-t, -y)`) and new
mixed characters such that in the raw product measure

* all prefix bounds hold strictly with constant `max K (1 + 10u) + τ`;
* the squared projection error is `< (1 - c_*/2) · dist²`, `c_* = u / (1 + 2u)`.

The order of the choices follows the paper: the residual (with real coefficients) and the
tag gain `z` (with `(d+1) z ≤ u`, so `K_V² ≤ (1+u)³`), then `α` and `N`, then a tag block
of gain exactly `z`, the coupling `κ`, and only then the selective engines (`2ε ≤ u`,
`K_s < 1 + u`, hence `K_sel² ≤ 1 + 16u`) and their number of copies (`n j ≈ u/20`).
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction ProductEngines

/-- The sharp product-space extension: `ProductExtension` with `12` replaced by `Kstar`, the
factor `1/2` by `θ`, for even weights, with a kernel invariant under simultaneous
inversion. -/
def ProductExtensionSharp (Kstar θ : ℝ) : Prop :=
  ∀ (w : Weight), (∀ t, w.density (-t) = w.density t) →
    ∀ (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
    Function.Injective μ → 1 ≤ K → PrefixBound w μ K →
    0 < distanceSq w μ ξ → 0 < δ → 0 < τ →
    ∃ (D r : ℕ) (W : ℝ → UnitAddTorus (Fin D) → ℝ) (M : ℝ)
      (lam : Fin r → ℝ) (k : Fin r → (Fin D → ℤ)),
      IsMixedTrigPoly (fun t y => (W t y : ℂ)) ∧
      (∀ t y, 0 < W t y ∧ W t y ≤ 1) ∧
      (∀ t y, W (-t) (-y) = W t y) ∧
      (∀ t, (∫ y, W t y ∂torusMeasure D) = M) ∧ 1 - M < δ ∧
      (∀ a, k a ≠ 0) ∧ Function.Injective (fun a => (lam a, k a)) ∧
      (productGram w W (Fin.append μ lam) (Fin.append 0 k)).PosDef ∧
      (∀ j : ℕ, (prefixGramDifference (max K Kstar + τ) (cutMatrix j)
        (productGram w W (Fin.append μ lam) (Fin.append 0 k))).PosDef) ∧
      M * (∫ t, w.density t) -
          gramCapture (productGram w W (Fin.append μ lam) (Fin.append 0 k))
            (productSource w W (Fin.append μ lam) (Fin.append 0 k) ξ) <
        θ * distanceSq w μ ξ

/-! ### Numerical bookkeeping -/

/-- The arithmetic of the prefix margin, for a general base constant. -/
theorem prefix_margin_sharp {K₁ τ ρs Q : ℝ} (hK₁ : 1 ≤ K₁) (hτ : 0 < τ)
    (hρ0 : 0 ≤ ρs) (hρ3 : ρs ≤ 1 / 3) (hρτ : ρs ≤ τ / (4 * K₁))
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ K₁ ^ 2) :
    (1 + ρs) / (1 - ρs) * Q < (K₁ + τ) ^ 2 := by
  have hK₁0 : 0 < K₁ := by linarith
  have hfrac : (1 + ρs) / (1 - ρs) ≤ 1 + 3 * ρs := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 3 * ρs * K₁ ^ 2 ≤ (3 / 4) * τ * K₁ := by
    have h4 : ρs * (4 * K₁) ≤ τ := (le_div_iff₀ (by positivity)).mp hρτ
    nlinarith
  calc (1 + ρs) / (1 - ρs) * Q
      ≤ (1 + 3 * ρs) * K₁ ^ 2 := by
        apply mul_le_mul hfrac hQ hQ0 (by linarith)
    _ = K₁ ^ 2 + 3 * ρs * K₁ ^ 2 := by ring
    _ ≤ K₁ ^ 2 + (3 / 4) * τ * K₁ := by linarith
    _ < (K₁ + τ) ^ 2 := by nlinarith

/-- Paper: `K_sel² < 1 + (√3 + √5)² u < 1 + 16u`. -/
theorem selectivePrefixSqSharp_le {u A B : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 100)
    (hA1 : 1 ≤ A) (hA : A ≤ (1 + u) ^ 2) (hB1 : 1 ≤ B) (hB : B ≤ (1 + u) ^ 4) :
    selectivePrefixSqSharp A B ≤ 1 + 16 * u := by
  have hx0 := Real.sqrt_nonneg (A - 1)
  have hy0 := Real.sqrt_nonneg (B - 1)
  have hx2 : Real.sqrt (A - 1) ^ 2 = A - 1 := Real.sq_sqrt (by linarith)
  have hy2 : Real.sqrt (B - 1) ^ 2 = B - 1 := Real.sq_sqrt (by linarith)
  have hu2 : u ^ 2 ≤ u / 100 := by nlinarith
  have hu3 : u ^ 3 ≤ u / 10000 := by nlinarith
  have hu4 : u ^ 4 ≤ u / 1000000 := by nlinarith
  have hA' : A - 1 ≤ 3 * u := by nlinarith
  have hB' : B - 1 ≤ 5 * u := by nlinarith
  unfold selectivePrefixSqSharp
  nlinarith [sq_nonneg (Real.sqrt (A - 1) - Real.sqrt (B - 1))]

/-- Paper `h2:eq:new-constant`: `(1 + 3u)(1 + 16u) ≤ 1 + 20u < K_*²`. -/
theorem new_constant_le {u K lam Qc : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 100) (hK : 1 ≤ K)
    (hlam : lam ≤ 3 * u) (hQc1 : 1 ≤ Qc) (hQc : Qc ≤ 1 + 16 * u) :
    max (K ^ 2) ((1 + lam) * Qc) ≤ max K (1 + 10 * u) ^ 2 := by
  have h1 : K ≤ max K (1 + 10 * u) := le_max_left _ _
  have h2 : 1 + 10 * u ≤ max K (1 + 10 * u) := le_max_right _ _
  apply max_le
  · exact pow_le_pow_left₀ (by linarith) h1 2
  · have h3 : (1 + lam) * Qc ≤ (1 + 3 * u) * (1 + 16 * u) :=
      mul_le_mul (by linarith) hQc (by linarith) (by linarith)
    have h4 : (1 + 3 * u) * (1 + 16 * u) ≤ (1 + 10 * u) ^ 2 := by nlinarith
    have h5 : (1 + 10 * u) ^ 2 ≤ max K (1 + 10 * u) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h2 2
    linarith

/-! ### The extension -/

/-- Paper `h2:prop:extension`, product-space part, with the factor
`ϑ = 1 - c_*/2`, `c_* = u/(1+2u)`. -/
theorem product_space_extension_sharp {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 100)
    (hSup : ScalarSupplySharp u) (hTune : ScalarTuneSharp u) :
    ProductExtensionSharp (1 + 10 * u) (1 - u / (1 + 2 * u) / 2) := by
  intro w hw d μ K ξ δ τ hμ hK hpre hdist hδ hτ
  -- the residual of the target, with real coefficients
  obtain ⟨c, hc0, hcre, horth, hdiff, hres⟩ := residual_exists_real w hw μ ξ
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
  obtain ⟨ct, hct, htune⟩ := hTune
  have hJ : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = min (ct / 2) (u / ((d + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hzdef]; exact lt_min (by positivity) (by positivity)
  have hzct : z < ct := by
    rw [hzdef]; exact (min_le_left _ _).trans_lt (by linarith)
  have hzJ : ((d + 1 : ℕ) : ℝ) * z ≤ u := by
    have h1 : z ≤ u / ((d + 1 : ℕ) : ℝ) := by rw [hzdef]; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans hJ)
    rwa [mul_div_cancel₀ _ (by positivity)] at h2
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
  obtain ⟨dt, nt, st, εt, Kt, hpoly, hstEven, _, _, hεt0, hεtδ, hεt1, hmass, hgain, hKt0, hKt2,
    hcent, _⟩ := htune z (δ / (4 * N * ((d + 1 : ℕ) : ℝ))) hz0 hzct hδt
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
      rw [hgain]; linarith
    · nlinarith
    · change (20 : ℝ) ≤ (N : ℝ) * T.α ^ 2
      rw [hTα]; exact hNbig
  -- the carrier constant `K_V² ≤ (1 + u)³`
  have hcar : ∀ i, FinitePrefixSqBound (fun k => (T.carrier i k).toL2 T.ρS)
      (Real.sqrt ((1 + u) ^ 3) ^ 2) := by
    intro i
    rw [Real.sq_sqrt (by positivity)]
    have h := tag_packet_prefix (M := T.Mt) T.st T.ρ (T.blk i) (TagSetup.blk_injective i) T.lam
      (sq_nonneg Kt) hcent
    apply h.mono
    change (1 + ((d + 1 : ℕ) : ℝ) * st.gain) * Kt ^ 2 ≤ (1 + u) ^ 3
    rw [hgain]
    have h1 : Kt ^ 2 ≤ (1 + u) ^ 2 := pow_le_pow_left₀ hKt0 hKt2.le 2
    have h2 : 1 + ((d + 1 : ℕ) : ℝ) * z ≤ 1 + u := by linarith
    have h3 : 0 ≤ ((d + 1 : ℕ) : ℝ) * z := mul_nonneg (zero_le_one.trans hJ) hz0.le
    calc (1 + ((d + 1 : ℕ) : ℝ) * z) * Kt ^ 2 ≤ (1 + u) * (1 + u) ^ 2 :=
          mul_le_mul h2 h1 (sq_nonneg _) (by linarith)
      _ = (1 + u) ^ 3 := by ring
  have hpow3 : (1 : ℝ) ≤ (1 + u) ^ 3 := by
    have : (1 : ℝ) ≤ 1 + u := by linarith
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (1 + u) ^ 3 := pow_le_pow_left₀ zero_le_one this 3
  have hKV1 : 1 ≤ Real.sqrt ((1 + u) ^ 3) := Real.one_le_sqrt.mpr hpow3
  -- the coupling parameter
  have hκ0 : 0 < T.κ := TagSetup.κ_pos
  have hκ1 : T.κ < 1 := TagSetup.κ_lt_one
  -- the margins
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = max K (1 + 10 * u) := ⟨_, rfl⟩
  have hK₁1 : 1 ≤ K₁ := by rw [hK₁def]; exact hK.trans (le_max_left _ _)
  have hK₁pos : 0 < K₁ := by linarith
  obtain ⟨ρs, hρsdef⟩ : ∃ ρs : ℝ, ρs = min (1 / 3) (τ / (4 * K₁)) := ⟨_, rfl⟩
  have hρs0 : 0 < ρs := by rw [hρsdef]; exact lt_min (by norm_num) (by positivity)
  have hρs3 : ρs ≤ 1 / 3 := by rw [hρsdef]; exact min_le_left _ _
  have hρsτ : ρs ≤ τ / (4 * K₁) := by rw [hρsdef]; exact min_le_right _ _
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ,
      η = min (u / 1000) (min (ρs ^ 2 / N) (min (u / N) (δ / (2 * N)))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hηu : η ≤ u / 1000 := by rw [hηdef]; exact min_le_left _ _
  have hηρ : η ≤ ρs ^ 2 / N := by
    rw [hηdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hηuN : η ≤ u / N := by
    rw [hηdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηδ : η ≤ δ / (2 * N) := by
    rw [hηdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNη : (N : ℝ) * η ≤ ρs ^ 2 := by
    have := mul_le_mul_of_nonneg_left hηρ hNr.le
    rwa [mul_div_cancel₀ _ hNr.ne'] at this
  have hNηu : (N : ℝ) * η ≤ u := by
    have := mul_le_mul_of_nonneg_left hηuN hNr.le
    rwa [mul_div_cancel₀ _ hNr.ne'] at this
  have hNηδ : (N : ℝ) * η ≤ δ / 2 := by
    have := mul_le_mul_of_nonneg_left hηδ hNr.le
    have he : (N : ℝ) * (δ / (2 * N)) = δ / 2 := by field_simp
    rwa [he] at this
  -- the selective engines
  obtain ⟨L, de, ne, se, m, cE, jE, εe, Ks, hm0, hmL, hsepoly, hseEven, hεe0, hεeu, hKs0, hKs1,
    hseaug, hsediag, hsel⟩ :=
    selective_blocks_sharp (ι := Fin ((d + 1) * nt)) hSup T.ρS hκ0 hκ1 hη0
      (show (0 : ℝ) < u / 2 by positivity)
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
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = ⌈(u / 20) / jE⌉₊ := ⟨_, rfl⟩
  have hnge : (u / 20) / jE ≤ n := by rw [hndef]; exact Nat.le_ceil _
  have hnlt : (n : ℝ) < (u / 20) / jE + 1 := by
    rw [hndef]; exact Nat.ceil_lt_add_one (by positivity)
  have hq1 : u / 20 ≤ n * jE := by
    have := mul_le_mul_of_nonneg_right hnge hjE0.le
    rwa [div_mul_cancel₀ _ hjE0.ne'] at this
  have hq2 : (n : ℝ) * jE ≤ u / 20 + u / 1000 := by
    have := mul_le_mul_of_nonneg_right hnlt.le hjE0.le
    rw [add_mul, div_mul_cancel₀ _ hjE0.ne', one_mul] at this
    linarith [hjEη.trans_le hηu]
  have hq2' : (n : ℝ) * jE ≤ 1 := by linarith
  have hq0 : 0 ≤ (n : ℝ) * jE := by positivity
  let a : Fin (N * n) → SelectiveKernelData T.Slow L de ne := fun cc =>
    ⟨se, T.lift (finProdFinEquiv.symm cc).1, m, T.κ, hm0, hmL, TagSetup.coupling _⟩
  let E : EngineSetup T := ⟨L, de, ne, n, a, cE, jE⟩
  have hE : E.ValidSharp := by
    refine ⟨fun cc => rfl, fun cc => ?_, hcE0, hjE0, fun cc => hsepoly⟩
    exact (hsel (a cc) (E.φ cc) rfl rfl rfl (TagSetup.carrier_independent (T := T) _)
      (TagSetup.lift_mem_span (T := T) _) (TagSetup.lift_norm (T := T) hT _)).1
  -- the centered constant of the engines: `K_sel² ≤ 1 + 16u`
  have hKs1' : (1 : ℝ) ≤ max Ks 1 := le_max_right _ _
  have hKsu : max Ks 1 < 1 + u := max_lt hKs1 (by linarith)
  have haug1 : se.AugmentedPrefixSqBound (max Ks 1 ^ 2) :=
    hseaug.mono (pow_le_pow_left₀ hKs0 (le_max_left _ _) 2)
  have hC1 : (1 : ℝ) ≤ 1 + 2 * εe := by linarith
  have hQsel : selectivePrefixSqSharp (max Ks 1 ^ 2)
      ((1 + 2 * εe) * max (Real.sqrt ((1 + u) ^ 3)) 1 ^ 2) ≤ 1 + 16 * u := by
    rw [max_eq_left hKV1, Real.sq_sqrt (by positivity)]
    apply selectivePrefixSqSharp_le hu0 hu1
    · exact one_le_pow₀ hKs1'
    · exact pow_le_pow_left₀ (by linarith only [hKs1']) hKsu.le 2
    · exact one_le_mul_of_one_le_of_one_le hC1 hpow3
    · have h1 : (0 : ℝ) ≤ (1 + u) ^ 3 := by positivity
      calc (1 + 2 * εe) * (1 + u) ^ 3 ≤ (1 + u) * (1 + u) ^ 3 :=
            mul_le_mul_of_nonneg_right (by linarith) h1
        _ = (1 + u) ^ 4 := by ring
  have hfast : ∀ cc, FinitePrefixSqBound (E.Rp cc) (1 + 16 * u) := by
    intro cc
    have h := EngineSetup.fast_prefix_sharp (E := E) hE (KV := Real.sqrt ((1 + u) ^ 3))
      (Ks := max Ks 1) (C := 1 + 2 * εe) (Real.sqrt_nonneg _) hcar hKs1'
      (fun _ => haug1) hC1 (fun _ k => hsediag k) cc
    exact h.mono hQsel
  -- the model conclusions
  have hNn : (0 : ℝ) ≤ (N : ℝ) * n := by positivity
  have hcEtot : (N : ℝ) * n * cE ≤ ((N : ℝ) * η) * ((n : ℝ) * jE) := by
    have h1 : (N : ℝ) * n * cE ≤ (N : ℝ) * n * (η * jE) :=
      mul_le_mul_of_nonneg_left hcEη.le hNn
    have h2 : (N : ℝ) * n * (η * jE) = ((N : ℝ) * η) * ((n : ℝ) * jE) := by ring
    linarith only [h1, h2]
  have hNη0 : 0 ≤ (N : ℝ) * η := by positivity
  have hang : ((T.N * E.n : ℕ) : ℝ) * E.cE ≤ ρs ^ 2 := by
    change ((N * n : ℕ) : ℝ) * cE ≤ ρs ^ 2
    push_cast
    have h3 : ((N : ℝ) * η) * ((n : ℝ) * jE) ≤ ρs ^ 2 * 1 :=
      mul_le_mul hNη hq2' hq0 (sq_nonneg _)
    linarith only [hcEtot, h3]
  have hlam : ((T.N * E.n : ℕ) : ℝ) * E.cE + E.n * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤
      3 * u := by
    have hfirst : ((T.N * E.n : ℕ) : ℝ) * E.cE ≤ u := by
      change ((N * n : ℕ) : ℝ) * cE ≤ u
      push_cast
      have h3 : ((N : ℝ) * η) * ((n : ℝ) * jE) ≤ u * 1 :=
        mul_le_mul hNηu hq2' hq0 hu0.le
      linarith only [hcEtot, h3]
    have hrest : (E.n : ℝ) * E.jE * (1 - T.α ^ 2 + T.N * T.α ^ 2) ≤ (u / 20 + u / 1000) * 22 := by
      change (n : ℝ) * jE * (1 - T.α ^ 2 + N * T.α ^ 2) ≤ _
      rw [hTα]
      have h1 : 1 - α ^ 2 + N * α ^ 2 ≤ 22 := by linarith only [hNsmall, hα2]
      have hα2le : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
      have h0 : 0 ≤ 1 - α ^ 2 + N * α ^ 2 := by linarith only [hNbig, hα2le]
      exact mul_le_mul hq2 h1 h0 (by positivity)
    linarith only [hrest, hfirst, hu0]
  have hQ : u ≤ E.n * E.jE * (T.N * T.α ^ 2) := by
    change u ≤ (n : ℝ) * jE * (N * T.α ^ 2)
    rw [hTα]
    have h1 : (u / 20) * 20 ≤ (n : ℝ) * jE * (N * α ^ 2) :=
      mul_le_mul hq1 hNbig (by norm_num) hq0
    linarith only [h1]
  have hρs1 : ρs < 1 := by linarith only [hρs3]
  obtain ⟨hind, hprefix, b, hb⟩ := EngineSetup.model_main_sharp hT hE hμ hK hpre hρs0.le hρs1
    (show (1 : ℝ) ≤ 1 + 16 * u by linarith) hfast hang hlam hu0 hQ
  -- the output
  refine ⟨E.D, T.N * E.n * E.q, E.Wflat, E.M, E.newLam, E.newFreq,
    EngineSetup.isMixedTrigPoly_Wflat_sharp hT hE,
    fun t x => ⟨EngineSetup.Wraw_pos t _, EngineSetup.Wraw_le_one t _⟩, ?_,
    EngineSetup.integral_Wflat, ?_, EngineSetup.newFreq_ne_zero,
    fun k k' h => EngineSetup.newFreq_injective (congrArg Prod.snd h), ?_, ?_, ?_⟩
  · -- invariance under simultaneous inversion
    intro t x
    refine Wflat_neg E hstEven (fun cc t' y => ?_) (fun cc => hseEven) t x
    rw [hE.e_eq]
    exact lift_neg T hcre hstEven _ t' y
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
    have h5 : ((N * n : ℕ) : ℝ) * (1 - ME) ≤ δ / 2 := by
      push_cast
      have h6 : (N : ℝ) * n * (1 - ME) ≤ (N : ℝ) * n * (η * jE) :=
        mul_le_mul_of_nonneg_left hMEloss.le hNn
      have h7 : (N : ℝ) * n * (η * jE) = ((N : ℝ) * η) * ((n : ℝ) * jE) := by ring
      have h8 : ((N : ℝ) * η) * ((n : ℝ) * jE) ≤ (δ / 2) * 1 :=
        mul_le_mul hNηδ hq2' hq0 (by positivity)
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
    change (prefixGramDifference (max K (1 + 10 * u) + τ) (cutMatrix j)
      (productGram T.w E.Wflat E.Λ E.κ)).PosDef
    rw [EngineSetup.productGram_eq, ← hK₁def]
    have hQle : max (K ^ 2) ((1 + 3 * u) * (1 + 16 * u)) ≤ K₁ ^ 2 := by
      rw [hK₁def]
      exact new_constant_le hu0 hu1 hK le_rfl (by linarith) le_rfl
    have hQ0 : 0 ≤ max (K ^ 2) ((1 + 3 * u) * (1 + 16 * u)) :=
      le_max_of_le_left (sq_nonneg _)
    exact EngineSetup.prefix_posDef hind hprefix
      (prefix_margin_sharp hK₁1 hτ hρs0.le hρs3 hρsτ hQ0 hQle)
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
    obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = u / (1 + 2 * u) := ⟨_, rfl⟩
    rw [← hcsdef] at herr ⊢
    have hcs0 : 0 < cs := by rw [hcsdef]; positivity
    have hcs1 : cs < 1 := by
      rw [hcsdef, div_lt_one (by positivity)]
      linarith
    have hfinal : (Z * E.M) * ((1 - cs) * ‖T.resid‖ ^ 2) = (1 - cs) * E.M * distanceSq w μ ξ := by
      rw [← hres']; ring
    have hlt : (1 - cs) * E.M * distanceSq w μ ξ < (1 - cs / 2) * distanceSq w μ ξ := by
      have h1 : (1 - cs) * E.M ≤ 1 - cs :=
        mul_le_of_le_one_right (by linarith) hM1
      have h2 : (1 - cs) * E.M * distanceSq w μ ξ ≤ (1 - cs) * distanceSq w μ ξ :=
        mul_le_mul_of_nonneg_right h1 hdist.le
      nlinarith only [h2, hcs0, hdist]
    linarith only [herr, hfinal, hlt]

end SchauderTranslates.Sharp
