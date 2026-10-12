import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.SchauderTranslates.LineTransferWeight

/-!
# Iterating a contracting extension step

`FiniteExtensionSharp Kstar` asks for a one-shot extension which halves the squared distance
of the target. The construction on the line only gives a contraction factor `θ < 1` per step
(`FiniteExtensionStep Kstar θ`). Here the step is repeated `m` times for the same target, with
`θ ^ m ≤ 1 / 2`:

* if the target has already entered the span, the remaining steps are left unchanged
  (`Iteration.step_total`);
* the factors are multiplied; the product is a positive even trigonometric polynomial bounded
  by one, and its loss against the reference weight is at most the sum of the individual
  losses, by `1 - W₁ W₂ ≤ (1 - W₁) + (1 - W₂)` (`Iteration.loss_mul_lt`);
* the loss and increment budgets are split at every step, so the final prefix constant is at
  most `max K Kstar + τ` (`Iteration.step_iterate`).
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction

/-- One extension step on the line with contraction factor `θ` (instead of `1/2`). -/
def FiniteExtensionStep (Kstar θ : ℝ) : Prop :=
  ∀ (w w₀ : Weight), (∫ t, w₀.density t) = 1 → (∀ t, w.density (-t) = w.density t) →
    ∀ (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
      Function.Injective μ → 1 ≤ K → PrefixBound w μ K →
      0 < distanceSq w μ ξ → 0 < δ → 0 < τ →
      ∃ (r : ℕ) (ν : Fin (d + r) → ℝ) (W : ℝ → ℝ) (w' : Weight),
        Function.Injective ν ∧
        (∀ i : Fin d, ν (Fin.castAdd r i) = μ i) ∧
        IsTrigPolynomial W ∧ (∀ t, 0 < W t ∧ W t ≤ 1) ∧ (∀ t, W (-t) = W t) ∧
        (∀ t, w'.density t = w.density t * W t) ∧
        (∫ t, w₀.density t * (1 - W t)) < δ ∧
        distanceSq w' ν ξ ≤ θ * distanceSq w μ ξ ∧
        PrefixBound w' ν (max K Kstar + τ)

namespace Iteration

/-! ### Prefix bounds -/

/-- Enlarging the constant preserves a prefix bound. -/
theorem prefixBound_mono {w : Weight} {d : ℕ} {μ : Fin d → ℝ} {K K' : ℝ}
    (h : PrefixBound w μ K) (hK : 0 ≤ K) (hKK' : K ≤ K') : PrefixBound w μ K' := fun k c =>
  (h k c).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK hKK' 2)
    (LimitAssembly.normSq_nonneg _ _))

/-! ### Trigonometric polynomials -/

theorem isTrigPolynomial_one : IsTrigPolynomial (fun _ => (1 : ℝ)) :=
  ⟨1, fun _ => 0, fun _ => 1, fun t => by simp [synthesis]⟩

/-- Products of trigonometric polynomials are trigonometric polynomials. -/
theorem isTrigPolynomial_mul {W₁ W₂ : ℝ → ℝ} (h₁ : IsTrigPolynomial W₁)
    (h₂ : IsTrigPolynomial W₂) : IsTrigPolynomial (fun t => W₁ t * W₂ t) := by
  obtain ⟨d₁, ξ₁, c₁, h₁⟩ := h₁
  obtain ⟨d₂, ξ₂, c₂, h₂⟩ := h₂
  refine ⟨d₁ * d₂, fun k => ξ₁ (finProdFinEquiv.symm k).1 + ξ₂ (finProdFinEquiv.symm k).2,
    fun k => c₁ (finProdFinEquiv.symm k).1 * c₂ (finProdFinEquiv.symm k).2, fun t => ?_⟩
  rw [Complex.ofReal_mul, h₁ t, h₂ t]
  simp only [synthesis]
  rw [Fintype.sum_mul_sum]
  refine Eq.trans ?_ ((Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin d₁ × Fin d₂ => c₁ p.1 * c₂ p.2 * character (ξ₁ p.1 + ξ₂ p.2) t)).trans
      (Fintype.sum_prod_type _)).symm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show c₁ i * character (ξ₁ i) t * (c₂ j * character (ξ₂ j) t) =
    c₁ i * c₂ j * character (ξ₁ i + ξ₂ j) t
  rw [← LineTransfer.character_mul]
  ring

theorem continuous_of_isTrigPolynomial {W : ℝ → ℝ} (h : IsTrigPolynomial W) :
    Continuous W := by
  obtain ⟨d, ξ, c, hW⟩ := h
  have he : W = fun t => (synthesis ξ c t).re := by
    funext t
    rw [← hW t, Complex.ofReal_re]
  rw [he]
  exact Complex.continuous_re.comp (LimitAssembly.continuous_synthesis ξ c)

/-! ### Transport along an equality of lengths -/

theorem prefixBound_cast {w : Weight} {n n' : ℕ} (h : n = n') (ν : Fin n' → ℝ) (K : ℝ) :
    PrefixBound w (fun i => ν (Fin.cast h i)) K ↔ PrefixBound w ν K := by
  subst h
  rfl

theorem distanceSq_cast {w : Weight} {n n' : ℕ} (h : n = n') (ν : Fin n' → ℝ) (ξ : ℝ) :
    distanceSq w (fun i => ν (Fin.cast h i)) ξ = distanceSq w ν ξ := by
  subst h
  rfl

/-! ### The loss of a product -/

theorem integrable_loss (w₀ : Weight) {W : ℝ → ℝ} (hc : Continuous W)
    (hW : ∀ t, 0 < W t ∧ W t ≤ 1) : Integrable (fun t => w₀.density t * (1 - W t)) := by
  refine w₀.integrable.mul_bdd (c := 1) (continuous_const.sub hc).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun t => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hW t).2], by linarith [(hW t).1]⟩

/-- The loss of a product is at most the sum of the losses:
`1 - W₁ W₂ ≤ (1 - W₁) + (1 - W₂)` for `W₁, W₂ ∈ (0, 1]`. -/
theorem loss_mul_lt (w₀ : Weight) {W₁ W₂ : ℝ → ℝ} (hc₁ : Continuous W₁) (hc₂ : Continuous W₂)
    (hW₁ : ∀ t, 0 < W₁ t ∧ W₁ t ≤ 1) (hW₂ : ∀ t, 0 < W₂ t ∧ W₂ t ≤ 1) {δ₁ δ₂ : ℝ}
    (h₁ : (∫ t, w₀.density t * (1 - W₁ t)) < δ₁)
    (h₂ : (∫ t, w₀.density t * (1 - W₂ t)) < δ₂) :
    (∫ t, w₀.density t * (1 - W₁ t * W₂ t)) < δ₁ + δ₂ := by
  have hi₁ := integrable_loss w₀ hc₁ hW₁
  have hi₂ := integrable_loss w₀ hc₂ hW₂
  have hle : (∫ t, w₀.density t * (1 - W₁ t * W₂ t)) ≤
      ∫ t, (w₀.density t * (1 - W₁ t) + w₀.density t * (1 - W₂ t)) := by
    apply integral_mono_of_nonneg
    · filter_upwards [w₀.positive] with t ht
      have h := mul_le_one₀ (hW₁ t).2 (hW₂ t).1.le (hW₂ t).2
      exact mul_nonneg ht.le (by linarith)
    · exact hi₁.add hi₂
    · filter_upwards [w₀.positive] with t ht
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ ht.le
      nlinarith [mul_nonneg (sub_nonneg.2 (hW₁ t).2) (sub_nonneg.2 (hW₂ t).2)]
  rw [integral_add hi₁ hi₂] at hle
  linarith

/-! ### Extensions -/

/-- The conclusion of an extension step for the list `μ` and the target `ξ`: loss budget `δ`
against `w₀`, contraction factor `c` of the squared distance, and new prefix constant `K'`. -/
abbrev HasExtension (w w₀ : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ δ c K' : ℝ) : Prop :=
  ∃ (r : ℕ) (ν : Fin (d + r) → ℝ) (W : ℝ → ℝ) (w' : Weight),
    Function.Injective ν ∧
    (∀ i : Fin d, ν (Fin.castAdd r i) = μ i) ∧
    IsTrigPolynomial W ∧ (∀ t, 0 < W t ∧ W t ≤ 1) ∧ (∀ t, W (-t) = W t) ∧
    (∀ t, w'.density t = w.density t * W t) ∧
    (∫ t, w₀.density t * (1 - W t)) < δ ∧
    distanceSq w' ν ξ ≤ c * distanceSq w μ ξ ∧
    PrefixBound w' ν K'

/-- The trivial extension: nothing is appended and the weight is unchanged. -/
theorem hasExtension_refl (w w₀ : Weight) {d : ℕ} {μ : Fin d → ℝ} {ξ δ c K' : ℝ}
    (hμ : Function.Injective μ) (hδ : 0 < δ)
    (hdist : distanceSq w μ ξ ≤ c * distanceSq w μ ξ) (hpre : PrefixBound w μ K') :
    HasExtension w w₀ μ ξ δ c K' := by
  refine ⟨0, μ, fun _ => 1, w, hμ, fun _ => rfl, isTrigPolynomial_one,
    fun _ => ⟨one_pos, le_rfl⟩, fun _ => rfl, fun t => (mul_one _).symm, ?_, hdist, hpre⟩
  simp only [sub_self, mul_zero, integral_zero]
  exact hδ

/-- The step without the positivity hypothesis on the distance: if the target is already in
the span, the trivial extension is used. -/
theorem step_total {Kstar θ : ℝ} (h : FiniteExtensionStep Kstar θ)
    (w w₀ : Weight) (hw₀ : (∫ t, w₀.density t) = 1) (hw : ∀ t, w.density (-t) = w.density t)
    {d : ℕ} (μ : Fin d → ℝ) (K ξ δ τ : ℝ) (hμ : Function.Injective μ) (hK : 1 ≤ K)
    (hpre : PrefixBound w μ K) (hδ : 0 < δ) (hτ : 0 < τ) :
    HasExtension w w₀ μ ξ δ θ (max K Kstar + τ) := by
  by_cases hpos : 0 < distanceSq w μ ξ
  · exact h w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre hpos hδ hτ
  · have h0 : distanceSq w μ ξ = 0 :=
      le_antisymm (not_lt.mp hpos) (LimitAssembly.distanceSq_nonneg w μ ξ)
    refine hasExtension_refl w w₀ hμ hδ (by rw [h0, mul_zero])
      (prefixBound_mono hpre (by linarith) ?_)
    have := le_max_left K Kstar
    linarith

/-- `m` successive steps for the same target: the squared distance is contracted by `θ ^ m`,
while the total loss and the total increment of the prefix constant stay within budget. -/
theorem step_iterate {Kstar θ : ℝ} (hθ0 : 0 ≤ θ) (h : FiniteExtensionStep Kstar θ) (m : ℕ) :
    ∀ (w w₀ : Weight), (∫ t, w₀.density t) = 1 → (∀ t, w.density (-t) = w.density t) →
      ∀ (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
        Function.Injective μ → 1 ≤ K → PrefixBound w μ K → 0 < δ → 0 < τ →
        HasExtension w w₀ μ ξ δ (θ ^ m) (max K Kstar + τ) := by
  induction m with
  | zero =>
    intro w w₀ _ _ d μ K ξ δ τ hμ hK hpre hδ hτ
    refine hasExtension_refl w w₀ hμ hδ (by rw [pow_zero, one_mul])
      (prefixBound_mono hpre (by linarith) ?_)
    have := le_max_left K Kstar
    linarith
  | succ m ih =>
    intro w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre hδ hτ
    obtain ⟨r₁, ν₁, W₁, w₁, hν₁, hext₁, htrig₁, hW₁, heven₁, hdens₁, hloss₁, hdist₁, hpre₁⟩ :=
      ih w w₀ hw₀ hw d μ K ξ (δ / 2) (τ / 2) hμ hK hpre (half_pos hδ) (half_pos hτ)
    have hK₁ : 1 ≤ max K Kstar + τ / 2 := by
      have := le_max_left K Kstar
      linarith
    have hw₁ : ∀ t, w₁.density (-t) = w₁.density t := by
      intro t
      rw [hdens₁, hdens₁, hw, heven₁]
    obtain ⟨r₂, ν₂, W₂, w₂, hν₂, hext₂, htrig₂, hW₂, heven₂, hdens₂, hloss₂, hdist₂, hpre₂⟩ :=
      step_total h w₁ w₀ hw₀ hw₁ ν₁ (max K Kstar + τ / 2) ξ (δ / 2) (τ / 2) hν₁ hK₁ hpre₁
        (half_pos hδ) (half_pos hτ)
    have hn : d + (r₁ + r₂) = d + r₁ + r₂ := (Nat.add_assoc d r₁ r₂).symm
    refine ⟨r₁ + r₂, fun i => ν₂ (Fin.cast hn i), fun t => W₁ t * W₂ t, w₂,
      hν₂.comp (Fin.cast_injective hn), ?_, isTrigPolynomial_mul htrig₁ htrig₂, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro i
      have hi : Fin.cast hn (Fin.castAdd (r₁ + r₂) i) = Fin.castAdd r₂ (Fin.castAdd r₁ i) :=
        Fin.ext rfl
      show ν₂ (Fin.cast hn (Fin.castAdd (r₁ + r₂) i)) = μ i
      rw [hi, hext₂, hext₁]
    · intro t
      exact ⟨mul_pos (hW₁ t).1 (hW₂ t).1, mul_le_one₀ (hW₁ t).2 (hW₂ t).1.le (hW₂ t).2⟩
    · intro t
      show W₁ (-t) * W₂ (-t) = W₁ t * W₂ t
      rw [heven₁, heven₂]
    · intro t
      rw [hdens₂, hdens₁, mul_assoc]
    · have hloss := loss_mul_lt w₀ (continuous_of_isTrigPolynomial htrig₁)
        (continuous_of_isTrigPolynomial htrig₂) hW₁ hW₂ hloss₁ hloss₂
      rwa [add_halves] at hloss
    · calc
        distanceSq w₂ (fun i => ν₂ (Fin.cast hn i)) ξ = distanceSq w₂ ν₂ ξ :=
          distanceSq_cast hn ν₂ ξ
        _ ≤ θ * distanceSq w₁ ν₁ ξ := hdist₂
        _ ≤ θ * (θ ^ m * distanceSq w μ ξ) := mul_le_mul_of_nonneg_left hdist₁ hθ0
        _ = θ ^ (m + 1) * distanceSq w μ ξ := by ring
    · refine (prefixBound_cast hn ν₂ _).mpr ?_
      have hmax : max (max K Kstar + τ / 2) Kstar = max K Kstar + τ / 2 :=
        max_eq_left (by have := le_max_right K Kstar; linarith)
      have he : max K Kstar + τ = max K Kstar + τ / 2 + τ / 2 := by ring
      rw [hmax] at hpre₂
      rw [he]
      exact hpre₂

end Iteration

/-- A contracting step with factor `θ < 1` yields the halving extension: choose `m` with
`θ ^ m ≤ 1 / 2` and repeat the step `m` times for the same target. -/
theorem finiteExtensionSharp_of_step {Kstar θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : FiniteExtensionStep Kstar θ) : FiniteExtensionSharp Kstar := by
  intro w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre _ hδ hτ
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hθ1
  obtain ⟨r, ν, W, w', hν, hext, htrig, hW, heven, hdens, hloss, hdist, hpre'⟩ :=
    Iteration.step_iterate hθ0 h m w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre hδ hτ
  exact ⟨r, ν, W, w', hν, hext, htrig, hW, heven, hdens, hloss,
    hdist.trans (mul_le_mul_of_nonneg_right hm.le (LimitAssembly.distanceSq_nonneg w μ ξ)),
    hpre'⟩

/-- The sharp finite extension property is monotone in the constant. -/
theorem FiniteExtensionSharp.mono {K₁ K₂ : ℝ} (h12 : K₁ ≤ K₂)
    (h : FiniteExtensionSharp K₁) : FiniteExtensionSharp K₂ := by
  intro w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre hpos hδ hτ
  obtain ⟨r, ν, W, w', hν, hext, htrig, hW, heven, hdens, hloss, hdist, hpre'⟩ :=
    h w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpre hpos hδ hτ
  refine ⟨r, ν, W, w', hν, hext, htrig, hW, heven, hdens, hloss, hdist,
    Iteration.prefixBound_mono hpre' ?_ ?_⟩
  · have := le_max_left K K₁
    linarith
  · have := max_le_max_left K h12
    linarith

end SchauderTranslates.Sharp
