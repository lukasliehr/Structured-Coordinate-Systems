import Lean_Code.SchauderTranslates.LineTransferWeight

/-!
# Finite extension on the line (`extend:line`)

The product-space extension `ProductExtension` (blueprint `extend:product`) is transferred
to the line by substituting the torus variables `y = A ω t`. The direction `ω` avoids all
finitely many relevant frequency hyperplanes and all collisions of the new frequencies
(`transfer:avoid`); every Gram entry, source moment, the target norm and the reference
loss converge (`transfer:moments`); and the strict finite Gram conclusions persist
(`transfer:stable`). This proves `Construction.FiniteExtensionPrinciple`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

namespace LineTransfer

/-- The transfer step for general product data: one direction and one scale give a line
weight on which all strict finite conclusions hold. -/
theorem line_extension_core (w w₀ : Weight) (hw₀ : (∫ t, w₀.density t) = 1)
    {D n : ℕ} (W : ℝ → UnitAddTorus (Fin D) → ℝ) (M : ℝ)
    (Λ : Fin n → ℝ) (κ : Fin n → (Fin D → ℤ)) (ξ δ L E : ℝ)
    (hWpoly : IsMixedTrigPoly (fun t y => (W t y : ℂ)))
    (hWpos : ∀ t y, 0 < W t y ∧ W t y ≤ 1)
    (hWmass : ∀ t, (∫ y, W t y ∂torusMeasure D) = M) (hM : 1 - M < δ)
    (hinj : Function.Injective (fun a => (Λ a, κ a)))
    (hBpos : (productGram w W Λ κ).PosDef)
    (hBpref : ∀ j : ℕ, (prefixGramDifference L (cutMatrix j) (productGram w W Λ κ)).PosDef)
    (hBcap : M * (∫ t, w.density t) -
      gramCapture (productGram w W Λ κ) (productSource w W Λ κ ξ) < E) :
    ∃ (ω : Fin D → ℝ) (A : ℝ),
      Function.Injective (fun a => Λ a + A * frequencyDot (κ a) ω) ∧
      (∫ t, w₀.density t * (1 - lineKernel W ω A t)) < δ ∧
      distanceSq (lineWeight W ω w hWpoly hWpos A)
        (fun a => Λ a + A * frequencyDot (κ a) ω) ξ < E ∧
      PrefixBound (lineWeight W ω w hWpoly hWpos A)
        (fun a => Λ a + A * frequencyDot (κ a) ω) L := by
  classical
  obtain ⟨s, c, hc⟩ := id hWpoly
  -- Checkpoint 2: freeze all finitely many torus frequencies and all frequency pairs.
  let κo : Option (Fin n) → (Fin D → ℤ) := fun o => o.elim 0 κ
  let Kset : Finset (Fin D → ℤ) :=
    (s ×ˢ (Finset.univ : Finset (Option (Fin n) × Option (Fin n)))).image
      (fun x => x.1.2 - κo x.2.1 + κo x.2.2)
  let pairs : Finset (ℝ × (Fin D → ℤ)) := Finset.univ.image (fun a => (Λ a, κ a))
  obtain ⟨ω, hωK, hωinj⟩ := avoid_frequency_collisions pairs Kset
  have hmemK (p : ℝ × (Fin D → ℤ)) (hp : p ∈ s) (o o' : Option (Fin n)) :
      p.2 - κo o + κo o' ∈ Kset :=
    Finset.mem_image.mpr ⟨(p, (o, o')), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩, rfl⟩
  have hωG : ∀ a b, ∀ p ∈ s, p.2 - κ a + κ b ≠ 0 → frequencyDot (p.2 - κ a + κ b) ω ≠ 0 :=
    fun a b p hp => hωK _ (hmemK p hp (some a) (some b))
  have hωS : ∀ a, ∀ p ∈ s, p.2 - κ a + 0 ≠ 0 → frequencyDot (p.2 - κ a + 0) ω ≠ 0 :=
    fun a p hp => hωK _ (hmemK p hp (some a) none)
  have hωM : ∀ p ∈ s, p.2 ≠ 0 → frequencyDot p.2 ω ≠ 0 := by
    intro p hp
    have h := hωK _ (hmemK p hp none none)
    simpa [κo] using h
  -- Checkpoint 3: transfer all moments and apply finite Gram stability.
  have hGt := tendsto_line_gram (w := w) (hWpoly := hWpoly) (hWpos := hWpos) Λ κ hc hωG
  have hvt := tendsto_line_source (w := w) (hWpoly := hWpoly) (hWpos := hWpos) Λ κ ξ hc hωS
  have hst := tendsto_line_norm (w := w) (hWpoly := hWpoly) (hWpos := hWpos) M hWmass hc hωM ξ
  have hlt := tendsto_line_loss hWpoly hWpos w₀ hw₀ M hWmass hc hωM
  have htend := hGt.prodMk_nhds (hvt.prodMk_nhds hst)
  have hstab := finite_gram_stability
    (fun j : Fin (n + 1) => (cutMatrix j.val : Matrix (Fin n) (Fin n) ℂ)) (fun _ => L)
    hBpos (fun j => hBpref j.val) (productSource w W Λ κ ξ) (M * ∫ t, w.density t) E hBcap
  have hev := htend.eventually hstab
  have hloss := hlt.eventually (gt_mem_nhds hM)
  obtain ⟨A, hA1, hA2, hA3⟩ := (hωinj.and (hev.and hloss)).exists
  have hνinj : Function.Injective (fun a => Λ a + A * frequencyDot (κ a) ω) := by
    intro a b hab
    apply hinj
    exact hA1 (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ b))) hab
  have hfin := hA2 (Matrix.isHermitian_gram ℂ _)
  refine ⟨ω, A, hνinj, hA3, ?_, ?_⟩
  · rw [distanceSq_eq_gram _ _ hνinj]
    exact hfin.2.2
  · exact prefixBound_of_posDef _ _ L hfin.2.1

/-- Old characters carry the zero torus frequency, new ones nonzero distinct frequencies. -/
theorem append_pairs_injective {d r D : ℕ} (μ : Fin d → ℝ) (lam : Fin r → ℝ)
    (k : Fin r → (Fin D → ℤ)) (hμ : Function.Injective μ) (hk0 : ∀ a, k a ≠ 0)
    (hkinj : Function.Injective (fun a => (lam a, k a))) :
    Function.Injective
      (fun a => (Fin.append μ lam a, Fin.append (0 : Fin d → Fin D → ℤ) k a)) := by
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      simp only [Fin.append_left] at h1
      rw [hμ h1]
    | right j =>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply] at h2
      exact absurd h2.symm (hk0 j)
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply] at h2
      exact absurd h2 (hk0 i)
    | right j =>
      simp only [Fin.append_right] at h1 h2
      have hij : i = j := hkinj (Prod.ext h1 h2)
      rw [hij]

end LineTransfer

open LineTransfer in
/-- Blueprint `extend:line`: the product-space extension transfers to the line. -/
theorem finite_extension_of_product (h : ProductExtension) :
    Construction.FiniteExtensionPrinciple := by
  intro w w₀ hw₀ d μ K ξ δ τ hμ hK hpb hdist hδ hτ
  -- Checkpoint 1: invoke the product extension with the same data.
  obtain ⟨D, r, W, M, lam, k, hWpoly, hWpos, hWmass, hM, hk0, hkinj, hBpos, hBpref, hBcap⟩ :=
    h w d μ K ξ δ τ hμ hK hpb hdist hδ hτ
  obtain ⟨ω, A, hinj, hloss, hdistA, hpref⟩ := line_extension_core w w₀ hw₀ W M
    (Fin.append μ lam) (Fin.append 0 k) ξ δ (max K 12 + τ) ((1 / 2 : ℝ) * distanceSq w μ ξ)
    hWpoly hWpos hWmass hM (append_pairs_injective μ lam k hμ hk0 hkinj) hBpos hBpref hBcap
  refine ⟨r, fun a => Fin.append μ lam a + A * frequencyDot (Fin.append 0 k a) ω,
    lineKernel W ω A, lineWeight W ω w hWpoly hWpos A, hinj, ?_,
    isTrigPolynomial_lineKernel ω hWpoly A, fun t => hWpos t (phase ω A t), fun t => rfl,
    hloss, hdistA.le, hpref⟩
  intro i
  simp [Fin.append_left]

end SchauderTranslates
