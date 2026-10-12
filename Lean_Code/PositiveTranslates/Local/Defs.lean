import Lean_Code.PositiveTranslates.StageMachine
import Lean_Code.PositiveTranslates.Global.LocalBasis
import Lean_Code.SchauderTranslates.Lp.LpSupportedSubmodule

/-!
# Local non-negative bases: the interface

`LocalBasis p β A B` says that `β` is a normalized Schauder basis of `Lᵖ(A)` (the functions
of `Lᵖ(ℝ)` vanishing almost everywhere outside `A`) which consists of non-negative compactly
supported step functions and whose finite prefix sums are bounded by `B`.

The basis property is recorded in the form of the finite prefix criterion
(`StructuredBases.exists_schauderBasis_of_prefix_bound`): dense span in `Lᵖ(A)` and
`‖∑_{n<N} cₙ βₙ‖ ≤ B ‖∑ₙ cₙ βₙ‖` for finitely supported coefficients.

`LocalBasis.map` transports a local basis through a continuous linear map which is isometric
on `Lᵖ(A)`, maps `Lᵖ(A)` onto `Lᵖ(A')`, and preserves the two structural properties
(step functions, non-negativity) on the basis vectors.

`IsCellIsometry T A` says that `T` is a positive linear isometry of `Lᵖ(ℝ)` onto `Lᵖ(A)`
preserving compactly supported step functions; `LocalBasis.of_cellIsometry` transports local
bases of the whole line through such maps.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞}

/-! ### Auxiliary lemmas (namespace `Local`) -/

/-- Multiplication by a real scalar, written with the complex scalar action. -/
theorem Local.ofReal_smul_eq (a : ℝ) (F : LebesgueLp p) : ((a : ℂ)) • F = a • F := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (a : ℂ) F, Lp.coeFn_smul a F] with x h1 h2
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Complex scalar multiples keep the support. -/
theorem Local.supportedOn_smul {F : LebesgueLp p} {A : Set ℝ} (hF : SupportedOn F A) (a : ℂ) :
    SupportedOn (a • F) A :=
  (supportedLpSubmodule p volume A).smul_mem a hF

/-- Finite sums keep the support. -/
theorem Local.supportedOn_sum {ι : Type*} (s : Finset ι) (F : ι → LebesgueLp p) {A : Set ℝ}
    (hF : ∀ i ∈ s, SupportedOn (F i) A) : SupportedOn (∑ i ∈ s, F i) A :=
  (supportedLpSubmodule p volume A).sum_mem hF

/-- Finite complex combinations of functions supported in `A` are supported in `A`. -/
theorem Local.supportedOn_linearCombination {β : ℕ → LebesgueLp p} {A : Set ℝ}
    (hβ : ∀ n, SupportedOn (β n) A) (c : ℕ →₀ ℂ) :
    SupportedOn (Finsupp.linearCombination ℂ β c) A := by
  rw [Finsupp.linearCombination_apply]
  exact Local.supportedOn_sum _ _ (fun n _ => Local.supportedOn_smul (hβ n) _)

/-- Exponents `p ≥ 1` are nonzero. -/
theorem Local.exponent_ne_zero [Fact (1 ≤ p)] : p ≠ 0 :=
  (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'

/-- Every function is supported in the whole line. -/
theorem Local.supportedOn_univ (F : LebesgueLp p) : SupportedOn F Set.univ :=
  Filter.Eventually.of_forall fun x hx => absurd (Set.mem_univ x) hx

open Local

/-! ### Basic properties and transport -/

namespace LocalBasis

variable [Fact (1 ≤ p)] {β : ℕ → LebesgueLp p} {A A' : Set ℝ} {B : ℝ}

theorem ne_zero (h : LocalBasis p β A B) (n : ℕ) : β n ≠ 0 := by
  intro h0
  have := h.norm n
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- The prefix constant of a local basis is at least one. -/
theorem one_le (h : LocalBasis p β A B) : 1 ≤ B := by
  have h1 := h.prefix_le 1 (Finsupp.single 0 1)
  simpa [h.norm 0] using h1

/-- The prefix constant may be enlarged. -/
theorem mono (h : LocalBasis p β A B) {B' : ℝ} (hB : B ≤ B') : LocalBasis p β A B' where
  step := h.step
  nonneg := h.nonneg
  norm := h.norm
  supported := h.supported
  dense := h.dense
  prefix_le N c := (h.prefix_le N c).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- The set may be replaced by an equal one. -/
theorem congr_set (h : LocalBasis p β A B) (hA : A = A') : LocalBasis p β A' B := hA ▸ h

/-- Transport of a local basis through a continuous linear map `T` which is isometric on
`Lᵖ(A)` and maps `Lᵖ(A)` onto `Lᵖ(A')`. The two structural properties are only required on
the basis vectors. -/
theorem map (h : LocalBasis p β A B) (T : LebesgueLp p →L[ℂ] LebesgueLp p)
    (hstep : ∀ n, IsCompactStep p (T (β n)))
    (hnonneg : ∀ n, IsNonneg (T (β n)))
    (hnorm : ∀ F, SupportedOn F A → ‖T F‖ = ‖F‖)
    (hsupp : ∀ F, SupportedOn F A → SupportedOn (T F) A')
    (hsurj : ∀ G, SupportedOn G A' → ∃ F, SupportedOn F A ∧ T F = G) :
    LocalBasis p (fun n => T (β n)) A' B where
  step := hstep
  nonneg := hnonneg
  norm n := by rw [hnorm _ (h.supported n), h.norm n]
  supported n := hsupp _ (h.supported n)
  dense G hG := by
    obtain ⟨F, hF, rfl⟩ := hsurj G hG
    have hmem : T F ∈ T '' closure (Submodule.span ℂ (Set.range β) : Set (LebesgueLp p)) :=
      ⟨F, h.dense F hF, rfl⟩
    have hsub : T '' (Submodule.span ℂ (Set.range β) : Set (LebesgueLp p)) ⊆
        (Submodule.span ℂ (Set.range fun n => T (β n)) : Set (LebesgueLp p)) := by
      rintro _ ⟨x, hx, rfl⟩
      have hmap : T x ∈ (Submodule.span ℂ (Set.range β)).map T.toLinearMap := ⟨x, hx, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at hmap
      exact hmap
    exact closure_mono hsub (image_closure_subset_closure_image T.continuous hmem)
  prefix_le N c := by
    have h1 : ∑ n ∈ Finset.range N, c n • T (β n) = T (∑ n ∈ Finset.range N, c n • β n) := by
      simp only [map_sum, map_smul]
    have h2 : Finsupp.linearCombination ℂ (fun n => T (β n)) c =
        T (Finsupp.linearCombination ℂ β c) := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    rw [h1, h2, hnorm _ (supportedOn_sum _ _ (fun n _ => supportedOn_smul (h.supported n) _)),
      hnorm _ (supportedOn_linearCombination h.supported c)]
    exact h.prefix_le N c

end LocalBasis

/-! ### Cell isometries -/

section CellIsometry

variable [Fact (1 ≤ p)]

/-- `T` is a positive linear isometry of `Lᵖ(ℝ)` onto `Lᵖ(A)` (the functions vanishing almost
everywhere outside `A`) which maps compactly supported step functions to compactly supported
step functions.

* `nonneg`: `T` maps almost everywhere non-negative functions to such functions;
* `step`: `T` maps compactly supported step functions to compactly supported step functions;
* `supported`: every `T F` vanishes almost everywhere outside `A`;
* `surj`: every `G` vanishing almost everywhere outside `A` is of the form `T F`.

Such a `T` transports every normalized non-negative compact-step basis of `Lᵖ(ℝ)` to one of
`Lᵖ(A)` with the same norms of all finite linear combinations
(`LocalBasis.of_cellIsometry`, `norm_linearCombination_isometry`). -/
structure IsCellIsometry (T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p) (A : Set ℝ) : Prop where
  nonneg : ∀ F, IsNonneg F → IsNonneg (T F)
  step : ∀ F, IsCompactStep p F → IsCompactStep p (T F)
  supported : ∀ F, SupportedOn (T F) A
  surj : ∀ G, SupportedOn G A → ∃ F, T F = G

/-- The identity is a cell isometry of the whole line. -/
theorem IsCellIsometry.id :
    IsCellIsometry (LinearIsometry.id : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p) Set.univ where
  nonneg _ hF := hF
  step _ hF := hF
  supported F := supportedOn_univ F
  surj G _ := ⟨G, rfl⟩

/-- The set may be replaced by an equal one. -/
theorem IsCellIsometry.congr_set {T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p} {A A' : Set ℝ}
    (h : IsCellIsometry T A) (hA : A = A') : IsCellIsometry T A' := hA ▸ h

/-- A linear isometry preserves the norms of all finite linear combinations. In particular
every estimate between `‖∑ₙ cₙ rₙ‖` and the coefficients `c` (prefix bounds, lower `ℓᵖ` bounds,
…) passes from `r` to its image with the same constant. -/
theorem norm_linearCombination_isometry (T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p)
    (r : ℕ → LebesgueLp p) (c : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (fun n => T (r n)) c‖ = ‖Finsupp.linearCombination ℂ r c‖ := by
  have h : Finsupp.linearCombination ℂ (fun n => T (r n)) c =
      T (Finsupp.linearCombination ℂ r c) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  rw [h, T.norm_map]

/-- A cell isometry onto `Lᵖ(A)` carries a local basis of the whole line to a local basis of
`A` with the same prefix constant. -/
theorem LocalBasis.of_cellIsometry {T : LebesgueLp p →ₗᵢ[ℂ] LebesgueLp p} {A : Set ℝ}
    (hT : IsCellIsometry T A) {r : ℕ → LebesgueLp p} {B : ℝ}
    (hr : LocalBasis p r Set.univ B) : LocalBasis p (fun n => T (r n)) A B :=
  hr.map T.toContinuousLinearMap (fun n => hT.step _ (hr.step n))
    (fun n => hT.nonneg _ (hr.nonneg n)) (fun F _ => T.norm_map F)
    (fun F _ => hT.supported F)
    (fun G hG => by
      obtain ⟨F, hF⟩ := hT.surj G hG
      exact ⟨F, supportedOn_univ F, hF⟩)

end CellIsometry

end StructuredBases.PositiveTranslates
