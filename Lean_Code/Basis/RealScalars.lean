import Lean_Code.Basis.Criterion

/-!
# From complex scalars to real scalars

A Schauder basis of the complex space `Lp ℂ p μ` all of whose vectors are real-valued is
also a Schauder basis of the real space `Lp ℝ p μ`, and its basis constant does not
increase.

The argument is the classical one. Let `ι : Lp ℝ p μ → Lp ℂ p μ` be the isometric
real-linear embedding (`complexifyLp`), `J` complex conjugation on `Lp ℂ p μ` (`conjLp`,
conjugate-linear and continuous) and `R` the real part (`realPartLp`). Conjugating the
expansion `x = ∑ cₙ(x) bₙ` and using `J bₙ = bₙ` gives `J x = ∑ conj (cₙ x) bₙ`, hence by
uniqueness of expansions `cₙ (J x) = conj (cₙ x)` (`coord_conjLp`). In particular the
coordinates of `ι h` are real, so the real partial sums of `h` are mapped by `ι` to the
complex partial sums of `ι h` (`complexifyLp_sum_realCoord`).

## Main statements

* `StructuredBases.exists_real_schauderBasis_of_complex`
* `StructuredBases.exists_real_schauderBasis_of_complex_of_ae`
* `StructuredBases.exists_real_translate_basis`
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

namespace StructuredBases

section RealScalars

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- On `Lp ℂ p μ`, multiplication by a real number is the same for both scalar fields. -/
theorem ofReal_smul_Lp (r : ℝ) (v : Lp ℂ p μ) : (r : ℂ) • v = r • v :=
  algebraMap_smul ℂ r v

variable [Fact (1 ≤ p)]

/-! ### Complexification, real part and conjugation on `Lp` -/

/-- The real-linear embedding `Lp ℝ p μ → Lp ℂ p μ`. -/
def complexifyLp (p : ℝ≥0∞) (μ : Measure α) [Fact (1 ≤ p)] : Lp ℝ p μ →L[ℝ] Lp ℂ p μ :=
  Complex.ofRealCLM.compLpL p μ

theorem complexifyLp_ae (h : Lp ℝ p μ) :
    (complexifyLp p μ h : α → ℂ) =ᵐ[μ] fun x => ((h x : ℝ) : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL h

/-- Complexification is isometric. -/
theorem norm_complexifyLp (h : Lp ℝ p μ) : ‖complexifyLp p μ h‖ = ‖h‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (complexifyLp_ae h)]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)

/-- Complexification as a linear isometry. -/
def complexifyLpₗᵢ (p : ℝ≥0∞) (μ : Measure α) [Fact (1 ≤ p)] : Lp ℝ p μ →ₗᵢ[ℝ] Lp ℂ p μ where
  toLinearMap := (complexifyLp p μ).toLinearMap
  norm_map' := norm_complexifyLp

/-- The real part, as a continuous real-linear map `Lp ℂ p μ → Lp ℝ p μ`. -/
def realPartLp (p : ℝ≥0∞) (μ : Measure α) [Fact (1 ≤ p)] : Lp ℂ p μ →L[ℝ] Lp ℝ p μ :=
  Complex.reCLM.compLpL p μ

theorem realPartLp_ae (x : Lp ℂ p μ) :
    (realPartLp p μ x : α → ℝ) =ᵐ[μ] fun a => (x a).re :=
  Complex.reCLM.coeFn_compLpL x

theorem realPartLp_complexifyLp (h : Lp ℝ p μ) : realPartLp p μ (complexifyLp p μ h) = h := by
  apply Lp.ext
  filter_upwards [realPartLp_ae (complexifyLp p μ h), complexifyLp_ae h] with a h1 h2
  rw [h1, h2, Complex.ofReal_re]

theorem complexifyLp_injective : Function.Injective (complexifyLp p μ) :=
  Function.LeftInverse.injective realPartLp_complexifyLp

/-- Complex conjugation, as a continuous conjugate-linear map of `Lp ℂ p μ`. -/
def conjLp (p : ℝ≥0∞) (μ : Measure α) [Fact (1 ≤ p)] : Lp ℂ p μ →L⋆[ℂ] Lp ℂ p μ :=
  ((starₗᵢ ℂ : ℂ ≃ₗᵢ⋆[ℂ] ℂ) : ℂ →L⋆[ℂ] ℂ).compLpL p μ

theorem conjLp_ae (x : Lp ℂ p μ) :
    (conjLp p μ x : α → ℂ) =ᵐ[μ] fun a => conj (x a) :=
  ((starₗᵢ ℂ : ℂ ≃ₗᵢ⋆[ℂ] ℂ) : ℂ →L⋆[ℂ] ℂ).coeFn_compLpL x

/-- A class which is a.e. real-valued is fixed by conjugation. -/
theorem conjLp_eq_self_of_ae_real {x : Lp ℂ p μ} {r : α → ℝ}
    (hx : (x : α → ℂ) =ᵐ[μ] fun a => (r a : ℂ)) : conjLp p μ x = x := by
  apply Lp.ext
  filter_upwards [conjLp_ae x, hx] with a h1 h2
  rw [h1, h2, Complex.conj_ofReal]

theorem conjLp_complexifyLp (h : Lp ℝ p μ) :
    conjLp p μ (complexifyLp p μ h) = complexifyLp p μ h :=
  conjLp_eq_self_of_ae_real (complexifyLp_ae h)

/-! ### Coordinates of real functions are real -/

/-- Conjugating an expansion: the coordinates of the conjugate are the conjugate
coordinates, provided the basis vectors are fixed by conjugation. -/
theorem coord_conjLp (b : SchauderBasis ℂ (Lp ℂ p μ)) (hb : ∀ n, conjLp p μ (b n) = b n)
    (x : Lp ℂ p μ) (n : ℕ) : b.coord n (conjLp p μ x) = conj (b.coord n x) := by
  apply coord_eq_of_tendsto b
  have h := ((conjLp p μ).continuous.tendsto x).comp (tendsto_expansion b x)
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, map_sum, map_smulₛₗ, hb]

/-- The coordinates of a (complexified) real function are real. -/
theorem coord_complexifyLp_real (b : SchauderBasis ℂ (Lp ℂ p μ))
    (hb : ∀ n, conjLp p μ (b n) = b n) (h : Lp ℝ p μ) (n : ℕ) :
    ((b.coord n (complexifyLp p μ h)).re : ℂ) = b.coord n (complexifyLp p μ h) := by
  rw [← Complex.conj_eq_iff_re, ← coord_conjLp b hb, conjLp_complexifyLp]

/-- The real coordinate functionals of a complex basis consisting of real functions. -/
def realCoord (b : SchauderBasis ℂ (Lp ℂ p μ)) (n : ℕ) : Lp ℝ p μ →L[ℝ] ℝ :=
  Complex.reCLM.comp (((b.coord n).restrictScalars ℝ).comp (complexifyLp p μ))

theorem realCoord_apply (b : SchauderBasis ℂ (Lp ℂ p μ)) (n : ℕ) (h : Lp ℝ p μ) :
    realCoord b n h = (b.coord n (complexifyLp p μ h)).re := rfl

/-- The complexification of a real partial sum is the complex partial sum. -/
theorem complexifyLp_sum_realCoord (b : SchauderBasis ℂ (Lp ℂ p μ)) (g : ℕ → Lp ℝ p μ)
    (hg : ∀ n, complexifyLp p μ (g n) = b n) (h : Lp ℝ p μ) (N : ℕ) :
    complexifyLp p μ (∑ n ∈ Finset.range N, realCoord b n h • g n) =
      b.proj N (complexifyLp p μ h) := by
  have hb : ∀ n, conjLp p μ (b n) = b n := fun n => by
    rw [← hg n, conjLp_complexifyLp]
  rw [map_sum, SchauderBasis.proj_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, hg n, ← ofReal_smul_Lp, realCoord_apply, coord_complexifyLp_real b hb]

/-! ### The real basis -/

/-- The real Schauder basis obtained from a complex Schauder basis of `Lp ℂ p μ` whose
vectors are the complexifications of the real functions `g n`. -/
def realBasis (b : SchauderBasis ℂ (Lp ℂ p μ)) (g : ℕ → Lp ℝ p μ)
    (hg : ∀ n, complexifyLp p μ (g n) = b n) : SchauderBasis ℝ (Lp ℝ p μ) :=
  ofCoord g (realCoord b)
    (fun n m => by
      rw [realCoord_apply, hg m, coord_apply_basis]
      split_ifs <;> simp)
    (fun h => by
      have ht := ((realPartLp p μ).continuous.tendsto (complexifyLp p μ h)).comp
        (b.tendsto_proj (complexifyLp p μ h))
      rw [realPartLp_complexifyLp] at ht
      refine ht.congr fun N => ?_
      rw [Function.comp_apply, ← complexifyLp_sum_realCoord b g hg h N,
        realPartLp_complexifyLp])

section RealBasis

variable (b : SchauderBasis ℂ (Lp ℂ p μ)) (g : ℕ → Lp ℝ p μ)
  (hg : ∀ n, complexifyLp p μ (g n) = b n)

@[simp] theorem realBasis_coe : ⇑(realBasis b g hg) = g := rfl

@[simp] theorem realBasis_coord (n : ℕ) : (realBasis b g hg).coord n = realCoord b n := rfl

/-- The real coordinates are the complex coordinates of the complexification. -/
theorem ofReal_realBasis_coord (n : ℕ) (h : Lp ℝ p μ) :
    (((realBasis b g hg).coord n h : ℝ) : ℂ) = b.coord n (complexifyLp p μ h) := by
  have hb : ∀ n, conjLp p μ (b n) = b n := fun n => by
    rw [← hg n, conjLp_complexifyLp]
  rw [realBasis_coord, realCoord_apply, coord_complexifyLp_real b hb]

/-- Complexification intertwines the real and the complex partial sum projections. -/
theorem complexifyLp_realBasis_proj (N : ℕ) (h : Lp ℝ p μ) :
    complexifyLp p μ ((realBasis b g hg).proj N h) = b.proj N (complexifyLp p μ h) := by
  rw [SchauderBasis.proj_apply]
  exact complexifyLp_sum_realCoord b g hg h N

/-- The real partial sum projections are no larger than the complex ones. -/
theorem norm_realBasis_proj_le (N : ℕ) : ‖(realBasis b g hg).proj N‖ ≤ ‖b.proj N‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h => ?_
  rw [← norm_complexifyLp, complexifyLp_realBasis_proj, ← norm_complexifyLp h]
  exact (b.proj N).le_opNorm _

/-- The basis constant of the real basis is at most the complex one. -/
theorem nnnormProjBound_realBasis_le :
    (realBasis b g hg).nnnormProjBound ≤ b.nnnormProjBound :=
  ciSup_le fun N =>
    (show ‖(realBasis b g hg).proj N‖₊ ≤ ‖b.proj N‖₊ from norm_realBasis_proj_le b g hg N).trans
      (b.nnnorm_proj_le_nnnormProjBound N)

end RealBasis

/-- **Real scalars.** A Schauder basis of the complex space `Lp ℂ p μ` all of whose vectors
are (a.e.) real-valued is also a Schauder basis of the real space `Lp ℝ p μ`, and the norms
of the partial sum projections do not increase. -/
theorem exists_real_schauderBasis_of_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : SchauderBasis ℂ (Lp ℂ p μ)) (g : ℕ → Lp ℝ p μ)
    (hg : ∀ n, (b n : α → ℂ) =ᵐ[μ] fun x => ((g n x : ℝ) : ℂ)) :
    ∃ b' : SchauderBasis ℝ (Lp ℝ p μ), ⇑b' = g ∧ ∀ N, ‖b'.proj N‖ ≤ ‖b.proj N‖ := by
  have hg' : ∀ n, complexifyLp p μ (g n) = b n := fun n =>
    Lp.ext ((complexifyLp_ae (g n)).trans (hg n).symm)
  exact ⟨realBasis b g hg', rfl, norm_realBasis_proj_le b g hg'⟩

/-- Variant of `exists_real_schauderBasis_of_complex` where the real basis vectors are given
by arbitrary real functions (membership in `Lp ℝ p μ` is automatic). -/
theorem exists_real_schauderBasis_of_complex_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : SchauderBasis ℂ (Lp ℂ p μ))
    (G : ℕ → α → ℝ) (hG : ∀ n, (b n : α → ℂ) =ᵐ[μ] fun x => ((G n x : ℝ) : ℂ)) :
    ∃ b' : SchauderBasis ℝ (Lp ℝ p μ),
      (∀ n, (b' n : α → ℝ) =ᵐ[μ] G n) ∧ ∀ N, ‖b'.proj N‖ ≤ ‖b.proj N‖ := by
  have hmem : ∀ n, MemLp (G n) p μ := by
    intro n
    have h1 : MemLp (fun x => ((G n x : ℝ) : ℂ)) p μ := (Lp.memLp (b n)).ae_eq (hG n)
    simpa using h1.re
  have hg : ∀ n, (b n : α → ℂ) =ᵐ[μ]
      fun x => ((((hmem n).toLp (G n) : Lp ℝ p μ) x : ℝ) : ℂ) := by
    intro n
    filter_upwards [hG n, (hmem n).coeFn_toLp] with x h1 h2
    rw [h1, h2]
  obtain ⟨b', hb', hN⟩ :=
    exists_real_schauderBasis_of_complex b (fun n => (hmem n).toLp (G n)) hg
  refine ⟨b', fun n => ?_, hN⟩
  rw [hb']
  exact (hmem n).coeFn_toLp

/-- **Real translate bases.** If the translates `x ↦ f (x - lam n)` of a real function form
(after complexification) a Schauder basis of `Lp ℂ p`, they form a Schauder basis of the real
space `Lp ℝ p`, with partial sum projections of no larger norm. -/
theorem exists_real_translate_basis {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℝ → ℝ) (lam : ℕ → ℝ)
    (b : SchauderBasis ℂ (Lp ℂ p (volume : Measure ℝ)))
    (hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) :
    ∃ b' : SchauderBasis ℝ (Lp ℝ p (volume : Measure ℝ)),
      (∀ n, (b' n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) ∧
        ∀ N, ‖b'.proj N‖ ≤ ‖b.proj N‖ :=
  exists_real_schauderBasis_of_complex_of_ae b (fun n x => f (x - lam n)) hb

end RealScalars

end StructuredBases
