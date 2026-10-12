import Lean_Code.SchauderTranslates.ProductInterface
import Lean_Code.SchauderTranslates.WeightedIsometry

/-!
# Basic bridges for the line transfer (`extend:line`)

Character algebra, the linear phase substitution `y = A ω t`, a finite-moment transfer
for mixed trigonometric polynomials indexed by an arbitrary finite set, and the identities
relating the raw weighted quantities `normSq`, `distanceSq`, `PrefixBound` of the contracts
to Gram matrices of weighted characters.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LineTransfer
open Construction

/-! ### Character algebra -/

theorem character_mul (a b t : ℝ) : character a t * character b t = character (a + b) t := by
  simp only [character, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_character (a t : ℝ) : star (character a t) = character (-a) t := by
  simp only [character, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

@[simp] theorem character_zero_freq (t : ℝ) : character 0 t = 1 := by
  simp [character]

@[simp] theorem frequencyDot_zero_left {D : ℕ} (ω : Fin D → ℝ) :
    frequencyDot (0 : Fin D → ℤ) ω = 0 := by
  simp [frequencyDot]

theorem mixedCharacter_mul {D : ℕ} (l l' : ℝ) (k k' : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) :
    mixedCharacter l k t y * mixedCharacter l' k' t y =
      mixedCharacter (l + l') (k + k') t y := by
  simp only [mixedCharacter, UnitAddTorus.mFourier_add, ← character_mul]
  ring

theorem star_mixedCharacter {D : ℕ} (l : ℝ) (k : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) :
    star (mixedCharacter l k t y) = mixedCharacter (-l) (-k) t y := by
  simp only [mixedCharacter, star_mul', star_character, UnitAddTorus.mFourier_neg,
    Complex.star_def]

theorem mixedCharacter_zero {D : ℕ} (l t : ℝ) (y : UnitAddTorus (Fin D)) :
    mixedCharacter l (0 : Fin D → ℤ) t y = character l t := by
  simp [mixedCharacter, UnitAddTorus.mFourier_zero]

theorem continuous_mixedCharacter {D : ℕ} (l : ℝ) (k : Fin D → ℤ) (t : ℝ) :
    Continuous (mixedCharacter l k t) := by
  unfold mixedCharacter
  exact continuous_const.mul (UnitAddTorus.mFourier k).continuous

@[simp] theorem norm_mixedCharacter {D : ℕ} (l : ℝ) (k : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) : ‖mixedCharacter l k t y‖ = 1 := by
  simp only [mixedCharacter, norm_mul, norm_character, one_mul, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

/-- The linear phase substitution `y = A ω t` of the torus variables. -/
def phase {D : ℕ} (ω : Fin D → ℝ) (A t : ℝ) : UnitAddTorus (Fin D) :=
  fun i => ((A * ω i * t : ℝ) : UnitAddCircle)

theorem mFourier_phase {D : ℕ} (k : Fin D → ℤ) (ω : Fin D → ℝ) (A t : ℝ) :
    UnitAddTorus.mFourier k (phase ω A t) = character (A * frequencyDot k ω) t :=
  torus_character_on_line k ω A t

theorem mixedCharacter_phase {D : ℕ} (l : ℝ) (k : Fin D → ℤ) (ω : Fin D → ℝ) (A t : ℝ) :
    mixedCharacter l k t (phase ω A t) = character (l + A * frequencyDot k ω) t := by
  rw [mixedCharacter, mFourier_phase, character_mul]

/-- A kernel times the pairing of two mixed characters is again a mixed polynomial. -/
theorem kernel_pairing_rep {D : ℕ} {F : ℝ → UnitAddTorus (Fin D) → ℂ}
    {s : Finset (ℝ × (Fin D → ℤ))} {c : ℝ × (Fin D → ℤ) → ℂ}
    (hF : ∀ t y, F t y = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (l l' : ℝ) (k k' : Fin D → ℤ) (t : ℝ) (y : UnitAddTorus (Fin D)) :
    F t y * (star (mixedCharacter l k t y) * mixedCharacter l' k' t y) =
      ∑ p ∈ s, c p * mixedCharacter (p.1 - l + l') (p.2 - k + k') t y := by
  rw [hF, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [star_mixedCharacter, mul_assoc, mixedCharacter_mul, mixedCharacter_mul]
  congr 2
  · ring
  · abel

/-! ### Finite-moment transfer for mixed polynomials -/

theorem integrable_mul_bounded_continuous {h g : ℝ → ℂ} (hh : Integrable h)
    (hg : Continuous g) {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) :
    Integrable (fun t => h t * g t) :=
  hh.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hC)

/-- Transfer of one weighted mixed polynomial along `y = A ω t`, with an arbitrary finite
index set (repeated frequencies are allowed). -/
theorem line_transfer {D : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ)
    (kk : ι → (Fin D → ℤ)) (F : ℝ → UnitAddTorus (Fin D) → ℂ)
    (hF : ∀ t y, F t y = ∑ i ∈ s, c i * mixedCharacter (lam i) (kk i) t y)
    (h : ℝ → ℂ) (hh : Integrable h) (ω : Fin D → ℝ)
    (hω : ∀ i ∈ s, kk i ≠ 0 → frequencyDot (kk i) ω ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, h t * F t (phase ω A t)) atTop
      (𝓝 (∫ t, h t * ∫ y, F t y ∂torusMeasure D)) := by
  classical
  have hcoef (i : ι) : Integrable (fun t => h t * (c i * character (lam i) t)) :=
    integrable_mul_bounded_continuous hh (by fun_prop) (C := ‖c i‖)
      (fun t => by simp)
  have hline (A : ℝ) : (∫ t, h t * F t (phase ω A t)) =
      ∑ i ∈ s, ∫ t, (h t * (c i * character (lam i) t)) *
        character (A * frequencyDot (kk i) ω) t := by
    have he : (fun t => h t * F t (phase ω A t)) = fun t => ∑ i ∈ s,
        (h t * (c i * character (lam i) t)) * character (A * frequencyDot (kk i) ω) t := by
      funext t
      rw [hF, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mixedCharacter, mFourier_phase]
      ring
    rw [he, integral_finsetSum]
    intro i _
    exact integrable_mul_bounded_continuous (hcoef i) (continuous_character _) (C := 1)
      (fun t => by simp)
  have htorus (t : ℝ) : (∫ y, F t y ∂torusMeasure D) =
      ∑ i ∈ s, if kk i = 0 then c i * character (lam i) t else 0 := by
    simp_rw [hF]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [mixedCharacter, ← mul_assoc]
      rw [integral_const_mul, integral_torus_character]
      split_ifs <;> simp
    · intro i _
      apply Integrable.of_bound
        ((continuous_const.mul (continuous_mixedCharacter _ _ t)).aestronglyMeasurable)
        ‖c i‖
      exact Eventually.of_forall (fun y => by simp)
  have hlim : (∫ t, h t * ∫ y, F t y ∂torusMeasure D) =
      ∑ i ∈ s, if kk i = 0 then ∫ t, h t * (c i * character (lam i) t) else 0 := by
    simp_rw [htorus, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    · intro i _
      split_ifs
      · exact hcoef i
      · simp
  rw [hlim]
  simp_rw [hline]
  apply tendsto_finsetSum
  intro i hi
  by_cases hk : kk i = 0
  · simp only [hk, if_true, frequencyDot_zero_left, mul_zero, character_zero_freq, mul_one]
    exact tendsto_const_nhds
  · simp only [if_neg hk]
    exact oscillatory_integral_tendsto_zero _ (hω i hi hk)

/-- The real-valued form for a real kernel and a real integrable multiplier. -/
theorem line_transfer_real {D : ℕ} (W : ℝ → UnitAddTorus (Fin D) → ℝ)
    (s : Finset (ℝ × (Fin D → ℤ))) (c : ℝ × (Fin D → ℤ) → ℂ)
    (hW : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (h : ℝ → ℝ) (hh : Integrable h) (ω : Fin D → ℝ)
    (hω : ∀ p ∈ s, p.2 ≠ 0 → frequencyDot p.2 ω ≠ 0) :
    Tendsto (fun A : ℝ => ∫ t, h t * W t (phase ω A t)) atTop
      (𝓝 (∫ t, h t * ∫ y, W t y ∂torusMeasure D)) := by
  have hc := line_transfer s c Prod.fst Prod.snd (fun t y => (W t y : ℂ)) hW
    (fun t => (h t : ℂ)) hh.ofReal ω hω
  have hre := (Complex.continuous_re.tendsto _).comp hc
  have e1 (A : ℝ) : (∫ t, (h t : ℂ) * (W t (phase ω A t) : ℂ)) =
      ((∫ t, h t * W t (phase ω A t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    rfl
  have e2 : (∫ t, (h t : ℂ) * ∫ y, (W t y : ℂ) ∂torusMeasure D) =
      ((∫ t, h t * ∫ y, W t y ∂torusMeasure D : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    rw [integral_complex_ofReal]
    push_cast
    rfl
  simp only [Function.comp_def, e1, e2, Complex.ofReal_re] at hre
  exact hre

/-! ### The weighted measure and raw weighted quantities -/

theorem integral_weight_measure (w : Weight) (f : ℝ → ℂ) :
    (∫ t, f t ∂w.measure) = ∫ t, (w.density t : ℂ) * f t := by
  rw [Weight.measure, integral_withDensity_eq_integral_toReal_smul w.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [w.positive] with t ht
  rw [ENNReal.toReal_ofReal ht.le, Complex.real_smul]

theorem integral_weight_measure_real (w : Weight) (f : ℝ → ℝ) :
    (∫ t, f t ∂w.measure) = ∫ t, f t * w.density t := by
  rw [Weight.measure, integral_withDensity_eq_integral_toReal_smul w.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [w.positive] with t ht
  rw [ENNReal.toReal_ofReal ht.le, smul_eq_mul, mul_comm]

/-- The raw squared norm of a representative is the squared norm of its class. -/
theorem normSq_eq_norm_sq (w : Weight) {f : ℝ → ℂ} {F : WeightedL2 w}
    (hF : (F : ℝ → ℂ) =ᵐ[w.measure] f) : normSq w f = ‖F‖ ^ 2 := by
  rw [l2_norm_sq_eq_integral, normSq, ← integral_weight_measure_real]
  apply integral_congr_ae
  filter_upwards [hF] with t ht
  rw [ht]

theorem inner_weightedCharacter (w : Weight) (a b : ℝ) :
    inner ℂ (weightedCharacter w a) (weightedCharacter w b) =
      ∫ t, (w.density t : ℂ) * (star (character a t) * character b t) := by
  rw [L2.inner_def, ← integral_weight_measure]
  apply integral_congr_ae
  filter_upwards [weightedCharacter_ae w a, weightedCharacter_ae w b] with t ha hb
  rw [ha, hb, RCLike.inner_apply, Complex.star_def, mul_comm]

theorem norm_sq_weightedCharacter (w : Weight) (ξ : ℝ) :
    ‖weightedCharacter w ξ‖ ^ 2 = ∫ t, w.density t := by
  rw [← normSq_eq_norm_sq w (weightedCharacter_ae w ξ), normSq]
  simp

/-! ### Gram matrices of weighted characters -/

section Gram
variable (w : Weight) {n : ℕ} (ν : Fin n → ℝ)

/-- The weighted characters of a finite frequency list. -/
def atoms : Fin n → WeightedL2 w := fun i => weightedCharacter w (ν i)

theorem gram_atoms_apply (a b : Fin n) :
    Matrix.gram ℂ (atoms w ν) a b =
      ∫ t, (w.density t : ℂ) * (star (character (ν a) t) * character (ν b) t) := by
  rw [Matrix.gram_apply]
  exact inner_weightedCharacter w (ν a) (ν b)

theorem sourceMoments_atoms_apply (ξ : ℝ) (a : Fin n) :
    sourceMoments (atoms w ν) (weightedCharacter w ξ) a =
      ∫ t, (w.density t : ℂ) * (star (character (ν a) t) * character ξ t) :=
  inner_weightedCharacter w (ν a) ξ

theorem synthesis_atoms_ae (c : Fin n → ℂ) :
    ((finiteSynthesis (atoms w ν) c : WeightedL2 w) : ℝ → ℂ) =ᵐ[w.measure]
      synthesis ν c := by
  have h := weightedCharacter_sum_ae w ν Finset.univ c
  filter_upwards [h] with t ht
  simpa [finiteSynthesis, synthesis, atoms] using ht

theorem normSq_synthesis (c : Fin n → ℂ) :
    normSq w (synthesis ν c) =
      gramQuadratic (Matrix.gram ℂ (atoms w ν)) (WithLp.toLp 2 c) := by
  rw [normSq_eq_norm_sq w (synthesis_atoms_ae w ν c), ← synthesis_norm_sq,
    WithLp.ofLp_toLp]

theorem cutMatrix_toEuclideanLin (k : ℕ) (c : Fin n → ℂ) :
    (cutMatrix k : Matrix (Fin n) (Fin n) ℂ).toEuclideanLin (WithLp.toLp 2 c) =
      WithLp.toLp 2 (fun i => if i.val < k then c i else 0) := by
  apply PiLp.ext
  intro i
  simp [Matrix.toLpLin_apply, cutMatrix, Matrix.mulVec_diagonal]

theorem normSq_prefix (k : ℕ) (c : Fin n → ℂ) :
    normSq w (fun t => ∑ i : Fin n, if i.val < k then c i * character (ν i) t else 0) =
      gramQuadratic (Matrix.gram ℂ (atoms w ν))
        ((cutMatrix k : Matrix (Fin n) (Fin n) ℂ).toEuclideanLin (WithLp.toLp 2 c)) := by
  have he : (fun t => ∑ i : Fin n, if i.val < k then c i * character (ν i) t else 0) =
      synthesis ν (fun i => if i.val < k then c i else 0) := by
    funext t
    simp only [synthesis]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he, normSq_synthesis, cutMatrix_toEuclideanLin]

theorem cutMatrix_eq_min (k : ℕ) :
    (cutMatrix k : Matrix (Fin n) (Fin n) ℂ) = cutMatrix (min k n) := by
  unfold cutMatrix
  congr 1
  funext i
  by_cases hk : i.val < k
  · have hm : i.val < min k n := lt_min hk i.isLt
    simp [hk, hm]
  · have hm : ¬ i.val < min k n := fun h => hk (lt_of_lt_of_le h (min_le_left _ _))
    simp [hk, hm]

/-- Strict Gram prefix conditions on all cuts give the raw `PrefixBound`. -/
theorem prefixBound_of_posDef (K : ℝ)
    (h : ∀ j : Fin (n + 1), (prefixGramDifference K (cutMatrix j.val)
      (Matrix.gram ℂ (atoms w ν))).PosDef) :
    PrefixBound w ν K := by
  intro k c
  rw [normSq_prefix, normSq_synthesis]
  have hj := h ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  rw [← cutMatrix_eq_min] at hj
  have hiff := (prefixGramDifference_posDef_iff K (cutMatrix k)
    (Matrix.isHermitian_gram ℂ (atoms w ν))).mp hj
  by_cases hc : (WithLp.toLp 2 c : EuclideanSpace ℂ (Fin n)) = 0
  · rw [hc, map_zero]
    simp [gramQuadratic]
  · exact (hiff _ hc).le

/-- The raw distance is the Gram projection error of the weighted characters. -/
theorem distanceSq_eq_gram (hν : Function.Injective ν) (ξ : ℝ) :
    distanceSq w ν ξ = ‖weightedCharacter w ξ‖ ^ 2 -
      gramCapture (Matrix.gram ℂ (atoms w ν))
        (sourceMoments (atoms w ν) (weightedCharacter w ξ)) := by
  rw [← gram_projection_error_inf (atoms w ν) (characters_linearIndependent w ν hν)]
  unfold distanceSq
  congr 1
  apply congrArg Set.range
  funext c
  apply normSq_eq_norm_sq
  filter_upwards [Lp.coeFn_sub (weightedCharacter w ξ) (finiteSynthesis (atoms w ν) c),
    weightedCharacter_ae w ξ, synthesis_atoms_ae w ν c] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

end Gram

end SchauderTranslates.LineTransfer
