import Lean_Code.SchauderTranslates.CutoffChoice
import Lean_Code.SchauderTranslates.ScalarProductPrefixes
import Lean_Code.SchauderTranslates.ScalarIterationBounds
import Lean_Code.SchauderTranslates.InverseNormFloor
import Lean_Code.SchauderTranslates.Sharp.ScalarSharpInitial
import Lean_Code.SchauderTranslates.Sharp.ScalarSharpStep

/-!
# The sharp scalar induction

Paper (`h2:ss:scalar-induction`): with `t = d / 4`, `a₀ = t / 100`, the stages keep
`3 Z₀ / 4 ≤ Z_n ≤ Z₀`, `(B_n⁻¹)_kk - 1 ≤ 2 ε_n` for `k ≠ 0`, `1 + t ≤ Q_n < 1 + 2 t`, the
recursion `Q_{n+1} = Q_n + (5 / t) η_n + ε_n² / 2`, and `‖B_n⁻¹‖ ≤ ε_n⁻²`.
The structure `Stage t k` is the parametrized counterpart of `ScalarStage k`; the reserve
terms `(1/2)^k` make the choice of the next block noncircular exactly as there.
-/

noncomputable section
open Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp.Scalar
open SchauderTranslates ScalarData

/-! ### The initial block as one independent copy -/

section Initial
variable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1 / 2)

/-- The initial scalar block in the independent-copy representation used by every later
stage. There is exactly one copy. -/
def sharpInductionInitial (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1 / 2) : ScalarData 1 1 :=
  (sharpInitial a ha0 ha1).product 1

theorem sharpInductionInitial_mass : (sharpInductionInitial a ha0 ha1).mass = 1 - a := by
  simp [sharpInductionInitial, ScalarData.product_mass, sharpInitial_mass]

theorem sharpInductionInitial_gain :
    (sharpInductionInitial a ha0 ha1).gain = a ^ 2 / (4 - 8 * a + 3 * a ^ 2) := by
  simp [sharpInductionInitial, ScalarData.product_gain, sharpInitial_gain]

theorem sharpInductionInitial_even : (sharpInductionInitial a ha0 ha1).IsEven :=
  (sharpInitial a ha0 ha1).product_even (sharpInitial_even ha0 ha1) 1

theorem sharpInductionInitial_floor : (sharpInductionInitial a ha0 ha1).HasPositiveFloor :=
  (sharpInitial a ha0 ha1).product_positiveFloor (sharpInitial_floor ha0 ha1) 1

theorem sharpInductionInitial_centered {q : ℝ} (hq : 1 ≤ q) :
    (sharpInductionInitial a ha0 ha1).CenteredPrefixSqBound q :=
  (sharpInitial a ha0 ha1).product_centered_prefix 1 (zero_le_one.trans hq)
    ((sharpInitial_centered_prefix_iff ha0 ha1 q).mpr hq)

/-- The nonconstant raw inverse diagonal of the initial block. -/
theorem sharpInductionInitial_inverse_diagonal (i : Fin 1) :
    ((sharpInductionInitial a ha0 ha1).rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re =
      (1 - a) / sharpDet a := by
  have he := congrArg (fun B : Matrix (Fin 1) (Fin 1) ℂ => B 0 0)
    (sharpInitial a ha0 ha1).rawGram_inverse_nonconstant
  change (sharpInitial a ha0 ha1).rawGram⁻¹ (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) =
    (sharpInitial a ha0 ha1).rawCenteredGram⁻¹ 0 0 at he
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hp := (sharpInitial a ha0 ha1).product_inverse_nonconstant 1 (0 : Fin 1) (0 : Fin 1)
  change (sharpInductionInitial a ha0 ha1).rawGram⁻¹ (Sum.inr (0 : Fin 1))
    (Sum.inr (0 : Fin 1)) = _ at hp
  have hm : (1 - a) ≠ 0 := by linarith
  rw [hp, ← he, sharpInitial_mass, sharpInitial_inverse_diagonal, ← Complex.ofReal_mul,
    Complex.ofReal_re, pow_one, div_self hm, one_mul]

end Initial

/-- Paper `h2:eq:scalar-initial`: `(B₀⁻¹)₁₁ - 1 ≤ 2 a₀`. -/
theorem sharpInductionInitial_inverse_excess {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (i : Fin 1) :
    ((sharpInductionInitial a ha0 (ha1.trans_lt (by norm_num))).rawGram⁻¹
      (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * a := by
  have hdet := sharpDet_pos (a := a) (ha1.trans_lt (by norm_num))
  rw [sharpInductionInitial_inverse_diagonal, sub_le_iff_le_add, div_le_iff₀ hdet]
  unfold sharpDet
  nlinarith [mul_nonneg ha0 ha0, mul_nonneg (mul_nonneg ha0 ha0) ha0]

/-- A coarse initial inverse norm already gives the required spectral floor
(paper: `B₀ ≥ a₀² I`). -/
theorem sharpInductionInitial_inverse_norm {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ))
      (sharpInductionInitial a ha0.le (ha1.trans_lt (by norm_num))).rawGram⁻¹‖ ≤ a⁻¹ ^ 2 := by
  have ha2 : a < 1 / 2 := ha1.trans_lt (by norm_num)
  have h := (sharpInitial a ha0.le ha2).product_rawInverse_norm_le 1
    (sharpInitial_inverse_norm_le ha0.le ha2)
  rw [sharpInitial_mass, sharpInitial_gain] at h
  refine h.trans ?_
  have hdet := sharpDet_pos (a := a) ha2
  have hD : 0 < 4 - 8 * a + 3 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hZ : a ^ 2 / (4 - 8 * a + 3 * a ^ 2) ≤ 1 := by
    rw [div_le_one hD]
    nlinarith [sq_nonneg a]
  have hh : (1 - a / 2) / sharpDet a ≤ 2 := by
    rw [div_le_iff₀ hdet]
    unfold sharpDet
    nlinarith [sq_nonneg a]
  have hm : 0 < 1 - a := by linarith
  have hnum : 1 + ((1 : ℕ) : ℝ) * (a ^ 2 / (4 - 8 * a + 3 * a ^ 2)) +
      (1 - a) * ((1 - a / 2) / sharpDet a) ≤ 4 := by
    have h1 : (1 - a) * ((1 - a / 2) / sharpDet a) ≤ 1 * 2 :=
      mul_le_mul (by linarith) hh (div_nonneg (by linarith) hdet.le) zero_le_one
    rw [Nat.cast_one, one_mul]
    linarith
  have hinv : (4 : ℝ) ≤ a⁻¹ := (le_inv_comm₀ (by norm_num) ha0).mpr (by linarith)
  have hsq : (16 : ℝ) ≤ a⁻¹ ^ 2 := by nlinarith
  rw [pow_one, div_le_iff₀ hm]
  nlinarith

/-! ### The stage invariant -/

/-- The full sharp scalar-stage invariant for the parameter `t = d / 4`. -/
structure Stage (t : ℝ) (k : ℕ) where
  dimension : ℕ
  length : ℕ
  data : ScalarData dimension length
  ε : ℝ
  q : ℝ
  η : ℝ
  deficit_pos : 0 < ε
  deficit_le : ε ≤ sharpA t
  mass_eq : data.mass = 1 - ε
  even : data.IsEven
  positiveFloor : data.HasPositiveFloor
  gain_lower : (3 / 4) * sharpZ t + (1 / 4) * sharpZ t * (1 / 2) ^ k ≤ data.gain
  gain_upper : data.gain ≤ sharpZ t
  inverse_norm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) data.rawGram⁻¹‖ ≤ ε⁻¹ ^ 2
  inverse_excess : ∀ i : Fin length, (data.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * ε
  q_lower : 1 + t ≤ q
  η_nonneg : 0 ≤ η
  centered : data.CenteredPrefixSqBound q
  augmented : data.AugmentedPrefixSqBound (q + (5 / t) * η)
  budget : q + (2 / 3) * ε + (5 / t) * η ≤
    sharpBudget t - (1 / 2) * ((5 / t) * sharpZ t) * (1 / 2) ^ k

namespace Stage
variable {t : ℝ} {k : ℕ}

theorem gain_retained (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    (3 / 4) * sharpZ t ≤ s.data.gain := by
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  have hZ := (sharpZ_pos ht0 ht1).le
  nlinarith [s.gain_lower, mul_nonneg hZ hp]

theorem gain_pos (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) : 0 < s.data.gain := by
  have h := s.gain_retained ht0 ht1
  have hZ := sharpZ_pos ht0 ht1
  linarith

theorem deficit_le_tenth (ht1 : t ≤ 1 / 4) (s : Stage t k) : s.ε ≤ 1 / 10 :=
  s.deficit_le.trans (sharpA_le_tenth ht1)

theorem deficit_sq_le (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    s.ε ^ 2 ≤ (16 / 3) * s.data.gain :=
  sharp_deficit_sq_le ht0 ht1 s.deficit_pos.le s.deficit_le (s.gain_retained ht0 ht1)

/-- The augmented budget stays strictly below `1 + 2 t`. -/
theorem augmented_budget_lt (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    s.q + (5 / t) * s.η < 1 + 2 * t := by
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  have hb := s.budget
  have he := s.deficit_pos
  have hB := sharpBudget_lt ht0 ht1
  have hc := mul_nonneg (sharp_copy_cost_nonneg ht0 ht1) hp
  nlinarith

theorem q_lt (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) : s.q < 1 + 2 * t := by
  have h := s.augmented_budget_lt ht0 ht1
  have hκ : 0 ≤ (5 / t) * s.η := mul_nonneg (by positivity) s.η_nonneg
  linarith

/-- The constant row costs less than the lower bound `1 + t` of the centered budget. -/
theorem constant_row_le (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    1 + s.data.gain + s.ε * (s.data.gain + s.ε) / (4 * (1 - s.ε)) ≤ s.q + (5 / t) * s.η := by
  have h := scalar_constant_row_sharp ht0 ht1 s.deficit_pos.le s.deficit_le
    s.data.gain_nonneg s.gain_upper
  have hκ : 0 ≤ (5 / t) * s.η := mul_nonneg (by positivity) s.η_nonneg
  linarith [s.q_lower]

theorem augmented_sharp (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    s.data.AugmentedPrefixSqBound (1 + 2 * t) :=
  FinitePrefixSqBound.mono s.augmented (s.augmented_budget_lt ht0 ht1).le

/-- Paper: `(B_n⁻¹)₀₀ = (1 + Z_n) / (1 - ε_n) < 2`. -/
theorem inverse_constant_lt_two (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    (s.data.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  rw [s.data.rawGram_inverse_constant_gain, Complex.ofReal_re, s.mass_eq]
  have he := s.deficit_le_tenth ht1
  apply (div_lt_iff₀ (by linarith : 0 < 1 - s.ε)).mpr
  linarith [s.gain_upper, sharpZ_le_sq ht0 ht1]

/-- The starting block satisfies the complete invariant, including the augmented bound. -/
def initial (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : Stage t 0 where
  dimension := 1
  length := 1
  data := sharpInductionInitial (sharpA t) (sharpA_pos ht0).le
    ((sharpA_le ht1).trans_lt (by norm_num))
  ε := sharpA t
  q := 1 + t
  η := sharpZ t
  deficit_pos := sharpA_pos ht0
  deficit_le := le_rfl
  mass_eq := sharpInductionInitial_mass _ _
  even := sharpInductionInitial_even _ _
  positiveFloor := sharpInductionInitial_floor _ _
  gain_lower := by
    rw [sharpInductionInitial_gain]
    have h : sharpA t ^ 2 / (4 - 8 * sharpA t + 3 * sharpA t ^ 2) = sharpZ t := rfl
    rw [h]
    norm_num
    linarith
  gain_upper := (sharpInductionInitial_gain _ _).le
  inverse_norm := sharpInductionInitial_inverse_norm (sharpA_pos ht0)
    ((sharpA_le ht1).trans (by norm_num))
  inverse_excess := sharpInductionInitial_inverse_excess (sharpA_pos ht0).le
    ((sharpA_le ht1).trans (by norm_num))
  q_lower := le_rfl
  η_nonneg := (sharpZ_pos ht0 ht1).le
  centered := sharpInductionInitial_centered _ _ (by linarith)
  augmented := by
    have h := product_augmented_prefix_sharp
      (sharpInitial (sharpA t) (sharpA_pos ht0).le ((sharpA_le ht1).trans_lt (by norm_num)))
      1 ht0 ht1 (le_refl (1 + t)) (by linarith)
      (by
        rw [sharpInitial_gain, Nat.cast_one, one_mul]
        exact sharpZ_le_half ht0 ht1)
      ((sharpInitial_centered_prefix_iff _ _ (1 + t)).mpr (by linarith))
    rw [sharpInitial_gain] at h
    exact h
  budget := by
    unfold sharpBudget
    norm_num
    linarith

/-- One full choice step: actual finite torus data, the ordered-prefix budget, and all
inverse/positivity estimates are constructed together. -/
theorem exists_next (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    ∃ u : Stage t (k + 1), s.ε / 12 ≤ u.ε ∧ u.ε ≤ s.ε - 3 * s.ε ^ 2 / 4 ∧
      u.data.gain ≤ s.data.gain ∧ u.q = s.q + (5 / t) * s.η + s.ε ^ 2 / 2 ∧
      u.η ≤ sharpZ t / 8 * (1 / 2) ^ k := by
  obtain ⟨b, hb, hfloor⟩ := s.positiveFloor
  have hκ : (0 : ℝ) ≤ 5 / t := by positivity
  have hZpos := sharpZ_pos ht0 ht1
  have he10 := s.deficit_le_tenth ht1
  have hgain0 := s.gain_pos ht0 ht1
  let C : ℝ := ∑ j : Unit ⊕ Fin s.length, |(s.data.rawGram⁻¹ j j).re - 1|
  have hC (j : Unit ⊕ Fin s.length) : (s.data.rawGram⁻¹ j j).re - 1 ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg
      ((s.data.rawGram⁻¹ i i).re - 1)) (Finset.mem_univ j))
  let δ : ℝ := sharpZ t / 8 * (1 / 2) ^ k
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨p, N, hp, hpmax, hpe, hpC, hgp, hgδ, hlo, hhi⟩ :=
    s.data.exists_small_relative_cutoff (C := C) hb hfloor s.mass_eq s.deficit_pos
      (by linarith) hgain0 hδ
  have hp1 : p ≤ 1 := by linarith
  let cut := s.data.orderedCutoffData p N
  have hcutgain : cut.gain = s.data.cutoffGain hb hfloor p N :=
    s.data.cutoffData_gain hb hfloor hp.le hp1 N (ScalarData.orderedCutoffEquiv s.length N)
  have hcutlo : (1 - s.ε / 4) * rareGain s.ε s.data.gain p ≤ cut.gain := by
    rw [hcutgain]
    exact hlo.le
  have hcuthi : cut.gain ≤ rareGain s.ε s.data.gain p := by
    rw [hcutgain]
    exact hhi
  have hη : cut.gain ≤ δ := hcuthi.trans hgδ.le
  let L := ⌊s.data.gain / cut.gain⌋₊
  let next := cut.product L
  let ε' := 1 - next.mass
  let q' := s.q + (5 / t) * s.η + s.ε ^ 2 / 2
  have hstep := cutoff_product_step_sharp s.data hb hfloor s.mass_eq s.deficit_pos he10
    hgain0 (s.deficit_sq_le ht0 ht1) (s.gain_upper.trans (sharpZ_le_one ht0 ht1))
    hp hpmax hpe s.inverse_norm N (ScalarData.orderedCutoffEquiv s.length N) hcutlo hcuthi
  change 0 < ε' ∧ s.ε / 12 ≤ ε' ∧ ε' ≤ s.ε - 3 * s.ε ^ 2 / 4 ∧
    s.data.gain - cut.gain < next.gain ∧ next.gain ≤ s.data.gain ∧
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) next.rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 ∧
    (∀ C : ℝ, (∀ j, (s.data.rawGram⁻¹ j j).re - 1 ≤ C) → p * C ≤ s.ε / 100 →
      ∀ i, (next.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 < 2 * ε') at hstep
  obtain ⟨hepos, helo, hedec, hgloss, hgupper, hinorm, hidiag⟩ := hstep
  have hbudget : q' + (2 / 3) * ε' + (5 / t) * cut.gain ≤
      sharpBudget t - (1 / 2) * ((5 / t) * sharpZ t) * (1 / 2) ^ (k + 1) :=
    sharp_stage_budget_step hκ hZpos.le s.budget hedec hη
  have hκη : 0 ≤ (5 / t) * s.η := mul_nonneg hκ s.η_nonneg
  have hq1 : 1 + t ≤ q' := by
    dsimp [q']
    nlinarith [s.q_lower, sq_nonneg s.ε]
  have hq2 : q' < 1 + 2 * t := by
    have hpw : (0 : ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
    have hB := sharpBudget_lt ht0 ht1
    have hc := mul_nonneg (sharp_copy_cost_nonneg ht0 ht1) hpw
    have hg : 0 ≤ (5 / t) * cut.gain := mul_nonneg hκ cut.gain_nonneg
    nlinarith
  have hcutprefix : cut.CenteredPrefixSqBound q' :=
    orderedCutoffData_prefix_step_sharp s.data s.even hb hfloor hp.le hp1 N s.deficit_pos.le
      s.mass_eq (by linarith [s.q_lower]) (s.constant_row_le ht0 ht1) s.augmented
      s.inverse_excess
  have hcutEven : cut.IsEven :=
    s.data.activationData_even s.even p _ Subtype.val_injective
      (ScalarData.cutoffConstantIndex s.length N).2 rfl (ScalarData.orderedCutoffEquiv s.length N)
  have hcutFloor : cut.HasPositiveFloor :=
    s.data.activationData_positiveFloor s.positiveFloor p _ Subtype.val_injective
      (ScalarData.cutoffConstantIndex s.length N).2 rfl (ScalarData.orderedCutoffEquiv s.length N)
  have hgainupper : next.gain ≤ sharpZ t := hgupper.trans s.gain_upper
  have hLgain : (L : ℝ) * cut.gain ≤ t / 2 := by
    rw [← cut.product_gain L]
    exact hgainupper.trans (sharpZ_le_half ht0 ht1)
  let u : Stage t (k + 1) := {
    dimension := L * (s.dimension + 1)
    length := L * Fintype.card (ScalarData.CutoffNonconstant s.length N)
    data := next
    ε := ε'
    q := q'
    η := cut.gain
    deficit_pos := hepos
    deficit_le := by nlinarith [s.deficit_le, sq_nonneg s.ε]
    mass_eq := by dsimp [ε']; ring
    even := cut.product_even hcutEven L
    positiveFloor := cut.product_positiveFloor hcutFloor L
    gain_lower := sharp_stage_gain_step s.gain_lower hgloss.le hη
    gain_upper := hgainupper
    inverse_norm := hinorm
    inverse_excess := fun i => (hidiag C hC hpC i).le
    q_lower := hq1
    η_nonneg := cut.gain_nonneg
    centered := cut.product_centered_prefix L (by linarith) hcutprefix
    augmented := product_augmented_prefix_sharp cut L ht0 ht1 hq1 hq2 hLgain hcutprefix
    budget := hbudget }
  exact ⟨u, helo, hedec, hgupper, rfl, hη⟩

/-- The next stage is chosen only from the fully proved finite construction. -/
def next (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) : Stage t (k + 1) :=
  Classical.choose (s.exists_next ht0 ht1)

theorem next_deficit_decrease (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) (s : Stage t k) :
    (s.next ht0 ht1).ε ≤ s.ε - 3 * s.ε ^ 2 / 4 :=
  (Classical.choose_spec (s.exists_next ht0 ht1)).2.1

/-- The whole sequence of stages for the parameter `t`. -/
def sequence (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) : (k : ℕ) → Stage t k
  | 0 => initial ht0 ht1
  | k + 1 => (sequence ht0 ht1 k).next ht0 ht1

/-- Paper `h2:eq:epsrec`: the mass losses decrease to zero. -/
theorem sequence_deficit_tendsto (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    Antitone (fun k => (sequence ht0 ht1 k).ε) ∧
      Tendsto (fun k => (sequence ht0 ht1 k).ε) atTop (𝓝 0) := by
  obtain ⟨ha, _, _, hlim⟩ := scalar_deficit_summable_tendsto (fun k => (sequence ht0 ht1 k).ε)
    (fun k => (sequence ht0 ht1 k).deficit_pos.le)
    (fun k => (sequence ht0 ht1 k).next_deficit_decrease ht0 ht1)
  exact ⟨ha, hlim⟩

end Stage

/-- Even measurable scalar blocks with vanishing deficit, retained gain `≥ 3 Z₀ / 4`, centered
squared prefix bound `< 1 + 2 t`, augmented squared prefix bound `1 + 2 t`, and the raw
inverse/spectral estimates required by smoothing and selection (paper: the measurable part
of Proposition `h2:lem:scalar`). -/
theorem measurable_scalar_blocks_sharp {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    ∃ (d n : ℕ → ℕ) (s : (j : ℕ) → ScalarData (d j) (n j)) (ε q : ℕ → ℝ),
      Antitone ε ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ j, (s j).IsEven ∧ (s j).HasPositiveFloor ∧
        0 < ε j ∧ ε j ≤ sharpA t ∧ (s j).mass = 1 - ε j ∧
        (3 / 4) * sharpZ t ≤ (s j).gain ∧ (s j).gain ≤ sharpZ t ∧
        (∀ i : Fin (n j), ((s j).rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * ε j) ∧
        ((s j).rawGram - (((ε j) ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
        1 + t ≤ q j ∧ q j < 1 + 2 * t ∧
        (s j).CenteredPrefixSqBound (q j) ∧ (s j).AugmentedPrefixSqBound (1 + 2 * t) ∧
        ((s j).rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2 := by
  let S := Stage.sequence ht0 ht1
  refine ⟨fun j => (S j).dimension, fun j => (S j).length, fun j => (S j).data,
    fun j => (S j).ε, fun j => (S j).q,
    (Stage.sequence_deficit_tendsto ht0 ht1).1, (Stage.sequence_deficit_tendsto ht0 ht1).2, ?_⟩
  intro j
  exact ⟨(S j).even, (S j).positiveFloor, (S j).deficit_pos, (S j).deficit_le, (S j).mass_eq,
    (S j).gain_retained ht0 ht1, (S j).gain_upper, (S j).inverse_excess,
    inverse_norm_matrix_floor (S j).data.rawGram_posDef (S j).deficit_pos (S j).inverse_norm,
    (S j).q_lower, (S j).q_lt ht0 ht1, (S j).centered,
    (S j).augmented_sharp ht0 ht1, (S j).inverse_constant_lt_two ht0 ht1⟩

end SchauderTranslates.Sharp.Scalar
