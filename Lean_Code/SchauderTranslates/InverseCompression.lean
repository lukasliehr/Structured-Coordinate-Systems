import Lean_Code.SchauderTranslates.FiniteGram

noncomputable section
open Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Coercivity supplies a genuine bounded inverse, also over the complex scalars. -/
theorem coercive_bijective (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re) : Function.Bijective B := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let form : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ (E := H)).comp (B.restrictScalars ℝ)
  have hc : IsCoercive form := by
    refine ⟨b, hb, fun x => ?_⟩
    change b * ‖x‖ * ‖x‖ ≤ (inner ℂ (B x) x).re
    simpa only [pow_two, mul_assoc] using hB x
  let e := hc.continuousLinearEquivOfBilin
  have he (x : H) : e x = B x := by
    apply ext_inner_right ℝ
    intro y
    exact hc.continuousLinearEquivOfBilin_apply x y
  have heq : (e : H → H) = B := funext he
  rw [← heq]
  exact e.bijective

def coerciveEquiv (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr (coercive_bijective B hb hB).1)
    (LinearMap.range_eq_top.mpr (coercive_bijective B hb hB).2)

@[simp] theorem coerciveEquiv_apply (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re) (x : H) :
    coerciveEquiv B hb hB x = B x := rfl

/-- The quadratic objective whose maximum is the inverse quadratic form. -/
def inverseObjective (B : H →L[ℂ] H) (v x : H) : ℝ :=
  2 * (inner ℂ x v).re - (inner ℂ (B x) x).re

omit [CompleteSpace H] in
theorem inverseObjective_complete_square (B : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y)) (v z : H) (hz : B z = v) (x : H) :
    inverseObjective B v x = (inner ℂ v z).re - (inner ℂ (B (x - z)) (x - z)).re := by
  have h1 : (inner ℂ (B x) z).re = (inner ℂ x v).re := by rw [hs, hz]
  have h2 : (inner ℂ v x).re = (inner ℂ x v).re := inner_re_symm (𝕜 := ℂ) _ _
  unfold inverseObjective
  simp only [map_sub, inner_sub_left, inner_sub_right, hz, Complex.sub_re, h1, h2]
  ring

omit [CompleteSpace H] in
theorem inverseObjective_le (B : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (hpos : ∀ x, 0 ≤ (inner ℂ (B x) x).re) (v z : H) (hz : B z = v) (x : H) :
    inverseObjective B v x ≤ (inner ℂ v z).re := by
  rw [inverseObjective_complete_square B hs v z hz x]
  exact sub_le_self _ (hpos _)

omit [CompleteSpace H] in
theorem inverseObjective_at_solution (B : H →L[ℂ] H) (v z : H) (hz : B z = v) :
    inverseObjective B v z = (inner ℂ v z).re := by
  have h : (inner ℂ z v).re = (inner ℂ v z).re := inner_re_symm (𝕜 := ℂ) _ _
  simp only [inverseObjective, hz, h]
  ring

omit [CompleteSpace H] in
/-- Completing the square proves the variational formula with an attained supremum. -/
theorem inverse_variational_formula (B : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (hpos : ∀ x, 0 ≤ (inner ℂ (B x) x).re) (v z : H) (hz : B z = v) :
    IsGreatest (Set.range (inverseObjective B v)) (inner ℂ v z).re := by
  refine ⟨⟨z, inverseObjective_at_solution B v z hz⟩, ?_⟩
  rintro r ⟨x, rfl⟩
  exact inverseObjective_le B hs hpos v z hz x

def compressedOperator (B : H →L[ℂ] H) (F : Submodule ℂ H) [CompleteSpace F] : F →L[ℂ] F :=
  F.orthogonalProjectionOnto.comp (B.comp F.subtypeL)

omit [CompleteSpace H] in
@[simp] theorem compressedOperator_inner (B : H →L[ℂ] H) (F : Submodule ℂ H)
    [CompleteSpace F] (x y : F) :
    inner ℂ (compressedOperator B F x) y = inner ℂ (B (x : H)) (y : H) := by
  exact F.inner_orthogonalProjectionOnto_eq_of_mem_right y (B x)

omit [CompleteSpace H] in
theorem compressedOperator_coercive (B : H →L[ℂ] H) {b : ℝ}
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re)
    (F : Submodule ℂ H) [CompleteSpace F] :
    ∀ x : F, b * ‖x‖ ^ 2 ≤ (inner ℂ (compressedOperator B F x) x).re := by
  intro x
  simpa only [compressedOperator_inner, Submodule.coe_norm] using hB x

/-- Inverse compression in quadratic-form order, for any closed subspace. -/
theorem inverse_compression (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (F : Submodule ℂ H) [CompleteSpace F] (v : F) :
    (inner ℂ v ((coerciveEquiv (compressedOperator B F) hb
      (compressedOperator_coercive B hB F)).symm v)).re ≤
    (inner ℂ (v : H) ((coerciveEquiv B hb hB).symm (v : H))).re := by
  let z : F := (coerciveEquiv (compressedOperator B F) hb
    (compressedOperator_coercive B hB F)).symm v
  have hz : compressedOperator B F z = v :=
    (coerciveEquiv (compressedOperator B F) hb
      (compressedOperator_coercive B hB F)).apply_symm_apply v
  have he : inverseObjective B (v : H) (z : H) = (inner ℂ v z).re := by
    have hq : (inner ℂ (B (z : H)) (z : H)).re = (inner ℂ v z).re := by
      rw [← compressedOperator_inner B F z z, hz]
    have hv : (inner ℂ (z : H) (v : H)).re = (inner ℂ v z).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    simp only [inverseObjective, hq, hv]
    ring
  rw [← he]
  apply inverseObjective_le B hs
  · intro x
    exact (mul_nonneg hb.le (sq_nonneg _)).trans (hB x)
  · exact (coerciveEquiv B hb hB).apply_symm_apply _

omit [CompleteSpace H] in
theorem compressed_inverse_variational (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (F : Submodule ℂ H) [CompleteSpace F] (v : F) :
    IsGreatest (Set.range (fun x : F => inverseObjective B (v : H) (x : H)))
      (inner ℂ v ((coerciveEquiv (compressedOperator B F) hb
        (compressedOperator_coercive B hB F)).symm v)).re := by
  have hsF : ∀ x y : F, inner ℂ (compressedOperator B F x) y =
      inner ℂ x (compressedOperator B F y) := by
    intro x y
    rw [compressedOperator_inner]
    change inner ℂ (B (x : H)) (y : H) =
      inner ℂ x (F.orthogonalProjectionOnto (B (y : H)))
    rw [F.inner_orthogonalProjectionOnto_eq_of_mem_left, hs]
  have hposF (x : F) : 0 ≤ (inner ℂ (compressedOperator B F x) x).re :=
    (mul_nonneg hb.le (sq_nonneg _)).trans (compressedOperator_coercive B hB F x)
  have h := inverse_variational_formula (compressedOperator B F) hsF hposF v
    ((coerciveEquiv (compressedOperator B F) hb (compressedOperator_coercive B hB F)).symm v)
    ((coerciveEquiv (compressedOperator B F) hb
      (compressedOperator_coercive B hB F)).apply_symm_apply v)
  have he (x : F) : inverseObjective (compressedOperator B F) v x =
      inverseObjective B (v : H) (x : H) := by
    unfold inverseObjective
    rw [compressedOperator_inner]
    rfl
  have hef : inverseObjective (compressedOperator B F) v =
      (fun x : F => inverseObjective B (v : H) (x : H)) := funext he
  rw [hef] at h
  exact h

/-- Maxima over nested sets with dense union increase to an attained global maximum. -/
theorem increasing_dense_maxima {X : Type*} [TopologicalSpace X]
    (φ : X → ℝ) (hc : Continuous φ) (S : ℕ → Set X) (hmono : Monotone S)
    (hd : Dense (⋃ n, S n)) (r : ℕ → ℝ)
    (hr : ∀ n, IsGreatest (φ '' S n) (r n))
    (z : X) (hz : ∀ x, φ x ≤ φ z) :
    Monotone r ∧ Tendsto r atTop (𝓝 (φ z)) := by
  have hupper (n : ℕ) : r n ≤ φ z := by
    obtain ⟨x, hx, he⟩ := (hr n).1
    rw [← he]
    exact hz x
  have hmonor : Monotone r := by
    intro n m hnm
    obtain ⟨x, hx, he⟩ := (hr n).1
    exact (hr m).2 ⟨x, hmono hnm hx, he⟩
  refine ⟨hmonor, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨x, hx, hax⟩ := hd.exists_mem_open
      (isOpen_lt continuous_const hc) ⟨z, ha⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hax.trans_le ((hr m).2 ⟨x, hmono hm hn, rfl⟩)
  · intro a ha
    exact Eventually.of_forall (fun n => (hupper n).trans_lt ha)

/-- Exhaustion by nested closed subspaces with dense union recovers the full inverse form. -/
theorem inverse_compression_exhaustion (B : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (F : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (F n)]
    (hmono : Monotone F) (hd : Dense (⋃ n, (F n : Set H)))
    (v : H) (hv : ∀ n, v ∈ F n) :
    let r := fun n => (inner ℂ (⟨v, hv n⟩ : F n)
      ((coerciveEquiv (compressedOperator B (F n)) hb
        (compressedOperator_coercive B hB (F n))).symm ⟨v, hv n⟩)).re
    Monotone r ∧ Tendsto r atTop
      (𝓝 (inner ℂ v ((coerciveEquiv B hb hB).symm v)).re) := by
  dsimp only
  let z := (coerciveEquiv B hb hB).symm v
  have hz : B z = v := (coerciveEquiv B hb hB).apply_symm_apply v
  have hc : Continuous (inverseObjective B v) := by
    unfold inverseObjective
    fun_prop
  have hpos (x : H) : 0 ≤ (inner ℂ (B x) x).re :=
    (mul_nonneg hb.le (sq_nonneg _)).trans (hB x)
  have hmax (x : H) : inverseObjective B v x ≤ inverseObjective B v z := by
    rw [inverseObjective_at_solution B v z hz]
    exact inverseObjective_le B hs hpos v z hz x
  have he (n : ℕ) : (inverseObjective B v) '' (F n : Set H) =
      Set.range (fun x : F n => inverseObjective B v (x : H)) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
  have hr (n : ℕ) := compressed_inverse_variational B hb hB hs (F n) ⟨v, hv n⟩
  have result := increasing_dense_maxima (inverseObjective B v) hc
    (fun n => (F n : Set H)) (fun n m h => hmono h) hd _
    (fun n => (he n).symm ▸ hr n) z hmax
  simpa only [inverseObjective_at_solution B v z hz] using result

end SchauderTranslates
