import Lean_Code.SchauderTranslates.Lp.HaarIntegrals
import Lean_Code.SchauderTranslates.Lp.HaarNorm

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_value_constant_on_finer_cell (n k m l : ℕ) (hnm : n < m) :
    ∃ c : ℂ, ∀ x ∈ dyadicInterval m l, (haarScale n : ℂ) *
      ((dyadicInterval (n + 1) (2 * k)).indicator (fun _ => (1 : ℂ)) x -
        (dyadicInterval (n + 1) (2 * k + 1)).indicator (fun _ => (1 : ℂ)) x) = c := by
  rcases dyadicInterval_nested_or_disjoint (Nat.succ_le_iff.mpr hnm) (2 * k) l with hl | hl
  · refine ⟨haarScale n, ?_⟩
    intro x hx
    have hxl := hl hx
    have hxr : x ∉ dyadicInterval (n + 1) (2 * k + 1) := fun h =>
      Set.disjoint_left.mp (dyadicInterval_children_disjoint n k) hxl h
    simp [hxl, hxr]
  · rcases dyadicInterval_nested_or_disjoint (Nat.succ_le_iff.mpr hnm) (2 * k + 1) l with hr | hr
    · refine ⟨-(haarScale n : ℂ), ?_⟩
      intro x hx
      have hxl : x ∉ dyadicInterval (n + 1) (2 * k) := fun h => Set.disjoint_left.mp hl hx h
      simp [hxl, hr hx]
    · refine ⟨0, ?_⟩
      intro x hx
      have hxl : x ∉ dyadicInterval (n + 1) (2 * k) := fun h => Set.disjoint_left.mp hl hx h
      have hxr : x ∉ dyadicInterval (n + 1) (2 * k + 1) := fun h => Set.disjoint_left.mp hr hx h
      simp [hxl, hxr]

theorem haar_inner_zero_of_disjoint (f g : HaarLp 2)
    (hd : ∀ᵐ x ∂haarMeasure, f x = 0 ∨ g x = 0) : inner ℂ f g = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hd] with x hx
  rcases hx with hx | hx <;> simp [hx]

theorem haar_inner_zero_of_const_on_support (f g : HaarLp 2) (S : Set ℝ) (c : ℂ)
    (hf : ∀ᵐ x ∂haarMeasure, x ∈ S → f x = c) (hg : SupportedOn g S)
    (hi : (∫ x, g x ∂haarMeasure) = 0) : inner ℂ f g = 0 := by
  calc
    _ = ∫ x, (starRingEnd ℂ c) * g x ∂haarMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hfx hgx
      by_cases hx : x ∈ S
      · simp [hfx hx, mul_comm]
      · simp [hgx hx]
    _ = (starRingEnd ℂ c) * ∫ x, g x ∂haarMeasure := integral_const_mul _ _
    _ = 0 := by rw [hi, mul_zero]

theorem haarConstant_inner_function_zero (n k : ℕ) (hk : k < 2 ^ n) :
    inner ℂ (haarConstant 2) (haarFunction 2 n k) = 0 := by
  apply haar_inner_zero_of_const_on_support _ _ (dyadicInterval n k) 1 _
    (haarFunction_supported 2 n k) (haarFunction_integral_zero 2 n k hk)
  filter_upwards [haarConstant_ae_one 2] with x hx
  exact fun _ => hx

theorem haarFunction_inner_zero_of_lt (n k m l : ℕ) (hnm : n < m) (hl : l < 2 ^ m) :
    inner ℂ (haarFunction 2 n k) (haarFunction 2 m l) = 0 := by
  obtain ⟨c, hc⟩ := haar_value_constant_on_finer_cell n k m l hnm
  apply haar_inner_zero_of_const_on_support _ _ (dyadicInterval m l) c _
    (haarFunction_supported 2 m l) (haarFunction_integral_zero 2 m l hl)
  filter_upwards [haarFunction_ae 2 n k] with x hx
  exact fun hxm => hx.trans (hc x hxm)

theorem haarFunction_inner_zero (n k m l : ℕ) (hk : k < 2 ^ n) (hl : l < 2 ^ m)
    (hne : (n, k) ≠ (m, l)) : inner ℂ (haarFunction 2 n k) (haarFunction 2 m l) = 0 := by
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · exact haarFunction_inner_zero_of_lt n k m l hnm hl
  · subst m
    have hkl : k ≠ l := by intro he; subst l; exact hne rfl
    exact haar_inner_zero_of_disjoint _ _ ((haarFunction_supported 2 n k).ae_disjoint
      (haarFunction_supported 2 n l) (dyadicInterval_disjoint_same n hkl))
  · exact inner_eq_zero_symm.mpr (haarFunction_inner_zero_of_lt m l n k hmn hk)

/-- The normalized constant and all dyadic Haar differences form an
orthonormal family in the actual complex Lebesgue L² space on the unit interval. -/
theorem haar_orthonormal : Orthonormal ℂ (haarAtom 2) := by
  refine ⟨norm_haarAtom_two, ?_⟩
  intro a b hab
  rcases a with _ | ⟨n, k⟩
  · rcases b with _ | ⟨m, l⟩
    · exact (hab rfl).elim
    · exact haarConstant_inner_function_zero m l l.isLt
  · rcases b with _ | ⟨m, l⟩
    · exact inner_eq_zero_symm.mpr (haarConstant_inner_function_zero n k k.isLt)
    · apply haarFunction_inner_zero n k m l k.isLt l.isLt
      intro he
      have hnm := congrArg Prod.fst he
      have hkl := congrArg Prod.snd he
      dsimp at hnm hkl
      subst m
      have he' : k = l := Fin.ext hkl
      subst l
      exact hab rfl

end SchauderTranslates.LpConstruction
