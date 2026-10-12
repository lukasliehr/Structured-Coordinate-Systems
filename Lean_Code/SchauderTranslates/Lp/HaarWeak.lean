import Lean_Code.SchauderTranslates.Lp.HaarBadSupport
import Lean_Code.SchauderTranslates.Lp.HaarChebyshev

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Blueprint `lp:haar-weak`: the uniform weak L¹ estimate for the actual
integral-defined finite Haar multipliers, on every finite complex dyadic
step function. The output is measured modulo a.e. representative changes. -/
theorem haar_weak_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ) (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    haarMeasure.real {x | a < ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖} ≤
      3 * ‖haarDyadicStep 1 N c‖ / a := by
  let f := dyadicStepValue N c
  let L := ‖haarDyadicStep 1 N c‖
  have hI : (∫ x, ‖f x‖ ∂haarMeasure) = L := dyadicStepValue_norm_integral N c
  by_cases hLa : L ≤ a
  · let s := maximalDyadicCells (dyadicBadCells N f a)
    let b := dyadicBadPartLp f (dyadicStepValue_memLp 2 N c) s
    let g := haarDyadicStep 2 N c - b
    let T := haarL2Multiplier t w
    have hgbound : ‖g‖ ^ 2 ≤ 2 * a * L := by
      have hgAE : (g : ℝ → ℂ) =ᵐ[haarMeasure] dyadicGoodPart f s := by
        filter_upwards [haarDyadicStep_ae_value 2 N c,
          dyadicBadPartLp_ae f (dyadicStepValue_memLp 2 N c) s,
          Lp.coeFn_sub (haarDyadicStep 2 N c) b] with x hfx hbx hsub
        change (haarDyadicStep 2 N c - b) x = _
        rw [hsub, Pi.sub_apply, hfx, hbx]
        rfl
      calc
        _ = ∫ x, ‖g x‖ ^ 2 ∂haarMeasure := (haar_l2_square_integral g).symm
        _ = ∫ x, ‖dyadicGoodPart f s x‖ ^ 2 ∂haarMeasure :=
          integral_congr_ae (hgAE.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
        _ ≤ 2 * a * ∫ x, ‖f x‖ ∂haarMeasure :=
          dyadicGoodPart_square_integral_bound N c ha.le (by rw [hI]; exact hLa)
        _ = _ := by rw [hI]
    have hTb : SupportedOn (T b) (dyadicBadUnion N f a) :=
      haar_bad_multiplier_supported f (dyadicStepValue_memLp 2 N c)
        (dyadicStepValue_integrable N c) s t w
    have hTsum : T (haarDyadicStep 2 N c) = T g + T b := by
      dsimp only [g]
      rw [map_sub, sub_add_cancel]
    have hsubset : {x | a < ‖T (haarDyadicStep 2 N c) x‖} ≤ᵐ[haarMeasure]
        (dyadicBadUnion N f a ∪ {x | a < ‖T g x‖} : Set ℝ) := by
      filter_upwards [hTb, Lp.coeFn_add (T g) (T b)] with x hb hsum
      intro hx
      by_cases hxΩ : x ∈ dyadicBadUnion N f a
      · exact Or.inl hxΩ
      · apply Or.inr
        have he : T (haarDyadicStep 2 N c) x = T g x := by
          rw [hTsum, hsum, Pi.add_apply, hb hxΩ, add_zero]
        change a < ‖T (haarDyadicStep 2 N c) x‖ at hx
        change a < ‖T g x‖
        rw [he] at hx
        exact hx
    calc
      _ ≤ haarMeasure.real (dyadicBadUnion N f a ∪ {x | a < ‖T g x‖}) :=
        haar_measureReal_mono_ae hsubset
      _ ≤ haarMeasure.real (dyadicBadUnion N f a) + haarMeasure.real {x | a < ‖T g x‖} :=
        measureReal_union_le _ _
      _ ≤ L / a + ‖T g‖ ^ 2 / a ^ 2 := add_le_add
        (by rw [← hI]; exact dyadicBadUnion_measure_bound N f (dyadicStepValue_integrable N c) ha)
        (haar_l2_chebyshev (T g) ha)
      _ ≤ L / a + ‖g‖ ^ 2 / a ^ 2 := add_le_add le_rfl
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
          (haar_l2_multiplier_bound t w hw g) 2) (sq_nonneg a))
      _ ≤ L / a + (2 * a * L) / a ^ 2 := add_le_add le_rfl
        (div_le_div_of_nonneg_right hgbound (sq_nonneg a))
      _ = _ := by field_simp [ha.ne']; ring
  · have hL : a < L := lt_of_not_ge hLa
    have hmeasure : haarMeasure.real {x | a < ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖} ≤ 1 := by
      simpa [measureReal_def] using (measureReal_mono
        (Set.subset_univ {x | a < ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖})
        (measure_ne_top haarMeasure Set.univ))
    apply hmeasure.trans
    apply (le_div_iff₀ ha).mpr
    change 1 * a ≤ 3 * L
    have hLn : 0 ≤ L := norm_nonneg _
    nlinarith

end SchauderTranslates.LpConstruction
