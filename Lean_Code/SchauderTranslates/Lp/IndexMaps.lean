import Lean_Code.SchauderTranslates.Lp.BranchNorm

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α β : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_restrict_sum_bound (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : β => ℂ) p) (s : Finset α) :
    (∑ i ∈ s, ‖z (e i)‖ ^ p.toReal) ≤ ‖z‖ ^ p.toReal := by
  classical
  calc
    _ = ∑ i ∈ s.image e, ‖z i‖ ^ p.toReal :=
      (Finset.sum_image (f := fun i => ‖z i‖ ^ p.toReal)
        (fun _ _ _ _ h => e.injective h)).symm
    _ ≤ ‖z‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hp z _

def lpRestrictLinear (hp : 0 < p.toReal) (e : α ↪ β) :
    lp (fun _ : β => ℂ) p →ₗ[ℂ] lp (fun _ : α => ℂ) p where
  toFun z := ⟨fun i => z (e i), memℓp_gen' (lp_restrict_sum_bound hp e z)⟩
  map_add' _ _ := by apply lp.ext; funext i; rfl
  map_smul' _ _ := by apply lp.ext; funext i; rfl

theorem lpRestrictLinear_bound (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : β => ℂ) p) : ‖lpRestrictLinear hp e z‖ ≤ ‖z‖ :=
  lp.norm_le_of_forall_sum_le hp (norm_nonneg z) (lp_restrict_sum_bound hp e z)

def lpRestrict (hp : 0 < p.toReal) (e : α ↪ β) :
    lp (fun _ : β => ℂ) p →L[ℂ] lp (fun _ : α => ℂ) p :=
  (lpRestrictLinear hp e).mkContinuous 1 (fun z => by simpa using lpRestrictLinear_bound hp e z)

@[simp] theorem lpRestrict_apply (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : β => ℂ) p) (i : α) : lpRestrict hp e z i = z (e i) := rfl

theorem lpRestrict_norm_le (hp : 0 < p.toReal) (e : α ↪ β) : ‖lpRestrict hp e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem extend_norm_power (hp : 0 < p.toReal) (e : α ↪ β) (z : α → ℂ) :
    (fun b => ‖Function.extend e z (fun _ => 0) b‖ ^ p.toReal) =
      Function.extend e (fun a => ‖z a‖ ^ p.toReal) (fun _ => 0) := by
  classical
  funext b
  by_cases hb : ∃ a, e a = b
  · obtain ⟨a, rfl⟩ := hb
    simp [e.injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ hb, hp.ne']

theorem lp_extend_mem (hp : 0 < p.toReal) (e : α ↪ β) (z : lp (fun _ : α => ℂ) p) :
    Memℓp (Function.extend e z (fun _ => 0)) p := by
  apply memℓp_gen
  rw [extend_norm_power hp e z]
  exact (summable_extend_zero e.injective).mpr ((lp.memℓp z).summable hp)

def lpExtendLinear (hp : 0 < p.toReal) (e : α ↪ β) :
    lp (fun _ : α => ℂ) p →ₗ[ℂ] lp (fun _ : β => ℂ) p where
  toFun z := ⟨Function.extend e z (fun _ => 0), lp_extend_mem hp e z⟩
  map_add' z w := by
    apply lp.ext
    funext b
    classical
    by_cases hb : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := hb
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ hb]
  map_smul' c z := by
    apply lp.ext
    funext b
    classical
    by_cases hb : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := hb
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ hb]

theorem lpExtendLinear_norm (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : α => ℂ) p) : ‖lpExtendLinear hp e z‖ = ‖z‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  change (∑' b, ‖Function.extend e z (fun _ => 0) b‖ ^ p.toReal) = ∑' a, ‖z a‖ ^ p.toReal
  rw [extend_norm_power hp e z]
  exact tsum_extend_zero e.injective _

def lpExtend (hp : 0 < p.toReal) (e : α ↪ β) :
    lp (fun _ : α => ℂ) p →ₗᵢ[ℂ] lp (fun _ : β => ℂ) p where
  toLinearMap := lpExtendLinear hp e
  norm_map' := lpExtendLinear_norm hp e

@[simp] theorem lpExtend_apply_image (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : α => ℂ) p) (a : α) : lpExtend hp e z (e a) = z a := by
  change Function.extend e z (fun _ => 0) (e a) = z a
  exact e.injective.extend_apply _ _ a

theorem lpExtend_apply_outside (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : α => ℂ) p) (b : β) (hb : ¬∃ a, e a = b) : lpExtend hp e z b = 0 := by
  change Function.extend e z (fun _ => 0) b = 0
  exact Function.extend_apply' _ _ _ hb

@[simp] theorem lpRestrict_extend (hp : 0 < p.toReal) (e : α ↪ β)
    (z : lp (fun _ : α => ℂ) p) : lpRestrict hp e (lpExtend hp e z) = z := by
  apply lp.ext
  funext a
  simp

@[simp] theorem lpRestrict_single_image [DecidableEq α] [DecidableEq β]
    (hp : 0 < p.toReal) (e : α ↪ β)
    (a : α) (c : ℂ) : lpRestrict hp e (lp.single p (e a) c) = lp.single p a c := by
  classical
  apply lp.ext
  funext b
  simp [Pi.single_apply, e.injective.eq_iff]

theorem lpRestrict_single_outside [DecidableEq α] [DecidableEq β]
    (hp : 0 < p.toReal) (e : α ↪ β)
    (b : β) (hb : ¬∃ a, e a = b) (c : ℂ) : lpRestrict hp e (lp.single p b c) = 0 := by
  classical
  apply lp.ext
  funext a
  have hab : e a ≠ b := fun h => hb ⟨a, h⟩
  simp [Pi.single_apply, hab]

@[simp] theorem lpExtend_single [DecidableEq α] [DecidableEq β]
    (hp : 0 < p.toReal) (e : α ↪ β)
    (a : α) (c : ℂ) : lpExtend hp e (lp.single p a c) = lp.single p (e a) c := by
  classical
  apply lp.ext
  funext b
  by_cases hb : ∃ a, e a = b
  · obtain ⟨a', rfl⟩ := hb
    simp [Pi.single_apply, e.injective.eq_iff]
  · have hba : b ≠ e a := fun h => hb ⟨a, h.symm⟩
    simp [lpExtend_apply_outside hp e _ b hb, Pi.single_apply, hba]

end SchauderTranslates.LpConstruction
