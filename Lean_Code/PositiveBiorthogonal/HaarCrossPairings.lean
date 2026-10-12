import Lean_Code.PositiveBiorthogonal.HaarIncrement

/-! Both off-diagonal pairings for a later split inside an earlier partition refinement. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

theorem IntervalCell.coe_normalizedIndicator (D : IntervalCell) :
    ((D.normalizedIndicator : L 𝕜 p) : ℝ → 𝕜) =ᵐ[volume]
      D.carrier.indicator (fun _ => (D.length : 𝕜)⁻¹) := by
  filter_upwards [Lp.coeFn_smul ((D.length : 𝕜)⁻¹) (D.indicator : L 𝕜 p),
    D.coe_indicator (𝕜 := 𝕜) (p := p)] with x hs hi
  change (((D.length : 𝕜)⁻¹) • D.indicator : L 𝕜 p) x = _
  rw [hs, Pi.smul_apply, hi]
  by_cases hx : x ∈ D.carrier <;> simp [hx]

theorem IntervalSplit.haarH_on_children (S : IntervalSplit) :
    ∀ᵐ x : ℝ,
      (x ∈ S.leftChild.carrier → (S.haarH : L 𝕜 p) x = (S.leftChild.length : 𝕜)⁻¹) ∧
      (x ∈ S.rightChild.carrier → (S.haarH : L 𝕜 p) x = -(S.rightChild.length : 𝕜)⁻¹) := by
  filter_upwards [Lp.coeFn_sub (S.leftChild.normalizedIndicator : L 𝕜 p) S.rightChild.normalizedIndicator,
    S.leftChild.coe_normalizedIndicator (𝕜 := 𝕜) (p := p), S.rightChild.coe_normalizedIndicator (𝕜 := 𝕜) (p := p)]
    with x hs hb hc
  change (_ → (S.leftChild.normalizedIndicator - S.rightChild.normalizedIndicator : L 𝕜 p) x = _) ∧
    (_ → (S.leftChild.normalizedIndicator - S.rightChild.normalizedIndicator : L 𝕜 p) x = _)
  rw [hs, Pi.sub_apply, hb, hc]
  constructor
  · intro hx
    have hy : x ∉ S.rightChild.carrier := fun hy => Set.disjoint_left.mp S.children_disjoint hx hy
    simp [hx, hy]
  · intro hy
    have hx : x ∉ S.leftChild.carrier := fun hx => Set.disjoint_left.mp S.children_disjoint hx hy
    simp [hx, hy]

theorem IntervalSplit.haarPhi_on_children (S : IntervalSplit) :
    ∀ᵐ x : ℝ,
      (x ∈ S.leftChild.carrier → (S.haarPhi : L 𝕜 p) x = 1 - (S.ratio : 𝕜)) ∧
      (x ∈ S.rightChild.carrier → (S.haarPhi : L 𝕜 p) x = -(S.ratio : 𝕜)) := by
  filter_upwards [Lp.coeFn_sub (S.leftChild.indicator : L 𝕜 p) ((S.ratio : 𝕜) • S.parent.indicator),
    Lp.coeFn_smul (S.ratio : 𝕜) (S.parent.indicator : L 𝕜 p),
    S.leftChild.coe_indicator (𝕜 := 𝕜) (p := p), S.parent.coe_indicator (𝕜 := 𝕜) (p := p)]
    with x hs hm hb hd
  change (_ → (S.leftChild.indicator - (S.ratio : 𝕜) • S.parent.indicator : L 𝕜 p) x = _) ∧
    (_ → (S.leftChild.indicator - (S.ratio : 𝕜) • S.parent.indicator : L 𝕜 p) x = _)
  rw [hs, Pi.sub_apply, hm, Pi.smul_apply, hb, hd]
  constructor
  · intro hx
    simp [hx, S.left_subset hx]
  · intro hy
    have hx : x ∉ S.leftChild.carrier := fun hx => Set.disjoint_left.mp S.children_disjoint hx hy
    simp [hx, S.right_subset hy]

theorem pairing_constant_supported (f : L 𝕜 p) (g : L 𝕜 q) (A : Set ℝ) (c : 𝕜)
    (hf : ∀ᵐ x : ℝ, x ∈ A → f x = c) (hg : ∀ᵐ x : ℝ, x ∉ A → g x = 0) :
    pairing f g = c * ∫ x : ℝ, g x := by
  rw [pairing, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hx hy
  by_cases ha : x ∈ A <;> simp [ha, hx, hy]

theorem pairing_zero_disjoint_support (f : L 𝕜 p) (g : L 𝕜 q) (A B : Set ℝ) (hAB : Disjoint A B)
    (hf : ∀ᵐ x : ℝ, x ∉ A → f x = 0) (hg : ∀ᵐ x : ℝ, x ∉ B → g x = 0) :
    pairing f g = 0 := by
  rw [pairing]
  calc
    _ = ∫ _ : ℝ, (0 : 𝕜) := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hx hy
      by_cases ha : x ∈ A
      · have hb : x ∉ B := fun hb => Set.disjoint_left.mp hAB ha hb
        simp [hy hb]
      · simp [hx ha]
    _ = 0 := integral_zero _ _

def SplitSeparated (S T : IntervalSplit) : Prop :=
  Disjoint S.parent.carrier T.parent.carrier ∨
    T.parent.carrier ⊆ S.leftChild.carrier ∨ T.parent.carrier ⊆ S.rightChild.carrier

theorem IntervalSplit.pairing_earlier_later (S T : IntervalSplit) (hST : SplitSeparated S T) :
    pairing (S.haarH : L 𝕜 p) (T.haarPhi : L 𝕜 q) = 0 := by
  rcases hST with hd | hb | hc
  · exact pairing_zero_disjoint_support _ _ _ _ hd S.haarH_supported T.haarPhi_supported
  · rw [pairing_constant_supported _ _ T.parent.carrier (S.leftChild.length : 𝕜)⁻¹
      (S.haarH_on_children.mono fun x hx ht => hx.1 (hb ht)) T.haarPhi_supported, T.integral_haarPhi, mul_zero]
  · rw [pairing_constant_supported _ _ T.parent.carrier (-(S.rightChild.length : 𝕜)⁻¹)
      (S.haarH_on_children.mono fun x hx ht => hx.2 (hc ht)) T.haarPhi_supported, T.integral_haarPhi, mul_zero]

theorem IntervalSplit.pairing_later_earlier (S T : IntervalSplit) (hST : SplitSeparated S T) :
    pairing (T.haarH : L 𝕜 p) (S.haarPhi : L 𝕜 q) = 0 := by
  rw [pairing_comm]
  rcases hST with hd | hb | hc
  · exact pairing_zero_disjoint_support _ _ _ _ hd S.haarPhi_supported T.haarH_supported
  · rw [pairing_constant_supported _ _ T.parent.carrier (1 - (S.ratio : 𝕜))
      (S.haarPhi_on_children.mono fun x hx ht => hx.1 (hb ht)) T.haarH_supported, T.integral_haarH, mul_zero]
  · rw [pairing_constant_supported _ _ T.parent.carrier (-(S.ratio : 𝕜))
      (S.haarPhi_on_children.mono fun x hx ht => hx.2 (hc ht)) T.haarH_supported, T.integral_haarH, mul_zero]

end PositiveBiorthogonal
