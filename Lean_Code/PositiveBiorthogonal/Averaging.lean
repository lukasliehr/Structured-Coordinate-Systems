import Lean_Code.PositiveBiorthogonal.Partitions

/-! Contractive averaging projections on interval cells and admissible partitions. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal
namespace IntervalCell
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem indicator_norm_product (D : IntervalCell) :
    ‖(D.indicator : L 𝕜 p)‖ * ‖(D.indicator : L 𝕜 q)‖ = D.length := by
  by_cases hp : p = ∞
  · subst p
    have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    subst q
    rw [D.indicator_norm_top, D.indicator_norm one_ne_zero ENNReal.one_ne_top]
    simp
  · by_cases hq : q = ∞
    · subst q
      have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
      subst p
      rw [D.indicator_norm_top, D.indicator_norm one_ne_zero ENNReal.one_ne_top]
      simp
    · have hrs := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
      rw [D.indicator_norm (ENNReal.HolderConjugate.ne_zero p q) hp,
        D.indicator_norm (ENNReal.HolderConjugate.ne_zero q p) hq,
        ← Real.rpow_add D.length_pos]
      simp only [one_div, hrs.inv_add_inv_eq_one, Real.rpow_one]

def averageCLM (D : IntervalCell) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  ((D.length : 𝕜)⁻¹) • (representedFunctional (D.indicator : L 𝕜 q)).smulRight D.indicator

@[simp] theorem averageCLM_apply (D : IntervalCell) (f : L 𝕜 p) :
    D.averageCLM (q := q) f = ((D.length : 𝕜)⁻¹ * ∫ x in D.carrier, f x) • D.indicator := by
  simp [averageCLM, D.pairing_indicator, smul_smul]

theorem averageCLM_norm (D : IntervalCell) : ‖D.averageCLM (𝕜 := 𝕜) (p := p) (q := q)‖ = 1 := by
  rw [averageCLM, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos D.length_pos,
    represented_rank_one_norm, D.indicator_norm_product, inv_mul_cancel₀ D.length_pos.ne']

theorem averageCLM_localized (D : IntervalCell) :
    LocalizedOperator D.carrier D.measurable (D.averageCLM (𝕜 := 𝕜) (p := p) (q := q)) where
  input f := by
    rw [averageCLM_apply, averageCLM_apply]
    congr 2
    apply setIntegral_congr_ae D.measurable
    filter_upwards [coeFn_cut D.carrier D.measurable f] with x hx
    intro hxd
    simp [hx, hxd]
  output f := by
    rw [averageCLM_apply]
    filter_upwards [Lp.coeFn_smul ((D.length : 𝕜)⁻¹ * ∫ x in D.carrier, f x)
      (D.indicator : L 𝕜 p), D.coe_indicator (𝕜 := 𝕜) (p := p)] with x hx hi
    intro hxd
    rw [hx, Pi.smul_apply, hi]
    simp [hxd]

theorem averageCLM_indicator (D : IntervalCell) :
    D.averageCLM (q := q) (D.indicator : L 𝕜 p) = D.indicator := by
  rw [averageCLM_apply, ← D.pairing_indicator (q := q), D.pairing_indicators,
    Set.inter_self, D.volume_real, inv_mul_cancel₀]
  · exact one_smul _ _
  · exact_mod_cast D.length_pos.ne'

theorem averageCLM_other_indicator (D E : IntervalCell) (hDE : Disjoint D.carrier E.carrier) :
    D.averageCLM (q := q) (E.indicator : L 𝕜 p) = 0 := by
  rw [averageCLM_apply, ← D.pairing_indicator (q := q), E.pairing_indicators,
    Set.disjoint_iff_inter_eq_empty.mp hDE.symm]
  simp

end IntervalCell

namespace ActivePartition
variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def averageCLM (P : ActivePartition) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  ∑ i : Fin P.R, (P.cell i).averageCLM (q := q)

@[simp] theorem averageCLM_apply (P : ActivePartition) (f : L 𝕜 p) :
    P.averageCLM (q := q) f = P.average f := by
  simp [averageCLM, average]

theorem averageCLM_localized_and_norm (P : ActivePartition) :
    LocalizedOperator P.active P.active_measurable (P.averageCLM (𝕜 := 𝕜) (p := p) (q := q)) ∧
      ‖P.averageCLM (𝕜 := 𝕜) (p := p) (q := q)‖ ≤ 1 := by
  have hb := disjoint_operator_sum Finset.univ (fun i : Fin P.R => (P.cell i).carrier)
    (fun i => (P.cell i).measurable) P.disjoint
    (fun i => (P.cell i).averageCLM (𝕜 := 𝕜) (p := p) (q := q))
    (fun i => (P.cell i).averageCLM_localized) 1 zero_le_one
    (fun i => (P.cell i).averageCLM_norm.le)
  simpa only [Finset.mem_univ, iUnion_true, P.cover, averageCLM, active] using hb

theorem averageCLM_norm_le (P : ActivePartition) :
    ‖P.averageCLM (𝕜 := 𝕜) (p := p) (q := q)‖ ≤ 1 := P.averageCLM_localized_and_norm.2

theorem averageCLM_localized (P : ActivePartition) :
    LocalizedOperator P.active P.active_measurable (P.averageCLM (𝕜 := 𝕜) (p := p) (q := q)) :=
  P.averageCLM_localized_and_norm.1

theorem averageCLM_indicator (P : ActivePartition) (j : Fin P.R) :
    P.averageCLM (q := q) ((P.cell j).indicator : L 𝕜 p) = (P.cell j).indicator := by
  classical
  rw [averageCLM, sum_apply, Finset.sum_eq_single j]
  · exact (P.cell j).averageCLM_indicator
  · intro i _ hij
    exact (P.cell i).averageCLM_other_indicator (P.cell j) (P.disjoint hij)
  · simp

/-- The functions constant on the cells and zero outside the active region. -/
def Cellwise (P : ActivePartition) (f : L 𝕜 p) : Prop :=
  ∃ c : Fin P.R → 𝕜, f = ∑ i : Fin P.R, c i • (P.cell i).indicator

omit [Fact (1 ≤ p)] in
theorem average_cellwise (P : ActivePartition) (f : L 𝕜 p) : P.Cellwise (P.average f) := by
  exact ⟨fun i => ((P.cell i).length : 𝕜)⁻¹ * ∫ x in (P.cell i).carrier, f x, rfl⟩

theorem averageCLM_fixed_of_cellwise (P : ActivePartition) (f : L 𝕜 p) (hf : P.Cellwise f) :
    P.averageCLM (q := q) f = f := by
  obtain ⟨c, rfl⟩ := hf
  simp only [map_sum, map_smul, P.averageCLM_indicator]

theorem averageCLM_idempotent (P : ActivePartition) (f : L 𝕜 p) :
    P.averageCLM (q := q) (P.averageCLM (q := q) f) = P.averageCLM (q := q) f := by
  apply P.averageCLM_fixed_of_cellwise
  rw [averageCLM_apply]
  exact P.average_cellwise f

theorem averageCLM_range (P : ActivePartition) :
    Set.range (P.averageCLM (𝕜 := 𝕜) (p := p) (q := q)) = {f | P.Cellwise f} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [averageCLM_apply]
    exact P.average_cellwise g
  · intro hf
    exact ⟨f, P.averageCLM_fixed_of_cellwise f hf⟩

omit [Fact (1 ≤ p)] in
theorem cell_sum_coe (P : ActivePartition) (c : Fin P.R → 𝕜) :
    ((∑ i : Fin P.R, c i • (P.cell i).indicator : L 𝕜 p) : ℝ → 𝕜) =ᵐ[volume]
      fun x => ∑ i : Fin P.R, (P.cell i).carrier.indicator (fun _ => c i) x := by
  have ht (i : Fin P.R) : ((c i • (P.cell i).indicator : L 𝕜 p) : ℝ → 𝕜) =ᵐ[volume]
      (P.cell i).carrier.indicator (fun _ => c i) := by
    filter_upwards [Lp.coeFn_smul (c i) ((P.cell i).indicator : L 𝕜 p),
      (P.cell i).coe_indicator (𝕜 := 𝕜) (p := p)] with x hx hi
    rw [hx, Pi.smul_apply, hi]
    by_cases hm : x ∈ (P.cell i).carrier <;> simp [hm]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin P.R => c i • ((P.cell i).indicator : L 𝕜 p)), ae_all_iff.mpr ht] with x hs hx
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem cell_sum_on_cell (P : ActivePartition) (c : Fin P.R → 𝕜) (j : Fin P.R)
    (x : ℝ) (hx : x ∈ (P.cell j).carrier) :
    (∑ i : Fin P.R, (P.cell i).carrier.indicator (fun _ => c i) x) = c j := by
  classical
  rw [Finset.sum_eq_single j]
  · simp [hx]
  · intro i _ hij
    have hi : x ∉ (P.cell i).carrier := fun hi => Set.disjoint_left.mp (P.disjoint hij) hi hx
    simp [hi]
  · simp

theorem cell_sum_off_active (P : ActivePartition) (c : Fin P.R → 𝕜)
    (x : ℝ) (hx : x ∉ P.active) :
    (∑ i : Fin P.R, (P.cell i).carrier.indicator (fun _ => c i) x) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : x ∉ (P.cell i).carrier := by
    intro hxi
    apply hx
    change x ∈ ⋃ n ∈ P.units, (gridUnit n).carrier
    rw [← P.cover]
    exact mem_iUnion.mpr ⟨i, hxi⟩
  simp [hi]

omit [Fact (1 ≤ p)] in
/-- The range description agrees with literal cellwise constants and vanishing off A. -/
theorem cellwise_iff_ae_constant (P : ActivePartition) (f : L 𝕜 p) :
    P.Cellwise f ↔ ∃ c : Fin P.R → 𝕜,
      ∀ᵐ x : ℝ, (∀ i : Fin P.R, x ∈ (P.cell i).carrier → f x = c i) ∧
        (x ∉ P.active → f x = 0) := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    filter_upwards [P.cell_sum_coe (p := p) c] with x hx
    rw [hx]
    exact ⟨fun i hi => P.cell_sum_on_cell c i x hi, P.cell_sum_off_active c x⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Lp.ext
    filter_upwards [hc, P.cell_sum_coe (p := p) c] with x hx hs
    rw [hs]
    by_cases ha : x ∈ P.active
    · have hu : x ∈ ⋃ i : Fin P.R, (P.cell i).carrier := by
        rw [P.cover]
        exact ha
      obtain ⟨i, hi⟩ := mem_iUnion.mp hu
      rw [hx.1 i hi, P.cell_sum_on_cell c i x hi]
    · rw [hx.2 ha, P.cell_sum_off_active c x ha]

end ActivePartition
end PositiveBiorthogonal
