import Lean_Code.SchauderTranslates.Lp.PermanentPrivateCells

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

abbrev PrivateCellIndex := {i : ℕ // (globalCell p q hp2 hpfin i).IsPrivate}

def privateCellVector (i : PrivateCellIndex p q hp2 hpfin) : LebesgueLp p :=
  (globalCell p q hp2 hpfin i.val).privateVector

def privateCellData (i : PrivateCellIndex p q hp2 hpfin) :
    DisjointStepData p (privateCellVector p q hp2 hpfin i) :=
  (globalCell p q hp2 hpfin i.val).privateData i.property

theorem privateCellVector_unit (i : PrivateCellIndex p q hp2 hpfin) :
    ‖privateCellVector p q hp2 hpfin i‖ = 1 :=
  (globalCell p q hp2 hpfin i.val).privateVector_unit i.property

theorem privateCellData_support (i : PrivateCellIndex p q hp2 hpfin) :
    (privateCellData p q hp2 hpfin i).supportSet = (globalCell p q hp2 hpfin i.val).support :=
  (globalCell p q hp2 hpfin i.val).privateData_support i.property

theorem privateCellData_disjoint :
    Pairwise (fun i j : PrivateCellIndex p q hp2 hpfin =>
      Disjoint (privateCellData p q hp2 hpfin i).supportSet (privateCellData p q hp2 hpfin j).supportSet) := by
  intro i j hij
  have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  rw [privateCellData_support, privateCellData_support]
  exact globalCell_pairwise_disjoint p q hp2 hpfin hv

theorem privateCellVector_disjoint :
    Pairwise (fun i j : PrivateCellIndex p q hp2 hpfin =>
      ∀ᵐ x ∂volume, privateCellVector p q hp2 hpfin i x = 0 ∨ privateCellVector p q hp2 hpfin j x = 0) := by
  intro i j hij
  exact (privateCellData p q hp2 hpfin i).supported.ae_disjoint
    (privateCellData p q hp2 hpfin j).supported (privateCellData_disjoint p q hp2 hpfin hij)

def privateCellCoefficients : LebesgueLp p →L[ℂ] lp (fun _ : PrivateCellIndex p q hp2 hpfin => ℂ) p :=
  cellCoefficients (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin
    (fun i => (privateCellData p q hp2 hpfin i).supportSet)
    (fun i => (privateCellData p q hp2 hpfin i).supportSet_measurable)
    (privateCellData_disjoint p q hp2 hpfin)
    (fun i => (privateCellData p q hp2 hpfin i).normingFunctional (q := q)
      (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (privateCellVector_unit p q hp2 hpfin i))
    (fun i => ((privateCellData p q hp2 hpfin i).normingFunctional_norm
      (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (privateCellVector_unit p q hp2 hpfin i)
      (lt_trans (by norm_num) hp2)).le)

theorem privateCellCoefficients_norm_le : ‖privateCellCoefficients p q hp2 hpfin‖ ≤ 1 :=
  cellCoefficients_norm_le ..

theorem privateCellCoefficients_apply (F : LebesgueLp p) (i : PrivateCellIndex p q hp2 hpfin) :
    privateCellCoefficients p q hp2 hpfin F i =
      (privateCellData p q hp2 hpfin i).wholeNormingFunctional (q := q)
        (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (privateCellVector_unit p q hp2 hpfin i) F := rfl

/-- The actual norming functionals of the permanent private cells are
biorthogonal to their unit coordinates. -/
theorem privateCellCoefficients_vector (i j : PrivateCellIndex p q hp2 hpfin) :
    privateCellCoefficients p q hp2 hpfin (privateCellVector p q hp2 hpfin j) i = if i = j then 1 else 0 := by
  classical
  rw [privateCellCoefficients_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact (privateCellData p q hp2 hpfin i).wholeNormingFunctional_self
      (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (privateCellVector_unit p q hp2 hpfin i)
  · rw [if_neg hij]
    exact (privateCellData p q hp2 hpfin i).wholeNormingFunctional_zero
      (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (privateCellVector_unit p q hp2 hpfin i)
      (privateCellVector p q hp2 hpfin j) (privateCellData p q hp2 hpfin j).supported
      (privateCellData_disjoint p q hp2 hpfin (Ne.symm hij))

end SchauderTranslates.LpConstruction
