import Lean_Code.SchauderTranslates.Lp.CompactCellRoots
import Lean_Code.SchauderTranslates.Lp.FiniteIntervalAllocation

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- A permanent cell records its actual geometry and, for a private cell,
its actual norm-one compact step coordinate. Roots are constructed from
these data; no basis-existence hypothesis is added to the stage input. -/
inductive PermanentCell (p : ℝ≥0∞) where
  | ordinary (ab : ℝ × ℝ) (length_pos : ab.1 < ab.2)
  | privateCell (e : LebesgueLp p) (D : DisjointStepData p e) (unit : ‖e‖ = 1)

def PermanentCell.intervals {p : ℝ≥0∞} : PermanentCell p → Finset (ℝ × ℝ)
  | .ordinary ab _ => {ab}
  | .privateCell _ D _ => D.cells

def PermanentCell.support {p : ℝ≥0∞} : PermanentCell p → Set ℝ
  | .ordinary ab _ => Set.Ico ab.1 ab.2
  | .privateCell _ D _ => D.supportSet

theorem PermanentCell.support_eq_intervalUnion {p : ℝ≥0∞} (c : PermanentCell p) :
    c.support = finiteIntervalUnion c.intervals := by
  cases c with
  | ordinary ab _ => simp [support, intervals, finiteIntervalUnion]
  | privateCell e D he => rfl

theorem PermanentCell.support_measurable {p : ℝ≥0∞} (c : PermanentCell p) : MeasurableSet c.support := by
  cases c with
  | ordinary ab _ => exact measurableSet_Ico
  | privateCell e D he => exact D.supportSet_measurable

theorem PermanentCell.intervals_positive {p : ℝ≥0∞} (c : PermanentCell p)
    {ab : ℝ × ℝ} (hab : ab ∈ c.intervals) : ab.1 < ab.2 := by
  cases c with
  | ordinary cd hcd => simpa only [Finset.mem_singleton.mp hab] using hcd
  | privateCell e D he => exact D.length_pos ab hab

theorem PermanentCell.intervals_disjoint {p : ℝ≥0∞} (c : PermanentCell p)
    {ab cd : ℝ × ℝ} (hab : ab ∈ c.intervals) (hcd : cd ∈ c.intervals) (hne : ab ≠ cd) :
    Disjoint (Set.Ico ab.1 ab.2) (Set.Ico cd.1 cd.2) := by
  cases c with
  | ordinary ef hef =>
      exact False.elim (hne ((Finset.mem_singleton.mp hab).trans (Finset.mem_singleton.mp hcd).symm))
  | privateCell e D he => exact D.disjoint ab hab cd hcd hne

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable (hp2 : 2 < p) (hpfin : p ≠ ∞)

def PermanentCell.roots (c : PermanentCell p) :
    CompactCellRoots p c.support (haarStrongConstant q.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  cases c with
  | ordinary ab hab => exact (Classical.choice (ordinary_interval_roots_full p q hp2 hpfin ab hab)).val
  | privateCell e D he => exact D.privateCellRoots (q := q) hp0 hpfin he hp2

theorem PermanentCell.roots_space_ordinary (ab : ℝ × ℝ) (hab : ab.1 < ab.2) :
    ((PermanentCell.ordinary ab hab).roots p q hp2 hpfin).space =
      supportedLpSubmodule p volume (Set.Ico ab.1 ab.2) :=
  (Classical.choice (ordinary_interval_roots_full p q hp2 hpfin ab hab)).property

theorem PermanentCell.roots_normalized (c : PermanentCell p) (n : ℕ) :
    ‖(c.roots p q hp2 hpfin).root n‖ = 1 := (c.roots p q hp2 hpfin).normalized n

theorem PermanentCell.roots_isCompactStep (c : PermanentCell p) (n : ℕ) :
    IsCompactStep p ((c.roots p q hp2 hpfin).root n).val :=
  (c.roots p q hp2 hpfin).compactStep n

theorem PermanentCell.roots_supported (c : PermanentCell p) (n : ℕ) :
    SupportedOn ((c.roots p q hp2 hpfin).root n).val c.support :=
  (c.roots p q hp2 hpfin).supported _

end SchauderTranslates.LpConstruction
