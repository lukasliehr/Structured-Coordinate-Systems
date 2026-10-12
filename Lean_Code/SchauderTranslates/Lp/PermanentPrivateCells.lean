import Lean_Code.SchauderTranslates.Lp.WholeCellFunctional

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞}

def PermanentCell.IsPrivate : PermanentCell p → Prop
  | .ordinary _ _ => False
  | .privateCell _ _ _ => True

def PermanentCell.privateVector : PermanentCell p → LebesgueLp p
  | .ordinary _ _ => 0
  | .privateCell e _ _ => e

def PermanentCell.privateData (c : PermanentCell p) (hc : c.IsPrivate) :
    DisjointStepData p c.privateVector := by
  cases c with
  | ordinary ab hab => exact False.elim hc
  | privateCell e D he => exact D

theorem PermanentCell.privateVector_unit (c : PermanentCell p) (hc : c.IsPrivate) :
    ‖c.privateVector‖ = 1 := by
  cases c with
  | ordinary ab hab => exact False.elim hc
  | privateCell e D he => exact he

theorem PermanentCell.privateData_support (c : PermanentCell p) (hc : c.IsPrivate) :
    (c.privateData hc).supportSet = c.support := by
  cases c with
  | ordinary ab hab => exact False.elim hc
  | privateCell e D he => rfl

theorem PermanentCell.privateVector_supported (c : PermanentCell p) (hc : c.IsPrivate) :
    SupportedOn c.privateVector c.support := by
  have h := (c.privateData hc).supported
  rwa [c.privateData_support hc] at h

end SchauderTranslates.LpConstruction
