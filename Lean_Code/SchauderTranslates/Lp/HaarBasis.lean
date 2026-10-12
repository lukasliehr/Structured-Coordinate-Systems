import Lean_Code.SchauderTranslates.Lp.HaarIntervalMeanZero
import Lean_Code.SchauderTranslates.Lp.UnconditionalSystem

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- The conclusion retains actual Haar atoms and continuous coordinates,
unique ordered expansions, arbitrary finite-subset convergence, the exact
constant, and rescaling to every interval of positive length. -/
def HaarBasisConclusion : Prop :=
  1 ≤ haarStrongConstant q.toReal ∧
  NormalizedUnconditionalSystem (haarNormalizedAtom p) (haarNormalizedCoordinate p q)
    (haarStrongConstant q.toReal) ∧
  NormalizedUnconditionalSystem (haarMeanZeroAtom p q) (haarMeanZeroCoordinate p q)
    (haarStrongConstant q.toReal) ∧
  ∀ (a l : ℝ) (hl : 0 < l),
    NormalizedUnconditionalSystem
      (fun i => haarIntervalEquiv p a l hl (haarNormalizedAtom p i))
      (fun i => (haarNormalizedCoordinate p q i).comp
        (haarIntervalEquiv p a l hl).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      (haarStrongConstant q.toReal) ∧
    NormalizedUnconditionalSystem
      (fun i => haarIntervalMeanZeroEquiv p q a l hl (haarMeanZeroAtom p q i))
      (fun i => (haarMeanZeroCoordinate p q i).comp
        (haarIntervalMeanZeroEquiv p q a l hl).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      (haarStrongConstant q.toReal) ∧
    (∀ g : HaarIntervalLp p a l, g ∈ haarIntervalMeanZero p q a l hl ↔
      (∫ x, g x ∂haarIntervalMeasure a l) = 0)

theorem haar_basis_conclusion (hp2 : 2 < p) (hpfin : p ≠ ∞) : HaarBasisConclusion p q := by
  have hfull : NormalizedUnconditionalSystem (haarNormalizedAtom p)
      (haarNormalizedCoordinate p q) (haarStrongConstant q.toReal) :=
    ⟨⟨haarOrdering⟩, haar_full_basis p q hp2 hpfin⟩
  have hzero : NormalizedUnconditionalSystem (haarMeanZeroAtom p q)
      (haarMeanZeroCoordinate p q) (haarStrongConstant q.toReal) :=
    ⟨⟨haarMeanZeroOrdering⟩, haar_meanZero_basis p q hp2 hpfin⟩
  refine ⟨haarStrongConstant_ge_one (q := q) hp2 hpfin, hfull, hzero, ?_⟩
  intro a l hl
  exact ⟨normalized_unconditional_system_transport (haarIntervalEquiv p a l hl) _ _ hfull,
    normalized_unconditional_system_transport (haarIntervalMeanZeroEquiv p q a l hl) _ _ hzero,
    haarIntervalMeanZero_mem_iff p q a l hl⟩

/-- Blueprint `lp:haar-basis`: normalized full and mean-zero Haar bases,
with the same bound on every bounded interval of positive length. The
Hölder conjugate is canonical and imposes no additional hypothesis. -/
theorem haar_basis (p : ℝ≥0∞) (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    letI : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
    letI : Fact (1 ≤ ENNReal.conjExponent p) :=
      ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
    HaarBasisConclusion p (ENNReal.conjExponent p) := by
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  exact haar_basis_conclusion p (ENNReal.conjExponent p) hp2 hpfin

end SchauderTranslates.LpConstruction
