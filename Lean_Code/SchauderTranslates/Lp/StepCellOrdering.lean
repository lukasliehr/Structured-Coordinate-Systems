import Lean_Code.SchauderTranslates.Lp.StepCellWeight

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem DisjointStepData.left_injective {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Set.InjOn Prod.fst (D.cells : Set (ℝ × ℝ)) := by
  intro ab hab cd hcd hleft
  by_contra hne
  have hxcd : ab.1 ∈ Set.Ico cd.1 cd.2 := by
    rw [hleft]
    exact ⟨le_rfl, D.length_pos cd hcd⟩
  exact Set.disjoint_left.mp (D.disjoint ab hab cd hcd hne)
    ⟨le_rfl, D.length_pos ab hab⟩ hxcd

def DisjointStepData.leftEndpoints {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    Finset ℝ := D.cells.image Prod.fst

theorem DisjointStepData.leftEndpoints_card {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : D.leftEndpoints.card = D.cells.card :=
  Finset.card_image_of_injOn D.left_injective

def DisjointStepData.toLeftEndpoint {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    D.cells → D.leftEndpoints := fun ab => ⟨ab.1.1, Finset.mem_image.mpr ⟨ab.1, ab.2, rfl⟩⟩

theorem DisjointStepData.toLeftEndpoint_bijective {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Function.Bijective D.toLeftEndpoint := by
  constructor
  · intro ab cd h
    apply Subtype.ext
    exact D.left_injective ab.2 cd.2 (congrArg Subtype.val h)
  · intro a
    obtain ⟨ab, hab, ha⟩ := Finset.mem_image.mp a.2
    exact ⟨⟨ab, hab⟩, Subtype.ext ha⟩

def DisjointStepData.leftEndpointEquiv {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    D.cells ≃ D.leftEndpoints := Equiv.ofBijective D.toLeftEndpoint D.toLeftEndpoint_bijective

/-- The cells are enumerated in increasing spatial order. This order is
derived from disjointness and positive length, so it adds no input hypothesis. -/
def DisjointStepData.cellOrdering {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    Fin D.cells.card ≃ D.cells :=
  (D.leftEndpoints.orderIsoOfFin D.leftEndpoints_card).toEquiv.trans D.leftEndpointEquiv.symm

theorem DisjointStepData.cellOrdering_left {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (i : Fin D.cells.card) :
    (D.cellOrdering i).1.1 = (D.leftEndpoints.orderIsoOfFin D.leftEndpoints_card i).1 := by
  have h := D.leftEndpointEquiv.apply_symm_apply (D.leftEndpoints.orderIsoOfFin D.leftEndpoints_card i)
  exact congrArg Subtype.val h

theorem DisjointStepData.cellOrdering_strictMono {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : StrictMono (fun i => (D.cellOrdering i).1.1) := by
  intro i j hij
  change (D.cellOrdering i).1.1 < (D.cellOrdering j).1.1
  rw [D.cellOrdering_left, D.cellOrdering_left]
  exact (D.leftEndpoints.orderIsoOfFin D.leftEndpoints_card).strictMono hij

end SchauderTranslates.LpConstruction
