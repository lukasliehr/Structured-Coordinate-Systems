import Lean_Code.SchauderTranslates.PlaneRowBound
import Lean_Code.SchauderTranslates.OrthogonalEnergy

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Select whole rows from a family of Hilbert-space vectors. -/
def familyCoordinateSelection (e : κ → ι) (f : ι → K) : ι → K :=
  fun i => ∑ k, if i = e k then f (e k) else 0

/-- A full Fourier-space row cut: all selected old rows and a projection in one new row. -/
def familyRowCut (e : κ → ι) (j : ι) (F : K →L[ℝ] K) (f : ι → K) : ι → K :=
  familyCoordinateSelection e f + Pi.single j (F (f j))

theorem coordinateSelection_apply_coordinate (e : κ → ι) (a : EuclideanSpace ℝ ι) (i : ι) :
    coordinateSelection e a i = ∑ k, if i = e k then a (e k) else 0 := by
  simp [coordinateSelection_apply, Pi.single_apply, mul_ite]

theorem familyCoordinateSelection_plane (e : κ → ι) (a b : EuclideanSpace ℝ ι)
    (v w : K) (i : ι) :
    familyCoordinateSelection e (fun i => a i • v + b i • w) i =
      (coordinateSelection e a) i • v + (coordinateSelection e b) i • w := by
  simp only [familyCoordinateSelection, coordinateSelection_apply_coordinate]
  rw [Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- On a reducing plane, a Hilbert row cut is exactly the finite coefficient cut. -/
theorem familyRowCut_plane (e : κ → ι) (j : ι) (F : K →L[ℝ] K)
    (v w : K) (t s : ℝ)
    (hFv : F v = t • v + s • w) (hFw : F w = s • v + (1 - t) • w)
    (a b : EuclideanSpace ℝ ι) :
    familyRowCut e j F (fun i => a i • v + b i • w) =
      (fun i => (coefficientPlaneCut e j t s a b).1 i • v +
        (coefficientPlaneCut e j t s a b).2 i • w) := by
  ext i
  simp only [familyRowCut, Pi.add_apply, familyCoordinateSelection_plane,
    map_add, map_smul, hFv, hFw, coefficientPlaneCut, PiLp.add_apply, PiLp.smul_apply]
  by_cases hij : i = j
  · subst i
    simp only [Pi.single_eq_same, PiLp.single_apply, Pi.single_eq_same, ite_true]
    module
  · simp [hij]

/-- The actual Hilbert row cut satisfies the paper's estimate on every active/inactive plane. -/
theorem familyRowCut_plane_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (e : κ → ι) (he : Function.Injective e) (j : ι) (hj : ∀ i, e i ≠ j)
    (F Q : K →L[ℝ] K) (v w : K) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hQv : Q v = v) (hQw : Q w = 0)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hFv : F v = t • v + Real.sqrt (t * (1 - t)) • w)
    (hFw : F w = Real.sqrt (t * (1 - t)) • v + (1 - t) • w)
    (a b : EuclideanSpace ℝ ι) :
    activationEnergy B Q (familyRowCut e j F (fun i => a i • v + b i • w)) ≤
      metricRowBound B e j * activationEnergy B Q (fun i => a i • v + b i • w) := by
  rw [familyRowCut_plane e j F v w _ _ hFv hFw,
    activationEnergy_plane B Q v w hv hw hQv hQw,
    activationEnergy_plane B Q v w hv hw hQv hQw]
  exact coefficientPlaneCut_energy_bound hB hBI e he j hj ht ht1 a b

end SchauderTranslates
