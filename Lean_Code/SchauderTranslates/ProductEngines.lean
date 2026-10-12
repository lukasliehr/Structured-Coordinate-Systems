import Lean_Code.SchauderTranslates.CombinedEngines
import Lean_Code.SchauderTranslates.SelectiveSupply

/-!
# Selective engines in the combined product space (blueprint `tag:engines`)

Finitely many selective engines over one slow law are combined by the product fiber
kernel. In the actual combined weighted L² space each engine contributes its ordered
packet; its slow part is the lifted marginal mean and its centered part has the engine's
own centered Gram. The selective information formula then yields the two properties used
by the replica argument: a mean-pairing bound `c ‖v‖² + j |⟪e, v⟫|²` and explicit
coefficients realizing `j • e` at centered cost `j`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ProductEngines

variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
variable {L de ne r mE : ℕ}
variable (a : Fin mE → SelectiveKernelData S L de ne)
variable (φ : Fin mE → Fin r → BoundedMeasurableComplex S)

/-- The fresh variables of one engine. -/
abbrev EngineFresh (L de : ℕ) := UnitAddTorus (Fin L) × UnitAddTorus (Fin de)

/-- The kernels of all engines. -/
abbrev kernels : Fin mE → FiberKernel S (EngineFresh L de) ((torusMeasure L).prod (torusMeasure de)) :=
  fun c => (a c).kernel

/-- The combined weighted law. -/
abbrev law : Measure (S × (Fin mE → EngineFresh L de)) :=
  (FiberKernel.piKernel (kernels a)).measure ρ

/-- The packet order of the selective prefix estimate. -/
abbrev packetIndex (p : Fin (ne * (r + L))) : Fin ne × (Fin r ⊕ Fin L) :=
  (packetEquiv ne r L).symm p

/-- The ordered packet of engine `c`. -/
def packetAtom (c : Fin mE) (p : Fin (ne * (r + L))) :
    BoundedMeasurableComplex (S × EngineFresh L de) :=
  (a c).packet (φ c) (packetIndex p)

/-- The slow part of a combined atom. -/
def slowPart (c : Fin mE) (p : Fin (ne * (r + L))) : Lp ℂ 2 (law ρ a) :=
  FiberKernel.engineMean (kernels a) ρ c (packetAtom a φ c p)

/-- The centered part of a combined atom. -/
def fastPart (c : Fin mE) (p : Fin (ne * (r + L))) : Lp ℂ 2 (law ρ a) :=
  FiberKernel.engineCentered (kernels a) ρ c (packetAtom a φ c p)

/-- The actual combined atom. -/
def atom (c : Fin mE) (p : Fin (ne * (r + L))) : Lp ℂ 2 (law ρ a) :=
  FiberKernel.engineAtom (kernels a) ρ c (packetAtom a φ c p)

theorem atom_eq (c : Fin mE) (p : Fin (ne * (r + L))) :
    atom ρ a φ c p = slowPart ρ a φ c p + fastPart ρ a φ c p :=
  FiberKernel.engineAtom_eq _ _ _ _

theorem slowPart_mem (c : Fin mE) (p : Fin (ne * (r + L))) :
    slowPart ρ a φ c p ∈ (FiberKernel.piKernel (kernels a)).slowSpace ρ :=
  FiberKernel.engineMean_mem _ _ _ _

theorem fastPart_inner_slow (c : Fin mE) (p : Fin (ne * (r + L)))
    (s : Lp ℂ 2 (law ρ a)) (hs : s ∈ (FiberKernel.piKernel (kernels a)).slowSpace ρ) :
    inner ℂ s (fastPart ρ a φ c p) = 0 :=
  FiberKernel.engineCentered_inner_slow _ _ _ _ s hs

theorem fastPart_inner_ne {c c' : Fin mE} (hcc : c ≠ c') (p p' : Fin (ne * (r + L))) :
    inner ℂ (fastPart ρ a φ c p) (fastPart ρ a φ c' p') = 0 :=
  FiberKernel.engineCentered_inner_ne _ _ hcc _ _

theorem fastPart_inner_same (c : Fin mE) (p p' : Fin (ne * (r + L))) :
    inner ℂ (fastPart ρ a φ c p) (fastPart ρ a φ c p') =
      inner ℂ ((a c).orderedCenteredPacket ρ (φ c) p) ((a c).orderedCenteredPacket ρ (φ c) p') := by
  have h := FiberKernel.engineCentered_inner_same (kernels a) ρ c (packetAtom a φ c) p p'
  exact h

theorem slowPart_eq_slowLift (c : Fin mE) (p : Fin (ne * (r + L))) :
    slowPart ρ a φ c p = (FiberKernel.piKernel (kernels a)).slowLift ρ
      ((a c).kernel.marginalMeans ρ ((a c).packet (φ c)) (packetIndex p)) :=
  FiberKernel.engineMean_eq_slowLift _ _ _ _

/-- Centered prefix bounds of each engine pass to the combined law. -/
theorem fastPart_prefix (c : Fin mE) {Q : ℝ}
    (h : FinitePrefixSqBound ((a c).orderedCenteredPacket ρ (φ c)) Q) :
    FinitePrefixSqBound (fastPart ρ a φ c) Q :=
  finitePrefixSqBound_of_inner_eq _ _ (fastPart_inner_same ρ a φ c) h

/-- The centered parts of one engine are independent. -/
theorem fastPart_independent (c : Fin mE)
    (hφ : LinearIndependent ℂ (fun i => (φ c i).toL2 ρ)) :
    LinearIndependent ℂ (fastPart ρ a φ c) := by
  have hpos := (a c).packet_centered_posDef ρ (φ c) hφ
  have hli : LinearIndependent ℂ ((a c).kernel.centered ρ ((a c).packet (φ c))) :=
    Matrix.posDef_gram_iff_linearIndependent.mp hpos
  have hord : LinearIndependent ℂ ((a c).orderedCenteredPacket ρ (φ c)) :=
    hli.comp _ (packetEquiv ne r L).symm.injective
  have hg : Matrix.gram ℂ (fastPart ρ a φ c) =
      Matrix.gram ℂ ((a c).orderedCenteredPacket ρ (φ c)) := by
    ext p p'
    exact fastPart_inner_same ρ a φ c p p'
  apply Matrix.posDef_gram_iff_linearIndependent.mp
  rw [hg]
  exact Matrix.posDef_gram_iff_linearIndependent.mpr hord

/-- Reindexed synthesis of the slow parts. -/
theorem slowPart_sum (c : Fin mE) (b : Fin (ne * (r + L)) → ℂ) :
    ∑ p, b p • slowPart ρ a φ c p = (FiberKernel.piKernel (kernels a)).slowLift ρ
      (∑ q, b (packetEquiv ne r L q) •
        (a c).kernel.marginalMeans ρ ((a c).packet (φ c)) q) := by
  simp only [slowPart_eq_slowLift, map_sum, map_smul]
  rw [← (packetEquiv ne r L).sum_comp]
  simp

/-- Reindexed synthesis of the centered parts has the engine's own centered norm. -/
theorem fastPart_sum_norm (c : Fin mE) (b : Fin (ne * (r + L)) → ℂ) :
    ‖∑ p, b p • fastPart ρ a φ c p‖ =
      ‖∑ q, b (packetEquiv ne r L q) • (a c).kernel.centered ρ ((a c).packet (φ c)) q‖ := by
  rw [norm_sum_of_inner_eq (fastPart ρ a φ c) ((a c).orderedCenteredPacket ρ (φ c))
    (fastPart_inner_same ρ a φ c) b]
  rw [← (packetEquiv ne r L).sum_comp]
  simp [SelectiveKernelData.orderedCenteredPacket]

/-- The selective information formula, as delivered by `selective_blocks`. -/
def HasSelectiveInformation (c : Fin mE) (cE jE : ℝ) : Prop :=
  informationOperator ((a c).kernel.marginalMeans ρ ((a c).packet (φ c)))
      (Matrix.gram ℂ ((a c).kernel.centered ρ ((a c).packet (φ c)))) =
    (cE : ℂ) • (atomSpan (fun i => (φ c i).toL2 ρ) ⊓ (ℂ ∙ (a c).e.toL2 ρ)ᗮ).starProjection +
      (jE : ℂ) • (ℂ ∙ (a c).e.toL2 ρ).starProjection

/-- The mean-pairing bound of one engine in the combined law. -/
theorem engine_information_bound (c : Fin mE) {cE jE : ℝ} (hc : 0 ≤ cE) (hj : 0 ≤ jE)
    (hφ : LinearIndependent ℂ (fun i => (φ c i).toL2 ρ)) (he1 : ‖(a c).e.toL2 ρ‖ = 1)
    (hinfo : HasSelectiveInformation ρ a φ c cE jE)
    (v : Lp ℂ 2 (law ρ a)) (hv : v ∈ (FiberKernel.piKernel (kernels a)).slowSpace ρ)
    (b : Fin (ne * (r + L)) → ℂ) :
    ‖inner ℂ v (∑ p, b p • slowPart ρ a φ c p)‖ ^ 2 ≤
      (cE * ‖v‖ ^ 2 + jE * ‖inner ℂ ((FiberKernel.piKernel (kernels a)).slowLift ρ
        ((a c).e.toL2 ρ)) v‖ ^ 2) * ‖∑ p, b p • fastPart ρ a φ c p‖ ^ 2 := by
  rw [(FiberKernel.piKernel (kernels a)).slowSpace_eq_range] at hv
  obtain ⟨v', rfl⟩ := hv
  set lift := (FiberKernel.piKernel (kernels a)).slowLift ρ
  rw [slowPart_sum, fastPart_sum_norm]
  change ‖inner ℂ (lift v') (lift _)‖ ^ 2 ≤ (cE * ‖lift v'‖ ^ 2 +
    jE * ‖inner ℂ (lift ((a c).e.toL2 ρ)) (lift v')‖ ^ 2) * _
  rw [LinearIsometry.inner_map_map, LinearIsometry.inner_map_map, LinearIsometry.norm_map]
  have hpos := (a c).packet_centered_posDef ρ (φ c) hφ
  have h1 := mean_pairing_le_information ((a c).kernel.marginalMeans ρ ((a c).packet (φ c)))
    ((a c).kernel.centered ρ ((a c).packet (φ c))) hpos v'
    (fun q => b (packetEquiv ne r L q))
  have h2 := selective_information_quadratic_le
    (atomSpan (fun i => (φ c i).toL2 ρ) ⊓ (ℂ ∙ (a c).e.toL2 ρ)ᗮ) ((a c).e.toL2 ρ) he1 hc hj v'
  rw [← hinfo] at h2
  have hn : 0 ≤ ‖∑ q, b (packetEquiv ne r L q) • (a c).kernel.centered ρ ((a c).packet (φ c)) q‖ ^ 2 :=
    sq_nonneg _
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hn

/-- The distinguished vector is realized exactly by explicit packet coefficients. -/
theorem engine_witness (c : Fin mE) {cE jE : ℝ}
    (hφ : LinearIndependent ℂ (fun i => (φ c i).toL2 ρ)) (he1 : ‖(a c).e.toL2 ρ‖ = 1)
    (hinfo : HasSelectiveInformation ρ a φ c cE jE) :
    ∃ b : Fin (ne * (r + L)) → ℂ,
      ∑ p, b p • slowPart ρ a φ c p =
        (jE : ℂ) • (FiberKernel.piKernel (kernels a)).slowLift ρ ((a c).e.toL2 ρ) ∧
      ‖∑ p, b p • fastPart ρ a φ c p‖ ^ 2 = jE := by
  have hpos := (a c).packet_centered_posDef ρ (φ c) hφ
  have heig : informationOperator ((a c).kernel.marginalMeans ρ ((a c).packet (φ c)))
      (Matrix.gram ℂ ((a c).kernel.centered ρ ((a c).packet (φ c)))) ((a c).e.toL2 ρ) =
      (jE : ℂ) • (a c).e.toL2 ρ := by
    rw [hinfo]
    exact selective_information_eigen _ _ _ _
  obtain ⟨b', hb1, hb2⟩ := information_eigen_witness _ _ hpos _ jE heig he1
  refine ⟨fun p => b' ((packetEquiv ne r L).symm p), ?_, ?_⟩
  · rw [slowPart_sum]
    simp only [Equiv.symm_apply_apply]
    rw [hb1, map_smul]
  · rw [fastPart_sum_norm]
    simp only [Equiv.symm_apply_apply]
    exact hb2

end ProductEngines
end SchauderTranslates
