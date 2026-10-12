import Lean_Code.SchauderTranslates.Lp.PhysicalPacketAllocation

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- A reference atom stores its generator at birth, permanently. -/
structure BirthAtom (p : ℝ≥0∞) where
  time : ℕ
  parameter : ℝ
  generator : LebesgueLp p

def BirthAtom.vector {p : ℝ≥0∞} (b : BirthAtom p) : LebesgueLp p :=
  translate p b.parameter b.generator

/-- The immutable layer data needed both by branch recovery and by the
later comparison of birth atoms with translates of the limiting generator. -/
structure PhysicalBirthLayer (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  time : ℕ
  size : ℕ
  size_pos : 1 ≤ size
  privateVector : Fin size → LebesgueLp p
  privateStep : ∀ i, IsCompactStep p (privateVector i)
  privateUnit : ∀ i, ‖privateVector i‖ = 1
  privateData : ∀ i, DisjointStepData p (privateVector i)
  privateDisjoint : ∀ i j, i ≠ j →
    ∀ᵐ x ∂volume, privateVector i x = 0 ∨ privateVector j x = 0
  input : LebesgueLp p
  input_unit : ‖input‖ = 1
  input_step : IsCompactStep p input
  inputDisjoint : ∀ i, ∀ᵐ x ∂volume, input x = 0 ∨ privateVector i x = 0
  parameter : Fin size → ℝ
  parameter_injective : Function.Injective parameter
  scale : ℝ
  scale_pos : 0 < scale
  generator : LebesgueLp p
  generator_step : IsCompactStep p generator
  birthIdentity : ∀ i, translate p (parameter i) generator =
    scale • (privateVector i + layerDualScale p.toReal size • input)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def PhysicalBirthLayer.ofPacket {R : ℝ} {v h : LebesgueLp p} {old : Finset ℝ} {ε : ℝ}
    (P : PhysicalPacket p R v h old ε) (t : ℕ) (hh : ‖h‖ = 1) (hstep : IsCompactStep p h) :
    PhysicalBirthLayer p where
  time := t
  size := P.size
  size_pos := P.size_pos
  privateVector := P.privateVector
  privateStep := P.privateStep
  privateUnit := P.privateUnit
  privateData := P.privateData
  privateDisjoint := P.privateDisjoint
  input := h
  input_unit := hh
  input_step := hstep
  inputDisjoint := P.residualDisjoint
  parameter := P.parameter
  parameter_injective := P.parameter_injective
  scale := P.scale
  scale_pos := P.scale_pos
  generator := P.generator
  generator_step := P.generator_step
  birthIdentity := P.birthIdentity

def PhysicalBirthLayer.mean (L : PhysicalBirthLayer p) : LebesgueLp p :=
  physicalLayerMean p L.privateVector

def PhysicalBirthLayer.nextResidual (L : PhysicalBirthLayer p) : LebesgueLp p :=
  physicalNextResidual p L.input L.mean

def PhysicalBirthLayer.cell (L : PhysicalBirthLayer p) (i : Fin L.size) : PermanentCell p :=
  .privateCell (L.privateVector i) (L.privateData i) (L.privateUnit i)

def PhysicalBirthLayer.birth (L : PhysicalBirthLayer p) (i : Fin L.size) : BirthAtom p :=
  ⟨L.time, L.parameter i, L.generator⟩

def PhysicalBirthLayer.births (L : PhysicalBirthLayer p) : List (BirthAtom p) := List.ofFn L.birth

theorem PhysicalBirthLayer.birth_vector (L : PhysicalBirthLayer p) (i : Fin L.size) :
    (L.birth i).vector = L.scale • (L.privateVector i + layerDualScale p.toReal L.size • L.input) :=
  L.birthIdentity i

theorem PhysicalBirthLayer.births_length (L : PhysicalBirthLayer p) : L.births.length = L.size :=
  List.length_ofFn

theorem PhysicalBirthLayer.mean_step (L : PhysicalBirthLayer p) : IsCompactStep p L.mean :=
  physicalLayerMean_isCompactStep L.privateVector L.privateStep

theorem PhysicalBirthLayer.nextResidual_unit (L : PhysicalBirthLayer p)
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) : ‖L.nextResidual‖ = 1 := by
  apply physical_next_residual_unit hp0 hpfin _ _ L.input_unit
    (physical_layer_mean_unit hp0 hpfin L.size_pos L.privateVector L.privateUnit L.privateDisjoint)
  exact ae_disjoint_real_smul_right _ _ _
    (ae_disjoint_finset_sum Finset.univ L.input L.privateVector (fun i _ => L.inputDisjoint i))

def physicalHistoryResidual (root : LebesgueLp p) (ls : List (PhysicalBirthLayer p)) : LebesgueLp p :=
  ls.foldl (fun h L => physicalNextResidual p h L.mean) root

theorem physicalHistoryResidual_append (root : LebesgueLp p) (ls : List (PhysicalBirthLayer p))
    (L : PhysicalBirthLayer p) :
    physicalHistoryResidual root (ls ++ [L]) = physicalNextResidual p (physicalHistoryResidual root ls) L.mean := by
  simp [physicalHistoryResidual, List.foldl_append]

/-- Branch histories retain the exact recursion and all disjointness
needed for their physical ℓᵖ identification. -/
inductive ValidPhysicalHistory (root : LebesgueLp p) : List (PhysicalBirthLayer p) → Prop where
  | nil : ValidPhysicalHistory root []
  | snoc {ls : List (PhysicalBirthLayer p)} (past : ValidPhysicalHistory root ls)
      (L : PhysicalBirthLayer p) (input_eq : L.input = physicalHistoryResidual root ls)
      (root_disjoint : ∀ i, ∀ᵐ x ∂volume, root x = 0 ∨ L.privateVector i x = 0)
      (past_disjoint : ∀ K ∈ ls, ∀ i j, ∀ᵐ x ∂volume, K.privateVector i x = 0 ∨ L.privateVector j x = 0) :
      ValidPhysicalHistory root (ls ++ [L])

theorem physicalHistoryResidual_unit (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    {root : LebesgueLp p} (hroot : ‖root‖ = 1) {ls : List (PhysicalBirthLayer p)}
    (hv : ValidPhysicalHistory root ls) : ‖physicalHistoryResidual root ls‖ = 1 := by
  induction hv with
  | nil => simpa [physicalHistoryResidual] using hroot
  | snoc past L hin _ _ _ =>
      rw [physicalHistoryResidual_append, ← hin]
      exact L.nextResidual_unit hp0 hpfin

theorem physicalHistoryResidual_step {root : LebesgueLp p} (hroot : IsCompactStep p root)
    (ls : List (PhysicalBirthLayer p)) : IsCompactStep p (physicalHistoryResidual root ls) := by
  induction ls generalizing root with
  | nil => exact hroot
  | cons L ls ih => exact ih (physicalNextResidual_isCompactStep hroot L.mean_step)

theorem physicalHistoryResidual_supported {root : LebesgueLp p} {A : Set ℝ}
    (hroot : SupportedOn root A) (ls : List (PhysicalBirthLayer p))
    (hls : ∀ L ∈ ls, ∀ i, SupportedOn (L.privateVector i) A) :
    SupportedOn (physicalHistoryResidual root ls) A := by
  induction ls generalizing root with
  | nil => exact hroot
  | cons L ls ih =>
      have hmean : SupportedOn L.mean A :=
        (SupportedOn.finset_sum Finset.univ L.privateVector
          (fun i _ => hls L (List.mem_cons_self ..) i)).real_smul _
      have hnext : SupportedOn (physicalNextResidual p root L.mean) A := by
        apply SupportedOn.real_smul
        simpa [sub_eq_add_neg] using hroot.add (hmean.real_smul (-1))
      exact ih hnext (fun K hK => hls K (List.mem_cons_of_mem _ hK))

structure PhysicalBranch (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  origin : ℕ × ℕ
  root : LebesgueLp p
  root_unit : ‖root‖ = 1
  root_step : IsCompactStep p root
  layers : List (PhysicalBirthLayer p)
  history : ValidPhysicalHistory root layers

def PhysicalBranch.residual (B : PhysicalBranch p) : LebesgueLp p :=
  physicalHistoryResidual B.root B.layers

def PhysicalBranch.start (origin : ℕ × ℕ) (root : LebesgueLp p) (hunit : ‖root‖ = 1)
    (hstep : IsCompactStep p root) : PhysicalBranch p :=
  ⟨origin, root, hunit, hstep, [], .nil⟩

theorem PhysicalBranch.residual_unit (B : PhysicalBranch p) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ‖B.residual‖ = 1 := physicalHistoryResidual_unit hp0 hpfin B.root_unit B.history

theorem PhysicalBranch.residual_step (B : PhysicalBranch p) : IsCompactStep p B.residual :=
  physicalHistoryResidual_step B.root_step B.layers

def PhysicalBranch.Supported (B : PhysicalBranch p) (R : ℝ) : Prop :=
  SupportedOn B.root (Set.Icc (-R) R) ∧
    ∀ L ∈ B.layers, ∀ i, SupportedOn (L.privateVector i) (Set.Icc (-R) R)

theorem PhysicalBranch.residual_supported (B : PhysicalBranch p) {R : ℝ} (hB : B.Supported R) :
    SupportedOn B.residual (Set.Icc (-R) R) := physicalHistoryResidual_supported hB.1 B.layers hB.2

def PhysicalBranch.extend (B : PhysicalBranch p) {R : ℝ} {v : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v B.residual old ε)
    (t : ℕ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hB : B.Supported R) : PhysicalBranch p where
  origin := B.origin
  root := B.root
  root_unit := B.root_unit
  root_step := B.root_step
  layers := B.layers ++ [PhysicalBirthLayer.ofPacket P t (B.residual_unit hp0 hpfin) B.residual_step]
  history := ValidPhysicalHistory.snoc B.history _ rfl
    (fun i => hB.1.ae_disjoint (P.privateOutside i) disjoint_compl_right)
    (fun K hK i j => (hB.2 K hK i).ae_disjoint (P.privateOutside j) disjoint_compl_right)

theorem PhysicalBranch.extend_residual (B : PhysicalBranch p) {R : ℝ} {v : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v B.residual old ε)
    (t : ℕ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hB : B.Supported R) :
    (B.extend P t hp0 hpfin hB).residual = P.nextResidual := by
  change physicalHistoryResidual B.root (B.layers ++ [_]) = _
  rw [physicalHistoryResidual_append]
  rfl

end SchauderTranslates.LpConstruction
