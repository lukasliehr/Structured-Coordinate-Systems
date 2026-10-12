import Lean_Code.SchauderTranslates.ProductFlat

/-!
# Atoms on the flat torus

Every atom of the ordered list is a mixed character on the line times the flat torus:
old atoms carry torus frequency zero, and every engine atom carries the sum of its tag
(or seed) frequency and its nonzero auxiliary frequency. The flat frequencies of the new
atoms are nonzero and pairwise distinct.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

theorem mFourier_single_one {L : ℕ} (j : Fin L) (z : UnitAddTorus (Fin L)) :
    UnitAddTorus.mFourier (Pi.single j 1) z = fourier (1 : ℤ) (z j) := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_apply, hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

namespace EngineSetup
variable {T : TagSetup} (E : EngineSetup T)

abbrev D : ℕ := fastDim T.Mt T.dt (T.N * E.n) E.L E.de

abbrev flat (x : UnitAddTorus (Fin E.D)) : E.Fast := fastFlat T.Mt T.dt (T.N * E.n) E.L E.de x

/-- The engine and packet index of a new atom. -/
abbrev eng (k : Fin (T.N * E.n * E.q)) : Fin (T.N * E.n) := (finProdFinEquiv.symm k).1
abbrev pk (k : Fin (T.N * E.n * E.q)) : Fin E.q := (finProdFinEquiv.symm k).2

/-- Line frequency of a new atom. -/
def newLam (k : Fin (T.N * E.n * E.q)) : ℝ :=
  match packetIndex (E.pk k) with
  | (_, Sum.inl i) => T.lam (finProdFinEquiv.symm i).1
  | (_, Sum.inr _) => 0

/-- Flat torus frequency of a new atom. -/
def newFreq (k : Fin (T.N * E.n * E.q)) : Fin E.D → ℤ :=
  match packetIndex (E.pk k) with
  | (l, Sum.inl i) =>
      tagFreq (mE := T.N * E.n) (L := E.L) (de := E.de)
        (T.blk (E.rep (E.eng k)) (finProdFinEquiv.symm i).1)
        (T.st.frequencies (finProdFinEquiv.symm i).2) +
      auxFreq (Mt := T.Mt) (dt := T.dt) (L := E.L) (E.eng k) ((E.a (E.eng k)).scalar.frequencies l)
  | (l, Sum.inr j) =>
      seedFreq (Mt := T.Mt) (dt := T.dt) (de := E.de) (E.eng k) (Pi.single j 1) +
      auxFreq (Mt := T.Mt) (dt := T.dt) (L := E.L) (E.eng k) ((E.a (E.eng k)).scalar.frequencies l)

/-- All line frequencies. -/
def Λ : Fin (T.d + T.N * E.n * E.q) → ℝ := Fin.append T.μ E.newLam

/-- All flat torus frequencies. -/
def κ : Fin (T.d + T.N * E.n * E.q) → (Fin E.D → ℤ) := Fin.append 0 E.newFreq

/-- Bounded representatives of all atoms. -/
def atomFn : Fin (T.d + T.N * E.n * E.q) →
    BoundedMeasurableComplex (T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de)) :=
  Fin.append
    (fun i => ((lineCharacter (T.μ i)).pullbackFst (Fin T.Mt → UnitAddTorus (Fin T.dt))).pullbackFst
      (Fin (T.N * E.n) → EngineFresh E.L E.de))
    (fun k => FiberKernel.liftAt (E.eng k) (packetAtom E.a E.φ (E.eng k) (E.pk k)))

/-- The bounded representative of the target. -/
def tgtFn : BoundedMeasurableComplex (T.Slow × (Fin (T.N * E.n) → EngineFresh E.L E.de)) :=
  ((lineCharacter T.ξ).pullbackFst (Fin T.Mt → UnitAddTorus (Fin T.dt))).pullbackFst
    (Fin (T.N * E.n) → EngineFresh E.L E.de)

variable {E}

theorem atomFn_toL2 (a : Fin (T.d + T.N * E.n * E.q)) : (E.atomFn a).toL2 E.P = E.u a := by
  refine Fin.addCases (fun i => ?_) (fun k => ?_) a
  · simp only [atomFn, Fin.append_left, u, engineConcat]
    rfl
  · simp only [atomFn, Fin.append_right, u, engineConcat]
    rw [Tp, Rp, ← atom_eq]
    rfl

theorem tgtFn_toL2 : E.tgtFn.toL2 E.P = E.tgt := rfl

theorem tgt_norm : ‖E.tgt‖ = 1 := by
  have h := lineVec_inner (E := E) (lineCharacter T.ξ) (lineCharacter T.ξ)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, lineCharacter_norm] at h
  have h1 : ((‖E.tgt‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [tgt]
    push_cast
    simpa using h
  have h2 : ‖E.tgt‖ ^ 2 = 1 := Complex.ofReal_injective h1
  have h0 := norm_nonneg E.tgt
  nlinarith [sq_nonneg (‖E.tgt‖ - 1)]

theorem packetAtom_carrier (k : Fin (T.N * E.n * E.q)) {l : Fin E.ne} {i : Fin ((T.d + 1) * T.nt)}
    (hp : packetIndex (E.pk k) = (l, Sum.inl i))
    (p : T.Slow × EngineFresh E.L E.de) :
    packetAtom E.a E.φ (E.eng k) (E.pk k) p =
      E.φ (E.eng k) i p.1 * UnitAddTorus.mFourier ((E.a (E.eng k)).scalar.frequencies l) p.2.2 := by
  unfold packetAtom
  rw [hp]
  rfl

theorem packetAtom_seed (k : Fin (T.N * E.n * E.q)) {l : Fin E.ne} {j : Fin E.L}
    (hp : packetIndex (E.pk k) = (l, Sum.inr j))
    (p : T.Slow × EngineFresh E.L E.de) :
    packetAtom E.a E.φ (E.eng k) (E.pk k) p =
      fourier (1 : ℤ) (p.2.1 j) *
        UnitAddTorus.mFourier ((E.a (E.eng k)).scalar.frequencies l) p.2.2 := by
  unfold packetAtom
  rw [hp]
  rfl

theorem φ_apply (c : Fin (T.N * E.n)) (i : Fin ((T.d + 1) * T.nt)) (s : T.Slow) :
    E.φ c i s = character (T.lam (finProdFinEquiv.symm i).1) s.1 *
      UnitAddTorus.mFourier (T.st.frequencies (finProdFinEquiv.symm i).2)
        (s.2 (T.blk (E.rep c) (finProdFinEquiv.symm i).1)) := rfl

/-- Every atom is a mixed character on the flat torus. -/
theorem atomFn_flat (a : Fin (T.d + T.N * E.n * E.q)) (t : ℝ) (x : UnitAddTorus (Fin E.D)) :
    E.atomFn a (E.pt t (E.flat x)) = mixedCharacter (E.Λ a) (E.κ a) t x := by
  refine Fin.addCases (fun i => ?_) (fun k => ?_) a
  · simp only [atomFn, Λ, κ, Fin.append_left]
    simp [mixedCharacter, UnitAddTorus.mFourier_zero]
    rfl
  · simp only [atomFn, Λ, κ, Fin.append_right]
    change packetAtom E.a E.φ (E.eng k) (E.pk k) ((t, (E.flat x).1), (E.flat x).2 (E.eng k)) = _
    unfold newLam newFreq
    rcases hp : packetIndex (E.pk k) with ⟨l, i | j⟩
    · rw [packetAtom_carrier k hp, φ_apply]
      simp only
      rw [mFourier_tag, mFourier_aux, mixedCharacter, UnitAddTorus.mFourier_add]
      ring
    · rw [packetAtom_seed k hp]
      simp only
      rw [← mFourier_single_one, mFourier_seed, mFourier_aux, mixedCharacter,
        UnitAddTorus.mFourier_add]
      simp [character]

theorem tgtFn_flat (t : ℝ) (x : UnitAddTorus (Fin E.D)) :
    E.tgtFn (E.pt t (E.flat x)) = character T.ξ t := rfl

/-! ### Frequencies of the new atoms -/

theorem flatAuxPart_newFreq (k : Fin (T.N * E.n * E.q)) (c : Fin (T.N * E.n)) :
    flatAuxPart (E.newFreq k) c =
      if c = E.eng k then (E.a (E.eng k)).scalar.frequencies (packetIndex (E.pk k)).1 else 0 := by
  unfold newFreq
  rcases hp : packetIndex (E.pk k) with ⟨l, i | j⟩
  · simp only [hp, flatAuxPart_add, flatAuxPart_tagFreq, flatAuxPart_auxFreq, zero_add]
  · simp only [hp, flatAuxPart_add, flatAuxPart_seedFreq, flatAuxPart_auxFreq, zero_add]

theorem newFreq_ne_zero (k : Fin (T.N * E.n * E.q)) : E.newFreq k ≠ 0 := by
  intro h
  have h1 := ((flat_eq_zero_iff _).mp h).2.2 (E.eng k)
  rw [flatAuxPart_newFreq, if_pos rfl] at h1
  exact (E.a (E.eng k)).scalar.nonconstant _ h1

theorem flatTagPart_newFreq (k : Fin (T.N * E.n * E.q)) (b : Fin T.Mt) :
    flatTagPart (E.newFreq k) b =
      match packetIndex (E.pk k) with
      | (_, Sum.inl i) => if b = T.blk (E.rep (E.eng k)) (finProdFinEquiv.symm i).1 then
          T.st.frequencies (finProdFinEquiv.symm i).2 else 0
      | (_, Sum.inr _) => 0 := by
  unfold newFreq
  rcases hp : packetIndex (E.pk k) with ⟨l, i | j⟩
  · simp only [hp, flatTagPart_add, flatTagPart_tagFreq, flatTagPart_auxFreq, add_zero]
  · simp only [hp, flatTagPart_add, flatTagPart_seedFreq, flatTagPart_auxFreq, add_zero]

theorem flatSeedPart_newFreq (k : Fin (T.N * E.n * E.q)) (c : Fin (T.N * E.n)) :
    flatSeedPart (E.newFreq k) c =
      match packetIndex (E.pk k) with
      | (_, Sum.inl _) => 0
      | (_, Sum.inr j) => if c = E.eng k then Pi.single j 1 else 0 := by
  unfold newFreq
  rcases hp : packetIndex (E.pk k) with ⟨l, i | j⟩
  · simp only [hp, flatSeedPart_add, flatSeedPart_tagFreq, flatSeedPart_auxFreq, add_zero]
  · simp only [hp, flatSeedPart_add, flatSeedPart_seedFreq, flatSeedPart_auxFreq, add_zero]

/-- The flat frequencies of the new atoms are pairwise distinct. -/
theorem newFreq_injective : Function.Injective E.newFreq := by
  intro k k' h
  -- the auxiliary part identifies the engine and the auxiliary column
  have haux := congrArg (fun κ => flatAuxPart κ (E.eng k)) h
  simp only [flatAuxPart_newFreq, ite_true] at haux
  have hc : E.eng k = E.eng k' := by
    by_contra hne
    rw [if_neg hne] at haux
    exact (E.a (E.eng k)).scalar.nonconstant _ haux
  rw [if_pos hc] at haux
  have hcl : (E.a (E.eng k)).scalar = (E.a (E.eng k')).scalar := by rw [hc]
  have hl : (packetIndex (E.pk k)).1 = (packetIndex (E.pk k')).1 := by
    have h2 : (E.a (E.eng k')).scalar.frequencies (packetIndex (E.pk k)).1 =
        (E.a (E.eng k')).scalar.frequencies (packetIndex (E.pk k')).1 := by
      rw [← haux, hc]
    exact (E.a (E.eng k')).scalar.injective h2
  -- the row: carrier rows by their tag part, seed rows by their seed part
  have hrow : (packetIndex (E.pk k)).2 = (packetIndex (E.pk k')).2 := by
    rcases hp : packetIndex (E.pk k) with ⟨l1, i1 | j1⟩ <;>
      rcases hp' : packetIndex (E.pk k') with ⟨l2, i2 | j2⟩
    · -- two carrier rows
      have htag := congrArg (fun κ => flatTagPart κ
        (T.blk (E.rep (E.eng k)) (finProdFinEquiv.symm i1).1)) h
      simp only [flatTagPart_newFreq, hp, hp', ite_true] at htag
      have hb : T.blk (E.rep (E.eng k)) (finProdFinEquiv.symm i1).1 =
          T.blk (E.rep (E.eng k')) (finProdFinEquiv.symm i2).1 := by
        by_contra hne
        rw [if_neg hne] at htag
        exact T.st.nonconstant _ htag
      rw [if_pos hb] at htag
      have hj := TagSetup.blk_injective (E.rep (E.eng k)) (hb.trans (by rw [hc]))
      have hk := T.st.injective htag
      have : finProdFinEquiv.symm i1 = finProdFinEquiv.symm i2 := Prod.ext hj hk
      simp only [Sum.inl.injEq]
      exact finProdFinEquiv.symm.injective this
    · -- carrier versus seed
      exfalso
      have htag := congrArg (fun κ => flatTagPart κ
        (T.blk (E.rep (E.eng k)) (finProdFinEquiv.symm i1).1)) h
      simp only [flatTagPart_newFreq, hp, hp', ite_true] at htag
      exact T.st.nonconstant _ htag
    · -- seed versus carrier
      exfalso
      have htag := congrArg (fun κ => flatTagPart κ
        (T.blk (E.rep (E.eng k')) (finProdFinEquiv.symm i2).1)) h
      simp only [flatTagPart_newFreq, hp, hp', ite_true] at htag
      exact T.st.nonconstant _ htag.symm
    · -- two seed rows
      have hseed := congrArg (fun κ => flatSeedPart κ (E.eng k)) h
      simp only [flatSeedPart_newFreq, hp, hp', ite_true, if_pos hc] at hseed
      have hj : j1 = j2 := by
        by_contra hne
        have := congrFun hseed j1
        simp [Pi.single_apply, hne] at this
      rw [hj]
  have hpk : E.pk k = E.pk k' := by
    apply (packetEquiv E.ne ((T.d + 1) * T.nt) E.L).symm.injective
    exact Prod.ext hl hrow
  have hkk : finProdFinEquiv.symm k = finProdFinEquiv.symm k' := Prod.ext hc hpk
  exact finProdFinEquiv.symm.injective hkk

end EngineSetup
end SchauderTranslates
