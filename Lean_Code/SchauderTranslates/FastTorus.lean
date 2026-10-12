import Lean_Code.SchauderTranslates.ProductInterface

/-!
# The fast torus of tags and engines

* Closure of mixed trigonometric polynomials (`IsMixedTrigPoly`) under constants, sums,
  products, conjugation, finite sums and finite products.
* The fast space `FastSpace Mt dt mE L de` of `Mt` tag blocks and `mE` engines (seed and
  auxiliary tori), its product Haar probability `fastHaar`, and the flattening map
  `fastFlat` from one flat torus, which is measure preserving.
* Flat frequencies of tag/seed/auxiliary characters and their components.
* `IsFastPoly`: functions on `ℝ × FastSpace` whose flattening is a mixed trigonometric
  polynomial, with the corresponding closure properties.

Helper lemmas live in the namespace `SchauderTranslates.FastTorus`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace SchauderTranslates
open Construction

namespace FastTorus

/-! ### Character algebra (local copies under distinct names) -/

theorem character_mul_character (a b t : ℝ) :
    character a t * character b t = character (a + b) t := by
  simp only [character, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_character_eq (a t : ℝ) : star (character a t) = character (-a) t := by
  simp only [character, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem character_zero_left (t : ℝ) : character 0 t = 1 := by
  simp [character]

theorem mixedCharacter_mul_mixedCharacter {D : ℕ} (l l' : ℝ) (k k' : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) :
    mixedCharacter l k t y * mixedCharacter l' k' t y =
      mixedCharacter (l + l') (k + k') t y := by
  simp only [mixedCharacter, UnitAddTorus.mFourier_add, ← character_mul_character]
  ring

theorem star_mixedCharacter_eq {D : ℕ} (l : ℝ) (k : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) :
    star (mixedCharacter l k t y) = mixedCharacter (-l) (-k) t y := by
  simp only [mixedCharacter, star_mul', star_character_eq, UnitAddTorus.mFourier_neg,
    Complex.star_def]

theorem mixedCharacter_zero_zero {D : ℕ} (t : ℝ) (y : UnitAddTorus (Fin D)) :
    mixedCharacter 0 (0 : Fin D → ℤ) t y = 1 := by
  simp [mixedCharacter, character_zero_left, UnitAddTorus.mFourier_zero]

theorem mixedCharacter_zero_freq {D : ℕ} (l t : ℝ) (y : UnitAddTorus (Fin D)) :
    mixedCharacter l (0 : Fin D → ℤ) t y = character l t := by
  simp [mixedCharacter, UnitAddTorus.mFourier_zero]

theorem mixedCharacter_zero_line {D : ℕ} (k : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) :
    mixedCharacter 0 k t y = UnitAddTorus.mFourier k y := by
  simp [mixedCharacter, character_zero_left]

/-- A finite sum of mixed characters indexed by an arbitrary finset (repeated frequencies
allowed) is a mixed trigonometric polynomial. -/
theorem isMixedTrigPoly_of_sum {D : ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (lam : ι → ℝ) (k : ι → Fin D → ℤ) {F : ℝ → UnitAddTorus (Fin D) → ℂ}
    (hF : ∀ t y, F t y = ∑ i ∈ s, a i * mixedCharacter (lam i) (k i) t y) :
    IsMixedTrigPoly F := by
  classical
  let g : ι → ℝ × (Fin D → ℤ) := fun i => (lam i, k i)
  refine ⟨s.image g, fun p => ∑ i ∈ s with g i = p, a i, fun t y => ?_⟩
  rw [hF t y]
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := s.image g)
    (fun i hi => Finset.mem_image_of_mem g hi)]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i hi => ?_))
  rw [(Finset.mem_filter.mp hi).2.symm]

end FastTorus

open FastTorus

/-! ## Closure of mixed trigonometric polynomials -/

theorem isMixedTrigPoly_const {D : ℕ} (c : ℂ) :
    IsMixedTrigPoly (fun (_ : ℝ) (_ : UnitAddTorus (Fin D)) => c) := by
  refine isMixedTrigPoly_of_sum (Finset.univ : Finset Unit) (fun _ => c) (fun _ => 0)
    (fun _ => 0) (fun t y => ?_)
  simp [mixedCharacter_zero_zero]

theorem isMixedTrigPoly_mixedCharacter {D : ℕ} (lam : ℝ) (k : Fin D → ℤ) :
    IsMixedTrigPoly (fun t y => mixedCharacter lam k t y) := by
  refine isMixedTrigPoly_of_sum (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => lam)
    (fun _ => k) (fun t y => ?_)
  simp

theorem IsMixedTrigPoly.add {D : ℕ} {F G : ℝ → UnitAddTorus (Fin D) → ℂ}
    (hF : IsMixedTrigPoly F) (hG : IsMixedTrigPoly G) :
    IsMixedTrigPoly (fun t y => F t y + G t y) := by
  obtain ⟨s, c, hs⟩ := hF
  obtain ⟨s', c', hs'⟩ := hG
  refine isMixedTrigPoly_of_sum (s.disjSum s') (Sum.elim c c')
    (Sum.elim Prod.fst Prod.fst) (Sum.elim Prod.snd Prod.snd) (fun t y => ?_)
  rw [Finset.sum_disjSum, hs, hs']
  rfl

theorem IsMixedTrigPoly.mul {D : ℕ} {F G : ℝ → UnitAddTorus (Fin D) → ℂ}
    (hF : IsMixedTrigPoly F) (hG : IsMixedTrigPoly G) :
    IsMixedTrigPoly (fun t y => F t y * G t y) := by
  obtain ⟨s, c, hs⟩ := hF
  obtain ⟨s', c', hs'⟩ := hG
  refine isMixedTrigPoly_of_sum (s ×ˢ s') (fun q => c q.1 * c' q.2)
    (fun q => q.1.1 + q.2.1) (fun q => q.1.2 + q.2.2) (fun t y => ?_)
  rw [hs, hs', Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [← mixedCharacter_mul_mixedCharacter]
  ring

theorem IsMixedTrigPoly.star {D : ℕ} {F : ℝ → UnitAddTorus (Fin D) → ℂ}
    (hF : IsMixedTrigPoly F) : IsMixedTrigPoly (fun t y => star (F t y)) := by
  obtain ⟨s, c, hs⟩ := hF
  refine isMixedTrigPoly_of_sum s (fun p => Star.star (c p)) (fun p => -p.1) (fun p => -p.2)
    (fun t y => ?_)
  rw [hs, star_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [star_mul', star_mixedCharacter_eq]

theorem IsMixedTrigPoly.const_mul {D : ℕ} {F : ℝ → UnitAddTorus (Fin D) → ℂ} (c : ℂ)
    (hF : IsMixedTrigPoly F) : IsMixedTrigPoly (fun t y => c * F t y) :=
  (isMixedTrigPoly_const c).mul hF

theorem IsMixedTrigPoly.sum {D : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → UnitAddTorus (Fin D) → ℂ} (hF : ∀ i ∈ s, IsMixedTrigPoly (F i)) :
    IsMixedTrigPoly (fun t y => ∑ i ∈ s, F i t y) := by
  have h : IsMixedTrigPoly (∑ i ∈ s, F i) :=
    Finset.sum_induction F IsMixedTrigPoly (fun _ _ hf hg => hf.add hg)
      (isMixedTrigPoly_const 0) hF
  obtain ⟨s', c, hs⟩ := h
  exact ⟨s', c, fun t y => by rw [← hs t y, Finset.sum_apply, Finset.sum_apply]⟩

theorem IsMixedTrigPoly.prod {D : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → UnitAddTorus (Fin D) → ℂ} (hF : ∀ i ∈ s, IsMixedTrigPoly (F i)) :
    IsMixedTrigPoly (fun t y => ∏ i ∈ s, F i t y) := by
  have h : IsMixedTrigPoly (∏ i ∈ s, F i) :=
    Finset.prod_induction F IsMixedTrigPoly (fun _ _ hf hg => hf.mul hg)
      (isMixedTrigPoly_const 1) hF
  obtain ⟨s', c, hs⟩ := h
  exact ⟨s', c, fun t y => by rw [← hs t y, Finset.prod_apply, Finset.prod_apply]⟩

theorem IsMixedTrigPoly.congr {D : ℕ} {F G : ℝ → UnitAddTorus (Fin D) → ℂ}
    (hF : IsMixedTrigPoly F) (h : ∀ t y, F t y = G t y) : IsMixedTrigPoly G := by
  obtain ⟨s, c, hs⟩ := hF
  exact ⟨s, c, fun t y => by rw [← h t y, hs t y]⟩

/-! ## The fast space of tags and engines, and its flattening -/

/-- `Mt` tag blocks of dimension `dt`, and `mE` engines with seed and auxiliary tori. -/
abbrev FastSpace (Mt dt mE L de : ℕ) :=
  (Fin Mt → UnitAddTorus (Fin dt)) × (Fin mE → UnitAddTorus (Fin L) × UnitAddTorus (Fin de))

/-- Product Haar probability on the fast space. -/
def fastHaar (Mt dt mE L de : ℕ) : Measure (FastSpace Mt dt mE L de) :=
  (Measure.pi fun _ : Fin Mt => torusMeasure dt).prod
    (Measure.pi fun _ : Fin mE => (torusMeasure L).prod (torusMeasure de))

/-- Coordinates of the fast space. -/
abbrev FastCoord (Mt dt mE L de : ℕ) := (Fin Mt × Fin dt) ⊕ (Fin mE × (Fin L ⊕ Fin de))

def fastDim (Mt dt mE L de : ℕ) : ℕ := Fintype.card (FastCoord Mt dt mE L de)

/-- A fixed enumeration of the fast coordinates. -/
def fastEquiv (Mt dt mE L de : ℕ) : FastCoord Mt dt mE L de ≃ Fin (fastDim Mt dt mE L de) :=
  Fintype.equivFin _

/-- The flattening map from one flat torus onto the fast space. -/
def fastFlat (Mt dt mE L de : ℕ) (x : UnitAddTorus (Fin (fastDim Mt dt mE L de))) :
    FastSpace Mt dt mE L de :=
  (fun b l => x (fastEquiv Mt dt mE L de (Sum.inl (b, l))),
   fun c => (fun l => x (fastEquiv Mt dt mE L de (Sum.inr (c, Sum.inl l))),
             fun k => x (fastEquiv Mt dt mE L de (Sum.inr (c, Sum.inr k)))))

namespace FastTorus

/-- An explicit right inverse of the flattening map. -/
def fastUnflat (Mt dt mE L de : ℕ) (u : FastSpace Mt dt mE L de) :
    UnitAddTorus (Fin (fastDim Mt dt mE L de)) := fun i =>
  match (fastEquiv Mt dt mE L de).symm i with
  | Sum.inl (b, l) => u.1 b l
  | Sum.inr (c, Sum.inl l) => (u.2 c).1 l
  | Sum.inr (c, Sum.inr l) => (u.2 c).2 l

theorem fastFlat_fastUnflat (Mt dt mE L de : ℕ) (u : FastSpace Mt dt mE L de) :
    fastFlat Mt dt mE L de (fastUnflat Mt dt mE L de u) = u := by
  obtain ⟨u₁, u₂⟩ := u
  simp only [fastFlat, fastUnflat, Equiv.symm_apply_apply]

theorem fastFlat_surjective (Mt dt mE L de : ℕ) :
    Function.Surjective (fastFlat Mt dt mE L de) :=
  fun u => ⟨fastUnflat Mt dt mE L de u, fastFlat_fastUnflat Mt dt mE L de u⟩

theorem fastFlat_continuous (Mt dt mE L de : ℕ) :
    Continuous (fastFlat Mt dt mE L de) := by
  unfold fastFlat
  fun_prop

theorem torusMeasure_isAddHaarMeasure (d : ℕ) : (torusMeasure d).IsAddHaarMeasure := by
  rw [torusMeasure_eq_volume]
  infer_instance

theorem unitAddTorus_borelSpace (d : ℕ) : BorelSpace (UnitAddTorus (Fin d)) := Pi.borelSpace

/-- Stated explicitly: the unaided instance search exceeds the default size limit. -/
instance fastSpace_borelSpace (Mt dt mE L de : ℕ) : BorelSpace (FastSpace Mt dt mE L de) := by
  have := unitAddTorus_borelSpace dt
  have := unitAddTorus_borelSpace L
  have := unitAddTorus_borelSpace de
  have : BorelSpace (Fin Mt → UnitAddTorus (Fin dt)) := Pi.borelSpace
  have : BorelSpace (UnitAddTorus (Fin L) × UnitAddTorus (Fin de)) := Prod.borelSpace
  have : BorelSpace (Fin mE → UnitAddTorus (Fin L) × UnitAddTorus (Fin de)) := Pi.borelSpace
  exact Prod.borelSpace

instance fastHaar_isProbabilityMeasure (Mt dt mE L de : ℕ) :
    IsProbabilityMeasure (fastHaar Mt dt mE L de) := by
  unfold fastHaar
  infer_instance

instance fastHaar_isAddHaarMeasure (Mt dt mE L de : ℕ) :
    (fastHaar Mt dt mE L de).IsAddHaarMeasure := by
  have := torusMeasure_isAddHaarMeasure dt
  have := torusMeasure_isAddHaarMeasure L
  have := torusMeasure_isAddHaarMeasure de
  have := unitAddTorus_borelSpace L
  have := unitAddTorus_borelSpace de
  have : BorelSpace (UnitAddTorus (Fin L) × UnitAddTorus (Fin de)) := Prod.borelSpace
  have : MeasurableAdd (UnitAddTorus (Fin L) × UnitAddTorus (Fin de)) := inferInstance
  have : (Measure.pi fun _ : Fin Mt => torusMeasure dt).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : ((torusMeasure L).prod (torusMeasure de)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : (Measure.pi fun _ : Fin mE =>
      (torusMeasure L).prod (torusMeasure de)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

end FastTorus

theorem fastFlat_measurePreserving (Mt dt mE L de : ℕ) :
    MeasurePreserving (fastFlat Mt dt mE L de) (torusMeasure (fastDim Mt dt mE L de))
      (fastHaar Mt dt mE L de) := by
  let f : UnitAddTorus (Fin (fastDim Mt dt mE L de)) →+ FastSpace Mt dt mE L de :=
    { toFun := fastFlat Mt dt mE L de
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have := torusMeasure_isAddHaarMeasure (fastDim Mt dt mE L de)
  exact f.measurePreserving (fastFlat_continuous Mt dt mE L de)
    (fastFlat_surjective Mt dt mE L de) (by simp only [measure_univ])

/-- Flat frequency of a tag character in block `b`. -/
def tagFreq {Mt dt mE L de : ℕ} (b : Fin Mt) (k : Fin dt → ℤ) :
    Fin (fastDim Mt dt mE L de) → ℤ :=
  fun i => match (fastEquiv Mt dt mE L de).symm i with
    | Sum.inl (b', l) => if b' = b then k l else 0
    | Sum.inr _ => 0

/-- Flat frequency of a seed character of engine `c`. -/
def seedFreq {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin L → ℤ) :
    Fin (fastDim Mt dt mE L de) → ℤ :=
  fun i => match (fastEquiv Mt dt mE L de).symm i with
    | Sum.inl _ => 0
    | Sum.inr (c', Sum.inl l) => if c' = c then k l else 0
    | Sum.inr (_, Sum.inr _) => 0

/-- Flat frequency of an auxiliary character of engine `c`. -/
def auxFreq {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin de → ℤ) :
    Fin (fastDim Mt dt mE L de) → ℤ :=
  fun i => match (fastEquiv Mt dt mE L de).symm i with
    | Sum.inl _ => 0
    | Sum.inr (_, Sum.inl _) => 0
    | Sum.inr (c', Sum.inr l) => if c' = c then k l else 0

theorem mFourier_tag {Mt dt mE L de : ℕ} (b : Fin Mt) (k : Fin dt → ℤ)
    (x : UnitAddTorus (Fin (fastDim Mt dt mE L de))) :
    UnitAddTorus.mFourier k ((fastFlat Mt dt mE L de x).1 b) =
      UnitAddTorus.mFourier (tagFreq (mE := mE) (L := L) (de := de) b k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [← (fastEquiv Mt dt mE L de).prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, tagFreq, Equiv.symm_apply_apply,
    fourier_zero, Finset.prod_const_one, mul_one]
  rw [Fintype.prod_eq_single b (fun b' hb' => by
    simp only [if_neg hb', fourier_zero, Finset.prod_const_one])]
  simp only [if_true]
  rfl

theorem mFourier_seed {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin L → ℤ)
    (x : UnitAddTorus (Fin (fastDim Mt dt mE L de))) :
    UnitAddTorus.mFourier k ((fastFlat Mt dt mE L de x).2 c).1 =
      UnitAddTorus.mFourier (seedFreq (Mt := Mt) (dt := dt) (de := de) c k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [← (fastEquiv Mt dt mE L de).prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, seedFreq, Equiv.symm_apply_apply,
    fourier_zero, Finset.prod_const_one, one_mul, mul_one]
  rw [Fintype.prod_eq_single c (fun c' hc' => by
    simp only [if_neg hc', fourier_zero, Finset.prod_const_one])]
  simp only [if_true]
  rfl

theorem mFourier_aux {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin de → ℤ)
    (x : UnitAddTorus (Fin (fastDim Mt dt mE L de))) :
    UnitAddTorus.mFourier k ((fastFlat Mt dt mE L de x).2 c).2 =
      UnitAddTorus.mFourier (auxFreq (Mt := Mt) (dt := dt) (L := L) c k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [← (fastEquiv Mt dt mE L de).prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, auxFreq, Equiv.symm_apply_apply,
    fourier_zero, Finset.prod_const_one, one_mul]
  rw [Fintype.prod_eq_single c (fun c' hc' => by
    simp only [if_neg hc', fourier_zero, Finset.prod_const_one])]
  simp only [if_true]
  rfl

/-- Reading the three kinds of components off a flat frequency. -/
def flatTagPart {Mt dt mE L de : ℕ} (κ : Fin (fastDim Mt dt mE L de) → ℤ) (b : Fin Mt) :
    Fin dt → ℤ := fun l => κ (fastEquiv Mt dt mE L de (Sum.inl (b, l)))

def flatSeedPart {Mt dt mE L de : ℕ} (κ : Fin (fastDim Mt dt mE L de) → ℤ) (c : Fin mE) :
    Fin L → ℤ := fun l => κ (fastEquiv Mt dt mE L de (Sum.inr (c, Sum.inl l)))

def flatAuxPart {Mt dt mE L de : ℕ} (κ : Fin (fastDim Mt dt mE L de) → ℤ) (c : Fin mE) :
    Fin de → ℤ := fun l => κ (fastEquiv Mt dt mE L de (Sum.inr (c, Sum.inr l)))

theorem flatTagPart_tagFreq {Mt dt mE L de : ℕ} (b b' : Fin Mt) (k : Fin dt → ℤ) :
    flatTagPart (tagFreq (mE := mE) (L := L) (de := de) b k) b' = if b' = b then k else 0 := by
  funext l
  simp only [flatTagPart, tagFreq, Equiv.symm_apply_apply]
  split_ifs <;> rfl

theorem flatTagPart_seedFreq {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin L → ℤ) (b' : Fin Mt) :
    flatTagPart (seedFreq (Mt := Mt) (dt := dt) (de := de) c k) b' = 0 := by
  funext l
  simp only [flatTagPart, seedFreq, Equiv.symm_apply_apply]
  rfl

theorem flatTagPart_auxFreq {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin de → ℤ) (b' : Fin Mt) :
    flatTagPart (auxFreq (Mt := Mt) (dt := dt) (L := L) c k) b' = 0 := by
  funext l
  simp only [flatTagPart, auxFreq, Equiv.symm_apply_apply]
  rfl

theorem flatSeedPart_tagFreq {Mt dt mE L de : ℕ} (b : Fin Mt) (k : Fin dt → ℤ) (c' : Fin mE) :
    flatSeedPart (tagFreq (mE := mE) (L := L) (de := de) b k) c' = 0 := by
  funext l
  simp only [flatSeedPart, tagFreq, Equiv.symm_apply_apply]
  rfl

theorem flatSeedPart_seedFreq {Mt dt mE L de : ℕ} (c c' : Fin mE) (k : Fin L → ℤ) :
    flatSeedPart (seedFreq (Mt := Mt) (dt := dt) (de := de) c k) c' = if c' = c then k else 0 := by
  funext l
  simp only [flatSeedPart, seedFreq, Equiv.symm_apply_apply]
  split_ifs <;> rfl

theorem flatSeedPart_auxFreq {Mt dt mE L de : ℕ} (c c' : Fin mE) (k : Fin de → ℤ) :
    flatSeedPart (auxFreq (Mt := Mt) (dt := dt) (L := L) c k) c' = 0 := by
  funext l
  simp only [flatSeedPart, auxFreq, Equiv.symm_apply_apply]
  rfl

theorem flatAuxPart_tagFreq {Mt dt mE L de : ℕ} (b : Fin Mt) (k : Fin dt → ℤ) (c' : Fin mE) :
    flatAuxPart (tagFreq (mE := mE) (L := L) (de := de) b k) c' = 0 := by
  funext l
  simp only [flatAuxPart, tagFreq, Equiv.symm_apply_apply]
  rfl

theorem flatAuxPart_seedFreq {Mt dt mE L de : ℕ} (c c' : Fin mE) (k : Fin L → ℤ) :
    flatAuxPart (seedFreq (Mt := Mt) (dt := dt) (de := de) c k) c' = 0 := by
  funext l
  simp only [flatAuxPart, seedFreq, Equiv.symm_apply_apply]
  rfl

theorem flatAuxPart_auxFreq {Mt dt mE L de : ℕ} (c c' : Fin mE) (k : Fin de → ℤ) :
    flatAuxPart (auxFreq (Mt := Mt) (dt := dt) (L := L) c k) c' = if c' = c then k else 0 := by
  funext l
  simp only [flatAuxPart, auxFreq, Equiv.symm_apply_apply]
  split_ifs <;> rfl

theorem flatTagPart_add {Mt dt mE L de : ℕ} (κ κ' : Fin (fastDim Mt dt mE L de) → ℤ) (b : Fin Mt) :
    flatTagPart (κ + κ') b = flatTagPart κ b + flatTagPart κ' b := rfl

theorem flatSeedPart_add {Mt dt mE L de : ℕ} (κ κ' : Fin (fastDim Mt dt mE L de) → ℤ) (c : Fin mE) :
    flatSeedPart (κ + κ') c = flatSeedPart κ c + flatSeedPart κ' c := rfl

theorem flatAuxPart_add {Mt dt mE L de : ℕ} (κ κ' : Fin (fastDim Mt dt mE L de) → ℤ) (c : Fin mE) :
    flatAuxPart (κ + κ') c = flatAuxPart κ c + flatAuxPart κ' c := rfl

/-- A flat frequency is zero iff all its parts are zero. -/
theorem flat_eq_zero_iff {Mt dt mE L de : ℕ} (κ : Fin (fastDim Mt dt mE L de) → ℤ) :
    κ = 0 ↔ (∀ b, flatTagPart κ b = 0) ∧ (∀ c, flatSeedPart κ c = 0) ∧
      (∀ c, flatAuxPart κ c = 0) := by
  constructor
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨hT, hS, hA⟩
    funext i
    obtain ⟨z, rfl⟩ := (fastEquiv Mt dt mE L de).surjective i
    rcases z with ⟨b, l⟩ | ⟨c, l | l⟩
    · exact congrFun (hT b) l
    · exact congrFun (hS c) l
    · exact congrFun (hA c) l

/-! ## Polynomiality transported from the fast space -/

/-- Functions of the line variable and the fast variables whose flattening is a mixed
trigonometric polynomial. -/
def IsFastPoly {Mt dt mE L de : ℕ} (F : ℝ → FastSpace Mt dt mE L de → ℂ) : Prop :=
  IsMixedTrigPoly (fun t x => F t (fastFlat Mt dt mE L de x))

theorem isFastPoly_line {Mt dt mE L de : ℕ} (lam : ℝ) :
    IsFastPoly (Mt := Mt) (dt := dt) (mE := mE) (L := L) (de := de)
      (fun t _ => character lam t) :=
  (isMixedTrigPoly_mixedCharacter lam 0).congr
    (fun t x => mixedCharacter_zero_freq lam t x)

theorem isFastPoly_tag {Mt dt mE L de : ℕ} (b : Fin Mt) (k : Fin dt → ℤ) :
    IsFastPoly (mE := mE) (L := L) (de := de)
      (fun _ y => UnitAddTorus.mFourier k (y.1 b)) :=
  (isMixedTrigPoly_mixedCharacter 0 (tagFreq (mE := mE) (L := L) (de := de) b k)).congr
    (fun _ x => by rw [mixedCharacter_zero_line]; exact (mFourier_tag b k x).symm)

theorem isFastPoly_seed {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin L → ℤ) :
    IsFastPoly (Mt := Mt) (dt := dt) (de := de)
      (fun _ y => UnitAddTorus.mFourier k (y.2 c).1) :=
  (isMixedTrigPoly_mixedCharacter 0 (seedFreq (Mt := Mt) (dt := dt) (de := de) c k)).congr
    (fun _ x => by rw [mixedCharacter_zero_line]; exact (mFourier_seed c k x).symm)

theorem isFastPoly_aux {Mt dt mE L de : ℕ} (c : Fin mE) (k : Fin de → ℤ) :
    IsFastPoly (Mt := Mt) (dt := dt) (L := L)
      (fun _ y => UnitAddTorus.mFourier k (y.2 c).2) :=
  (isMixedTrigPoly_mixedCharacter 0 (auxFreq (Mt := Mt) (dt := dt) (L := L) c k)).congr
    (fun _ x => by rw [mixedCharacter_zero_line]; exact (mFourier_aux c k x).symm)

/-- Finite Fourier polynomials of a single tag block / auxiliary block. -/
theorem isFastPoly_tag_poly {Mt dt mE L de : ℕ} (b : Fin Mt) (K : Finset (Fin dt → ℤ))
    (a : (Fin dt → ℤ) → ℂ) :
    IsFastPoly (mE := mE) (L := L) (de := de)
      (fun _ y => ∑ k ∈ K, a k * UnitAddTorus.mFourier k (y.1 b)) :=
  IsMixedTrigPoly.sum K
    (F := fun k _ x => a k * UnitAddTorus.mFourier k ((fastFlat Mt dt mE L de x).1 b))
    (fun k _ => (isFastPoly_tag b k).const_mul (a k))

theorem isFastPoly_aux_poly {Mt dt mE L de : ℕ} (c : Fin mE) (K : Finset (Fin de → ℤ))
    (a : (Fin de → ℤ) → ℂ) :
    IsFastPoly (Mt := Mt) (dt := dt) (L := L)
      (fun _ y => ∑ k ∈ K, a k * UnitAddTorus.mFourier k (y.2 c).2) :=
  IsMixedTrigPoly.sum K
    (F := fun k _ x => a k * UnitAddTorus.mFourier k ((fastFlat Mt dt mE L de x).2 c).2)
    (fun k _ => (isFastPoly_aux c k).const_mul (a k))

theorem IsFastPoly.add {Mt dt mE L de : ℕ} {F G : ℝ → FastSpace Mt dt mE L de → ℂ}
    (hF : IsFastPoly F) (hG : IsFastPoly G) : IsFastPoly (fun t y => F t y + G t y) :=
  IsMixedTrigPoly.add hF hG

theorem IsFastPoly.mul {Mt dt mE L de : ℕ} {F G : ℝ → FastSpace Mt dt mE L de → ℂ}
    (hF : IsFastPoly F) (hG : IsFastPoly G) : IsFastPoly (fun t y => F t y * G t y) :=
  IsMixedTrigPoly.mul hF hG

theorem IsFastPoly.star {Mt dt mE L de : ℕ} {F : ℝ → FastSpace Mt dt mE L de → ℂ}
    (hF : IsFastPoly F) : IsFastPoly (fun t y => star (F t y)) :=
  IsMixedTrigPoly.star hF

theorem IsFastPoly.const_mul {Mt dt mE L de : ℕ} {F : ℝ → FastSpace Mt dt mE L de → ℂ} (c : ℂ)
    (hF : IsFastPoly F) : IsFastPoly (fun t y => c * F t y) :=
  IsMixedTrigPoly.const_mul c hF

theorem IsFastPoly.sum {Mt dt mE L de : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → FastSpace Mt dt mE L de → ℂ} (hF : ∀ i ∈ s, IsFastPoly (F i)) :
    IsFastPoly (fun t y => ∑ i ∈ s, F i t y) :=
  IsMixedTrigPoly.sum s (F := fun i t x => F i t (fastFlat Mt dt mE L de x)) hF

theorem IsFastPoly.prod {Mt dt mE L de : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → FastSpace Mt dt mE L de → ℂ} (hF : ∀ i ∈ s, IsFastPoly (F i)) :
    IsFastPoly (fun t y => ∏ i ∈ s, F i t y) :=
  IsMixedTrigPoly.prod s (F := fun i t x => F i t (fastFlat Mt dt mE L de x)) hF

theorem IsFastPoly.congr {Mt dt mE L de : ℕ} {F G : ℝ → FastSpace Mt dt mE L de → ℂ}
    (hF : IsFastPoly F) (h : ∀ t y, F t y = G t y) : IsFastPoly G :=
  IsMixedTrigPoly.congr hF (fun t x => h t (fastFlat Mt dt mE L de x))

end SchauderTranslates
