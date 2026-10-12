import Lean_Code.SchauderTranslates.ProductPoly

/-!
# Evenness of the product kernel

If the tag block and all auxiliary scalar blocks are even and the residual coefficients are
real, every ingredient of the product kernel is symmetric under the simultaneous inversion
`(t, x) ↦ (-t, -x)`:

* the means and Gram matrices of an even scalar block are real, hence so are the
  coefficients of its minimum-variance tag polynomial;
* the lifted residual satisfies `h (-t, -y) = conj (h (t, y))`;
* every seed factor `1/2 + Re (a · conj (e(z)))` is unchanged by `(a, z) ↦ (conj a, -z)`;
* the scalar densities are even.

Hence the raw kernel and its flattening are invariant under simultaneous inversion.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction ProductEngines

namespace Evenness

/-! ### Real complex numbers -/

theorem im_mul_eq_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) : (a * b).im = 0 := by
  rw [Complex.mul_im, ha, hb, mul_zero, zero_mul, add_zero]

theorem im_ofReal_inv_mul (r : ℝ) {b : ℂ} (hb : b.im = 0) : ((r : ℂ)⁻¹ * b).im = 0 := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, hb, mul_zero]

theorem star_eq_self_of_im {a : ℂ} (ha : a.im = 0) : star a = a :=
  Complex.conj_eq_iff_im.mpr ha

/-- A real positive definite complex matrix has a real inverse. -/
theorem inv_im_eq_zero_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.PosDef) (hre : ∀ i j, (B i j).im = 0) (i j : ι) : (B⁻¹ i j).im = 0 := by
  obtain ⟨R, hR⟩ : ∃ R : Matrix ι ι ℝ, R = B.map Complex.re := ⟨_, rfl⟩
  have hRpos : R.PosDef := hR ▸ posDef_realPart hB
  have hmap : R.map Complex.ofReal = B := by
    ext k l
    apply Complex.ext
    · rw [hR]
      rfl
    · rw [hR]
      exact (hre k l).symm
  have hinv : B⁻¹ = (R⁻¹).map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [← hmap]
    change R.map (Complex.ofRealHom : ℝ → ℂ) *
      R⁻¹.map (Complex.ofRealHom : ℝ → ℂ) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hRpos.isUnit)]
    simp
  rw [hinv]
  exact Complex.ofReal_im _

/-! ### Even scalar blocks have real means and Gram matrices -/

section Scalar
variable {d n : ℕ} (s : ScalarData d n)

theorem moment_im (hs : s.IsEven) (i : Fin n) : (s.moment i).im = 0 :=
  s.rawGram_real hs _ _

theorem nonconstantGram_im (hs : s.IsEven) (i j : Fin n) : (s.nonconstantGram i j).im = 0 :=
  s.rawGram_real hs _ _

theorem mean_im (hs : s.IsEven) (i : Fin n) : (s.mean i).im = 0 :=
  im_ofReal_inv_mul s.mass (moment_im s hs i)

theorem rawCenteredGram_im (hs : s.IsEven) (i j : Fin n) : (s.rawCenteredGram i j).im = 0 := by
  have h : s.rawCenteredGram i j =
      s.nonconstantGram i j - (s.mass : ℂ)⁻¹ * (s.moment i * star (s.moment j)) := rfl
  have hm : (s.moment i * star (s.moment j)).im = 0 := by
    rw [star_eq_self_of_im (moment_im s hs j)]
    exact im_mul_eq_zero (moment_im s hs i) (moment_im s hs j)
  rw [h, Complex.sub_im, nonconstantGram_im s hs, im_ofReal_inv_mul s.mass hm, sub_zero]

theorem centeredGram_im (hs : s.IsEven) (i j : Fin n) : (s.centeredGram i j).im = 0 :=
  im_ofReal_inv_mul s.mass (rawCenteredGram_im s hs i j)

theorem centeredGram_inv_im (hs : s.IsEven) (i j : Fin n) : (s.centeredGram⁻¹ i j).im = 0 :=
  inv_im_eq_zero_of_posDef s.centeredGram_posDef (centeredGram_im s hs) i j

/-- The minimum-variance tag polynomial of an even block has real coefficients. -/
theorem liftCoefficients_im (hs : s.IsEven) (k : Fin n) : (s.liftCoefficients k).im = 0 := by
  have h : s.liftCoefficients k =
      (s.gain : ℂ)⁻¹ * ∑ j, s.centeredGram⁻¹ k j * s.mean j := rfl
  rw [h]
  apply im_ofReal_inv_mul
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero
    (fun j _ => im_mul_eq_zero (centeredGram_inv_im s hs k j) (mean_im s hs j))

end Scalar

/-! ### Inversion of characters and seed factors -/

/-- Inversion of the line variable conjugates a character. -/
theorem character_neg (a t : ℝ) : character a (-t) = star (character a t) := by
  rw [LineTransfer.star_character]
  simp only [character]
  congr 1
  push_cast
  ring

/-- A seed factor is unchanged by conjugating the moment and inverting the phase. -/
theorem seedFactor_star_neg (a : ℂ) (x : UnitAddCircle) :
    seedFactor (star a) (-x) = seedFactor a x := by
  unfold seedFactor
  rw [circle_character_neg_apply, star_star]
  have h : star a * fourier (1 : ℤ) x = star (a * star (fourier (1 : ℤ) x)) := by
    rw [star_mul', star_star]
  rw [h, Complex.star_def, Complex.conj_re]

theorem seedProduct_star_neg (L : ℕ) (a : ℂ) (z : UnitAddTorus (Fin L)) :
    seedProduct L (star a) (-z) = seedProduct L a z := by
  unfold seedProduct
  exact Finset.prod_congr rfl (fun i _ => seedFactor_star_neg a (z i))

theorem seedKernel_star_neg (L : ℕ) (m : ℝ) (a : ℂ) (z : UnitAddTorus (Fin L)) :
    seedKernel L m (star a) (-z) = seedKernel L m a z := by
  unfold seedKernel
  rw [seedProduct_star_neg]

/-- The raw selective kernel of an even block is unchanged when the slow representative is
conjugated and the fresh variables are inverted. -/
theorem raw_neg {S : Type*} [MeasurableSpace S] {L d n : ℕ} (a : SelectiveKernelData S L d n)
    (ha : a.scalar.IsEven) {x x' : S} (hx : a.e x' = star (a.e x))
    (z : UnitAddTorus (Fin L) × UnitAddTorus (Fin d)) :
    a.raw (x', -z) = a.raw (x, z) := by
  have hk : (a.κ : ℂ) * star (a.e x) = star ((a.κ : ℂ) * a.e x) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  simp only [SelectiveKernelData.raw, Prod.fst_neg, Prod.snd_neg]
  rw [ha z.2, hx, hk, seedKernel_star_neg]

/-- The normalized residual coefficients are real. -/
theorem cn_im (T : TagSetup) (hc : ∀ j, (T.c j).im = 0) (j : Fin (T.d + 1)) :
    (T.cn j).im = 0 :=
  im_ofReal_inv_mul (Real.sqrt T.D) (hc j)

/-- The packet coefficients of the lift are real. -/
theorem liftPacketCoeff_im (T : TagSetup) (hc : ∀ j, (T.c j).im = 0) (hst : T.st.IsEven)
    (q : Fin (T.d + 1) × Fin T.nt) : (liftPacketCoeff T.st T.cn q).im = 0 :=
  im_mul_eq_zero (cn_im T hc q.1) (liftCoefficients_im T.st hst q.2)

end Evenness

open Evenness

/-- Real residual coefficients and an even tag block give a lift with
`h(−t, −y) = conj h(t, y)`. -/
theorem lift_neg (T : TagSetup) (hc : ∀ j, (T.c j).im = 0) (hst : T.st.IsEven)
    (i : Fin T.N) (t : ℝ) (y : Fin T.Mt → UnitAddTorus (Fin T.dt)) :
    T.lift i (-t, -y) = star (T.lift i (t, y)) := by
  have h : ∀ (t : ℝ) (y : Fin T.Mt → UnitAddTorus (Fin T.dt)),
      T.lift i (t, y) = ∑ q : Fin (T.d + 1) × Fin T.nt,
        liftPacketCoeff T.st T.cn q * (character (T.lam q.1) t *
          UnitAddTorus.mFourier (T.st.frequencies q.2) (y (T.blk i q.1))) := fun t y => rfl
  rw [h, h, star_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [star_mul', star_mul', star_eq_self_of_im (liftPacketCoeff_im T hc hst q), Pi.neg_apply,
    character_neg, torus_character_neg_apply]

/-- The raw product kernel is invariant under simultaneous inversion. -/
theorem Wraw_neg {T : TagSetup} (E : EngineSetup T) (hst : T.st.IsEven)
    (he : ∀ (c : Fin (T.N * E.n)) (t : ℝ) (y : Fin T.Mt → UnitAddTorus (Fin T.dt)),
      (E.a c).e (-t, -y) = star ((E.a c).e (t, y)))
    (hse : ∀ c, (E.a c).scalar.IsEven) (t : ℝ) (y : E.Fast) :
    E.Wraw (-t) (-y) = E.Wraw t y := by
  unfold EngineSetup.Wraw
  congr 1
  · exact Finset.prod_congr rfl (fun b _ => hst (y.1 b))
  · exact Finset.prod_congr rfl (fun c _ => raw_neg (E.a c) (hse c) (he c t y.1) (y.2 c))

/-- The flat product kernel is invariant under simultaneous inversion. -/
theorem Wflat_neg {T : TagSetup} (E : EngineSetup T) (hst : T.st.IsEven)
    (he : ∀ (c : Fin (T.N * E.n)) (t : ℝ) (y : Fin T.Mt → UnitAddTorus (Fin T.dt)),
      (E.a c).e (-t, -y) = star ((E.a c).e (t, y)))
    (hse : ∀ c, (E.a c).scalar.IsEven) (t : ℝ) (x : UnitAddTorus (Fin E.D)) :
    E.Wflat (-t) (-x) = E.Wflat t x := by
  have hflat : E.flat (-x) = -E.flat x := rfl
  unfold EngineSetup.Wflat
  rw [hflat]
  exact Wraw_neg E hst he hse t (E.flat x)

end SchauderTranslates.Sharp
