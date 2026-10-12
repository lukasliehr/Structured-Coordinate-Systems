import Lean_Code.SchauderTranslates.TorusTransfer

noncomputable section
open Filter
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- A finite set of integer coefficient vectors can be separated by a
direction whose every coordinate is positive. This reuses the finite
hyperplane-avoidance proof from the L² construction. -/
theorem exists_positive_direction {N : ℕ} (K : Finset (Fin N → ℤ)) :
    ∃ ω : Fin N → ℝ, (∀ i, 0 < ω i) ∧
      ∀ k ∈ K, k ≠ 0 → frequencyDot k ω ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := SchauderTranslates.exists_direction_avoiding_modes K
  have hformula (k : Fin N → ℤ) (A : ℝ) :
      frequencyDot k (fun i => v i + A) =
        frequencyDot k v + A * ∑ i, (k i : ℝ) := by
    simp only [frequencyDot, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have havoid (k : Fin N → ℤ) (hk : k ∈ K) :
      ∀ᶠ A : ℝ in atTop, k ≠ 0 → frequencyDot k (fun i => v i + A) ≠ 0 := by
    by_cases hs : (∑ i, (k i : ℝ)) = 0
    · exact Eventually.of_forall (fun A hne => by simpa [hformula, hs] using hv k hk hne)
    · filter_upwards [eventually_gt_atTop (-(frequencyDot k v) / ∑ i, (k i : ℝ))] with A hA
      intro _ hz
      rw [hformula] at hz
      have he : A = -(frequencyDot k v) / ∑ i, (k i : ℝ) :=
        (eq_div_iff hs).mpr (by linarith)
      exact (ne_of_gt hA) he
  have hall : ∀ᶠ A : ℝ in atTop,
      ∀ k ∈ K, k ≠ 0 → frequencyDot k (fun i => v i + A) ≠ 0 := by
    simp only [Filter.eventually_all_finset]
    exact havoid
  have hpos : ∀ᶠ A : ℝ in atTop, ∀ i : Fin N, 0 < v i + A := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [eventually_gt_atTop (-v i)] with A hA
    linarith
  obtain ⟨A, hAp, hAa⟩ := (hpos.and hall).exists
  exact ⟨fun i => v i + A, hAp, hAa⟩

/-- Symbolic centers used in one packet: zero, positive and negative
single coordinates, and ordered coordinate differences. -/
def packetModes (N : ℕ) : Finset (Fin N → ℤ) := by
  classical
  exact insert 0 ((Finset.univ.image (fun i : Fin N => Pi.single i (1 : ℤ))) ∪
    (Finset.univ.image (fun i : Fin N => -Pi.single i (1 : ℤ))) ∪
    (Finset.univ.image (fun ij : Fin N × Fin N =>
      Pi.single ij.1 (1 : ℤ) - Pi.single ij.2 (1 : ℤ))))

@[simp] theorem zero_mem_packetModes (N : ℕ) : 0 ∈ packetModes N := by
  classical
  simp [packetModes]

theorem single_mem_packetModes {N : ℕ} (i : Fin N) :
    Pi.single i (1 : ℤ) ∈ packetModes N := by
  classical
  simp [packetModes]

theorem neg_single_mem_packetModes {N : ℕ} (i : Fin N) :
    -Pi.single i (1 : ℤ) ∈ packetModes N := by
  classical
  simp [packetModes]

theorem difference_mem_packetModes {N : ℕ} (i j : Fin N) :
    Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ) ∈ packetModes N := by
  classical
  simp [packetModes]

@[simp] theorem frequencyDot_single {N : ℕ} (i : Fin N) (ω : Fin N → ℝ) :
    frequencyDot (Pi.single i (1 : ℤ)) ω = ω i := by
  classical
  simp [frequencyDot, Pi.single_apply]

@[simp] theorem frequencyDot_zero {N : ℕ} (ω : Fin N → ℝ) : frequencyDot 0 ω = 0 := by
  simp [frequencyDot]

@[simp] theorem frequencyDot_neg {N : ℕ} (k : Fin N → ℤ) (ω : Fin N → ℝ) :
    frequencyDot (-k) ω = -frequencyDot k ω := by
  simp [frequencyDot, Finset.sum_neg_distrib]

theorem frequencyDot_scale {N : ℕ} (k : Fin N → ℤ) (ω : Fin N → ℝ) (A : ℝ) :
    frequencyDot k (fun i => A * ω i) = A * frequencyDot k ω := by
  simp [frequencyDot, Finset.mul_sum, mul_left_comm]

@[simp] theorem sum_single_mode {N : ℕ} (i : Fin N) :
    ∑ j : Fin N, (Pi.single i (1 : ℤ) : Fin N → ℤ) j = 1 := by
  classical
  simp [Pi.single_apply]

theorem single_mode_injective {N : ℕ} :
    Function.Injective (fun i : Fin N => (Pi.single i (1 : ℤ) : Fin N → ℤ)) := by
  classical
  intro i j h
  by_contra hne
  have hi := congrFun h i
  simp [Pi.single_apply, hne, Ne.symm hne] at hi

theorem difference_mode_ne_zero {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (Pi.single i (1 : ℤ) : Fin N → ℤ) - Pi.single j (1 : ℤ) ≠ 0 := by
  intro hz
  exact hij (single_mode_injective (sub_eq_zero.mp hz))

/-- Distinct ordered pairs give distinct nonzero difference centers. -/
theorem difference_mode_injective {N : ℕ} {i j k l : Fin N}
    (hij : i ≠ j) (hkl : k ≠ l)
    (h : (Pi.single i (1 : ℤ) : Fin N → ℤ) - Pi.single j (1 : ℤ) =
      Pi.single k (1 : ℤ) - Pi.single l (1 : ℤ)) : i = k ∧ j = l := by
  classical
  have hik : i = k := by
    by_contra hne
    have hi := congrFun h i
    by_cases hil : i = l
    · subst l
      simp [hij, hne] at hi
    · simp [hij, hne, hil] at hi
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hjl
  have hj := congrFun h j
  simp [Pi.single_apply, hij, Ne.symm hij, hjl, Ne.symm hjl] at hj

theorem single_mode_ne_zero {N : ℕ} (i : Fin N) :
    (Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ 0 := by
  classical
  intro h
  have hi := congrFun h i
  simp [Pi.single_apply] at hi

theorem single_mode_ne_neg_single {N : ℕ} (i j : Fin N) :
    (Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ -Pi.single j (1 : ℤ) := by
  intro h
  have hs := congrArg (fun k : Fin N → ℤ => ∑ a, k a) h
  simp [Finset.sum_neg_distrib] at hs

theorem single_mode_ne_difference {N : ℕ} (i j k : Fin N) :
    (Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ Pi.single j (1 : ℤ) - Pi.single k (1 : ℤ) := by
  intro h
  have hs := congrArg (fun k : Fin N → ℤ => ∑ a, k a) h
  simp [Finset.sum_sub_distrib] at hs

theorem neg_single_mode_ne_difference {N : ℕ} (i j k : Fin N) :
    -(Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ Pi.single j (1 : ℤ) - Pi.single k (1 : ℤ) := by
  intro h
  have hs := congrArg (fun k : Fin N → ℤ => ∑ a, k a) h
  simp [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hs

/-- Separate an arbitrary finite family of distinct symbolic centers by more
than `2R`, while choosing positive coordinates avoiding any old finite list. -/
theorem separated_positive_coordinates {N : ℕ}
    (S : Finset (Fin N → ℤ)) (R : ℝ) (old : Finset ℝ) :
    ∃ Λ : Fin N → ℝ, (∀ i, 0 < Λ i) ∧ (∀ i, Λ i ∉ old) ∧
      ∀ k ∈ S, ∀ l ∈ S, k ≠ l →
        2 * R < |frequencyDot k Λ - frequencyDot l Λ| := by
  classical
  let D := (S.product S).image (fun kl => kl.1 - kl.2)
  obtain ⟨ω, hpos, hω⟩ := exists_positive_direction D
  have hpair (k l : Fin N → ℤ) (hk : k ∈ S) (hl : l ∈ S) :
      ∀ᶠ A : ℝ in atTop, k ≠ l →
        2 * R < |frequencyDot k (fun i => A * ω i) -
          frequencyDot l (fun i => A * ω i)| := by
    by_cases hkl : k = l
    · exact Eventually.of_forall (fun _ hne => False.elim (hne hkl))
    have hd0 : frequencyDot (k - l) ω ≠ 0 := hω (k - l)
      (Finset.mem_image.mpr ⟨(k,l), Finset.mem_product.mpr ⟨hk,hl⟩, rfl⟩)
      (sub_ne_zero.mpr hkl)
    have hd : 0 < |frequencyDot (k - l) ω| := abs_pos.mpr hd0
    filter_upwards [eventually_gt_atTop (max 0 (2 * R / |frequencyDot (k - l) ω|))]
      with A hA
    intro _
    have hApos : 0 < A := (le_max_left _ _).trans_lt hA
    rw [← SchauderTranslates.frequencyDot_sub, frequencyDot_scale, abs_mul, abs_of_pos hApos]
    exact (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hA)
  have hsep : ∀ᶠ A : ℝ in atTop, ∀ k ∈ S, ∀ l ∈ S, k ≠ l →
      2 * R < |frequencyDot k (fun i => A * ω i) -
        frequencyDot l (fun i => A * ω i)| := by
    simp only [Filter.eventually_all_finset]
    exact fun k hk l hl => hpair k l hk hl
  have hbig : ∀ᶠ A : ℝ in atTop, ∀ i : Fin N, ∀ x ∈ old, x < A * ω i := by
    simp only [Filter.eventually_all, Filter.eventually_all_finset]
    intro i x _
    filter_upwards [eventually_gt_atTop (x / ω i)] with A hA
    exact (div_lt_iff₀ (hpos i)).mp hA
  obtain ⟨A, hA, hs, hb⟩ := ((eventually_gt_atTop 0).and (hsep.and hbig)).exists
  refine ⟨fun i => A * ω i, fun i => mul_pos hA (hpos i), ?_, hs⟩
  intro i hi
  exact (lt_irrefl (A * ω i)) (hb i (A * ω i) hi)

theorem disjoint_center_intervals {R c d : ℝ} (h : 2 * R < |c - d|) :
    Disjoint (Set.Icc (c - R) (c + R)) (Set.Icc (d - R) (d + R)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hbound : |c - d| ≤ 2 * R := abs_le.mpr ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩
  exact (not_lt_of_ge hbound) h

/-- Blueprint `lp:placement`. The coefficient-vector centers represent zero,
±Λᵢ and every Λᵢ − Λⱼ. Separation is proved before placing supports. -/
theorem support_placement {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (old : Finset ℝ) :
    ∃ Λ : Fin N → ℝ, (∀ i, 0 < Λ i) ∧ (∀ i, Λ i ∉ old) ∧
      Function.Injective Λ ∧
      ∀ k ∈ packetModes N, ∀ l ∈ packetModes N, k ≠ l →
        2 * R < |frequencyDot k Λ - frequencyDot l Λ| ∧
        Disjoint
          (Set.Icc (frequencyDot k Λ - R) (frequencyDot k Λ + R))
          (Set.Icc (frequencyDot l Λ - R) (frequencyDot l Λ + R)) := by
  classical
  obtain ⟨Λ, hp, hold, hsep⟩ := separated_positive_coordinates (packetModes N) R old
  refine ⟨Λ, hp, hold, ?_, fun k hk l hl hkl =>
    ⟨hsep k hk l hl hkl, disjoint_center_intervals (hsep k hk l hl hkl)⟩⟩
  intro i j heq
  by_contra hne
  have hm : (Pi.single i (1 : ℤ) : Fin N → ℤ) ≠ Pi.single j (1 : ℤ) := by
    intro h
    have hi := congrFun h i
    simpa [Pi.single_apply, hne, Ne.symm hne] using hi
  have hg := hsep _ (single_mem_packetModes i) _ (single_mem_packetModes j) hm
  simp only [frequencyDot_single, heq, sub_self, abs_zero] at hg
  linarith

end SchauderTranslates.LpConstruction
