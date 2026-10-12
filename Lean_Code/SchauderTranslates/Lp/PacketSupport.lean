import Lean_Code.SchauderTranslates.Lp.Placement

noncomputable section
open scoped BigOperators

namespace SchauderTranslates.LpConstruction

def privateModes {N : ℕ} (i : Fin N) : Finset (Fin N → ℤ) := by
  classical
  exact insert (Pi.single i (1 : ℤ)) ((Finset.univ.erase i).image
    (fun j : Fin N => Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)))

def modeInterval {N : ℕ} (R : ℝ) (Λ : Fin N → ℝ) (k : Fin N → ℤ) : Set ℝ :=
  Set.Icc (frequencyDot k Λ - R) (frequencyDot k Λ + R)

def modesRegion {N : ℕ} (R : ℝ) (Λ : Fin N → ℝ) (S : Finset (Fin N → ℤ)) : Set ℝ :=
  ⋃ k ∈ S, modeInterval R Λ k

def SeparatedModeIntervals {N : ℕ} (R : ℝ) (Λ : Fin N → ℝ) : Prop :=
  ∀ k ∈ packetModes N, ∀ l ∈ packetModes N, k ≠ l →
    Disjoint (modeInterval R Λ k) (modeInterval R Λ l)

theorem privateModes_subset {N : ℕ} (i : Fin N) : privateModes i ⊆ packetModes N := by
  classical
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact single_mem_packetModes i
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact difference_mem_packetModes i j

theorem privateModes_nonzero {N : ℕ} (i : Fin N) : ∀ k ∈ privateModes i, k ≠ 0 := by
  classical
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact single_mode_ne_zero i
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact difference_mode_ne_zero (Ne.symm (Finset.mem_erase.mp hj).1)

theorem privateModes_disjoint {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Disjoint (privateModes i) (privateModes j) := by
  classical
  rw [Finset.disjoint_left]
  intro k hki hkj
  rcases Finset.mem_insert.mp hki with hi | hi
  · subst k
    rcases Finset.mem_insert.mp hkj with hj | hj
    · exact hij (single_mode_injective hj)
    · obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hj
      exact single_mode_ne_difference i j l he.symm
  · obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hi
    subst k
    rcases Finset.mem_insert.mp hkj with hj | hj
    · exact single_mode_ne_difference j i l hj.symm
    · obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hj
      exact hij (difference_mode_injective
        (Ne.symm (Finset.mem_erase.mp hl).1)
        (Ne.symm (Finset.mem_erase.mp hm).1) he.symm).1

theorem modeInterval_subset_region {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    {S : Finset (Fin N → ℤ)} {k : Fin N → ℤ} (hk : k ∈ S) :
    modeInterval R Λ k ⊆ modesRegion R Λ S := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hx⟩⟩

theorem regions_disjoint {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ)
    {S T : Finset (Fin N → ℤ)} (hS : S ⊆ packetModes N) (hT : T ⊆ packetModes N)
    (hST : Disjoint S T) : Disjoint (modesRegion R Λ S) (modesRegion R Λ T) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hk, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨l, hy⟩ := Set.mem_iUnion.mp hy
  obtain ⟨hl, hy⟩ := Set.mem_iUnion.mp hy
  have hkl : k ≠ l := by
    intro he
    subst l
    exact Finset.disjoint_left.mp hST hk hl
  exact Set.disjoint_left.mp (hsep k (hS hk) l (hT hl) hkl) hx hy

theorem region_disjoint_base {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) {S : Finset (Fin N → ℤ)}
    (hS : S ⊆ packetModes N) (hzero : ∀ k ∈ S, k ≠ 0) :
    Disjoint (modesRegion R Λ S) (Set.Icc (-R) R) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hk, hx⟩ := Set.mem_iUnion.mp hx
  have hz : modeInterval R Λ 0 = Set.Icc (-R) R := by simp [modeInterval, frequencyDot]
  rw [← hz] at hy
  exact Set.disjoint_left.mp (hsep k (hS hk) 0 (zero_mem_packetModes N) (hzero k hk)) hx hy

theorem private_regions_disjoint {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (modesRegion R Λ (privateModes i)) (modesRegion R Λ (privateModes j)) :=
  regions_disjoint hsep (privateModes_subset i) (privateModes_subset j) (privateModes_disjoint hij)

theorem private_region_disjoint_base {N : ℕ} {R : ℝ} {Λ : Fin N → ℝ}
    (hsep : SeparatedModeIntervals R Λ) (i : Fin N) :
    Disjoint (modesRegion R Λ (privateModes i)) (Set.Icc (-R) R) :=
  region_disjoint_base hsep (privateModes_subset i) (privateModes_nonzero i)

end SchauderTranslates.LpConstruction
