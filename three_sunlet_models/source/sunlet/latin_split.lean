module

public import sunlet.latin_orbits

/-! A balanced partition of every normalized Latin system of order at least five
into two transitive nonidentity color families. -/

@[expose] public section
noncomputable section
open Finset

namespace Sunlet.NormalizedLatinSystem

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
variable (L : NormalizedLatinSystem ι Ω)

theorem outside_color_leaves (P : Finset ι) (S : Finset Ω)
    (he : L.identity ∉ P)
    (hS : ∀ a ∈ P, ∀ x ∈ S, L.perm a x ∈ S)
    (hcard : S.card = P.card + 1)
    {a : ι} (haP : a ∉ P) (hae : a ≠ L.identity) {x : Ω} (hx : x ∈ S) :
    L.perm a x ∉ S := by
  have heq : L.neighbors P x = S :=
    eq_of_subset_of_card_le (L.neighbors_subset hS hx)
      (by rw [hcard, L.card_neighbors P he x])
  intro h
  rw [← heq] at h
  rcases mem_insert.mp h with hfix | hm
  · exact L.derangement a hae x hfix
  · obtain ⟨b, hb, heq⟩ := mem_image.mp hm
    have hba : b = a := (L.column_bijective x).injective heq
    exact haP (hba ▸ hb)

/-- In even order, a nontransitive balanced family can be repaired by exchanging
one color, without changing its size. -/
theorem repair_even (r : ℕ) (hr : 3 ≤ r) (hm : Fintype.card Ω = 2 * r)
    (P : Finset ι) (he : L.identity ∉ P) (hP : P.card = r - 1)
    (hnot : ¬TransitiveFamily L.perm (P : Set ι)) :
    ∃ P' : Finset ι, L.identity ∉ P' ∧ P'.card = r - 1 ∧
      TransitiveFamily L.perm (P' : Set ι) := by
  classical
  have hnot' : ∃ x y, ¬ColorConnected L.perm (P : Set ι) x y := by
    simpa only [TransitiveFamily, not_forall] using hnot
  obtain ⟨x, y, hxy⟩ := hnot'
  let S := L.orbit P x
  let T := univ \ S
  have hxS : x ∈ S := L.self_mem_orbit P x
  have hyT : y ∈ T := by simpa [T, S] using hxy
  have hSstable : ∀ a ∈ P, ∀ z ∈ S, L.perm a z ∈ S := by
    intro a ha z hz
    exact (L.perm_mem_orbit_iff ha x z).mpr hz
  have hTstable : ∀ a ∈ P, ∀ z ∈ T, L.perm a z ∈ T := by
    intro a ha z hz
    have hzS : z ∉ S := (mem_sdiff.mp hz).2
    simp only [T, mem_sdiff, mem_univ, true_and]
    exact fun h => hzS ((L.perm_mem_orbit_iff ha x z).mp h)
  have hScard : r ≤ S.card := by
    have hh := L.orbit_card_lower P he x
    dsimp [S]
    omega
  have hTcard : r ≤ T.card := by
    have hh := card_le_card (L.neighbors_subset hTstable hyT)
    rw [L.card_neighbors P he y] at hh
    omega
  have htotal : T.card + S.card = 2 * r := by
    have hh := card_sdiff_add_card_eq_card (subset_univ S)
    simpa only [card_univ, hm] using hh
  have hSsize : S.card = r := by omega
  have hTsize : T.card = r := by omega
  have hC : (univ.erase L.identity : Finset ι).card = 2 * r - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, L.card_eq x, hm]
  have hsub : P ⊆ univ.erase L.identity := by
    intro a ha
    exact mem_erase.mpr ⟨fun heq => he (heq ▸ ha), mem_univ _⟩
  have hNcard : ((univ.erase L.identity) \ P).card = r := by
    rw [card_sdiff_of_subset hsub, hC, hP]
    omega
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < ((univ.erase L.identity) \ P).card by omega)
  have haP : a ∉ P := (mem_sdiff.mp ha).2
  have hae : a ≠ L.identity := (mem_erase.mp (mem_sdiff.mp ha).1).1
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < P.card by omega)
  let Q := P.erase p
  let P' := insert a Q
  have hQcard : Q.card = r - 2 := by dsimp [Q]; rw [card_erase_of_mem hp, hP]; omega
  have hQsub : Q ⊆ P := erase_subset _ _
  have hQe : L.identity ∉ Q := fun h => he (hQsub h)
  have hQP' : (Q : Set ι) ⊆ (P' : Set ι) := by
    intro i hi
    exact mem_insert_of_mem hi
  have hQonS : ∀ z ∈ S, ∀ w ∈ S, ColorConnected L.perm (Q : Set ι) z w :=
    L.connected_on_of_card Q S hQe (fun i hi => hSstable i (hQsub hi)) (by omega)
  have hQonT : ∀ z ∈ T, ∀ w ∈ T, ColorConnected L.perm (Q : Set ι) z w :=
    L.connected_on_of_card Q T hQe (fun i hi => hTstable i (hQsub hi)) (by omega)
  have hStoT : ∀ z ∈ S, L.perm a z ∈ T := by
    intro z hz
    simp only [T, mem_sdiff, mem_univ, true_and]
    exact L.outside_color_leaves P S he hSstable (by omega) haP hae hz
  have hTtoS : ∀ z ∈ T, L.perm a z ∈ S := by
    intro z hz
    have hh := L.outside_color_leaves P T he hTstable (by omega) haP hae hz
    simpa [T] using hh
  refine ⟨P', ?_, ?_, ?_⟩
  · simp only [P', mem_insert, not_or]
    exact ⟨Ne.symm hae, hQe⟩
  · have haQ : a ∉ Q := fun h => haP (hQsub h)
    dsimp [P']
    rw [card_insert_of_notMem haQ, hQcard]
    omega
  · intro z w
    have hstep : ColorConnected L.perm (P' : Set ι) z (L.perm a z) :=
      colorConnected_step _ _ (mem_insert_self _ _) z
    by_cases hz : z ∈ S <;> by_cases hw : w ∈ S
    · exact colorConnected_mono hQP' (hQonS z hz w hw)
    · have hwT : w ∈ T := by simpa [T] using hw
      exact Relation.EqvGen.trans _ _ _ hstep
        (colorConnected_mono hQP' (hQonT _ (hStoT z hz) w hwT))
    · have hzT : z ∈ T := by simpa [T] using hz
      exact Relation.EqvGen.trans _ _ _ hstep
        (colorConnected_mono hQP' (hQonS _ (hTtoS z hzT) w hw))
    · have hzT : z ∈ T := by simpa [T] using hz
      have hwT : w ∈ T := by simpa [T] using hw
      exact colorConnected_mono hQP' (hQonT z hzT w hwT)

/-- The complete combinatorial assertion of Lemma 2.2. -/
theorem exists_transitive_partition (o : Ω) (hm : 5 ≤ Fintype.card Ω) :
    ∃ P N : Finset ι,
      Disjoint P N ∧ P ∪ N = univ.erase L.identity ∧
      2 ≤ P.card ∧ 2 ≤ N.card ∧
      TransitiveFamily L.perm (P : Set ι) ∧ TransitiveFamily L.perm (N : Set ι) := by
  classical
  let m := Fintype.card Ω
  let r := m / 2
  let C : Finset ι := univ.erase L.identity
  have hC : C.card = m - 1 := by
    dsimp [C, m]
    rw [card_erase_of_mem (mem_univ _), card_univ, L.card_eq o]
  have hchoose : r - 1 ≤ C.card := by dsimp [r, m] at *; omega
  obtain ⟨P₀, hP₀C, hP₀card⟩ := exists_subset_card_eq hchoose
  have he₀ : L.identity ∉ P₀ := fun h => (mem_erase.mp (hP₀C h)).1 rfl
  have hpar : m = 2 * r ∨ m = 2 * r + 1 := by dsimp [r]; omega
  have hPexists : ∃ P : Finset ι, P ⊆ C ∧ 2 ≤ P.card ∧
      m < 2 * ((C \ P).card + 1) ∧ TransitiveFamily L.perm (P : Set ι) := by
    rcases hpar with heven | hodd
    · have hr : 3 ≤ r := by dsimp [m] at *; omega
      have hfound : ∃ P : Finset ι, L.identity ∉ P ∧ P.card = r - 1 ∧
          TransitiveFamily L.perm (P : Set ι) := by
        by_cases htr : TransitiveFamily L.perm (P₀ : Set ι)
        · exact ⟨P₀, he₀, hP₀card, htr⟩
        · exact L.repair_even r hr heven P₀ he₀ hP₀card htr
      obtain ⟨P, heP, hPcard, hPtr⟩ := hfound
      have hPC : P ⊆ C := by
        intro a ha
        exact mem_erase.mpr ⟨fun he => heP (he ▸ ha), mem_univ _⟩
      refine ⟨P, hPC, by omega, ?_, hPtr⟩
      rw [card_sdiff_of_subset hPC, hC, hPcard]
      omega
    · have hr : 2 ≤ r := by dsimp [m] at *; omega
      obtain ⟨P, hPC, hPcard⟩ := exists_subset_card_eq (show r ≤ C.card by omega)
      have heP : L.identity ∉ P := fun h => (mem_erase.mp (hPC h)).1 rfl
      refine ⟨P, hPC, by omega, ?_, L.transitive_of_card P heP (by dsimp [m] at *; omega)⟩
      rw [card_sdiff_of_subset hPC, hC, hPcard]
      omega
  obtain ⟨P, hPC, hPcard, hNbig, hPtr⟩ := hPexists
  let N := C \ P
  have heN : L.identity ∉ N := fun h => (mem_erase.mp (mem_sdiff.mp h).1).1 rfl
  have hNcard : 2 ≤ N.card := by
    have h := hNbig
    change m < 2 * (N.card + 1) at h
    dsimp [m] at *
    omega
  have hdis : Disjoint P N :=
    Finset.disjoint_left.mpr (fun i hiP hiN => (mem_sdiff.mp hiN).2 hiP)
  refine ⟨P, N, hdis, ?_, hPcard, hNcard, hPtr, ?_⟩
  · exact union_sdiff_of_subset hPC
  · exact L.transitive_of_card N heN hNbig

end Sunlet.NormalizedLatinSystem
