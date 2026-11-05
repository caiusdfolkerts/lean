import Characterizations.Strands.DeletedFaces
import Characterizations.Strands.BettiTransport

/-! # Proposition 4.3: all nonlinear multigraded and total Betti numbers -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def exceptionalFaces (a : Exponent V) (i : ℕ) : Finset (Finset V) :=
  ((Finset.univ : Finset V).powersetCard (i+1)).filter (a.support ⊆ ·)

def exceptionalDegrees (a : Exponent V) (i : ℕ) : Finset (Exponent V) :=
  (exceptionalFaces a i).image (fun T => a + faceExponent T)

@[simp] lemma mem_exceptionalFaces (a : Exponent V) (i : ℕ) (T : Finset V) :
    T ∈ exceptionalFaces a i ↔ a.support ⊆ T ∧ T.card = i+1 := by
  simp [exceptionalFaces, and_comm]

@[simp] lemma mem_exceptionalDegrees (a b : Exponent V) (i : ℕ) :
    b ∈ exceptionalDegrees a i ↔
      ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T := by
  simp only [exceptionalDegrees, Finset.mem_image, mem_exceptionalFaces]
  constructor
  · rintro ⟨T, ⟨hT, hc⟩, he⟩; exact ⟨T, hT, hc, he.symm⟩
  · rintro ⟨T, hT, hc, he⟩; exact ⟨T, ⟨hT, hc⟩, he.symm⟩

lemma degree_faceExponent (T : Finset V) : (faceExponent T).degree = T.card := by
  have h := degree_sub_faceExponent (a := faceExponent T) (s := T) (le_refl _)
  simpa using h.symm

lemma exceptionalDegrees_degree {a b : Exponent V} {i : ℕ}
    (h : b ∈ exceptionalDegrees a i) : b.degree = a.degree+i+1 := by
  obtain ⟨T, hT, hc, rfl⟩ := (mem_exceptionalDegrees a b i).mp h
  rw [map_add, degree_faceExponent, hc]
  omega

lemma deletedVeronese_betti_off_linear (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    bettiNumber (k := k) (deletedVeronese a) b i =
      if b ∈ exceptionalDegrees a i then 1 else 0 := by
  split_ifs with hb
  · obtain ⟨T, hT, hc, rfl⟩ := (mem_exceptionalDegrees a b i).mp hb
    exact bettiNumber_eq_one_of_boundary _ _ T i hc (deleted_faces_eq_boundary a ha T hT)
  · apply Nat.eq_zero_of_not_pos
    rw [bettiNumber_pos_iff_faces, deleted_faces_nonzero_iff_off_linear a b ha i hoff,
      ← mem_exceptionalDegrees]
    exact hb

lemma deletedVeronese_first_nonlinear (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ i < a.support.card - 1, ∀ b, b.degree ≠ a.degree+i →
      bettiNumber (k := k) (deletedVeronese a) b i = 0) ∧
    bettiNumber (k := k) (deletedVeronese a) (a + faceExponent a.support)
      (a.support.card - 1) = 1 := by
  constructor
  · intro i hi b hoff
    rw [deletedVeronese_betti_off_linear a b ha i hoff, if_neg]
    intro hb
    obtain ⟨T, hT, hc, _⟩ := (mem_exceptionalDegrees a b i).mp hb
    have hh := Finset.card_le_card hT
    omega
  · exact bettiNumber_eq_one_of_boundary _ _ a.support _ (by omega)
      (deleted_faces_eq_boundary a ha a.support (Finset.Subset.refl _))

/-- Total-degree Betti number, the sum of the genuine finite multigraded dimensions. -/
def totalBettiNumber (B : Family V) (i j : ℕ) : ℕ :=
  ∑ b ∈ (Finsupp.finite_of_degree_eq (σ := V) j).toFinset, bettiNumber (k := k) B b i

lemma exceptionalDegrees_card (a : Exponent V) (i : ℕ) :
    (exceptionalDegrees a i).card =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V - a.support.card) (i+1-a.support.card) else 0 := by
  rw [exceptionalDegrees, Finset.card_image_of_injective]
  · by_cases h : a.support.card ≤ i+1
    · rw [if_pos h]
      exact (Finset.card_filter_powersetCard_subset a.support Finset.univ (i+1)
        (Finset.subset_univ _) h).trans (by simp)
    · rw [if_neg h]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hs, hc⟩ := (mem_exceptionalFaces a i T).mp hT
      exact h (hc ▸ Finset.card_le_card hs)
  · intro T U he
    exact faceExponent_injective (add_left_cancel he)

lemma deletedVeronese_total_nonlinear (a : Exponent V) (ha : 2 ≤ a.support.card) (i : ℕ) :
    totalBettiNumber (k := k) (deletedVeronese a) i (a.degree+i+1) =
      if a.support.card ≤ i+1 then
        Nat.choose (Fintype.card V - a.support.card) (i+1-a.support.card) else 0 := by
  rw [totalBettiNumber]
  trans (exceptionalDegrees a i).card
  · have he : ∀ b ∈ (Finsupp.finite_of_degree_eq (σ := V) (a.degree+i+1)).toFinset,
        bettiNumber (k := k) (deletedVeronese a) b i =
          if b ∈ exceptionalDegrees a i then 1 else 0 := by
      intro b hb
      have hd : b.degree = a.degree+i+1 := by simpa using hb
      exact deletedVeronese_betti_off_linear a b ha i (by omega)
    rw [Finset.sum_congr rfl he, Finset.sum_boole]
    simp only [Nat.cast_id]
    apply congrArg Finset.card
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using exceptionalDegrees_degree h, h⟩⟩
  · exact exceptionalDegrees_card a i

lemma deletedVeronese_total_other (a : Exponent V) (ha : 2 ≤ a.support.card) (i j : ℕ)
    (hlin : j ≠ a.degree+i) (hnonlin : j ≠ a.degree+i+1) :
    totalBettiNumber (k := k) (deletedVeronese a) i j = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  have hd : b.degree = j := by simpa using hb
  rw [deletedVeronese_betti_off_linear a b ha i (hd ▸ hlin), if_neg]
  intro he
  exact hnonlin (hd.symm.trans (exceptionalDegrees_degree he))

end Characterizations.Strands
