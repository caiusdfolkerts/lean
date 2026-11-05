import Characterizations.Strands.BettiTransport
import CommAlg.KoszulComplex.FaceMatroid

/-! # A monomial socle element produces the actual top derived-Tor class -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

lemma socle_faces_eq_boundary (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent Finset.univ) = simplexBoundary (Finset.univ : Finset V) := by
  funext s
  apply propext
  constructor
  · rintro ⟨hs, hmem⟩
    refine ⟨Finset.subset_univ s, ?_⟩
    intro hsub
    have he : s = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ s) hsub
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent Finset.univ :=
      (faceExponent_mono (Finset.subset_univ s)).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply,
      Finset.mem_univ, ite_true, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs]
    · by_cases hxs : x ∈ s <;> simp [hxj, Ne.symm hxj, hxs] <;> omega

lemma socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    bettiNumber (k := k) B (a + faceExponent Finset.univ) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ Finset.univ i (by simpa using hcard)
    (socle_faces_eq_boundary B a hout hmul)

lemma socle_gradedBettiNonzero [Field k] (B : Family V) (a : Exponent V)
    (hout : ¬Contains B a) (hmul : ∀ j, Contains B (a + Finsupp.single j 1))
    (i : ℕ) (hcard : Fintype.card V = i+1) :
    GradedBettiNonzero (k := k) B (a + faceExponent Finset.univ) i := by
  rw [← bettiNumber_pos_iff, socle_bettiNumber_eq_one B a hout hmul i hcard]
  exact Nat.zero_lt_one

lemma relative_socle_faces_eq_boundary (B : Family V) (a : Exponent V) (U : Finset V)
    (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) :
    koszulFaces B (a + faceExponent U) = simplexBoundary U := by
  have hsupp' : (a + faceExponent U).support = U := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, faceExponent_apply]
    by_cases hj : j ∈ U
    · simp [hj]
    · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hsupp h))
      simp [hj, hz]
  funext s
  apply propext
  constructor
  · rintro ⟨hdiv, hmem⟩
    have hs : s ⊆ U := by
      simpa only [hsupp'] using (faceExponent_le_iff_subset_support s _).mp hdiv
    refine ⟨hs, ?_⟩
    intro hUs
    have he : s = U := Finset.Subset.antisymm hs hUs
    subst s
    apply hout
    simpa using hmem
  · intro hs
    have hdiv : faceExponent s ≤ a + faceExponent U :=
      (faceExponent_mono hs.subset).trans
        (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    refine ⟨hdiv, ?_⟩
    obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
    obtain ⟨b, hb, hba⟩ := hmul j hj
    refine ⟨b, hb, hba.trans ?_⟩
    intro x
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, faceExponent_apply, Finsupp.single_apply]
    by_cases hxj : x = j
    · subst x
      simp [hjs, hj]
    · by_cases hxs : x ∈ s
      · have hxU := hs.subset hxs
        simp [hxj, Ne.symm hxj, hxs, hxU]
      · simp [hxj, Ne.symm hxj, hxs]

lemma relative_socle_bettiNumber_eq_one [Field k] (B : Family V) (a : Exponent V)
    (U : Finset V) (hsupp : a.support ⊆ U) (hout : ¬Contains B a)
    (hmul : ∀ j ∈ U, Contains B (a + Finsupp.single j 1)) (i : ℕ)
    (hcard : U.card = i+1) : bettiNumber (k := k) B (a+faceExponent U) i = 1 :=
  bettiNumber_eq_one_of_boundary B _ U i hcard
    (relative_socle_faces_eq_boundary B a U hsupp hout hmul)

end Characterizations.Strands
