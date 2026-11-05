import Characterizations.Strands.DeletedGenerators
import Characterizations.Strands.SimplexHomology
import CommAlg.KoszulComplex.FaceMatroid

/-! # Complete multigraded face calculation for a deleted Veronese generator -/
noncomputable section
set_option maxHeartbeats 700000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

lemma degree_sub_faceExponent {a : Exponent V} {s : Finset V} (hs : faceExponent s ≤ a) :
    (a - faceExponent s).degree + s.card = a.degree := by
  simpa only [subsetSum_univ, Finset.inter_univ] using subsetSum_sub_faceExponent hs Finset.univ

lemma deleted_faces_iff (a b : Exponent V) (ha : 2 ≤ a.support.card) (s : Finset V) :
    koszulFaces (deletedVeronese a) b s ↔
      s ⊆ b.support ∧ a.degree + s.card ≤ b.degree ∧ b - faceExponent s ≠ a := by
  rw [koszulFaces, deletedVeronese_contains a _ ha]
  constructor
  · rintro ⟨hdiv, hdeg, hne⟩
    exact ⟨(faceExponent_le_iff_subset_support s b).mp hdiv,
      by have h := degree_sub_faceExponent hdiv; omega, hne⟩
  · rintro ⟨hs, hdeg, hne⟩
    have hdiv := (faceExponent_le_iff_subset_support s b).mpr hs
    exact ⟨hdiv, by have h := degree_sub_faceExponent hdiv; omega, hne⟩

lemma deleted_faces_extension_low (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (e : V) (he : e ∈ b.support) (i : ℕ) (hdeg : a.degree + i + 1 < b.degree) :
    ∀ s, koszulFaces (deletedVeronese a) b s → s.card = i → e ∉ s →
      koszulFaces (deletedVeronese a) b (insert e s) := by
  intro s hs hc hes
  obtain ⟨hsub, hbound, hne⟩ := (deleted_faces_iff a b ha s).mp hs
  apply (deleted_faces_iff a b ha _).mpr
  have hsub' := Finset.insert_subset he hsub
  have hcard : (insert e s).card = i+1 := by simp [hes, hc]
  refine ⟨hsub', by omega, ?_⟩
  intro hbad
  have hh := degree_sub_faceExponent ((faceExponent_le_iff_subset_support _ b).mpr hsub')
  rw [hbad, hcard] at hh
  omega

lemma deleted_faces_eq_boundary (a : Exponent V) (ha : 2 ≤ a.support.card)
    (T : Finset V) (hT : a.support ⊆ T) :
    koszulFaces (deletedVeronese a) (a + faceExponent T) = simplexBoundary T := by
  have hsupp : (a + faceExponent T).support = T := by
    ext j
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, faceExponent_apply]
    by_cases hj : j ∈ T
    · simp [hj]
    · have ha0 : a j = 0 := Finsupp.notMem_support_iff.mp (fun hh => hj (hT hh))
      simp [hj, ha0]
  have hdeg : (a + faceExponent T).degree = a.degree + T.card := by
    rw [map_add]
    have hd := degree_sub_faceExponent (a := faceExponent T) (le_refl _)
    simpa using hd.symm
  funext s
  apply propext
  rw [deleted_faces_iff a _ ha s, hsupp, hdeg]
  constructor
  · rintro ⟨hs, hc, hne⟩
    exact ⟨hs, fun hTs => hne (by rw [Finset.Subset.antisymm hs hTs]; simp)⟩
  · intro hs
    refine ⟨hs.subset, by have h := Finset.card_le_card hs.subset; omega, ?_⟩
    intro he
    have hdiv : faceExponent s ≤ a + faceExponent T :=
      (faceExponent_mono hs.subset).trans (le_add_of_nonneg_left (show (0 : Exponent V) ≤ a from zero_le))
    have hh := degree_sub_faceExponent hdiv
    rw [he, hdeg] at hh
    have hlt := Finset.card_lt_card hs
    omega

section Ring
variable [CommRing k]

lemma faceExponent_injective : Function.Injective (faceExponent (V := V)) := by
  intro s t he
  ext j
  have h := congrArg (fun a : Exponent V => a j) he
  simp only [faceExponent_apply] at h
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

lemma deleted_faces_exact_critical (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : b.degree = a.degree + i + 1)
    (hn : ¬ ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  have hb : b.support.Nonempty := by
    by_contra hb
    have he : b = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hb)
    subst b
    simp at hdeg
  have hex : ∃ e ∈ b.support, ∀ T : Finset V, b = a + faceExponent T → e ∉ T := by
    by_cases hT : ∃ T : Finset V, b = a + faceExponent T
    · obtain ⟨T, hT⟩ := hT
      have hcard : T.card = i+1 := by
        have hh := degree_sub_faceExponent (a := faceExponent T) (le_refl _)
        have he := congrArg Finsupp.degree hT
        simp only [map_add, tsub_self, map_zero, zero_add] at hh he
        omega
      have hsub : ¬a.support ⊆ T := fun h => hn ⟨T, h, hcard, hT⟩
      obtain ⟨e, hea, heT⟩ := Finset.not_subset.mp hsub
      have heb : e ∈ b.support := by
        rw [hT, Finsupp.mem_support_iff, Finsupp.add_apply]
        have hepos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hea)
        omega
      refine ⟨e, heb, ?_⟩
      intro T' hT'
      have heq := faceExponent_injective (add_left_cancel (hT.symm.trans hT'))
      simpa only [← heq] using heT
    · obtain ⟨e, he⟩ := hb
      exact ⟨e, he, fun T heq => (hT ⟨T, heq⟩).elim⟩
  obtain ⟨e, he, heT⟩ := hex
  apply exactIn_of_degree_extension e i
  intro s hs hc hes
  obtain ⟨hsub, hbound, hne⟩ := (deleted_faces_iff a b ha s).mp hs
  apply (deleted_faces_iff a b ha _).mpr
  have hsub' := Finset.insert_subset he hsub
  have hcard : (insert e s).card = i+1 := by simp [hes, hc]
  refine ⟨hsub', by omega, ?_⟩
  intro heq
  have hdiv := (faceExponent_le_iff_subset_support _ b).mpr hsub'
  have hb' : b = a + faceExponent (insert e s) := by
    rw [← heq]
    exact (tsub_add_cancel_of_le hdiv).symm
  exact heT (insert e s) hb' (Finset.mem_insert_self e s)

lemma deleted_faces_exact_of_large_degree (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : a.degree + i + 1 < b.degree) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  have hb : b.support.Nonempty := by
    by_contra hb
    have he : b = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hb)
    subst b
    simp at hdeg
  obtain ⟨e, he⟩ := hb
  exact exactIn_of_degree_extension e i (deleted_faces_extension_low a b ha e he i hdeg)

lemma deleted_faces_exact_of_small_degree (a b : Exponent V) (ha : 2 ≤ a.support.card)
    (i : ℕ) (hdeg : b.degree < a.degree + i) :
    ExactIn (k := k) (koszulFaces (deletedVeronese a) b) i := by
  apply exactIn_of_no_face
  intro s hs hc
  have hh := ((deleted_faces_iff a b ha s).mp hs).2.1
  omega

lemma deleted_faces_nonzero_iff_off_linear [Nontrivial k] (a b : Exponent V)
    (ha : 2 ≤ a.support.card) (i : ℕ) (hoff : b.degree ≠ a.degree+i) :
    NonzeroHomology (k := k) (koszulFaces (deletedVeronese a) b) i ↔
      ∃ T : Finset V, a.support ⊆ T ∧ T.card = i+1 ∧ b = a + faceExponent T := by
  constructor
  · intro h
    by_contra hn
    have hnot := (nonzeroHomology_iff_not_exactIn _ _).mp h
    by_cases hsmall : b.degree < a.degree+i
    · exact hnot (deleted_faces_exact_of_small_degree a b ha i hsmall)
    by_cases hlarge : a.degree+i+1 < b.degree
    · exact hnot (deleted_faces_exact_of_large_degree a b ha i hlarge)
    exact hnot (deleted_faces_exact_critical a b ha i (by omega) hn)
  · rintro ⟨T, hT, hc, rfl⟩
    rw [deleted_faces_eq_boundary a ha T hT]
    exact simplexBoundary_nonzero T i hc

end Ring
end Characterizations.Strands
