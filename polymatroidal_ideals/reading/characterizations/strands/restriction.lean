import Characterizations.Strands.OrderEmbedding
import Characterizations.Localization
import CommAlg.KoszulComplex.FaceMatroid

/-! # Exact fine Betti transport under deletion of unused coordinates -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def subsetOrderEmbedding (U : Finset V) : U ↪o V :=
  OrderEmbedding.ofMapLEIff Subtype.val (by intros; rfl)

lemma extend_faceExponent (U : Finset V) (s : Finset U) :
    extendExponent U (faceExponent s) = faceExponent (s.map (subsetOrderEmbedding U).toEmbedding) := by
  ext j
  by_cases hj : j ∈ U
  · simp only [extendExponent_apply, dif_pos hj, faceExponent_apply, Finset.mem_map]
    have he : (∃ a, a ∈ s ∧ (subsetOrderEmbedding U).toEmbedding a = j) ↔
        (⟨j, hj⟩ : U) ∈ s := by
      constructor
      · rintro ⟨a, ha, he⟩
        have he' : a = ⟨j, hj⟩ := Subtype.ext he
        simpa only [he'] using ha
      · intro h; exact ⟨⟨j, hj⟩, h, rfl⟩
    simp only [he]
    split_ifs <;> first | rfl | contradiction
  · simp only [extendExponent_apply, dif_neg hj, faceExponent_apply]
    rw [if_neg]
    intro hm
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hm
    exact hj (he ▸ a.property)

lemma extend_sub (U : Finset V) (a b : Exponent U) :
    extendExponent U (a-b) = extendExponent U a - extendExponent U b := by
  ext j
  by_cases hj : j ∈ U <;> simp [extendExponent_apply, hj]

lemma extend_support_subset (U : Finset V) (a : Exponent U) :
    (extendExponent U a).support ⊆ U := by
  intro j hj
  by_contra hjU
  have h := Finsupp.mem_support_iff.mp hj
  exact h (by simp [hjU])

lemma koszulFaces_extend_image (U : Finset V) (B : Family V) (C : Family U)
    (hcontains : ∀ a, Contains B (extendExponent U a) ↔ Contains C a) (a : Exponent U) :
    ∀ s, koszulFaces B (extendExponent U a) s ↔
      ∃ t, koszulFaces C a t ∧ s=t.map (subsetOrderEmbedding U).toEmbedding := by
  have mapped (t : Finset U) :
      koszulFaces B (extendExponent U a) (t.map (subsetOrderEmbedding U).toEmbedding) ↔
        koszulFaces C a t := by
    unfold koszulFaces
    rw [← extend_faceExponent, extendExponent_le_iff, ← extend_sub, hcontains]
  intro s
  constructor
  · intro hs
    have hsub : s ⊆ U := ((faceExponent_le_iff_subset_support s _).mp hs.1).trans
      (extend_support_subset U a)
    let t := s.subtype (· ∈ U)
    have he : t.map (subsetOrderEmbedding U).toEmbedding = s :=
      Finset.subtype_map_of_mem (fun j hj => hsub hj)
    refine ⟨t, (mapped t).mp (by simpa only [he] using hs), he.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact (mapped t).mpr ht

theorem betti_restriction_transport (U : Finset V) (B : Family V) (C : Family U)
    (hcontains : ∀ a, Contains B (extendExponent U a) ↔ Contains C a) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) B (extendExponent U a) i = bettiNumber (k := k) C a i := by
  rw [bettiNumber_eq_face_homology_finrank, bettiNumber_eq_face_homology_finrank]
  exact (embedded_homology_finrank (subsetOrderEmbedding U) (koszulFaces_downward C a)
    (koszulFaces_downward B _) (koszulFaces_extend_image U B C hcontains a) i).symm

/-- Set the omitted variables to zero; generators involving them disappear. -/
def restrictionFamily (B : Family V) (U : Finset V) : Family U :=
  (B.filter (fun b => b.support ⊆ U)).image (restrictExponent U)

lemma contains_restrictionFamily (B : Family V) (U : Finset V) (a : Exponent U) :
    Contains B (extendExponent U a) ↔ Contains (restrictionFamily B U) a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hs : b.support ⊆ U := by
      intro j hj
      by_contra hjU
      have h := hba j
      have hp := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      simp only [extendExponent_apply, dif_neg hjU] at h
      omega
    refine ⟨restrictExponent U b, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, rfl⟩, ?_⟩
    intro j
    simpa using hba j
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hcB, hcU⟩ := Finset.mem_filter.mp hc
    refine ⟨c, hcB, ?_⟩
    intro j
    by_cases hj : j ∈ U
    · simpa [hj] using hba ⟨j, hj⟩
    · have hz : c j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hcU h))
      simp [hj, hz]

theorem betti_restriction (B : Family V) (U : Finset V) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) B (extendExponent U a) i =
      bettiNumber (k := k) (restrictionFamily B U) a i :=
  betti_restriction_transport U B _ (contains_restrictionFamily B U) a i

lemma contains_extendedFamily (U : Finset V) (B : Family U) (a : Exponent U) :
    Contains (B.image (extendExponent U)) (extendExponent U a) ↔ Contains B a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨c, hc, (extendExponent_le_iff U c a).mp hba⟩
  · rintro ⟨b, hb, hba⟩
    exact ⟨extendExponent U b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      (extendExponent_le_iff U b a).mpr hba⟩

theorem betti_extension (U : Finset V) (B : Family U) (a : Exponent U) (i : ℕ) :
    bettiNumber (k := k) (B.image (extendExponent U)) (extendExponent U a) i =
      bettiNumber (k := k) B a i :=
  betti_restriction_transport U _ B (contains_extendedFamily U B) a i

lemma ambient_restriction_faces (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) :
    koszulFaces (B.filter (fun b => b.support ⊆ U)) a = koszulFaces B a := by
  funext s
  apply propext
  constructor
  · rintro ⟨hdiv, b, hb, hba⟩
    exact ⟨hdiv, b, (Finset.mem_filter.mp hb).1, hba⟩
  · rintro ⟨hdiv, b, hb, hba⟩
    refine ⟨hdiv, b, Finset.mem_filter.mpr ⟨hb, ?_⟩, hba⟩
    intro j hj
    apply ha
    have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
    have hbj : b j ≤ a j := (hba.trans tsub_le_self) j
    exact Finsupp.mem_support_iff.mpr (by omega)

theorem betti_ambient_restriction (B : Family V) (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) (i : ℕ) :
    bettiNumber (k := k) (B.filter (fun b => b.support ⊆ U)) a i =
      bettiNumber (k := k) B a i :=
  bettiNumber_congr_faces _ _ _ _ _ (ambient_restriction_faces B U a ha)

end Characterizations.Strands
