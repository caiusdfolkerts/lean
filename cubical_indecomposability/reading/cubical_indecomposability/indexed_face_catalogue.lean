import cubical_indecomposability.face_certificate
import cubical.polytope.face_incidence

/-!
# Reading a finite incidence catalogue as geometric faces

The catalogue stores genuine exposed faces and their proved dimensions.
Its local rank-two incidence condition supplies the face-completeness
theorem.  This produces an explicit bijection with all geometric faces
and transports face numbers to finite cardinalities.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ} {ι : Type*}

structure IndexedFaceCatalogue (P : ConvexPolytope n) (ι : Type*) where
  face : ι → FaceType P
  rank : ι → ℕ
  dimension : ∀ i, faceDim (face i).val = rank i
  injective : Function.Injective face
  top : ∃ i, (face i).val = P.toSet
  vertices : ∀ v ∈ P.vertices, ∃ i, (face i).val = {v}
  facet : ∀ a, 2 ≤ rank a →
    ∃ b, (face b).val ⊆ (face a).val ∧ rank b + 1 = rank a
  ridgePartner : ∀ a b r,
    (face b).val ⊆ (face a).val → (face r).val ⊆ (face b).val →
    rank b + 1 = rank a → rank r + 2 = rank a →
    ∃ c, (face c).val ⊆ (face a).val ∧
      (face r).val ⊆ (face c).val ∧ rank c + 1 = rank a ∧ c ≠ b

namespace IndexedFaceCatalogue

variable {P : ConvexPolytope n} (C : IndexedFaceCatalogue P ι)

def certificate : FaceCertificate P where
  listed := Set.range (fun i => (C.face i).val)
  isFace := by
    rintro F ⟨i, rfl⟩
    exact (C.face i).property
  top_mem := C.top
  singleton_mem := C.vertices
  hasFacet := by
    rintro A ⟨a, rfl⟩ hdim
    rw [C.dimension] at hdim
    obtain ⟨b, hba, hrank⟩ := C.facet a hdim
    exact ⟨(C.face b).val, ⟨b, rfl⟩, hba, by simpa only [C.dimension] using hrank⟩
  ridgePartner := by
    rintro A B R ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨r, rfl⟩ hba hrb hdb hdr
    simp only [C.dimension] at hdb hdr
    obtain ⟨c, hca, hrc, hdc, hcb⟩ := C.ridgePartner a b r hba hrb hdb hdr
    refine ⟨(C.face c).val, ⟨c, rfl⟩, hca, hrc, ?_, ?_⟩
    · simpa only [C.dimension] using hdc
    · intro h
      exact hcb (C.injective (Subtype.ext h))

/-- Every ordinary exposed face occurs in the finite catalogue. -/
theorem surjective : Function.Surjective C.face := by
  intro F
  obtain ⟨i, hi⟩ := C.certificate.complete F.property
  exact ⟨i, Subtype.ext hi⟩

/-- The catalogue is exactly the set of nonempty geometric faces. -/
def equiv : ι ≃ FaceType P :=
  Equiv.ofBijective C.face ⟨C.injective, C.surjective⟩

@[simp] theorem equiv_apply (i : ι) : C.equiv i = C.face i := rfl

def rankEquiv (k : ℕ) : {i : ι // C.rank i = k} ≃ DimFaceType P k :=
  C.equiv.subtypeEquiv fun i => by
    change C.rank i = k ↔ faceDim (C.face i).val = k
    rw [C.dimension]

/-- Count actual geometric faces by counting catalogue ranks. -/
theorem faceNumber_eq [Fintype ι] (k : ℕ) :
    faceNumber P k = Fintype.card {i : ι // C.rank i = k} := by
  classical
  rw [← card_dimFaceType P k]
  exact (Fintype.card_congr (C.rankEquiv k)).symm

end IndexedFaceCatalogue

end CubicalIndecomposability
