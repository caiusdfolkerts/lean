import cubical_indecomposability.facet_completeness

/-!
# Exhaustive finite descriptions of a polytope's face lattice

This module turns a closed list of genuine exposed faces into an exhaustive
list.  The hypotheses are local incidence statements, checked separately
for the concrete polytope.  Completeness is proved from the geometric ridge
connectivity and diamond theorems; it is not part of the certificate data.
-/

noncomputable section

namespace CubicalIndecomposability

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {n : ℕ}

/-- A locally closed family of actual exposed faces.  In every interval of
rank two, each listed facet has a second listed facet through the ridge. -/
structure FaceCertificate (P : ConvexPolytope n) where
  listed : Set (Set (E n))
  isFace : ∀ {F}, F ∈ listed → P.IsFace F
  top_mem : P.toSet ∈ listed
  singleton_mem : ∀ v ∈ P.vertices, ({v} : Set (E n)) ∈ listed
  hasFacet : ∀ {A}, A ∈ listed → 2 ≤ faceDim A →
    ∃ B ∈ listed, B ⊆ A ∧ faceDim B + 1 = faceDim A
  ridgePartner : ∀ {A B R}, A ∈ listed → B ∈ listed → R ∈ listed →
    B ⊆ A → R ⊆ B → faceDim B + 1 = faceDim A →
    faceDim R + 2 = faceDim A →
    ∃ C ∈ listed, C ⊆ A ∧ R ⊆ C ∧
      faceDim C + 1 = faceDim A ∧ C ≠ B

namespace FaceCertificate

variable {P : ConvexPolytope n} (C : FaceCertificate P)

/-- Every actual face contained in a listed face is listed. -/
theorem complete_below {A : Set (E n)} (hA : A ∈ C.listed)
    {F : Set (E n)} (hF : P.IsFace F) (hFA : F ⊆ A) : F ∈ C.listed := by
  classical
  suffices main : ∀ k : ℕ, ∀ A : Set (E n), A ∈ C.listed → faceDim A = k →
      ∀ F : Set (E n), P.IsFace F → F ⊆ A → F ∈ C.listed by
    exact main (faceDim A) A hA rfl F hF hFA
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA hdA F hF hFA
    by_cases hEq : F = A
    · exact hEq.symm ▸ hA
    have hdimFA : faceDim F < faceDim A :=
      faceDim_lt_of_ssubset P hF (C.isFace hA)
        (hFA.ssubset_of_ne hEq)
    by_cases hk : k < 2
    · have hdF : faceDim F = 0 := by omega
      obtain ⟨v, rfl, hv⟩ := punto_di_faccia0_e_vertice P hF hdF
      exact C.singleton_mem v hv
    let Q : ConvexPolytope n := facePolytope P (C.isFace hA)
    have hQdim : Q.dim = faceDim A := by
      change faceDim (facePolytope P (C.isFace hA)).toSet = _
      rw [facePolytope_toSet]
    let I := {B : FacetType Q // B.val.val ∈ C.listed}
    have hI : Nonempty I := by
      obtain ⟨B, hB, hBA, hdB⟩ := C.hasFacet hA (by omega)
      let b : FacetType Q :=
        ⟨⟨B, facePolytope_isFace_of P (C.isFace hA) (C.isFace hB) hBA⟩,
          hdB.trans hQdim.symm⟩
      exact ⟨⟨b, hB⟩⟩
    letI : Nonempty I := hI
    have hallFacets : Function.Surjective (fun i : I => i.val) := by
      apply facets_surjective_of_ridge_pairing Q (by omega)
      intro i R hRQ hdR hRB
      have hRP : P.IsFace R := isFace_of_facePolytope P (C.isFace hA) hRQ
      have hBA : i.val.val.val ⊆ A := by
        have h := face_subset_toSet Q i.val.val.property
        simpa only [Q, facePolytope_toSet] using h
      have hdB : faceDim i.val.val.val + 1 = faceDim A :=
        i.val.property.trans hQdim
      have hRlisted : R ∈ C.listed :=
        ih (faceDim i.val.val.val) (by omega) i.val.val.val i.property rfl
          R hRP hRB
      obtain ⟨B', hB', hB'A, hRB', hdB', hne⟩ :=
        C.ridgePartner hA i.property hRlisted hBA hRB hdB (hdR.trans hQdim)
      let b' : FacetType Q :=
        ⟨⟨B', facePolytope_isFace_of P (C.isFace hA) (C.isFace hB') hB'A⟩,
          hdB'.trans hQdim.symm⟩
      refine ⟨⟨b', hB'⟩, ?_, hRB'⟩
      intro heq
      exact hne (congrArg (fun b : FacetType Q => b.val.val) heq)
    have hFQ : Q.IsFace F :=
      facePolytope_isFace_of P (C.isFace hA) hF hFA
    obtain ⟨B, hBQ, hdB, hFB⟩ :=
      face_contained_in_facet Q hFQ (by omega)
    let b : FacetType Q := ⟨⟨B, hBQ⟩, hdB⟩
    obtain ⟨i, hi⟩ := hallFacets b
    have hB : B ∈ C.listed := by
      have h := i.property
      change i.val.val.val ∈ C.listed at h
      simpa only [hi] using h
    exact ih (faceDim B) (by omega) B hB rfl F hF hFB

/-- Local incidence closure implies global completeness. -/
theorem complete {F : Set (E n)} (hF : P.IsFace F) : F ∈ C.listed :=
  C.complete_below C.top_mem hF (face_subset_toSet P hF)

/-- The listed family is exactly the ordinary nonempty exposed-face family. -/
theorem mem_iff_isFace (F : Set (E n)) : F ∈ C.listed ↔ P.IsFace F :=
  ⟨C.isFace, C.complete⟩

end FaceCertificate

end CubicalIndecomposability
