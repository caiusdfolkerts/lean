module
public import TargetAlternatives
public import Papers.IntegerFacetRealization
public import Consolidated.IntegerPolytopeWitnesses

@[expose] public section
/-! The AppendixB alternative identifies the ordinary face lattice with the
convex hull of the stated exact coordinates. A facet-family name is not
silently substituted for that geometric conclusion. -/
noncomputable section
namespace Nonrational.TerminalVerification
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.RationalWitnesses
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

/-- Exact homogeneous integer witnesses for the twelve Appendix B types. -/
def appendixCoordinates : AppendixConfiguration → IntegerConfiguration 10
  | .type452 => Papers.RationalWitnesses.Type452.coordinates
  | .type52 => Papers.RationalWitnesses.Type52.coordinates
  | .type53 => Papers.RationalWitnesses.Type53.coordinates
  | .type679 => Papers.RationalWitnesses.Type679.coordinates
  | .type85 => Papers.RationalWitnesses.Type85.coordinates
  | .typeA14 => Papers.RationalWitnesses.TypeA14.coordinates
  | .typeA73 => Papers.RationalWitnesses.TypeA73.coordinates
  | .typeD0 => Papers.RationalWitnesses.TypeD0.coordinates
  | .typeD4 => Papers.RationalWitnesses.TypeD4.coordinates
  | .fourprism => Papers.RationalWitnesses.Typefourprism.coordinates
  | .twoprism0 => Papers.RationalWitnesses.Typetwoprism0.coordinates
  | .twoprism2 => Papers.RationalWitnesses.Typetwoprism2.coordinates

/-- Equality with an actual convex hull and its complete face order. -/
def IsExplicitAppendixConfiguration (P : ConvexPolytope 4) : Prop :=
  ∃ a, ∃ Q : ConvexPolytope 4,
    Q.vertices = Finset.univ.image (fun i => (euclideanCoordinateEquiv 4).symm
      (ordinaryPoints (normalizedConfiguration (appendixCoordinates a)) i)) ∧
    CombinatoriallyEquivalent P Q

theorem polytope_of_certificate {n f l c : Nat}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices) (hP : P.IsFullDim)
    (w : IntegerConfiguration n) (C : FacetCertificate n f l c)
    (hC : C.Valid w) (hw : ∀ i, 0 < w i 0)
    (hfacets : ∀ T : Finset (Fin n),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (C.facets k).vertices) :
    ∃ Q : ConvexPolytope 4,
      Q.vertices = Finset.univ.image (fun i => (euclideanCoordinateEquiv 4).symm
        (ordinaryPoints (normalizedConfiguration w) i)) ∧
      CombinatoriallyEquivalent P Q := by
  classical
  let p := vertexCoordinates P e
  let q := normalizedConfiguration w
  have hp : Spans p := vertexCoordinates_spans P e hP
  have hq : Spans q := normalizedConfiguration_spans w hw
    (spans_of_spanning_minor w C.spanningRows hC.1)
  have hpfirst : ∀ i, p i 0 = 1 := by intro i; rfl
  have hqfirst : ∀ i, q i 0 = 1 := normalizedConfiguration_first w hw
  have hf : ∀ T, FacetMask p T ↔ FacetMask q T := by
    intro T
    exact (hfacets T).trans ((C.facets_iff hC T).symm.trans
      (normalizedConfiguration_facets_iff w hw T).symm)
  have hequiv : LabelledPolytopeEquivalent p q :=
    ⟨actualFaceOrderIso_of_equal_facets p q hp hq hpfirst hqfirst hf,
      actualFaceOrderIso_preserves_labels p q hp hq hpfirst hqfirst hf⟩
  have hord : LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) (ordinaryPoints q) := by
    apply ordinary_equivalent_of_homogeneous
    simpa only [ordinaryVertexCoordinates_homogeneous,
      homogeneousPoints_ordinaryPoints q hqfirst] using hequiv
  obtain ⟨Q, φ, hvertices, _⟩ := actual_polytope_of_labelled_coordinates P e (ordinaryPoints q) hord
  exact ⟨Q, hvertices, ⟨φ⟩⟩

/-- The exact complete facet-family alternative gives the stated explicit
coordinate configuration, with the ordinary polytope face-order isomorphism. -/
theorem explicit_appendix_of_facets (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (h : HasAppendixFacetFamily P) : IsExplicitAppendixConfiguration P := by
  obtain ⟨a, lab, hfacets⟩ := h
  refine ⟨a, ?_⟩
  cases a with
  | type452 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Type452.coordinates
      Papers.RationalWitnesses.Type452.certificate
      Papers.RationalWitnesses.Type452.certificate_valid
      Papers.RationalWitnesses.Type452.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | type52 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Type52.coordinates
      Papers.RationalWitnesses.Type52.certificate
      Papers.RationalWitnesses.Type52.certificate_valid
      Papers.RationalWitnesses.Type52.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | type53 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Type53.coordinates
      Papers.RationalWitnesses.Type53.certificate
      Papers.RationalWitnesses.Type53.certificate_valid
      Papers.RationalWitnesses.Type53.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | type679 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Type679.coordinates
      Papers.RationalWitnesses.Type679.certificate
      Papers.RationalWitnesses.Type679.certificate_valid
      Papers.RationalWitnesses.Type679.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | type85 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Type85.coordinates
      Papers.RationalWitnesses.Type85.certificate
      Papers.RationalWitnesses.Type85.certificate_valid
      Papers.RationalWitnesses.Type85.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | typeA14 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.TypeA14.coordinates
      Papers.RationalWitnesses.TypeA14.certificate
      Papers.RationalWitnesses.TypeA14.certificate_valid
      Papers.RationalWitnesses.TypeA14.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | typeA73 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.TypeA73.coordinates
      Papers.RationalWitnesses.TypeA73.certificate
      Papers.RationalWitnesses.TypeA73.certificate_valid
      Papers.RationalWitnesses.TypeA73.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | typeD0 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.TypeD0.coordinates
      Papers.RationalWitnesses.TypeD0.certificate
      Papers.RationalWitnesses.TypeD0.certificate_valid
      Papers.RationalWitnesses.TypeD0.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | typeD4 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.TypeD4.coordinates
      Papers.RationalWitnesses.TypeD4.certificate
      Papers.RationalWitnesses.TypeD4.certificate_valid
      Papers.RationalWitnesses.TypeD4.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | fourprism =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Typefourprism.coordinates
      Papers.RationalWitnesses.Typefourprism.certificate
      Papers.RationalWitnesses.Typefourprism.certificate_valid
      Papers.RationalWitnesses.Typefourprism.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | twoprism0 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Typetwoprism0.coordinates
      Papers.RationalWitnesses.Typetwoprism0.certificate
      Papers.RationalWitnesses.Typetwoprism0.certificate_valid
      Papers.RationalWitnesses.Typetwoprism0.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T
  | twoprism2 =>
    apply polytope_of_certificate P lab hP Papers.RationalWitnesses.Typetwoprism2.coordinates
      Papers.RationalWitnesses.Typetwoprism2.certificate
      Papers.RationalWitnesses.Typetwoprism2.certificate_valid
      Papers.RationalWitnesses.Typetwoprism2.positive_first_coordinate
    intro T
    simpa only [appendixFacetFamily, Finset.mem_image, Finset.mem_univ,
      true_and, eq_comm] using hfacets T

theorem projection_or_explicit_appendix_of_target (P : ConvexPolytope 4)
    (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (j : Nat) (hj : j < Nonrational.TerminalData.targetCount)
    (hB : RealizesBoundary P lab (decode (Nonrational.TerminalData.targets j))) :
    SatisfiesProjectionCriterion P ∨ IsExplicitAppendixConfiguration P := by
  rcases projection_or_appendix_of_target P lab hP j hj hB with h | h
  · exact Or.inl h
  · exact Or.inr (explicit_appendix_of_facets P hP h)

#print axioms explicit_appendix_of_facets
#print axioms projection_or_explicit_appendix_of_target
end Nonrational.TerminalVerification
