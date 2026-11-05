module
public import Papers.RawWitnesses.Type52
public import Papers.IntegerFacetRawBridge
public import Papers.IntegerFacetRealization
public import Papers.RawWitnesses.Type53
public import Papers.RawWitnesses.Type679
public import Papers.RawWitnesses.Type85
public import Papers.RawWitnesses.TypeD0
public import Papers.RawWitnesses.TypeD4
public import Papers.RawWitnesses.Type452
public import Papers.RawWitnesses.TypeA14
public import Papers.RawWitnesses.TypeA73
public import Papers.RawWitnesses.Typefourprism
public import Papers.RawWitnesses.Typetwoprism0
public import Papers.RawWitnesses.Typetwoprism2

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/Witnesses/Type52.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Type52

def coordinates : IntegerConfiguration 10 := RawWitnesses.Type52.coordinates

def certificate : FacetCertificate 10 11 6 18 :=
  RawWitnesses.Type52.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Type52.certificate.valid_toFacetCertificate
    RawWitnesses.Type52.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Type52.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Type52.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Type52

end
end BundlePart0

section BundlePart1
/- Source: Papers/Witnesses/Type52Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.Type52

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Type52

end
end BundlePart1

section BundlePart2
/- Source: Papers/Witnesses/Type53.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Type53

def coordinates : IntegerConfiguration 10 := RawWitnesses.Type53.coordinates

def certificate : FacetCertificate 10 11 7 20 :=
  RawWitnesses.Type53.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Type53.certificate.valid_toFacetCertificate
    RawWitnesses.Type53.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Type53.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Type53.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Type53

end
end BundlePart2

section BundlePart3
/- Source: Papers/Witnesses/Type53Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.Type53

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Type53

end
end BundlePart3

section BundlePart4
/- Source: Papers/Witnesses/Type679.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Type679

def coordinates : IntegerConfiguration 10 := RawWitnesses.Type679.coordinates

def certificate : FacetCertificate 10 13 1 23 :=
  RawWitnesses.Type679.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Type679.certificate.valid_toFacetCertificate
    RawWitnesses.Type679.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Type679.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Type679.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Type679

end
end BundlePart4

section BundlePart5
/- Source: Papers/Witnesses/Type679Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.Type679

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Type679

end
end BundlePart5

section BundlePart6
/- Source: Papers/Witnesses/Type85.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Type85

def coordinates : IntegerConfiguration 10 := RawWitnesses.Type85.coordinates

def certificate : FacetCertificate 10 12 3 22 :=
  RawWitnesses.Type85.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Type85.certificate.valid_toFacetCertificate
    RawWitnesses.Type85.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Type85.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Type85.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Type85

end
end BundlePart6

section BundlePart7
/- Source: Papers/Witnesses/Type85Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.Type85

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Type85

end
end BundlePart7

section BundlePart8
/- Source: Papers/Witnesses/TypeD0.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.TypeD0

def coordinates : IntegerConfiguration 10 := RawWitnesses.TypeD0.coordinates

def certificate : FacetCertificate 10 15 3 25 :=
  RawWitnesses.TypeD0.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.TypeD0.certificate.valid_toFacetCertificate
    RawWitnesses.TypeD0.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.TypeD0.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.TypeD0.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.TypeD0

end
end BundlePart8

section BundlePart9
/- Source: Papers/Witnesses/TypeD0Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.TypeD0

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.TypeD0

end
end BundlePart9

section BundlePart10
/- Source: Papers/Witnesses/TypeD4.lean -/




@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.TypeD4

def coordinates : IntegerConfiguration 10 := RawWitnesses.TypeD4.coordinates

def certificate : FacetCertificate 10 15 3 25 :=
  RawWitnesses.TypeD4.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.TypeD4.certificate.valid_toFacetCertificate
    RawWitnesses.TypeD4.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.TypeD4.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.TypeD4.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.TypeD4

end
end BundlePart10

section BundlePart11
/- Source: Papers/Witnesses/TypeD4Realization.lean -/




@[expose] public section

namespace Papers.RationalWitnesses.TypeD4

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.TypeD4

end
end BundlePart11

section BundlePart12
/- Source: Papers/Witnesses/Type452.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Type452

def coordinates : IntegerConfiguration 10 := RawWitnesses.Type452.coordinates

def certificate : FacetCertificate 10 16 1 26 :=
  RawWitnesses.Type452.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Type452.certificate.valid_toFacetCertificate
    RawWitnesses.Type452.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Type452.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Type452.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Type452

end
end BundlePart12

section BundlePart13
/- Source: Papers/Witnesses/Type452Realization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.Type452

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Type452

end
end BundlePart13

section BundlePart14
/- Source: Papers/Witnesses/TypeA14.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.TypeA14

def coordinates : IntegerConfiguration 10 := RawWitnesses.TypeA14.coordinates

def certificate : FacetCertificate 10 15 0 24 :=
  RawWitnesses.TypeA14.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.TypeA14.certificate.valid_toFacetCertificate
    RawWitnesses.TypeA14.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.TypeA14.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.TypeA14.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.TypeA14

end
end BundlePart14

section BundlePart15
/- Source: Papers/Witnesses/TypeA14Realization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.TypeA14

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.TypeA14

end
end BundlePart15

section BundlePart16
/- Source: Papers/Witnesses/TypeA73.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.TypeA73

def coordinates : IntegerConfiguration 10 := RawWitnesses.TypeA73.coordinates

def certificate : FacetCertificate 10 14 0 21 :=
  RawWitnesses.TypeA73.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.TypeA73.certificate.valid_toFacetCertificate
    RawWitnesses.TypeA73.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.TypeA73.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.TypeA73.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.TypeA73

end
end BundlePart16

section BundlePart17
/- Source: Papers/Witnesses/TypeA73Realization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.TypeA73

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.TypeA73

end
end BundlePart17

section BundlePart18
/- Source: Papers/Witnesses/Typefourprism.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Typefourprism

def coordinates : IntegerConfiguration 10 := RawWitnesses.Typefourprism.coordinates

def certificate : FacetCertificate 10 12 9 20 :=
  RawWitnesses.Typefourprism.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Typefourprism.certificate.valid_toFacetCertificate
    RawWitnesses.Typefourprism.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Typefourprism.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Typefourprism.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Typefourprism

end
end BundlePart18

section BundlePart19
/- Source: Papers/Witnesses/TypefourprismRealization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.Typefourprism

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Typefourprism

end
end BundlePart19

section BundlePart20
/- Source: Papers/Witnesses/Typetwoprism0.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Typetwoprism0

def coordinates : IntegerConfiguration 10 := RawWitnesses.Typetwoprism0.coordinates

def certificate : FacetCertificate 10 14 5 23 :=
  RawWitnesses.Typetwoprism0.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Typetwoprism0.certificate.valid_toFacetCertificate
    RawWitnesses.Typetwoprism0.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Typetwoprism0.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Typetwoprism0.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Typetwoprism0

end
end BundlePart20

section BundlePart21
/- Source: Papers/Witnesses/Typetwoprism0Realization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.Typetwoprism0

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Typetwoprism0

end
end BundlePart21

section BundlePart22
/- Source: Papers/Witnesses/Typetwoprism2.lean -/





@[expose] public section

/-! Exact Mathlib interpretation of the same integer data. There is no second
coordinate table and no unproved connection to the finite checks. -/

namespace Papers.RationalWitnesses.Typetwoprism2

def coordinates : IntegerConfiguration 10 := RawWitnesses.Typetwoprism2.coordinates

def certificate : FacetCertificate 10 14 5 24 :=
  RawWitnesses.Typetwoprism2.certificate.toFacetCertificate

theorem certificate_valid : certificate.Valid coordinates :=
  RawWitnesses.Typetwoprism2.certificate.valid_toFacetCertificate
    RawWitnesses.Typetwoprism2.certificate_valid

theorem spanning_check : (coordinates.submatrix certificate.spanningRows id).det ≠ 0 :=
  certificate_valid.1

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  certificate_valid.2.1

theorem low_ranks_check : ∀ k, (certificate.lowRanks k).Valid coordinates :=
  certificate_valid.2.2.1

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  certificate_valid.2.2.2.1

theorem coverage_check : ∀ T : Finset (Fin 10),
    (∃ k, T = (certificate.facets k).vertices) ∨
    T.card ≤ 3 ∨ T = Finset.univ ∨
    (∃ k, T ⊆ (certificate.lowRanks k).vertices) ∨
    ∃ k, RelationExcludes (certificate.relations k) T :=
  certificate_valid.2.2.2.2

theorem positive_first_coordinate : ∀ i, 0 < coordinates i 0 :=
  RawWitnesses.Typetwoprism2.positive_first_coordinate

theorem facet_separation : ∀ i j : Fin 10, i ≠ j →
    ∃ k, i ∈ (certificate.facets k).vertices ∧ j ∉ (certificate.facets k).vertices := by
  intro i j hij
  obtain ⟨k, hi, hj⟩ := RawWitnesses.Typetwoprism2.facet_separation i j hij
  refine ⟨k, (Raw.mem_maskFinset _ _).mpr hi, ?_⟩
  intro h
  exact hj ((Raw.mem_maskFinset _ _).mp h)

end Papers.RationalWitnesses.Typetwoprism2

end
end BundlePart22

section BundlePart23
/- Source: Papers/Witnesses/Typetwoprism2Realization.lean -/





@[expose] public section

namespace Papers.RationalWitnesses.Typetwoprism2

open Papers.RationalityTen.ChirotopeDensity
open LeanEval.Geometry.PlatonicClassification

theorem facets_exact (T : Finset (Fin 10)) :
    FacetMask (realConfiguration coordinates) T ↔
      ∃ k, T = (certificate.facets k).vertices :=
  certificate.facets_iff certificate_valid T

theorem rationallyRealizable (P : ConvexPolytope 4) (e : Fin 10 ≃ P.vertices)
    (hP : P.IsFullDim)
    (hfacets : ∀ T : Finset (Fin 10),
      FacetMask (vertexCoordinates P e) T ↔ ∃ k, T = (certificate.facets k).vertices) :
    Papers.Polytopes.RationallyRealizable P :=
  rationallyRealizable_of_certificate P e hP coordinates certificate
    certificate_valid positive_first_coordinate hfacets

end Papers.RationalWitnesses.Typetwoprism2

end
end BundlePart23
