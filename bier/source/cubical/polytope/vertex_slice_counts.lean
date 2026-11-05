import cubical.polytope.vertex_slice
import cubical.polytope.face_incidence
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Geometric vertex-figure dimension and face incidence counts -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

/-- Positive-dimensional faces incident to a specified geometric vertex. -/
abbrev PositiveFaceStar (P : ConvexPolytope n) (v : VertexType P) :=
  {F : FaceType P // v.val ∈ F.val ∧ 1 ≤ faceDim F.val}

instance positiveFaceStarFintype (P : ConvexPolytope n) (v : VertexType P) :
    Fintype (PositiveFaceStar P v) := Fintype.ofFinite _

namespace DatiFetta

variable {v : VertexType P} (D : DatiFetta P v.val)

def sliceFace (F : PositiveFaceStar P v) : FaceType D.politopo :=
  ⟨F.val.val ∩ {x | D.l x = D.c}, D.faccia_fetta F.val.property F.property.1 F.property.2⟩

theorem sliceFace_injective : Function.Injective D.sliceFace := by
  intro F G h
  have hset : F.val.val ∩ {x | D.l x = D.c} = G.val.val ∩ {x | D.l x = D.c} :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  exact Set.Subset.antisymm
    (D.fetta_mono F.val.property F.property.1 G.val.property G.property.1 hset.subset)
    (D.fetta_mono G.val.property G.property.1 F.val.property F.property.1 hset.symm.subset)

theorem sliceFace_surjective : Function.Surjective D.sliceFace := by
  intro G
  obtain ⟨F, hF, hvF, hdF, hslice⟩ := D.faccia_dalla_fetta G.property
  exact ⟨⟨⟨F, hF⟩, hvF, hdF⟩, Subtype.ext hslice⟩

/-- The complete face correspondence for the actual hyperplane slice. -/
def sliceFaceOrderIso : PositiveFaceStar P v ≃o FaceType D.politopo where
  __ := Equiv.ofBijective D.sliceFace ⟨D.sliceFace_injective, D.sliceFace_surjective⟩
  map_rel_iff' := by
    intro F G
    constructor
    · exact D.fetta_mono F.val.property F.property.1 G.val.property G.property.1
    · intro h x hx
      exact ⟨h hx.1, hx.2⟩

@[simp] theorem sliceFaceOrderIso_val (F : PositiveFaceStar P v) :
    (D.sliceFaceOrderIso F).val = F.val.val ∩ {x | D.l x = D.c} := rfl

theorem sliceFaceOrderIso_dimension (F : PositiveFaceStar P v) :
    faceDim (D.sliceFaceOrderIso F).val + 1 = faceDim F.val.val :=
  D.fetta_faceDim F.val.property F.property.1 F.property.2

/-- A vertex figure has intrinsic dimension one less than its polytope. -/
theorem politopo_dim_add_one (hdim : 1 ≤ P.dim) : D.politopo.dim + 1 = P.dim := by
  have hvP : v.val ∈ P.toSet := subset_convexHull ℝ _ v.property
  have hdim' := D.fetta_faceDim (toSet_isFace P) hvP hdim
  rw [← D.politopo_toSet] at hdim'
  exact hdim'

def incidentFaceSliceEquiv (i : ℕ) :
    IncidentFaceType P v (i + 1) ≃ DimFaceType D.politopo i := by
  let e : IncidentFaceType P v (i + 1) ≃
      {F : PositiveFaceStar P v // faceDim F.val.val = i + 1} :=
    { toFun := fun F => ⟨⟨F.val, F.property.2, by omega⟩, F.property.1⟩
      invFun := fun F => ⟨F.val.val, F.property, F.val.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans (D.sliceFaceOrderIso.toEquiv.subtypeEquiv ?_)
  intro F
  have hdim := D.sliceFaceOrderIso_dimension F
  change faceDim F.val.val = i + 1 ↔ faceDim (D.sliceFaceOrderIso F).val = i
  omega

/-- Every face of a vertex figure corresponds to exactly one incident face
of the original polytope, with dimension increased by one. -/
theorem faceNumber_eq_incidentFaceNumber (i : ℕ) :
    faceNumber D.politopo i = incidentFaceNumber P v (i + 1) := by
  rw [← card_dimFaceType]
  exact (Fintype.card_congr (D.incidentFaceSliceEquiv i)).symm

theorem vertices_card_eq_degree :
    D.politopo.vertices.card = (polytopeGraph P).degree v := by
  have h := Fintype.card_congr D.neighborEquiv
  change Fintype.card ((polytopeGraph P).neighborSet v) =
    Fintype.card (VertexType D.politopo) at h
  rw [SimpleGraph.card_neighborSet_eq_degree] at h
  simpa [VertexType] using h.symm

end DatiFetta

/-- Sum all vertex-figure face numbers by double-counting geometric incidences. -/
theorem sum_vertexFigure_faceNumber (D : (v : VertexType P) → DatiFetta P v.val) (i : ℕ) :
    ∑ v : VertexType P, faceNumber (D v).politopo i =
      ∑ F : DimFaceType P (i + 1), (facePolytope P F.val.property).vertices.card := by
  simp_rw [DatiFetta.faceNumber_eq_incidentFaceNumber]
  exact sum_incidentFaceNumber P (i + 1)

theorem sum_vertexFigure_faceNumber_of_uniform_vertices
    (D : (v : VertexType P) → DatiFetta P v.val) (i k : ℕ)
    (hvertices : ∀ F : DimFaceType P (i + 1),
      (facePolytope P F.val.property).vertices.card = k) :
    ∑ v : VertexType P, faceNumber (D v).politopo i = faceNumber P (i + 1) * k := by
  simp_rw [DatiFetta.faceNumber_eq_incidentFaceNumber]
  exact sum_incidentFaceNumber_of_uniform_vertices P (i + 1) k hvertices

end LeanEval.Geometry.PlatonicClassification
