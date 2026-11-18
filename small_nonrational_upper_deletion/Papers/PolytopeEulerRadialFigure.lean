module

public import Papers.PolytopeBasicExtreme

public import Papers.ActualVertexFigureGraph
public import Papers.PolytopeBalinski
public import Papers.RationalityTenPolygonMorseGraph

@[expose] public section

/-!
# The radial vertex figure used in the Euler argument

The order isomorphism is built from the actual section
D.politopo; its vertex map is proved to be D.attra. Thus a height sign at
a neighbor is transported by a strictly positive scalar, not inferred
from an arbitrary combinatorial vertex figure.
-/

noncomputable section

namespace Papers.PolytopeEulerRadialFigure

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeBalinski Papers.PolytopeVertexCone
open scoped Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : E n}

@[reducible] def toGaloisData (D : DatiFetta P v) :
    VertexFigureGaloisData P P.toSet v := by
  choose Finv hFinvF hFinvV hFinvD hFinvS using
    fun G : PolytopeFace D.politopo => D.faccia_dalla_fetta G.isFace
  refine
    { figure := D.politopo
      faceEquiv :=
        { toFun := fun F =>
            ⟨F.carrier ∩ {z | D.l z = D.c},
              D.faccia_fetta F.isFace F.mem_vertex F.dim_pos⟩
          invFun := fun G =>
            ⟨Finv G, hFinvF G, face_subset_toSet P (hFinvF G),
              hFinvV G, hFinvD G⟩
          left_inv := ?_
          right_inv := ?_ }
      map_subset_iff := ?_
      map_dim := ?_ }
  · intro F
    apply PositiveVertexStarFace.ext
    have hs := hFinvS
      ⟨F.carrier ∩ {z | D.l z = D.c},
        D.faccia_fetta F.isFace F.mem_vertex F.dim_pos⟩
    exact Set.Subset.antisymm
      (D.fetta_mono (hFinvF _) (hFinvV _) F.isFace F.mem_vertex hs.subset)
      (D.fetta_mono F.isFace F.mem_vertex (hFinvF _) (hFinvV _) hs.symm.subset)
  · intro G
    apply PolytopeFace.ext
    exact hFinvS G
  · intro F G
    constructor
    · intro h z hz
      exact ⟨h hz.1, hz.2⟩
    · exact D.fetta_mono F.isFace F.mem_vertex G.isFace G.mem_vertex
  · intro F
    exact D.fetta_faceDim F.isFace F.mem_vertex F.dim_pos

@[simp] theorem toGaloisData_figure (D : DatiFetta P v) :
    (toGaloisData D).figure = D.politopo := rfl

@[simp] theorem toGaloisData_face (D : DatiFetta P v)
    (F : PositiveVertexStarFace P P.toSet v) :
    ((toGaloisData D).faceEquiv F).carrier =
      F.carrier ∩ {z | D.l z = D.c} := rfl

theorem neighborImage_eq_attra (D : DatiFetta P v)
    (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    (neighborImage (toGaloisData D) D.hv y).val = D.attra y.val := by
  have hstep := neighbor_step P v y
  have hyc : D.l y.val < D.c := D.hsep y.val hstep.1 hstep.2.1.symm
  have hmem : D.attra y.val ∈
      ((toGaloisData D).faceEquiv (neighborStarFace P D.hv y)).carrier := by
    rw [toGaloisData_face]
    exact ⟨D.attra_mem_segment hyc, D.attra_level hyc⟩
  rw [neighborImage_face] at hmem
  exact (Set.mem_singleton_iff.mp hmem).symm

theorem neighborImage_height_difference (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L (neighborImage (toGaloisData D) D.hv y).val - L v =
      ((D.l v - D.c) / (D.l v - D.l y.val)) * (L y.val - L v) := by
  rw [neighborImage_eq_attra, ← map_sub, D.attra_sub]
  simp only [map_smul, map_sub, smul_eq_mul]

theorem neighborImage_height_lt_iff (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L (neighborImage (toGaloisData D) D.hv y).val < L v ↔ L y.val < L v := by
  have hstep := neighbor_step P v y
  have hτ := D.tau_pos (D.hsep y.val hstep.1 hstep.2.1.symm)
  rw [← sub_neg, neighborImage_height_difference]
  constructor
  · intro h
    have : L y.val - L v < 0 := by nlinarith
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hτ (sub_neg.mpr h)

theorem neighborImage_height_gt_iff (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L v < L (neighborImage (toGaloisData D) D.hv y).val ↔ L v < L y.val := by
  have hstep := neighbor_step P v y
  have hτ := D.tau_pos (D.hsep y.val hstep.1 hstep.2.1.symm)
  rw [← sub_pos, neighborImage_height_difference, mul_pos_iff_of_pos_left hτ, sub_pos]

def lowerNeighborEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ) :
    {y : Papers.PolytopeVertexCone.actualNeighbors P v // L y.val < L v} ≃
      {q : D.politopo.vertices // L q.val < L v} where
  toFun y := ⟨neighborEquiv (toGaloisData D) D.hv y.val,
    (neighborImage_height_lt_iff D L y.val).mpr y.property⟩
  invFun q := ⟨(neighborEquiv (toGaloisData D) D.hv).symm q.val, by
    apply (neighborImage_height_lt_iff D L _).mp
    change L ((neighborEquiv (toGaloisData D) D.hv)
      ((neighborEquiv (toGaloisData D) D.hv).symm q.val)).val < L v
    simpa using q.property⟩
  left_inv y := Subtype.ext ((neighborEquiv (toGaloisData D) D.hv).left_inv y.val)
  right_inv q := Subtype.ext ((neighborEquiv (toGaloisData D) D.hv).right_inv q.val)

theorem figure_dim_two (D : DatiFetta P v) (hdim : P.dim = 3) :
    D.politopo.dim = 2 := by
  have hpos : 1 ≤ faceDim P.toSet := by
    change 1 ≤ P.dim
    omega
  have hh := D.fetta_faceDim (toSet_isFace P)
    (Papers.PolytopeBasicExtreme.vertex_mem_body P D.hv) hpos
  rw [← D.politopo_toSet] at hh
  change D.politopo.dim + 1 = P.dim at hh
  omega

end Papers.PolytopeEulerRadialFigure
