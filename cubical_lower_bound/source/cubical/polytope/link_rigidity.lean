import cubical.polytope.square_stars
import cubical.polytope.vertex_slice_simplicial
import cubical.polytope.simplicial_rigidity

/-! # Generic rigidity of the actual vertex links of cubical polytopes -/

open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem IsCubical.neighborLink_genericallyRigid (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (v : VertexType P) :
    Cubical.Rigidity.GenericallyRigid (neighborLinkGraph v)
      (EuclideanSpace ℝ (Fin (P.dim - 1))) := by
  have hd1 : 1 ≤ P.dim := by omega
  let D : DatiFetta P v.val := Classical.choice (esiste_datiFetta P v.property hd1)
  have hd := D.politopo_dim_add_one (by omega)
  have hdimD : D.politopo.dim = P.dim - 1 := by omega
  have hs := D.isSimplicial_of_cubical hc (by omega)
  have hrigid := hs.genericallyRigid (H := EuclideanSpace ℝ (Fin (P.dim - 1)))
    D.politopo (by omega) (by simp [hdimD])
  exact hrigid.of_iso D.neighborGraphIso.symm

end LeanEval.Geometry.PlatonicClassification
