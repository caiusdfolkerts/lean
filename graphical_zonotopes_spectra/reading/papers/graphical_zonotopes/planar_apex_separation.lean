module

public import Papers.GraphicalZonotopes.PlanarApexArc
public import Papers.GraphicalZonotopes.ArcK5Geometry
public import Papers.GraphicalZonotopes.ThreeTreeTriangleApex

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a genuinely drawn planar graph, two distinct apices on one triangle
lie in different components after deleting that triangle. The proof constructs
a K₅ configuration from any alleged avoiding path and uses the complete
Jordan-separation obstruction for arbitrary continuous arcs. -/
theorem HasPlaneDrawing.triangle_apex_separated {G : SimpleGraph V}
    (hG : HasPlaneDrawing G) : TriangleApexSeparated G := by
  intro T hT hcT u w hu hw huw huAdj hwAdj hreach
  obtain ⟨x,P,hK5⟩ := hG.arcK5_of_triangle_apex_path
    T hT hcT u w hu hw huw huAdj hwAdj hreach
  exact hK5.elim

end GraphicalZonotopes
