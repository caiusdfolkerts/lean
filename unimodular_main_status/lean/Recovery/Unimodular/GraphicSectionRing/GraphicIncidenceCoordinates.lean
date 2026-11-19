module

public import Recovery.Unimodular.GraphicSectionRing.GraphicIncidenceLattice
public import Recovery.Unimodular.GraphicSectionRing.IntegralDualCoordinates
public import Recovery.Unimodular.GraphicSectionRing.GraphicFanCoordinates

/-!
# Arbitrary integral graphic configurations give the paper's difference normals

The input is an integral isomorphism with the literal integer span of the
incidence columns of an arbitrary finite graph. The rooted coordinates,
dimension equality, and contragredient character coordinates are all derived.
No connectedness, spanning-tree choice, or coordinate-normal hypothesis is added.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open Unimodular.GraphicRootedLattice Unimodular.GraphicSectionRing
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} (F : SmoothCompleteFan n) {V : Type*} [Fintype V]

/-- An actual integral graphic realization, in the original graph vertex
lattice and the actual integer span of its directed incidence columns. -/
structure IntegralGraphicPresentation (G : SimpleGraph V) where
  equiv : Lattice n ≃ₗ[ℤ] incidenceSpan G
  source : F.rays → V
  target : F.rays → V
  adjacent : ∀ v, G.Adj (source v) (target v)
  ray_image : ∀ v, (equiv v.val).val = edge (source v) (target v)

namespace IntegralGraphicPresentation
variable {F} {G : SimpleGraph V} (P : F.IntegralGraphicPresentation G)

abbrev Index := FreeVertex G.connectedComponentMk (graphRoot G)

 def rawCoordinates : Lattice n ≃ₗ[ℤ] (Index (G := G) → ℤ) :=
  P.equiv.trans (incidenceCoordinates G)

include P in
 theorem index_card : Fintype.card (Index (G := G)) = n := by
  have h := integral_coordinate_card P.rawCoordinates
  simpa only [Fintype.card_fin] using h.symm

 def indexEquiv : Index (G := G) ≃ Fin n :=
  Fintype.equivOfCardEq (by rw [P.index_card, Fintype.card_fin])

 def vertexIndex (v : V) : Coordinate n :=
  (vertexCoordinate G.connectedComponentMk (graphRoot G) v).map P.indexEquiv

 def rayCoordinates : Lattice n ≃ₗ[ℤ] Lattice n :=
  P.rawCoordinates.trans (LinearEquiv.funCongrLeft ℤ ℤ P.indexEquiv.symm)

 theorem rawCoordinates_apply (x : Lattice n) (i : Index (G := G)) :
    P.rawCoordinates x i = (P.equiv x).val i.val := by
  simp only [rawCoordinates, incidenceCoordinates, LinearEquiv.trans_apply,
    coordinates_apply, LinearEquiv.coe_ofEq_apply]

 theorem rawCoordinates_ray (v : F.rays) :
    P.rawCoordinates v.val =
      coordinateVertex G.connectedComponentMk (graphRoot G)
        (vertexCoordinate G.connectedComponentMk (graphRoot G) (P.source v)) -
      coordinateVertex G.connectedComponentMk (graphRoot G)
        (vertexCoordinate G.connectedComponentMk (graphRoot G) (P.target v)) := by
  ext i
  rw [P.rawCoordinates_apply, P.ray_image]
  have h := coordinates_edge G.connectedComponentMk (graphRoot G) (graphRoot_component G)
    (SimpleGraph.ConnectedComponent.sound (P.adjacent v).reachable)
  exact congrFun h i

 theorem coordinateVertex_reindex (i : Option (Index (G := G))) :
    LinearEquiv.funCongrLeft ℤ ℤ P.indexEquiv.symm
        (coordinateVertex G.connectedComponentMk (graphRoot G) i) =
      coordinateNormal (i.map P.indexEquiv) := by
  cases i with
  | none => rfl
  | some i =>
    ext j
    change (Pi.single i (1 : ℤ) : Index (G := G) → ℤ) (P.indexEquiv.symm j) =
      (Pi.single (P.indexEquiv i) (1 : ℤ) : Fin n → ℤ) j
    simp [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

/-- The original primitive ray vectors are transformed, not replaced. -/
theorem rayCoordinates_ray (v : F.rays) :
    P.rayCoordinates v.val = coordinateNormal (P.vertexIndex (P.source v)) -
      coordinateNormal (P.vertexIndex (P.target v)) := by
  simp only [rayCoordinates, LinearEquiv.trans_apply, P.rawCoordinates_ray, map_sub,
    P.coordinateVertex_reindex, vertexIndex]

/-- The inverse transpose provides the exact character pairings required
by the checked geometric section-ring theorem. -/
def graphicCoordinates : F.GraphicCoordinates where
  equiv := dualCoordinates P.rayCoordinates
  left v := P.vertexIndex (P.target v)
  right v := P.vertexIndex (P.source v)
  pairing v m := by
    change dotProduct v.val m = _
    rw [dualCoordinates_pairing P.rayCoordinates, P.rayCoordinates_ray,
      differenceNormal_pairing]
    unfold difference
    ring

#print axioms index_card
#print axioms rayCoordinates_ray
#print axioms graphicCoordinates

end IntegralGraphicPresentation
end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.IntegralGraphicPresentation.graphicCoordinates
