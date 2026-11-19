module

public import RawGraphGrowthFrames
public import LiteralGraphGrowthRenaming
public import TenGraphTriangleSemantics

@[expose] public section

/-!
# Checked raw records supply complete graph-growth renamings

The only data are a vertex permutation and a cell permutation. Their inverse
laws, exact cell images, and graph invariance are checked by the pure Boolean
tests. The ridge and unordered-pair maps are derived from that same vertex
permutation. Compatibility invariance follows from the complete decoded cells.
-/

noncomputable section
namespace Papers.RationalityTen.CheckedGraphGrowthFrames

open Finset
open GrowthRenaming RawBoundaryMatch RawGraphGrowthFrames
open LiteralMaskGeometry LiteralGraphGrowthRenaming
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open GraphGrowthConstraints
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeFaceCounting Papers.PolytopeBoundaryIncidence

def bijectionEquiv {α : Type} (p : Bijection α) : Equiv.Perm α where
  toFun := p.forward
  invFun := p.inverse
  left_inv := p.left_inverse
  right_inv := p.right_inverse

def equivBijection {α : Type} (p : Equiv.Perm α) : Bijection α where
  forward := p
  inverse := p.symm
  left_inverse := p.symm_apply_apply
  right_inverse := p.apply_symm_apply

def ridgeBijection (p : Bijection (Fin 10)) : Bijection (Fin 1024) :=
  equivBijection
    ((maskEquiv.trans (Equiv.finsetCongr (bijectionEquiv p))).trans maskEquiv.symm)

theorem ridgeBijection_geometry (p : Bijection (Fin 10)) (q : Fin 1024) :
    maskSet ((ridgeBijection p).forward q).val =
      (maskSet q.val).image (bijectionEquiv p) := by
  change maskEquiv
      (maskEquiv.symm ((maskEquiv q).map (bijectionEquiv p).toEmbedding)) = _
  rw [maskEquiv.apply_symm_apply, Finset.map_eq_image]
  rfl

theorem maskSet_rename (p : Bijection (Fin 10)) (mask : Nat) :
    maskSet (renameMask p.forward mask) = (maskSet mask).image (bijectionEquiv p) := by
  ext a
  constructor
  · intro ha
    have hbit := (mem_maskSet _ _).mp ha
    refine Finset.mem_image.mpr ⟨p.inverse a, ?_, p.right_inverse a⟩
    apply (mem_maskSet _ _).mpr
    have h := renameMask_bit p mask (p.inverse a)
    rw [p.right_inverse] at h
    exact h.symm.trans hbit
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    apply (mem_maskSet _ _).mpr
    exact (renameMask_bit p mask b).trans ((mem_maskSet _ _).mp hb)

theorem maskFamily_rename (p : Bijection (Fin 10)) (L : List Nat) :
    (L.map (renameMask p.forward)).toFinset.image maskSet =
      (L.toFinset.image maskSet).image (fun S => S.image (bijectionEquiv p)) := by
  ext S
  constructor
  · intro hS
    obtain ⟨mask, hm, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact Finset.mem_image.mpr ⟨maskSet a,
      Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, rfl⟩,
      (maskSet_rename p a).symm⟩
  · intro hS
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_image.mpr ⟨renameMask p.forward a,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩),
      maskSet_rename p a⟩

theorem cellRelabelCheck_decode (p : Bijection (Fin 10))
    (A B : ConcreteGrowth.Cell) (h : cellRelabelCheck p.forward A B = true) :
    decodeCell B = mapCell (bijectionEquiv p).toEmbedding (decodeCell A) := by
  obtain ⟨_, hv, he, hr⟩ := cellRelabelCheck_sound _ _ _ h
  have hedges : (A.edges.map (renameMask p.forward)).toFinset = B.edges.toFinset := by
    ext m
    simpa only [List.mem_toFinset] using he m
  have hridges : (A.ridgeMasks.map (renameMask p.forward)).toFinset =
      B.ridgeMasks.toFinset := by
    ext m
    simpa only [List.mem_toFinset] using hr m
  apply cell_ext
  · change maskSet B.vertices = (maskSet A.vertices).image (bijectionEquiv p)
    rw [hv, maskSet_rename]
  · change B.edges.toFinset.image maskSet =
      (A.edges.toFinset.image maskSet).image (fun S => S.image (bijectionEquiv p))
    rw [← hedges, maskFamily_rename]
  · change B.ridgeMasks.toFinset.image maskSet =
      (A.ridgeMasks.toFinset.image maskSet).image (fun S => S.image (bijectionEquiv p))
    rw [← hridges, maskFamily_rename]

theorem edgeBijection_geometry (p : Bijection (Fin 10)) (q : Fin 45) :
    maskSet (TenGraphEdges.edgeMask ((TenGraphEdges.edgeBijection p).forward q)) =
      (maskSet (TenGraphEdges.edgeMask q)).image (bijectionEquiv p) := by
  ext a
  constructor
  · intro ha
    have hbit := (TenGraphTriangleSemantics.pair_membership _ _).mp ha
    refine Finset.mem_image.mpr ⟨p.inverse a, ?_, p.right_inverse a⟩
    apply (TenGraphTriangleSemantics.pair_membership _ _).mpr
    have h := TenGraphEdges.edgeMap_incidence p q (p.inverse a)
    rw [p.right_inverse] at h
    exact h.symm.trans hbit
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    apply (TenGraphTriangleSemantics.pair_membership _ _).mpr
    exact (TenGraphEdges.edgeMap_incidence p q b).trans
      ((TenGraphTriangleSemantics.pair_membership _ _).mp hb)

/-- Pointwise checked records construct the semantic frame. The checks are
split into bounded intervals by concrete certificates; no giant aggregate
decision procedure is part of this constructor. -/
def checkedFrame {n k : Nat} (D : Problem n 1024 45 10 k)
    (cells : Fin n → ConcreteGrowth.Cell)
    (vertexForward vertexInverse : Nat)
    (hvertices : TenGraphEdges.permutationCheck vertexForward vertexInverse = true)
    (forward inverse : Fin n → Fin n)
    (hinverse : ∀ i, inverseCheckAt forward inverse i = true)
    (hcells : ∀ i, cellRelabelCheck (TenGraphEdges.vertexMap vertexForward)
      (cells i) (cells (forward i)) = true)
    (hgraph : ∀ q, graphCheckAt D.requiredEdges
      (TenGraphEdges.vertexMap vertexForward) q = true) : Frame D cells := by
  let p := TenGraphEdges.checkedBijection vertexForward vertexInverse hvertices
  exact
    { vertices := bijectionEquiv p
      cellMap := checkedCellBijection forward inverse hinverse
      ridgeMap := ridgeBijection p
      featureMap := TenGraphEdges.edgeBijection p
      cell_geometry := fun i => cellRelabelCheck_decode p _ _ (hcells i)
      ridge_geometry := ridgeBijection_geometry p
      feature_geometry := edgeBijection_geometry p
      kind_preserved := fun i => (cellRelabelCheck_sound _ _ _ (hcells i)).1
      graph_preserved := fun q => of_decide_eq_true (hgraph q) }

def identityBijection {α : Type} : Bijection α where
  forward := id
  inverse := id
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl

/-- Apply the first map and then the second map. -/
def composeBijection {α : Type} (first second : Bijection α) : Bijection α where
  forward a := second.forward (first.forward a)
  inverse a := first.inverse (second.inverse a)
  left_inverse a := by rw [second.left_inverse, first.left_inverse]
  right_inverse a := by rw [first.right_inverse, second.right_inverse]

theorem mapCell_composition (first second : Equiv.Perm (Fin 10)) (C : Cell 10) :
    mapCell second.toEmbedding (mapCell first.toEmbedding C) =
      mapCell (first.trans second).toEmbedding C := by
  apply cell_ext <;>
    simp only [mapCell, Finset.image_image, Equiv.coe_toEmbedding,
      Equiv.coe_trans, Function.comp_def]

def identityFrame {n k : Nat} (D : Problem n 1024 45 10 k)
    (cells : Fin n → ConcreteGrowth.Cell) : Frame D cells where
  vertices := Equiv.refl _
  cellMap := identityBijection
  ridgeMap := identityBijection
  featureMap := identityBijection
  cell_geometry i := by
    apply cell_ext <;> simp [identityBijection, mapCell,
      Function.Embedding.coe_refl, Finset.image_id']
  ridge_geometry q := by simp only [Equiv.coe_refl, Finset.image_id]; rfl
  feature_geometry q := by simp only [Equiv.coe_refl, Finset.image_id]; rfl
  kind_preserved _ := rfl
  graph_preserved _ := rfl

/-- Compose verified generators without replaying their geometric cell
records. All ridge, pair, graph and compatibility semantics are retained. -/
def composeFrame {n k : Nat} {D : Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (first second : Frame D cells) :
    Frame D cells where
  vertices := first.vertices.trans second.vertices
  cellMap := composeBijection first.cellMap second.cellMap
  ridgeMap := composeBijection first.ridgeMap second.ridgeMap
  featureMap := composeBijection first.featureMap second.featureMap
  cell_geometry i := by
    change decodeCell (cells (second.cellMap.forward (first.cellMap.forward i))) = _
    rw [second.cell_geometry, first.cell_geometry, mapCell_composition]
  ridge_geometry q := by
    change maskSet (second.ridgeMap.forward (first.ridgeMap.forward q)).val = _
    rw [second.ridge_geometry, first.ridge_geometry, Finset.image_image]
    rfl
  feature_geometry q := by
    change maskSet (TenGraphEdges.edgeMask
      (second.featureMap.forward (first.featureMap.forward q))) = _
    rw [second.feature_geometry, first.feature_geometry, Finset.image_image]
    rfl
  kind_preserved i := by
    change (cells (second.cellMap.forward (first.cellMap.forward i))).kind = _
    rw [second.kind_preserved, first.kind_preserved]
  graph_preserved q := by
    change D.requiredEdges.testBit
      (second.featureMap.forward (first.featureMap.forward q)).val = _
    rw [second.graph_preserved, first.graph_preserved]

/-- Replace the forward maps by their literal checked tables. The cell
inverse is inherited from the verified frame, so only the pointwise forward
recurrence is required for a derived group element. -/
def frameWithForward {n k : Nat} {D : Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (F : Frame D cells)
    (vertices : Equiv.Perm (Fin 10)) (forward : Fin n → Fin n)
    (hvertices : ∀ v, vertices v = F.vertices v)
    (hforward : ∀ i, forward i = F.cellMap.forward i) : Frame D cells where
  vertices := vertices
  cellMap :=
    { forward := forward
      inverse := F.cellMap.inverse
      left_inverse := fun i => by rw [hforward, F.cellMap.left_inverse]
      right_inverse := fun i => by rw [hforward, F.cellMap.right_inverse] }
  ridgeMap := F.ridgeMap
  featureMap := F.featureMap
  cell_geometry i := by
    have hv : vertices = F.vertices := Equiv.ext hvertices
    change decodeCell (cells (forward i)) =
      mapCell vertices.toEmbedding (decodeCell (cells i))
    rw [hforward, hv]
    exact F.cell_geometry i
  ridge_geometry q := by
    rw [F.ridge_geometry]
    exact congrArg (fun p : Equiv.Perm (Fin 10) => (maskSet q.val).image p)
      (Equiv.ext hvertices).symm
  feature_geometry q := by
    rw [F.feature_geometry]
    exact congrArg (fun p : Equiv.Perm (Fin 10) =>
      (maskSet (TenGraphEdges.edgeMask q)).image p) (Equiv.ext hvertices).symm
  kind_preserved i := by
    change (cells (forward i)).kind = (cells i).kind
    rw [hforward, F.kind_preserved]
  graph_preserved := F.graph_preserved

/-- A group-table edge says that the new frame is the parent followed by
one checked generator. The supplied raw forward table is retained verbatim. -/
def composedFrameWithForward {n k : Nat} {D : Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (parent generator : Frame D cells)
    (vertices : Equiv.Perm (Fin 10)) (forward : Fin n → Fin n)
    (hvertices : ∀ v, vertices v = generator.vertices (parent.vertices v))
    (hforward : ∀ i, forward i = generator.cellMap.forward (parent.cellMap.forward i)) :
    Frame D cells :=
  frameWithForward (composeFrame parent generator) vertices forward hvertices hforward

theorem actualCell_relabel {d n : Nat} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (vertices : Equiv.Perm (Fin n)) (F : Face P 3) :
    actualCell P (lab.trans vertices) F =
      mapCell vertices.toEmbedding (actualCell P lab F) := by
  classical
  apply cell_ext
  · exact ActualGraphNormalization.faceLabels_relabel P lab vertices F
  · change ((Finset.univ : Finset (Face P 1)).filter
        (fun A => A.val.carrier ⊆ F.val.carrier)).image
          (faceLabels P (lab.trans vertices)) =
      (((Finset.univ : Finset (Face P 1)).filter
        (fun A => A.val.carrier ⊆ F.val.carrier)).image (faceLabels P lab)).image
          (fun A => A.image vertices)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro A _
    exact ActualGraphNormalization.faceLabels_relabel P lab vertices A
  · change (actualRidges P 2 F).image (faceLabels P (lab.trans vertices)) =
      ((actualRidges P 2 F).image (faceLabels P lab)).image (fun A => A.image vertices)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro A _
    exact ActualGraphNormalization.faceLabels_relabel P lab vertices A

/-- A frame renames a genuine encoding by the same vertex permutation.
Thus orbit leaves retain an actual polytope interpretation, not only an
abstract search-target predicate. -/
def renameEncoding {d n k : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {D : Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (F : Frame D cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) :
    Encoding P (lab.trans F.vertices) (fun i => decodeCell (cells i)) where
  index A := F.cellMap.forward (E.index A)
  index_spec A := by
    rw [F.cell_geometry, E.index_spec, ← actualCell_relabel]

theorem renameEncoding_family {d n k : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {D : Problem n 1024 45 10 k}
    {cells : Fin n → ConcreteGrowth.Cell} (F : Frame D cells)
    (E : Encoding P lab (fun i => decodeCell (cells i))) :
    (renameEncoding F E).family = E.family.image F.cellMap.forward := by
  simp only [Encoding.family, Finset.image_image]
  rfl

#print axioms checkedFrame
#print axioms renameEncoding

end Papers.RationalityTen.CheckedGraphGrowthFrames
