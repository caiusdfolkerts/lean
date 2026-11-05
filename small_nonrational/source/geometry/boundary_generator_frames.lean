module

public import CheckedGraphGrowthFrames
public import RawGeneratorWords

@[expose] public section

/-!
# Geometric generator words for ordinary boundary growth

These frames carry no fixed graph and impose no graph-invariance condition.
The same vertex permutation transports complete cells and ridge masks, and
therefore every ordinary growth target and every genuine polytope encoding.
-/

noncomputable section
namespace Papers.RationalityTen.BoundaryGeneratorFrames

open Finset
open GrowthRenaming RawGraphGrowthFrames
open LiteralMaskGeometry CheckedGraphGrowthFrames
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

structure BoundaryFrame {n : Nat} (cells : Fin n → ConcreteGrowth.Cell) where
  vertices : Equiv.Perm (Fin 10)
  cellMap : Bijection (Fin n)
  ridgeMap : Bijection (Fin 1024)
  cell_geometry : ∀ i, decodeCell (cells (cellMap.forward i)) =
    mapCell vertices.toEmbedding (decodeCell (cells i))
  ridge_geometry : ∀ q, maskSet (ridgeMap.forward q).val = (maskSet q.val).image vertices
  kind_preserved : ∀ i, (cells (cellMap.forward i)).kind = (cells i).kind

def checkedFrame {n : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (vertexForward vertexInverse : Nat)
    (hvertices : TenGraphEdges.permutationCheck vertexForward vertexInverse = true)
    (forward inverse : Fin n → Fin n)
    (hinverse : ∀ i, inverseCheckAt forward inverse i = true)
    (hcells : ∀ i, cellRelabelCheck (TenGraphEdges.vertexMap vertexForward)
      (cells i) (cells (forward i)) = true) : BoundaryFrame cells := by
  let p := TenGraphEdges.checkedBijection vertexForward vertexInverse hvertices
  exact
    { vertices := bijectionEquiv p
      cellMap := checkedCellBijection forward inverse hinverse
      ridgeMap := ridgeBijection p
      cell_geometry := fun i => cellRelabelCheck_decode p _ _ (hcells i)
      ridge_geometry := ridgeBijection_geometry p
      kind_preserved := fun i => (cellRelabelCheck_sound _ _ _ (hcells i)).1 }

def BoundaryFrame.toBoundaryRenaming {n : Nat} {cells : Fin n → ConcreteGrowth.Cell}
    (F : BoundaryFrame cells) (hwell : ∀ i, WellFormed (cells i)) :
    GrowthRenaming.Renaming
      (fun i q => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells i) q)
      (fun i j => ConcreteGrowth.compatible (cells i) (cells j))
      (fun i => (cells i).kind) where
  cells := F.cellMap
  ridgeMap := F.ridgeMap
  incidence := literal_ridges_relabel cells hwell F.vertices F.cellMap.forward
    F.ridgeMap.forward F.cell_geometry F.ridge_geometry
  compatibility := literal_compatibility_relabel cells hwell F.vertices
    F.cellMap.forward F.cell_geometry
  kind_preserved := F.kind_preserved

def identityFrame {n : Nat} (cells : Fin n → ConcreteGrowth.Cell) : BoundaryFrame cells where
  vertices := Equiv.refl _
  cellMap := identityBijection
  ridgeMap := identityBijection
  cell_geometry i := by
    apply cell_ext <;> simp [identityBijection, mapCell,
      Function.Embedding.coe_refl, Finset.image_id']
  ridge_geometry q := by simp only [Equiv.coe_refl, Finset.image_id]; rfl
  kind_preserved _ := rfl

def composeFrame {n : Nat} {cells : Fin n → ConcreteGrowth.Cell}
    (first second : BoundaryFrame cells) : BoundaryFrame cells where
  vertices := first.vertices.trans second.vertices
  cellMap := composeBijection first.cellMap second.cellMap
  ridgeMap := composeBijection first.ridgeMap second.ridgeMap
  cell_geometry i := by
    change decodeCell (cells (second.cellMap.forward (first.cellMap.forward i))) = _
    rw [second.cell_geometry, first.cell_geometry, mapCell_composition]
  ridge_geometry q := by
    change maskSet (second.ridgeMap.forward (first.ridgeMap.forward q)).val = _
    rw [second.ridge_geometry, first.ridge_geometry, Finset.image_image]
    rfl
  kind_preserved i := by
    change (cells (second.cellMap.forward (first.cellMap.forward i))).kind = _
    rw [second.kind_preserved, first.kind_preserved]

def wordFrame {n h : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (generators : Fin h → BoundaryFrame cells) : List (Fin h) → BoundaryFrame cells
  | [] => identityFrame cells
  | g :: rest => composeFrame (generators g) (wordFrame cells generators rest)

theorem wordFrame_forward_val {n h : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (generators : Fin h → BoundaryFrame cells) (rawGenerators : Nat → Nat → Nat)
    (hgenerators : ∀ (g : Fin h) (i : Fin n),
      rawGenerators g.val i.val = ((generators g).cellMap.forward i).val)
    (word : List (Fin h)) (rawWord : List Nat)
    (hword : rawWord = word.map Fin.val) (i : Fin n) :
    CheckedGraphGrowthWords.rawApply rawGenerators rawWord i.val =
      ((wordFrame cells generators word).cellMap.forward i).val := by
  subst rawWord
  induction word generalizing i with
  | nil => rfl
  | cons g rest ih =>
    change CheckedGraphGrowthWords.rawApply rawGenerators (rest.map Fin.val)
      (rawGenerators g.val i.val) =
      ((wordFrame cells generators rest).cellMap.forward
        ((generators g).cellMap.forward i)).val
    rw [hgenerators]
    exact ih _

def renameEncoding {d n : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin n → ConcreteGrowth.Cell}
    (F : BoundaryFrame cells) (E : Encoding P lab (fun i => decodeCell (cells i))) :
    Encoding P (lab.trans F.vertices) (fun i => decodeCell (cells i)) where
  index A := F.cellMap.forward (E.index A)
  index_spec A := by
    rw [F.cell_geometry, E.index_spec, ← actualCell_relabel]

theorem renameEncoding_family {d n : Nat} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin n → ConcreteGrowth.Cell}
    (F : BoundaryFrame cells) (E : Encoding P lab (fun i => decodeCell (cells i))) :
    (renameEncoding F E).family = E.family.image F.cellMap.forward := by
  simp only [Encoding.family, Finset.image_image]
  rfl

end Papers.RationalityTen.BoundaryGeneratorFrames
