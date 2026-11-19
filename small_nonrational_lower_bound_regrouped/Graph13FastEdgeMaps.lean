module
prelude
public import Graph13Frames
public import FastTenGraphEdges
public import CachedGraphCatalogueCheck

@[expose] public section

/-! Arithmetic edge maps for the same exact graph-catalogue checker.
Only the implementation of a proved vertex-induced edge permutation changes. -/

namespace Papers.RationalityTen.Graph13FastEdgeMaps
open GraphCatalogueCore GraphCatalogueCheck
abbrev Frames := GraphCatalogue.Generated.Graph13.Frames.count

noncomputable def edgeMaps (f : Fin Frames) (e : Fin 45) : Fin 45 :=
  FastTenGraphEdges.edgeMap (GraphCatalogue.Generated.Graph13.Frames.entry f).1 e

theorem edgeMaps_eq (f : Fin Frames) (e : Fin 45) :
    edgeMaps f e =
      (GraphCatalogue.Generated.Graph13.Frames.renamings f).cells.forward e := by
  exact FastTenGraphEdges.edgeMap_eq _
    (GraphCatalogue.Generated.Graph13.Frames.vertexBijections f) rfl e

noncomputable def extensionCheck {after : Nat}
    (source : State 45) (next : Fin after → State 45) (edge : Fin 45)
    (choice : Choice 10 after Frames) : Bool :=
  CachedGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 edgeMaps
    source next edge choice

theorem extensionCheck_eq {after : Nat}
    (source : State 45) (next : Fin after → State 45) (edge : Fin 45)
    (choice : Choice 10 after Frames) :
    extensionCheck source next edge choice =
      FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4
        GraphCatalogue.Generated.Graph13.Frames.renamings source next edge choice := by
  exact (CachedGraphCatalogueCheck.extensionCheck_eq TenGraphEdges.incidence 4
    GraphCatalogue.Generated.Graph13.Frames.renamings edgeMaps edgeMaps_eq
    source next edge choice).trans
      (FastGraphCatalogueCheck.extensionCheck_eq TenGraphEdges.incidence 4
        GraphCatalogue.Generated.Graph13.Frames.renamings source next edge choice).symm

#print axioms extensionCheck_eq
end Papers.RationalityTen.Graph13FastEdgeMaps
