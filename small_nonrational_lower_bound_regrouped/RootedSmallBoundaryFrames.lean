module

public import BoundaryGeneratorFrames
public import RootedSmallGeneratorWords
public import RootedSmallCache

@[expose] public section

/-!
# Geometric meaning of the rooted small-facet symmetries

Each of the seven adjacent transpositions is checked on every literal cell.
The 1,440 words used by the search therefore act simultaneously on vertices,
complete cells and ridge masks. No symmetry of an actual polytope is assumed:
the action relabels its complete boundary encoding.
-/

noncomputable section
namespace Papers.RationalityTen.RootedSmallBoundaryFrames

open BoundaryGeneratorFrames RawGraphGrowthFrames
open LiteralMaskGeometry RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 7) (i : Fin 3436) :
    inverseCheckAt (RootedSmallGeneratorWords.forward g)
      (RootedSmallGeneratorWords.forward g) i = true ∧
    cellRelabelCheck (RootedSmallGeneratorWords.vertices g)
      (FacetUniverses.Small.cells i)
      (FacetUniverses.Small.cells (RootedSmallGeneratorWords.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [RootedSmallGeneratorWords.cellTest, Fin.ofNat_val_eq_self] using
    RootedSmallGeneratorWords.cell_checked g i

/-- The literal generator checks induce honest geometric permutations. -/
def generator (g : Fin 7) : BoundaryFrame FacetUniverses.Small.cells :=
  checkedFrame FacetUniverses.Small.cells
    (RootedSmallGeneratorWords.vertexTable.get g.val)
    (RootedSmallGeneratorWords.vertexTable.get g.val)
    (RootedSmallGeneratorWords.vertex_checks g)
    (RootedSmallGeneratorWords.forward g) (RootedSmallGeneratorWords.forward g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

/-- Every word in the finite search has its full geometric interpretation. -/
def frame (f : Fin 1440) : BoundaryFrame FacetUniverses.Small.cells :=
  wordFrame FacetUniverses.Small.cells generator (RootedSmallGeneratorWords.words f)

theorem cells_wellFormed (i : Fin FacetUniverses.Small.cellCount) :
    WellFormed (FacetUniverses.Small.cells i) :=
  wellFormed_of_check _ (RootedSmallCache.well_formed i)

theorem maps_exact (f : Fin 1440) (i : Fin FacetUniverses.Small.cellCount) :
    RootedSmallGeneratorWords.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.Small.cells generator
    RootedSmallGeneratorWords.rawGenerators
    (fun g c => RootedSmallGeneratorWords.raw_generators_exact g c)
    (RootedSmallGeneratorWords.words f) (RootedSmallGeneratorWords.rawWords f.val)
    (RootedSmallGeneratorWords.raw_words_exact f)

#print axioms maps_exact

end Papers.RationalityTen.RootedSmallBoundaryFrames
