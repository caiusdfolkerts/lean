module

public import BoundaryGeneratorFrames
public import RootedSixBase04Generators
public import RootedSixBase04GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixBase04

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 6)
    (i : Fin 2824) :
    inverseCheckAt (FacetUniverses.RootedSixBase04.Generators.forward g)
      (FacetUniverses.RootedSixBase04.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase04.Generators.vertexCode g))
      (FacetUniverses.RootedSixBase04.cells i)
      (FacetUniverses.RootedSixBase04.cells
        (FacetUniverses.RootedSixBase04.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixBase04.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase04.Generators.cell_checked g i

def generator (g : Fin 6) :
    BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  checkedFrame FacetUniverses.RootedSixBase04.cells
    (FacetUniverses.RootedSixBase04.Generators.vertexCode g)
    (FacetUniverses.RootedSixBase04.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixBase04.Generators.vertex_checks g)
    (FacetUniverses.RootedSixBase04.Generators.forward g)
    (FacetUniverses.RootedSixBase04.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 1152) :
    BoundaryFrame FacetUniverses.RootedSixBase04.cells :=
  wordFrame FacetUniverses.RootedSixBase04.cells generator
    (FacetUniverses.RootedSixBase04.Generators.words f)

theorem cells_wellFormed (i : Fin 2824) :
    WellFormed (FacetUniverses.RootedSixBase04.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixBase04.well_formed i)

theorem maps_exact (f : Fin 1152) (i : Fin 2824) :
    FacetUniverses.RootedSixBase04.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixBase04.cells generator
    FacetUniverses.RootedSixBase04.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixBase04.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixBase04.Generators.words f)
    (FacetUniverses.RootedSixBase04.Generators.rawWords f.val)
    (FacetUniverses.RootedSixBase04.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixBase04
