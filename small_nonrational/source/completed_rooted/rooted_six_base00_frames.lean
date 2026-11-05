module

public import BoundaryGeneratorFrames
public import RootedSixBase00Generators
public import RootedSixBase00GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixBase00

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 5)
    (i : Fin 21976) :
    inverseCheckAt (FacetUniverses.RootedSixBase00.Generators.forward g)
      (FacetUniverses.RootedSixBase00.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase00.Generators.vertexCode g))
      (FacetUniverses.RootedSixBase00.cells i)
      (FacetUniverses.RootedSixBase00.cells
        (FacetUniverses.RootedSixBase00.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixBase00.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase00.Generators.cell_checked g i

def generator (g : Fin 5) :
    BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  checkedFrame FacetUniverses.RootedSixBase00.cells
    (FacetUniverses.RootedSixBase00.Generators.vertexCode g)
    (FacetUniverses.RootedSixBase00.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixBase00.Generators.vertex_checks g)
    (FacetUniverses.RootedSixBase00.Generators.forward g)
    (FacetUniverses.RootedSixBase00.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 96) :
    BoundaryFrame FacetUniverses.RootedSixBase00.cells :=
  wordFrame FacetUniverses.RootedSixBase00.cells generator
    (FacetUniverses.RootedSixBase00.Generators.words f)

theorem cells_wellFormed (i : Fin 21976) :
    WellFormed (FacetUniverses.RootedSixBase00.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixBase00.well_formed i)

theorem maps_exact (f : Fin 96) (i : Fin 21976) :
    FacetUniverses.RootedSixBase00.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixBase00.cells generator
    FacetUniverses.RootedSixBase00.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixBase00.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixBase00.Generators.words f)
    (FacetUniverses.RootedSixBase00.Generators.rawWords f.val)
    (FacetUniverses.RootedSixBase00.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixBase00
