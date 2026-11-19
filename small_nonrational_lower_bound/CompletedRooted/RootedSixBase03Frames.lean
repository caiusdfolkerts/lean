module

public import BoundaryGeneratorFrames
public import RootedSixBase03Generators
public import RootedSixBase03GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixBase03

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 5)
    (i : Fin 5238) :
    inverseCheckAt (FacetUniverses.RootedSixBase03.Generators.forward g)
      (FacetUniverses.RootedSixBase03.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase03.Generators.vertexCode g))
      (FacetUniverses.RootedSixBase03.cells i)
      (FacetUniverses.RootedSixBase03.cells
        (FacetUniverses.RootedSixBase03.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixBase03.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase03.Generators.cell_checked g i

def generator (g : Fin 5) :
    BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  checkedFrame FacetUniverses.RootedSixBase03.cells
    (FacetUniverses.RootedSixBase03.Generators.vertexCode g)
    (FacetUniverses.RootedSixBase03.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixBase03.Generators.vertex_checks g)
    (FacetUniverses.RootedSixBase03.Generators.forward g)
    (FacetUniverses.RootedSixBase03.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 96) :
    BoundaryFrame FacetUniverses.RootedSixBase03.cells :=
  wordFrame FacetUniverses.RootedSixBase03.cells generator
    (FacetUniverses.RootedSixBase03.Generators.words f)

theorem cells_wellFormed (i : Fin 5238) :
    WellFormed (FacetUniverses.RootedSixBase03.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixBase03.well_formed i)

theorem maps_exact (f : Fin 96) (i : Fin 5238) :
    FacetUniverses.RootedSixBase03.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixBase03.cells generator
    FacetUniverses.RootedSixBase03.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixBase03.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixBase03.Generators.words f)
    (FacetUniverses.RootedSixBase03.Generators.rawWords f.val)
    (FacetUniverses.RootedSixBase03.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixBase03
