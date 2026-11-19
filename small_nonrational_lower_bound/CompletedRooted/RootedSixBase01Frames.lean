module

public import BoundaryGeneratorFrames
public import RootedSixBase01Generators
public import RootedSixBase01GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixBase01

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 4)
    (i : Fin 15246) :
    inverseCheckAt (FacetUniverses.RootedSixBase01.Generators.forward g)
      (FacetUniverses.RootedSixBase01.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixBase01.Generators.vertexCode g))
      (FacetUniverses.RootedSixBase01.cells i)
      (FacetUniverses.RootedSixBase01.cells
        (FacetUniverses.RootedSixBase01.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixBase01.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixBase01.Generators.cell_checked g i

def generator (g : Fin 4) :
    BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  checkedFrame FacetUniverses.RootedSixBase01.cells
    (FacetUniverses.RootedSixBase01.Generators.vertexCode g)
    (FacetUniverses.RootedSixBase01.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixBase01.Generators.vertex_checks g)
    (FacetUniverses.RootedSixBase01.Generators.forward g)
    (FacetUniverses.RootedSixBase01.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 48) :
    BoundaryFrame FacetUniverses.RootedSixBase01.cells :=
  wordFrame FacetUniverses.RootedSixBase01.cells generator
    (FacetUniverses.RootedSixBase01.Generators.words f)

theorem cells_wellFormed (i : Fin 15246) :
    WellFormed (FacetUniverses.RootedSixBase01.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixBase01.well_formed i)

theorem maps_exact (f : Fin 48) (i : Fin 15246) :
    FacetUniverses.RootedSixBase01.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixBase01.cells generator
    FacetUniverses.RootedSixBase01.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixBase01.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixBase01.Generators.words f)
    (FacetUniverses.RootedSixBase01.Generators.rawWords f.val)
    (FacetUniverses.RootedSixBase01.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixBase01
