module

public import BoundaryGeneratorFrames
public import RootedSixExtra06Generators
public import RootedSixExtra06GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra06

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 5)
    (i : Fin 2300) :
    inverseCheckAt (FacetUniverses.RootedSixExtra06.Generators.forward g)
      (FacetUniverses.RootedSixExtra06.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra06.Generators.vertexCode g))
      (FacetUniverses.RootedSixExtra06.cells i)
      (FacetUniverses.RootedSixExtra06.cells
        (FacetUniverses.RootedSixExtra06.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixExtra06.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra06.Generators.cell_checked g i

def generator (g : Fin 5) :
    BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  checkedFrame FacetUniverses.RootedSixExtra06.cells
    (FacetUniverses.RootedSixExtra06.Generators.vertexCode g)
    (FacetUniverses.RootedSixExtra06.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixExtra06.Generators.vertex_checks g)
    (FacetUniverses.RootedSixExtra06.Generators.forward g)
    (FacetUniverses.RootedSixExtra06.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 240) :
    BoundaryFrame FacetUniverses.RootedSixExtra06.cells :=
  wordFrame FacetUniverses.RootedSixExtra06.cells generator
    (FacetUniverses.RootedSixExtra06.Generators.words f)

theorem cells_wellFormed (i : Fin 2300) :
    WellFormed (FacetUniverses.RootedSixExtra06.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixExtra06.well_formed i)

theorem maps_exact (f : Fin 240) (i : Fin 2300) :
    FacetUniverses.RootedSixExtra06.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixExtra06.cells generator
    FacetUniverses.RootedSixExtra06.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixExtra06.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixExtra06.Generators.words f)
    (FacetUniverses.RootedSixExtra06.Generators.rawWords f.val)
    (FacetUniverses.RootedSixExtra06.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra06
