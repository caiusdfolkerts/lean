module

public import BoundaryGeneratorFrames
public import RootedSixExtra03Generators
public import RootedSixExtra03GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra03

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 5)
    (i : Fin 3150) :
    inverseCheckAt (FacetUniverses.RootedSixExtra03.Generators.forward g)
      (FacetUniverses.RootedSixExtra03.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra03.Generators.vertexCode g))
      (FacetUniverses.RootedSixExtra03.cells i)
      (FacetUniverses.RootedSixExtra03.cells
        (FacetUniverses.RootedSixExtra03.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixExtra03.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra03.Generators.cell_checked g i

def generator (g : Fin 5) :
    BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  checkedFrame FacetUniverses.RootedSixExtra03.cells
    (FacetUniverses.RootedSixExtra03.Generators.vertexCode g)
    (FacetUniverses.RootedSixExtra03.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixExtra03.Generators.vertex_checks g)
    (FacetUniverses.RootedSixExtra03.Generators.forward g)
    (FacetUniverses.RootedSixExtra03.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 96) :
    BoundaryFrame FacetUniverses.RootedSixExtra03.cells :=
  wordFrame FacetUniverses.RootedSixExtra03.cells generator
    (FacetUniverses.RootedSixExtra03.Generators.words f)

theorem cells_wellFormed (i : Fin 3150) :
    WellFormed (FacetUniverses.RootedSixExtra03.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixExtra03.well_formed i)

theorem maps_exact (f : Fin 96) (i : Fin 3150) :
    FacetUniverses.RootedSixExtra03.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixExtra03.cells generator
    FacetUniverses.RootedSixExtra03.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixExtra03.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixExtra03.Generators.words f)
    (FacetUniverses.RootedSixExtra03.Generators.rawWords f.val)
    (FacetUniverses.RootedSixExtra03.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra03
