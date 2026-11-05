module

public import BoundaryGeneratorFrames
public import RootedSixExtra01Generators
public import RootedSixExtra01GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra01

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 4)
    (i : Fin 3150) :
    inverseCheckAt (FacetUniverses.RootedSixExtra01.Generators.forward g)
      (FacetUniverses.RootedSixExtra01.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra01.Generators.vertexCode g))
      (FacetUniverses.RootedSixExtra01.cells i)
      (FacetUniverses.RootedSixExtra01.cells
        (FacetUniverses.RootedSixExtra01.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixExtra01.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra01.Generators.cell_checked g i

def generator (g : Fin 4) :
    BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  checkedFrame FacetUniverses.RootedSixExtra01.cells
    (FacetUniverses.RootedSixExtra01.Generators.vertexCode g)
    (FacetUniverses.RootedSixExtra01.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixExtra01.Generators.vertex_checks g)
    (FacetUniverses.RootedSixExtra01.Generators.forward g)
    (FacetUniverses.RootedSixExtra01.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 48) :
    BoundaryFrame FacetUniverses.RootedSixExtra01.cells :=
  wordFrame FacetUniverses.RootedSixExtra01.cells generator
    (FacetUniverses.RootedSixExtra01.Generators.words f)

theorem cells_wellFormed (i : Fin 3150) :
    WellFormed (FacetUniverses.RootedSixExtra01.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixExtra01.well_formed i)

theorem maps_exact (f : Fin 48) (i : Fin 3150) :
    FacetUniverses.RootedSixExtra01.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixExtra01.cells generator
    FacetUniverses.RootedSixExtra01.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixExtra01.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixExtra01.Generators.words f)
    (FacetUniverses.RootedSixExtra01.Generators.rawWords f.val)
    (FacetUniverses.RootedSixExtra01.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra01
