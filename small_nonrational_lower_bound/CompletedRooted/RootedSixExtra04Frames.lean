module

public import BoundaryGeneratorFrames
public import RootedSixExtra04Generators
public import RootedSixExtra04GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra04

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 6)
    (i : Fin 3640) :
    inverseCheckAt (FacetUniverses.RootedSixExtra04.Generators.forward g)
      (FacetUniverses.RootedSixExtra04.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra04.Generators.vertexCode g))
      (FacetUniverses.RootedSixExtra04.cells i)
      (FacetUniverses.RootedSixExtra04.cells
        (FacetUniverses.RootedSixExtra04.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixExtra04.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra04.Generators.cell_checked g i

def generator (g : Fin 6) :
    BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  checkedFrame FacetUniverses.RootedSixExtra04.cells
    (FacetUniverses.RootedSixExtra04.Generators.vertexCode g)
    (FacetUniverses.RootedSixExtra04.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixExtra04.Generators.vertex_checks g)
    (FacetUniverses.RootedSixExtra04.Generators.forward g)
    (FacetUniverses.RootedSixExtra04.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 1152) :
    BoundaryFrame FacetUniverses.RootedSixExtra04.cells :=
  wordFrame FacetUniverses.RootedSixExtra04.cells generator
    (FacetUniverses.RootedSixExtra04.Generators.words f)

theorem cells_wellFormed (i : Fin 3640) :
    WellFormed (FacetUniverses.RootedSixExtra04.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixExtra04.well_formed i)

theorem maps_exact (f : Fin 1152) (i : Fin 3640) :
    FacetUniverses.RootedSixExtra04.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixExtra04.cells generator
    FacetUniverses.RootedSixExtra04.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixExtra04.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixExtra04.Generators.words f)
    (FacetUniverses.RootedSixExtra04.Generators.rawWords f.val)
    (FacetUniverses.RootedSixExtra04.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra04
