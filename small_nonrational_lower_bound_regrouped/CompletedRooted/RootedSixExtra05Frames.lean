module

public import BoundaryGeneratorFrames
public import RootedSixExtra05Generators
public import RootedSixExtra05GrowthCache

@[expose] public section

/-! Every generator is a checked vertex permutation preserving the entire
literal cell. Composing the prescribed words therefore gives geometric
relabelings, without assuming any symmetry of an actual polytope. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra05

open BoundaryGeneratorFrames RawGraphGrowthFrames LiteralMaskGeometry
open RawFacetEmbeddingSemantics

theorem generator_checks (g : Fin 6)
    (i : Fin 2170) :
    inverseCheckAt (FacetUniverses.RootedSixExtra05.Generators.forward g)
      (FacetUniverses.RootedSixExtra05.Generators.inverse g) i = true ∧
    cellRelabelCheck
      (TenGraphEdges.vertexMap (FacetUniverses.RootedSixExtra05.Generators.vertexCode g))
      (FacetUniverses.RootedSixExtra05.cells i)
      (FacetUniverses.RootedSixExtra05.cells
        (FacetUniverses.RootedSixExtra05.Generators.forward g i)) = true := by
  apply Bool.and_eq_true_iff.mp
  simpa only [FacetUniverses.RootedSixExtra05.Generators.cellTest, Fin.ofNat_val_eq_self] using
    FacetUniverses.RootedSixExtra05.Generators.cell_checked g i

def generator (g : Fin 6) :
    BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  checkedFrame FacetUniverses.RootedSixExtra05.cells
    (FacetUniverses.RootedSixExtra05.Generators.vertexCode g)
    (FacetUniverses.RootedSixExtra05.Generators.vertexInverseCode g)
    (FacetUniverses.RootedSixExtra05.Generators.vertex_checks g)
    (FacetUniverses.RootedSixExtra05.Generators.forward g)
    (FacetUniverses.RootedSixExtra05.Generators.inverse g)
    (fun i => (generator_checks g i).1) (fun i => (generator_checks g i).2)

def frame (f : Fin 288) :
    BoundaryFrame FacetUniverses.RootedSixExtra05.cells :=
  wordFrame FacetUniverses.RootedSixExtra05.cells generator
    (FacetUniverses.RootedSixExtra05.Generators.words f)

theorem cells_wellFormed (i : Fin 2170) :
    WellFormed (FacetUniverses.RootedSixExtra05.cells i) :=
  wellFormed_of_check _ (RootedCaches.RootedSixExtra05.well_formed i)

theorem maps_exact (f : Fin 288) (i : Fin 2170) :
    FacetUniverses.RootedSixExtra05.Generators.rawMaps f.val i.val =
      ((frame f).cellMap.forward i).val := by
  apply wordFrame_forward_val FacetUniverses.RootedSixExtra05.cells generator
    FacetUniverses.RootedSixExtra05.Generators.rawGenerators
    (fun g c => FacetUniverses.RootedSixExtra05.Generators.raw_generators_exact g c)
    (FacetUniverses.RootedSixExtra05.Generators.words f)
    (FacetUniverses.RootedSixExtra05.Generators.rawWords f.val)
    (FacetUniverses.RootedSixExtra05.Generators.raw_words_exact f)

#print axioms maps_exact
end Papers.RationalityTen.CompletedRootedFrames.RootedSixExtra05
