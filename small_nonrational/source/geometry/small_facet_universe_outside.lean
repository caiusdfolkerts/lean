module
prelude
public import RootedSmallGeneratorWords
public import SmallFacetUniverseOutsideData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.Small.Outside
open Papers.RationalityTen ConcreteGrowth FiniteChecks

theorem cell_checked (g : Fin generatorCount) (i : Fin cellCount) :
    cellTest g.val i.val = true := by
  have h := RootedSmallGeneratorWords.cell_checked (generator g) i
  simpa only [cellTest, RootedSmallGeneratorWords.cellTest,
    Fin.ofNat_val_eq_self, RootedSmallGeneratorWords.vertices, forward, vertexCode] using h

#print axioms cell_checked

end Papers.RationalityTen.FacetUniverses.Small.Outside
