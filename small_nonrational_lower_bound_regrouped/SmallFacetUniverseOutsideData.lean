module
prelude
public import RootedSmallGeneratorWordsData

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.Small.Outside
open Papers.RationalityTen
abbrev generatorCount : Nat := 4
def generator (g : Fin generatorCount) : Fin 7 := ⟨3 + g.val, by
  have hg : g.val < 4 := g.isLt
  omega⟩
def vertexCode (g : Fin generatorCount) :=
  RootedSmallGeneratorWords.vertexTable.get (generator g).val
def forward (g : Fin generatorCount) := RootedSmallGeneratorWords.forward (generator g)
def rawMap (g c : Nat) :=
  RootedSmallGeneratorWords.rawGenerators (3 + g % generatorCount) c
theorem rawMap_exact (g : Fin generatorCount) (c : Fin cellCount) :
    rawMap g.val c.val = (forward g c).val := by
  simp only [rawMap, Nat.mod_eq_of_lt g.isLt]
  exact RootedSmallGeneratorWords.raw_generators_exact (generator g) c
theorem vertex_checks (g : Fin generatorCount) :
    TenGraphEdges.permutationCheck (vertexCode g) (vertexCode g) = true :=
  RootedSmallGeneratorWords.vertex_checks (generator g)
noncomputable def cellTest (g i : Nat) : Bool :=
  let gen := Fin.ofNat generatorCount g
  let cell := Fin.ofNat cellCount i
  RawGraphGrowthFrames.inverseCheckAt (forward gen) (forward gen) cell &&
    RawGraphGrowthFrames.cellRelabelCheck (TenGraphEdges.vertexMap (vertexCode gen))
      (cells cell) (cells (forward gen cell))
end Papers.RationalityTen.FacetUniverses.Small.Outside
