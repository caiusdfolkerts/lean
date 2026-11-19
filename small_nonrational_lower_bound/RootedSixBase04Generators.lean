module
prelude
public import RootedSixBase04GeneratorsVerifiedCheck0
public import RootedSixBase04GeneratorsVerifiedCheck1
public import RootedSixBase04GeneratorsVerifiedCheck2
public import RootedSixBase04GeneratorsVerifiedCheck3
public import RootedSixBase04GeneratorsVerifiedCheck4
public import RootedSixBase04GeneratorsVerifiedCheck5

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Verified
open Papers.RationalityTen FiniteChecks
open Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators
theorem fast_checked (g : Fin generatorCount) (i : Fin 2824) :
    fastCellTest g.val i.val = true := by
  have hg : g.val < 6 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 ∨ g.val = 2 ∨ g.val = 3 ∨ g.val = 4 ∨ g.val = 5 := by omega
  rcases hc with h | h | h | h | h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator0_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator1_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨2, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator2_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨3, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator3_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨4, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator4_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨5, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator5_complete i.val (Nat.zero_le _) i.isLt
end Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Verified
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators
theorem cell_checked (g : Fin generatorCount) (i : Fin 2824) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Verified.fast_checked g i
end Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators
