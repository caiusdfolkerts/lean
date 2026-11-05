module
prelude
public import RootedSixExtra02GeneratorsVerifiedCheck0
public import RootedSixExtra02GeneratorsVerifiedCheck1
public import RootedSixExtra02GeneratorsVerifiedCheck2
public import RootedSixExtra02GeneratorsVerifiedCheck3

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Verified
open Papers.RationalityTen FiniteChecks
open Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators
theorem fast_checked (g : Fin generatorCount) (i : Fin 6620) :
    fastCellTest g.val i.val = true := by
  have hg : g.val < 4 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 ∨ g.val = 2 ∨ g.val = 3 := by omega
  rcases hc with h | h | h | h
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
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Verified
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators
theorem cell_checked (g : Fin generatorCount) (i : Fin 6620) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Verified.fast_checked g i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators
