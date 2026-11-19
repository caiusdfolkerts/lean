module
prelude
public import RootedSixExtra05GeneratorsVerifiedCheck0
public import RootedSixExtra05GeneratorsVerifiedCheck1
public import RootedSixExtra05GeneratorsVerifiedCheck2
public import RootedSixExtra05GeneratorsVerifiedCheck3
public import RootedSixExtra05GeneratorsVerifiedCheck4
public import RootedSixExtra05GeneratorsVerifiedCheck5

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Verified
open Papers.RationalityTen FiniteChecks
open Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators
theorem fast_checked (g : Fin generatorCount) (i : Fin 2170) :
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
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Verified
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators
theorem cell_checked (g : Fin generatorCount) (i : Fin 2170) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Verified.fast_checked g i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators
