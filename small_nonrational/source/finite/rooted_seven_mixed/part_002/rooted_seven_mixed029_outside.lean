module
prelude
public import RootedSevenMixed029OutsideVerifiedCheck0
public import RootedSevenMixed029OutsideVerifiedCheck1

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified
open Papers.RationalityTen FiniteChecks
open Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside
theorem fast_checked (g : Fin generatorCount) (i : Fin 376) :
    fastCellTest g.val i.val = true := by
  have hg : g.val < 2 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 := by omega
  rcases hc with h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator0_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator1_complete i.val (Nat.zero_le _) i.isLt
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside
theorem cell_checked (g : Fin generatorCount) (i : Fin 376) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside.Verified.fast_checked g i
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed029.Outside
