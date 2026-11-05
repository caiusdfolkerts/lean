module
prelude
public import RootedSevenMixed017OutsideVerifiedCheck0
public import RootedSevenMixed017OutsideVerifiedCheck1

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside.Verified
open Papers.RationalityTen FiniteChecks
open Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside
theorem fast_checked (g : Fin generatorCount) (i : Fin 646) :
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
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside.Verified
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside
theorem cell_checked (g : Fin generatorCount) (i : Fin 646) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside.Verified.fast_checked g i
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed017.Outside
