module
prelude
public import RootedSevenMixed006
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed006.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed006.cells (Fin.ofNat 556 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed006.Validity
