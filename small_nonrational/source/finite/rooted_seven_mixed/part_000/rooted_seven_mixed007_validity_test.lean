module
prelude
public import RootedSevenMixed007
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.cells (Fin.ofNat 556 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.Validity
