module
prelude
public import RootedSevenMixed004
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed004.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed004.cells (Fin.ofNat 646 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed004.Validity
