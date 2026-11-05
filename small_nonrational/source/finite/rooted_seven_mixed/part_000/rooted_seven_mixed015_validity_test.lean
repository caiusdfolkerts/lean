module
prelude
public import RootedSevenMixed015
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed015.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed015.cells (Fin.ofNat 521 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed015.Validity
