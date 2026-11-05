module
prelude
public import RootedSevenMixed012
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.cells (Fin.ofNat 838 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
