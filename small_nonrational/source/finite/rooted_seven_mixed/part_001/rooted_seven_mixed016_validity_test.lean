module
prelude
public import RootedSevenMixed016
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.cells (Fin.ofNat 646 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.Validity
