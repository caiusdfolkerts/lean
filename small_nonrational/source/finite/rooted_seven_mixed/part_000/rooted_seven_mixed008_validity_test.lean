module
prelude
public import RootedSevenMixed008
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.cells (Fin.ofNat 694 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.Validity
