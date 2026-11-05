module
prelude
public import RootedSevenMixed009
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.cells (Fin.ofNat 910 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
