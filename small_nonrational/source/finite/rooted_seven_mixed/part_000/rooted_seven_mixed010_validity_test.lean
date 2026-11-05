module
prelude
public import RootedSevenMixed010
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.cells (Fin.ofNat 430 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
