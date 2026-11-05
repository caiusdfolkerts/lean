module
prelude
public import RootedSevenMixed011
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed011.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed011.cells (Fin.ofNat 658 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed011.Validity
