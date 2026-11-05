module
prelude
public import RootedSevenMixed013
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.cells (Fin.ofNat 466 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
