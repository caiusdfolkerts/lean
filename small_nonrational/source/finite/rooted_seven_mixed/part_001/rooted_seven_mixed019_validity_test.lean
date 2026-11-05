module
prelude
public import RootedSevenMixed019
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed019.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed019.cells (Fin.ofNat 556 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed019.Validity
