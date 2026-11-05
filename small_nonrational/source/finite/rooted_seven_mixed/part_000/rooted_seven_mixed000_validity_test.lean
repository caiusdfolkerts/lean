module
prelude
public import RootedSevenMixed000
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed000.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed000.cells (Fin.ofNat 646 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed000.Validity
