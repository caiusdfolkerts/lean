module
prelude
public import RootedSevenMixed021
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed021.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenMixed021.cells (Fin.ofNat 556 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed021.Validity
