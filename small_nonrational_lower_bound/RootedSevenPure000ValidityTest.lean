module
prelude
public import RootedSevenPure000
public import RawFacetEmbedding

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
noncomputable def test (i : Nat) : Bool :=
  Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
    (Papers.RationalityTen.FacetUniverses.RootedSevenPure000.cells (Fin.ofNat 758 i))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
