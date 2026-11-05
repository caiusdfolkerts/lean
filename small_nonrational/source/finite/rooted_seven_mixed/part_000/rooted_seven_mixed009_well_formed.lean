module
prelude
public import RootedSevenMixed009Validity

@[expose] public section

namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed009

/-- Every literal cell in this exact candidate universe has bounded masks
and a canonical ordered edge list. This reuses the standalone metadata
certificate, without constructing a second compatibility cache. -/
theorem well_formed (c : Fin 910) :
    Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
      (Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.cells c) = true :=
  Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity.record_checked c

end Papers.RationalityTen.RootedCaches.RootedSevenMixed009
