module
prelude
public import RootedSevenMixed007Validity

@[expose] public section

namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed007

/-- Every literal cell in this exact candidate universe has bounded masks
and a canonical ordered edge list. This reuses the standalone metadata
certificate, without constructing a second compatibility cache. -/
theorem well_formed (c : Fin 556) :
    Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
      (Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.cells c) = true :=
  Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.Validity.record_checked c

end Papers.RationalityTen.RootedCaches.RootedSevenMixed007
