module
prelude
public import RootedSevenMixed005Validity

@[expose] public section

namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed005

/-- Every literal cell in this exact candidate universe has bounded masks
and a canonical ordered edge list. This reuses the standalone metadata
certificate, without constructing a second compatibility cache. -/
theorem well_formed (c : Fin 646) :
    Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
      (Papers.RationalityTen.FacetUniverses.RootedSevenMixed005.cells c) = true :=
  Papers.RationalityTen.FacetUniverses.RootedSevenMixed005.Validity.record_checked c

end Papers.RationalityTen.RootedCaches.RootedSevenMixed005
