module
prelude
public import RootedSevenMixed012Validity

@[expose] public section

namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed012

/-- Every literal cell in this exact candidate universe has bounded masks
and a canonical ordered edge list. This reuses the standalone metadata
certificate, without constructing a second compatibility cache. -/
theorem well_formed (c : Fin 838) :
    Papers.RationalityTen.RawFacetEmbedding.wellFormedCheck
      (Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.cells c) = true :=
  Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity.record_checked c

end Papers.RationalityTen.RootedCaches.RootedSevenMixed012
