module
prelude
public import RootedSevenMixed013ValidityPart000

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 466 :=
  part_000
theorem record_checked (i : Fin 466) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
