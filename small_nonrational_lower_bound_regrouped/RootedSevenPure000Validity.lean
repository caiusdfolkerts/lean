module
prelude
public import RootedSevenPure000ValidityPart000
public import RootedSevenPure000ValidityPart001

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 758 :=
  (FiniteChecks.interval_append test 0 512 758
  part_000
  part_001)
theorem record_checked (i : Fin 758) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenPure000.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
