module
prelude
public import RootedSevenMixed009ValidityPart000
public import RootedSevenMixed009ValidityPart001

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 910 :=
  (FiniteChecks.interval_append test 0 512 910
  part_000
  part_001)
theorem record_checked (i : Fin 910) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
