module
prelude
public import RootedSevenMixed012ValidityPart000
public import RootedSevenMixed012ValidityPart001

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 838 :=
  (FiniteChecks.interval_append test 0 512 838
  part_000
  part_001)
theorem record_checked (i : Fin 838) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
