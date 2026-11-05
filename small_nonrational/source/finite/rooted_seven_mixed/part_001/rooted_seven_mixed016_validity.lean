module
prelude
public import RootedSevenMixed016ValidityPart000
public import RootedSevenMixed016ValidityPart001

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 646 :=
  (FiniteChecks.interval_append test 0 512 646
  part_000
  part_001)
theorem record_checked (i : Fin 646) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed016.Validity
