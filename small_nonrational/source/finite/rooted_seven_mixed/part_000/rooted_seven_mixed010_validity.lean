module
prelude
public import RootedSevenMixed010ValidityPart000

@[expose] public section
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
open Papers.RationalityTen
theorem checked : FiniteChecks.Interval test 0 430 :=
  part_000
theorem record_checked (i : Fin 430) :
    RawFacetEmbedding.wellFormedCheck (Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.cells i) = true := by
  have h := checked i.val (Nat.zero_le _) i.isLt
  simpa only [test, Fin.ofNat_val_eq_self] using h
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
