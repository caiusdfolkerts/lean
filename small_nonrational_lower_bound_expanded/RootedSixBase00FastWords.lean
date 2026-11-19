module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase00FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
cert_checked_8 0 64
theorem checked_64 : Interval test 64 96 :=
  interval_of_check test 64 32 (by decide +kernel)

theorem checked : Interval test 0 96 :=
  (FiniteChecks.interval_append test 0 64 96
  checked_0
  checked_64)
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawWords frame := by
  by_cases hf : frame < 96
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 21976) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast.raw_maps_eq frame cell hc
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords
