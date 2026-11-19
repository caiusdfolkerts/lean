module
prelude
public import Papers.RawWitnesses.Type53Data

/-! Small ordinary kernel checks for Appendix B type 53. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type53
open Papers.RationalWitnesses.Raw

theorem facets_00 : (certificate.facets 0).Valid coordinates := by decide +kernel

theorem facets_01 : (certificate.facets 1).Valid coordinates := by decide +kernel

theorem facets_02 : (certificate.facets 2).Valid coordinates := by decide +kernel

theorem facets_03 : (certificate.facets 3).Valid coordinates := by decide +kernel

theorem facets_04 : (certificate.facets 4).Valid coordinates := by decide +kernel

theorem facets_05 : (certificate.facets 5).Valid coordinates := by decide +kernel

theorem facets_06 : (certificate.facets 6).Valid coordinates := by decide +kernel

theorem facets_07 : (certificate.facets 7).Valid coordinates := by decide +kernel

theorem facets_08 : (certificate.facets 8).Valid coordinates := by decide +kernel

theorem facets_09 : (certificate.facets 9).Valid coordinates := by decide +kernel

theorem facets_10 : (certificate.facets 10).Valid coordinates := by decide +kernel

theorem facets_check : ∀ k, (certificate.facets k).Valid coordinates :=
  (Fin.cases facets_00 (Fin.cases facets_01 (Fin.cases facets_02 (Fin.cases facets_03 (Fin.cases facets_04 (Fin.cases facets_05 (Fin.cases facets_06 (Fin.cases facets_07 (Fin.cases facets_08 (Fin.cases facets_09 (Fin.cases facets_10 (fun i => Fin.elim0 i))))))))))))

end Papers.RationalWitnesses.RawWitnesses.Type53
