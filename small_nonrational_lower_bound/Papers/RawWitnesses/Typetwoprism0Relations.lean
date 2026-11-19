module
prelude
public import Papers.RawWitnesses.Typetwoprism0Data

/-! Small ordinary kernel checks for Appendix B type two_prism_0. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Typetwoprism0
open Papers.RationalWitnesses.Raw

theorem relations_00 : RelationValid coordinates (certificate.relations 0) := by decide +kernel

theorem relations_01 : RelationValid coordinates (certificate.relations 1) := by decide +kernel

theorem relations_02 : RelationValid coordinates (certificate.relations 2) := by decide +kernel

theorem relations_03 : RelationValid coordinates (certificate.relations 3) := by decide +kernel

theorem relations_04 : RelationValid coordinates (certificate.relations 4) := by decide +kernel

theorem relations_05 : RelationValid coordinates (certificate.relations 5) := by decide +kernel

theorem relations_06 : RelationValid coordinates (certificate.relations 6) := by decide +kernel

theorem relations_07 : RelationValid coordinates (certificate.relations 7) := by decide +kernel

theorem relations_08 : RelationValid coordinates (certificate.relations 8) := by decide +kernel

theorem relations_09 : RelationValid coordinates (certificate.relations 9) := by decide +kernel

theorem relations_10 : RelationValid coordinates (certificate.relations 10) := by decide +kernel

theorem relations_11 : RelationValid coordinates (certificate.relations 11) := by decide +kernel

theorem relations_12 : RelationValid coordinates (certificate.relations 12) := by decide +kernel

theorem relations_13 : RelationValid coordinates (certificate.relations 13) := by decide +kernel

theorem relations_14 : RelationValid coordinates (certificate.relations 14) := by decide +kernel

theorem relations_15 : RelationValid coordinates (certificate.relations 15) := by decide +kernel

theorem relations_16 : RelationValid coordinates (certificate.relations 16) := by decide +kernel

theorem relations_17 : RelationValid coordinates (certificate.relations 17) := by decide +kernel

theorem relations_18 : RelationValid coordinates (certificate.relations 18) := by decide +kernel

theorem relations_19 : RelationValid coordinates (certificate.relations 19) := by decide +kernel

theorem relations_20 : RelationValid coordinates (certificate.relations 20) := by decide +kernel

theorem relations_21 : RelationValid coordinates (certificate.relations 21) := by decide +kernel

theorem relations_22 : RelationValid coordinates (certificate.relations 22) := by decide +kernel

theorem relations_check : ∀ k, RelationValid coordinates (certificate.relations k) :=
  (Fin.cases relations_00 (Fin.cases relations_01 (Fin.cases relations_02 (Fin.cases relations_03 (Fin.cases relations_04 (Fin.cases relations_05 (Fin.cases relations_06 (Fin.cases relations_07 (Fin.cases relations_08 (Fin.cases relations_09 (Fin.cases relations_10 (Fin.cases relations_11 (Fin.cases relations_12 (Fin.cases relations_13 (Fin.cases relations_14 (Fin.cases relations_15 (Fin.cases relations_16 (Fin.cases relations_17 (Fin.cases relations_18 (Fin.cases relations_19 (Fin.cases relations_20 (Fin.cases relations_21 (Fin.cases relations_22 (fun i => Fin.elim0 i))))))))))))))))))))))))

end Papers.RationalWitnesses.RawWitnesses.Typetwoprism0
