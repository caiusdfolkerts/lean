module
prelude
public import GraphInputsRow31Part00071Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M084

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00071
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota [] (.quota 1) = true
  exact empty_checked record000.data.quota 1 (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2703))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2704)))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M084.r2703) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M084.r2703
    Nonrational.InducedTerminalMatches.M084.r2703_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M084.r2704) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M084.r2704
    Nonrational.InducedTerminalMatches.M084.r2704_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (fun j => Fin.elim0 j)))
#print axioms record001_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00071
