module
prelude
public import GraphInputsRow31Part00036Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M078
public import InducedTerminalMatches.M079

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2521))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2522))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2523))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2524))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2525)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2526))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2527)))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M078.r2521) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M078.r2521
    Nonrational.InducedTerminalMatches.M078.r2521_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M078.r2522) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M078.r2522
    Nonrational.InducedTerminalMatches.M078.r2522_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M078.r2523) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M078.r2523
    Nonrational.InducedTerminalMatches.M078.r2523_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M078.r2524) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M078.r2524
    Nonrational.InducedTerminalMatches.M078.r2524_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M078.r2525) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M078.r2525
    Nonrational.InducedTerminalMatches.M078.r2525_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M078.r2526) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M078.r2526
    Nonrational.InducedTerminalMatches.M078.r2526_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M078.r2527) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M078.r2527
    Nonrational.InducedTerminalMatches.M078.r2527_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (fun j => Fin.elim0 j))))))))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.leaf (.vertexLink 0))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  decide +kernel
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record001_leaf_certificates_checked

noncomputable def record002_rawLeaves (j : Fin record002.l) : List Cell :=
  (record002.leaf j).map record002.data.cells
theorem record002_raw_exact (j : Fin record002.l) :
    (record002.leaf j).map record002.data.cells = record002_rawLeaves j := rfl
noncomputable def record002_certificateTable : Table Certificate :=
(.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2528))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M079.r2528) = true
  exact matching_checked record002.data.quota (record002_rawLeaves 0) Nonrational.InducedTerminalMatches.M079.r2528
    Nonrational.InducedTerminalMatches.M079.r2528_checked (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record002_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036
