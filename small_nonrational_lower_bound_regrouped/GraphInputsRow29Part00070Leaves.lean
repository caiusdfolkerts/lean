module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00070Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M045

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_5 000
cert_graph_certificates 000
cert_graph_leaf_checked_3 000
cert_graph_leaf_certificates_checked_7 000
#print axioms record000_leaf_certificates_checked

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
cert_graph_certificateTable_5 001
cert_graph_certificates 001
cert_graph_leaf_checked_3 001
cert_graph_leaf_certificates_checked_7 001
#print axioms record001_leaf_certificates_checked

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
noncomputable def record002_certificateTable : Table Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1441))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1442))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1443))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1444))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1445))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1446)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1447))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1448))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1449))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1450))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1451))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M045.r1452))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 045 1441
cert_graph_leaf_checked_2 002 1 045 1442
cert_graph_leaf_checked_2 002 2 045 1443
cert_graph_leaf_checked_2 002 3 045 1444
cert_graph_leaf_checked_2 002 4 045 1445
cert_graph_leaf_checked_2 002 5 045 1446
cert_graph_leaf_checked_2 002 6 045 1447
cert_graph_leaf_checked_2 002 7 045 1448
cert_graph_leaf_checked_2 002 8 045 1449
cert_graph_leaf_checked_2 002 9 045 1450
cert_graph_leaf_checked_2 002 10 045 1451
cert_graph_leaf_checked_2 002 11 045 1452
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (fun j => Fin.elim0 j)))))))))))))
#print axioms record002_leaf_certificates_checked

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
cert_graph_certificateTable_5 003
cert_graph_certificates 003
cert_graph_leaf_checked_3 003
cert_graph_leaf_certificates_checked_7 003
#print axioms record003_leaf_certificates_checked

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_5 004
cert_graph_certificates 004
cert_graph_leaf_checked_3 004
cert_graph_leaf_certificates_checked_7 004
#print axioms record004_leaf_certificates_checked

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_5 005
cert_graph_certificates 005
cert_graph_leaf_checked_3 005
cert_graph_leaf_certificates_checked_7 005
#print axioms record005_leaf_certificates_checked

cert_graph_rawLeaves 006
cert_graph_raw_exact 006
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006
#print axioms record006_leaf_certificates_checked

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_5 007
cert_graph_certificates 007
cert_graph_leaf_checked_3 007
cert_graph_leaf_certificates_checked_7 007
#print axioms record007_leaf_certificates_checked

cert_graph_rawLeaves 008
cert_graph_raw_exact 008
cert_graph_certificateTable_5 008
cert_graph_certificates 008
cert_graph_leaf_checked_3 008
cert_graph_leaf_certificates_checked_7 008
#print axioms record008_leaf_certificates_checked

cert_graph_rawLeaves 009
cert_graph_raw_exact 009
cert_graph_certificateTable_5 009
cert_graph_certificates 009
cert_graph_leaf_checked_3 009
cert_graph_leaf_certificates_checked_7 009
#print axioms record009_leaf_certificates_checked

cert_graph_rawLeaves 010
cert_graph_raw_exact 010
cert_graph_certificateTable_5 010
cert_graph_certificates 010
cert_graph_leaf_checked_3 010
cert_graph_leaf_certificates_checked_7 010
#print axioms record010_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070
