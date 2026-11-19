module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00014Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M033
public import InducedTerminalMatches.M034

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014
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
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1081))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1082))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1083))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1084))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1085)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1086))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M033.r1087)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1088))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1089)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1090))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1091))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1092))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1093)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1094))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1095))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 033 1081
cert_graph_leaf_checked_2 002 1 033 1082
cert_graph_leaf_checked_2 002 2 033 1083
cert_graph_leaf_checked_2 002 3 033 1084
cert_graph_leaf_checked_2 002 4 033 1085
cert_graph_leaf_checked_2 002 5 033 1086
cert_graph_leaf_checked_2 002 6 033 1087
cert_graph_leaf_checked_2 002 7 034 1088
cert_graph_leaf_checked_2 002 8 034 1089
cert_graph_leaf_checked_2 002 9 034 1090
cert_graph_leaf_checked_2 002 10 034 1091
cert_graph_leaf_checked_2 002 11 034 1092
cert_graph_leaf_checked_2 002 12 034 1093
cert_graph_leaf_checked_2 002 13 034 1094
cert_graph_leaf_checked_2 002 14 034 1095
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (Fin.cases record002_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))
#print axioms record002_leaf_certificates_checked

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
noncomputable def record003_certificateTable : Table Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1096))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1097)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1098))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1099))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1100))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1101)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1102))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1103))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1104))))))
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 034 1096
cert_graph_leaf_checked_2 003 1 034 1097
cert_graph_leaf_checked_2 003 2 034 1098
cert_graph_leaf_checked_2 003 3 034 1099
cert_graph_leaf_checked_2 003 4 034 1100
cert_graph_leaf_checked_2 003 5 034 1101
cert_graph_leaf_checked_2 003 6 034 1102
cert_graph_leaf_checked_2 003 7 034 1103
cert_graph_leaf_checked_2 003 8 034 1104
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (fun j => Fin.elim0 j))))))))))
#print axioms record003_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014
