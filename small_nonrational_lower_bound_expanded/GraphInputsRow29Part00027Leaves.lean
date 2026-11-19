module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00027Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M034
public import InducedTerminalMatches.M035

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_5 000
cert_graph_certificates 000
cert_graph_leaf_checked_3 000
cert_graph_leaf_certificates_checked_7 000

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
cert_graph_certificateTable_5 001
cert_graph_certificates 001
cert_graph_leaf_checked_3 001
cert_graph_leaf_certificates_checked_7 001

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
cert_graph_certificateTable_5 002
cert_graph_certificates 002
cert_graph_leaf_checked_3 002
cert_graph_leaf_certificates_checked_7 002

cert_graph_rawLeaves 003
cert_graph_raw_exact 003
cert_graph_certificateTable_5 003
cert_graph_certificates 003
cert_graph_leaf_checked_3 003
cert_graph_leaf_certificates_checked_7 003

cert_graph_rawLeaves 004
cert_graph_raw_exact 004
cert_graph_certificateTable_5 004
cert_graph_certificates 004
cert_graph_leaf_checked_3 004
cert_graph_leaf_certificates_checked_7 004

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_5 005
cert_graph_certificates 005
cert_graph_leaf_checked_3 005
cert_graph_leaf_certificates_checked_7 005

cert_graph_rawLeaves 006
cert_graph_raw_exact 006
noncomputable def record006_certificateTable : Table Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1114))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1115)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1116))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1117))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1118))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1119)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1120))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1121))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M035.r1122))))))
cert_graph_certificates 006
cert_graph_leaf_checked_2 006 0 034 1114
cert_graph_leaf_checked_2 006 1 034 1115
cert_graph_leaf_checked_2 006 2 034 1116
cert_graph_leaf_checked_2 006 3 034 1117
cert_graph_leaf_checked_2 006 4 034 1118
cert_graph_leaf_checked_2 006 5 034 1119
cert_graph_leaf_checked_2 006 6 035 1120
cert_graph_leaf_checked_2 006 7 035 1121
cert_graph_leaf_checked_2 006 8 035 1122
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (Fin.cases record006_leaf_checked_1 (Fin.cases record006_leaf_checked_2 (Fin.cases record006_leaf_checked_3 (Fin.cases record006_leaf_checked_4 (Fin.cases record006_leaf_checked_5 (Fin.cases record006_leaf_checked_6 (Fin.cases record006_leaf_checked_7 (Fin.cases record006_leaf_checked_8 (fun j => Fin.elim0 j))))))))))

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_2 007 035 035 035 035 1123 1124 1125 1126 1127 1128
cert_graph_certificates 007
cert_graph_leaf_checked_2 007 0 035 1123
cert_graph_leaf_checked_2 007 1 035 1124
cert_graph_leaf_checked_2 007 2 035 1125
cert_graph_leaf_checked_2 007 3 035 1126
cert_graph_leaf_checked_2 007 4 035 1127
cert_graph_leaf_checked_2 007 5 035 1128
cert_graph_leaf_certificates_checked_6 007
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027
