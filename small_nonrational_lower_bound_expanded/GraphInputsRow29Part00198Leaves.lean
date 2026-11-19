module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00198Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M065
public import InducedTerminalMatches.M066

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable_3 000 065 066 2111 2112
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 065 2111
cert_graph_leaf_checked_2 000 1 066 2112
cert_graph_leaf_certificates_checked_9 000

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
cert_graph_certificateTable_5 001
cert_graph_certificates 001
cert_graph_leaf_checked_3 001
cert_graph_leaf_certificates_checked_7 001

cert_graph_rawLeaves 002
cert_graph_raw_exact 002
noncomputable def record002_certificateTable : Table Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2113))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2114))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2115))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2116))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2117))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2118)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2119))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2120))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2121))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2122))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2123))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2124))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 066 2113
cert_graph_leaf_checked_2 002 1 066 2114
cert_graph_leaf_checked_2 002 2 066 2115
cert_graph_leaf_checked_2 002 3 066 2116
cert_graph_leaf_checked_2 002 4 066 2117
cert_graph_leaf_checked_2 002 5 066 2118
cert_graph_leaf_checked_2 002 6 066 2119
cert_graph_leaf_checked_2 002 7 066 2120
cert_graph_leaf_checked_2 002 8 066 2121
cert_graph_leaf_checked_2 002 9 066 2122
cert_graph_leaf_checked_2 002 10 066 2123
cert_graph_leaf_checked_2 002 11 066 2124
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (fun j => Fin.elim0 j)))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00198
