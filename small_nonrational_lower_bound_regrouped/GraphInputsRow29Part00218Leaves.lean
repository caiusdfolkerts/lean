module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00218Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M067
public import InducedTerminalMatches.M068

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
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
cert_graph_certificateTable_5 002
cert_graph_certificates 002
cert_graph_leaf_checked_3 002
cert_graph_leaf_certificates_checked_7 002
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
noncomputable def record006_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2168))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2169))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2170))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2171))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2172)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2173))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2174)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2175))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2176)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2177))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2178))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2179))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2180)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2181))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M068.r2182))))))
cert_graph_certificates 006
cert_graph_leaf_checked_2 006 0 067 2168
cert_graph_leaf_checked_2 006 1 067 2169
cert_graph_leaf_checked_2 006 2 067 2170
cert_graph_leaf_checked_2 006 3 067 2171
cert_graph_leaf_checked_2 006 4 067 2172
cert_graph_leaf_checked_2 006 5 067 2173
cert_graph_leaf_checked_2 006 6 067 2174
cert_graph_leaf_checked_2 006 7 067 2175
cert_graph_leaf_checked_2 006 8 068 2176
cert_graph_leaf_checked_2 006 9 068 2177
cert_graph_leaf_checked_2 006 10 068 2178
cert_graph_leaf_checked_2 006 11 068 2179
cert_graph_leaf_checked_2 006 12 068 2180
cert_graph_leaf_checked_2 006 13 068 2181
cert_graph_leaf_checked_2 006 14 068 2182
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (Fin.cases record006_leaf_checked_1 (Fin.cases record006_leaf_checked_2 (Fin.cases record006_leaf_checked_3 (Fin.cases record006_leaf_checked_4 (Fin.cases record006_leaf_checked_5 (Fin.cases record006_leaf_checked_6 (Fin.cases record006_leaf_checked_7 (Fin.cases record006_leaf_checked_8 (Fin.cases record006_leaf_checked_9 (Fin.cases record006_leaf_checked_10 (Fin.cases record006_leaf_checked_11 (Fin.cases record006_leaf_checked_12 (Fin.cases record006_leaf_checked_13 (Fin.cases record006_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))
#print axioms record006_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218
