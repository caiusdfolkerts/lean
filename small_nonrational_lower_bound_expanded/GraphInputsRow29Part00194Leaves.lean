module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00194Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M065

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
cert_graph_certificateTable 000 065 2083
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 065 2083
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
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_5 007
cert_graph_certificates 007
cert_graph_leaf_checked_3 007
cert_graph_leaf_certificates_checked_7 007

cert_graph_rawLeaves 008
cert_graph_raw_exact 008
cert_graph_certificateTable_5 008
cert_graph_certificates 008
cert_graph_leaf_checked_3 008
cert_graph_leaf_certificates_checked_7 008

cert_graph_rawLeaves 009
cert_graph_raw_exact 009
noncomputable def record009_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2084))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2085))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2086))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2087))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2088)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2089))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2090)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2091))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2092)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2093))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2094))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2095))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2096)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2097))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M065.r2098))))))
cert_graph_certificates 009
cert_graph_leaf_checked_2 009 0 065 2084
cert_graph_leaf_checked_2 009 1 065 2085
cert_graph_leaf_checked_2 009 2 065 2086
cert_graph_leaf_checked_2 009 3 065 2087
cert_graph_leaf_checked_2 009 4 065 2088
cert_graph_leaf_checked_2 009 5 065 2089
cert_graph_leaf_checked_2 009 6 065 2090
cert_graph_leaf_checked_2 009 7 065 2091
cert_graph_leaf_checked_2 009 8 065 2092
cert_graph_leaf_checked_2 009 9 065 2093
cert_graph_leaf_checked_2 009 10 065 2094
cert_graph_leaf_checked_2 009 11 065 2095
cert_graph_leaf_checked_2 009 12 065 2096
cert_graph_leaf_checked_2 009 13 065 2097
cert_graph_leaf_checked_2 009 14 065 2098
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (Fin.cases record009_leaf_checked_1 (Fin.cases record009_leaf_checked_2 (Fin.cases record009_leaf_checked_3 (Fin.cases record009_leaf_checked_4 (Fin.cases record009_leaf_checked_5 (Fin.cases record009_leaf_checked_6 (Fin.cases record009_leaf_checked_7 (Fin.cases record009_leaf_checked_8 (Fin.cases record009_leaf_checked_9 (Fin.cases record009_leaf_checked_10 (Fin.cases record009_leaf_checked_11 (Fin.cases record009_leaf_checked_12 (Fin.cases record009_leaf_checked_13 (Fin.cases record009_leaf_checked_14 (fun j => Fin.elim0 j))))))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00194
