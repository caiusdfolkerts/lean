module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00037Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M039
public import InducedTerminalMatches.M040

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037
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
cert_graph_certificateTable_5 009
cert_graph_certificates 009
cert_graph_leaf_checked_3 009
cert_graph_leaf_certificates_checked_7 009

cert_graph_rawLeaves 010
cert_graph_raw_exact 010
cert_graph_certificateTable_5 010
cert_graph_certificates 010
cert_graph_leaf_checked_3 010
cert_graph_leaf_certificates_checked_7 010

cert_graph_rawLeaves 011
cert_graph_raw_exact 011
cert_graph_certificateTable_5 011
cert_graph_certificates 011
cert_graph_leaf_checked_3 011
cert_graph_leaf_certificates_checked_7 011

cert_graph_rawLeaves 012
cert_graph_raw_exact 012
noncomputable def record012_certificateTable : Table Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1265))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1266)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1267))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1268))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1269))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1270)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1271))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1272)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1273))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1274)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1275))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1276))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1277))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1278)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M039.r1279))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1280))))))
cert_graph_certificates 012
cert_graph_leaf_checked_2 012 0 039 1265
cert_graph_leaf_checked_2 012 1 039 1266
cert_graph_leaf_checked_2 012 2 039 1267
cert_graph_leaf_checked_2 012 3 039 1268
cert_graph_leaf_checked_2 012 4 039 1269
cert_graph_leaf_checked_2 012 5 039 1270
cert_graph_leaf_checked_2 012 6 039 1271
cert_graph_leaf_checked_2 012 7 039 1272
cert_graph_leaf_checked_2 012 8 039 1273
cert_graph_leaf_checked_2 012 9 039 1274
cert_graph_leaf_checked_2 012 10 039 1275
cert_graph_leaf_checked_2 012 11 039 1276
cert_graph_leaf_checked_2 012 12 039 1277
cert_graph_leaf_checked_2 012 13 039 1278
cert_graph_leaf_checked_2 012 14 039 1279
cert_graph_leaf_checked_2 012 15 040 1280
theorem record012_leaf_certificates_checked : ∀ j : Fin record012.l,
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves j)
      (record012_certificates j) = true :=
  (Fin.cases record012_leaf_checked_0 (Fin.cases record012_leaf_checked_1 (Fin.cases record012_leaf_checked_2 (Fin.cases record012_leaf_checked_3 (Fin.cases record012_leaf_checked_4 (Fin.cases record012_leaf_checked_5 (Fin.cases record012_leaf_checked_6 (Fin.cases record012_leaf_checked_7 (Fin.cases record012_leaf_checked_8 (Fin.cases record012_leaf_checked_9 (Fin.cases record012_leaf_checked_10 (Fin.cases record012_leaf_checked_11 (Fin.cases record012_leaf_checked_12 (Fin.cases record012_leaf_checked_13 (Fin.cases record012_leaf_checked_14 (Fin.cases record012_leaf_checked_15 (fun j => Fin.elim0 j)))))))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037
