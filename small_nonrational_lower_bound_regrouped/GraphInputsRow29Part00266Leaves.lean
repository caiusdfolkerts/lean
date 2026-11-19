module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00266Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M070

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266
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
noncomputable def record005_certificateTable : Table Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2252))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2253)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2254))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2255))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2256))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2257)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2258))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2259))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2260))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2261))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2262)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2263))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2264))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2265))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2266)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2267))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2268))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M070.r2269)))))))
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 070 2252
cert_graph_leaf_checked_2 005 1 070 2253
cert_graph_leaf_checked_2 005 2 070 2254
cert_graph_leaf_checked_2 005 3 070 2255
cert_graph_leaf_checked_2 005 4 070 2256
cert_graph_leaf_checked_2 005 5 070 2257
cert_graph_leaf_checked_2 005 6 070 2258
cert_graph_leaf_checked_2 005 7 070 2259
cert_graph_leaf_checked_2 005 8 070 2260
cert_graph_leaf_checked_2 005 9 070 2261
cert_graph_leaf_checked_2 005 10 070 2262
cert_graph_leaf_checked_2 005 11 070 2263
cert_graph_leaf_checked_2 005 12 070 2264
cert_graph_leaf_checked_2 005 13 070 2265
cert_graph_leaf_checked_2 005 14 070 2266
cert_graph_leaf_checked_2 005 15 070 2267
cert_graph_leaf_checked_2 005 16 070 2268
cert_graph_leaf_checked_2 005 17 070 2269
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (Fin.cases record005_leaf_checked_3 (Fin.cases record005_leaf_checked_4 (Fin.cases record005_leaf_checked_5 (Fin.cases record005_leaf_checked_6 (Fin.cases record005_leaf_checked_7 (Fin.cases record005_leaf_checked_8 (Fin.cases record005_leaf_checked_9 (Fin.cases record005_leaf_checked_10 (Fin.cases record005_leaf_checked_11 (Fin.cases record005_leaf_checked_12 (Fin.cases record005_leaf_checked_13 (Fin.cases record005_leaf_checked_14 (Fin.cases record005_leaf_checked_15 (Fin.cases record005_leaf_checked_16 (Fin.cases record005_leaf_checked_17 (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record005_leaf_certificates_checked

cert_graph_rawLeaves 006
cert_graph_raw_exact 006
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006
#print axioms record006_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266
