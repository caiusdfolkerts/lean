module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00106Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M094

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106
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
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3010))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3011))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3012))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3013))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3014)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3015))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3016)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3017))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3018))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3019))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3020))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3021)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3022))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M094.r3023))))))
cert_graph_certificates 002
cert_graph_leaf_checked_2 002 0 094 3010
cert_graph_leaf_checked_2 002 1 094 3011
cert_graph_leaf_checked_2 002 2 094 3012
cert_graph_leaf_checked_2 002 3 094 3013
cert_graph_leaf_checked_2 002 4 094 3014
cert_graph_leaf_checked_2 002 5 094 3015
cert_graph_leaf_checked_2 002 6 094 3016
cert_graph_leaf_checked_2 002 7 094 3017
cert_graph_leaf_checked_2 002 8 094 3018
cert_graph_leaf_checked_2 002 9 094 3019
cert_graph_leaf_checked_2 002 10 094 3020
cert_graph_leaf_checked_2 002 11 094 3021
cert_graph_leaf_checked_2 002 12 094 3022
cert_graph_leaf_checked_2 002 13 094 3023
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (Fin.cases record002_leaf_checked_1 (Fin.cases record002_leaf_checked_2 (Fin.cases record002_leaf_checked_3 (Fin.cases record002_leaf_checked_4 (Fin.cases record002_leaf_checked_5 (Fin.cases record002_leaf_checked_6 (Fin.cases record002_leaf_checked_7 (Fin.cases record002_leaf_checked_8 (Fin.cases record002_leaf_checked_9 (Fin.cases record002_leaf_checked_10 (Fin.cases record002_leaf_checked_11 (Fin.cases record002_leaf_checked_12 (Fin.cases record002_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106
