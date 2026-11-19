module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00026Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M034

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026
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
cert_graph_certificateTable_5 012
cert_graph_certificates 012
cert_graph_leaf_checked_3 012
cert_graph_leaf_certificates_checked_7 012

cert_graph_rawLeaves 013
cert_graph_raw_exact 013
cert_graph_certificateTable_5 013
cert_graph_certificates 013
cert_graph_leaf_checked_3 013
cert_graph_leaf_certificates_checked_7 013

cert_graph_rawLeaves 014
cert_graph_raw_exact 014
cert_graph_certificateTable_5 014
cert_graph_certificates 014
cert_graph_leaf_checked_3 014
cert_graph_leaf_certificates_checked_7 014

cert_graph_rawLeaves 015
cert_graph_raw_exact 015
cert_graph_certificateTable_5 015
cert_graph_certificates 015
cert_graph_leaf_checked_3 015
cert_graph_leaf_certificates_checked_7 015

cert_graph_rawLeaves 016
cert_graph_raw_exact 016
cert_graph_certificateTable_5 016
cert_graph_certificates 016
cert_graph_leaf_checked_3 016
cert_graph_leaf_certificates_checked_7 016

cert_graph_rawLeaves 017
cert_graph_raw_exact 017
cert_graph_certificateTable_5 017
cert_graph_certificates 017
cert_graph_leaf_checked_3 017
cert_graph_leaf_certificates_checked_7 017

cert_graph_rawLeaves 018
cert_graph_raw_exact 018
noncomputable def record018_certificateTable : Table Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1105))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1106)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1107))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1108))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1109))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1110)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1111))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1112))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M034.r1113))))))
cert_graph_certificates 018
cert_graph_leaf_checked_2 018 0 034 1105
cert_graph_leaf_checked_2 018 1 034 1106
cert_graph_leaf_checked_2 018 2 034 1107
cert_graph_leaf_checked_2 018 3 034 1108
cert_graph_leaf_checked_2 018 4 034 1109
cert_graph_leaf_checked_2 018 5 034 1110
cert_graph_leaf_checked_2 018 6 034 1111
cert_graph_leaf_checked_2 018 7 034 1112
cert_graph_leaf_checked_2 018 8 034 1113
theorem record018_leaf_certificates_checked : ∀ j : Fin record018.l,
    RawLeafCertificate.check record018.data.quota (record018_rawLeaves j)
      (record018_certificates j) = true :=
  (Fin.cases record018_leaf_checked_0 (Fin.cases record018_leaf_checked_1 (Fin.cases record018_leaf_checked_2 (Fin.cases record018_leaf_checked_3 (Fin.cases record018_leaf_checked_4 (Fin.cases record018_leaf_checked_5 (Fin.cases record018_leaf_checked_6 (Fin.cases record018_leaf_checked_7 (Fin.cases record018_leaf_checked_8 (fun j => Fin.elim0 j))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00026
