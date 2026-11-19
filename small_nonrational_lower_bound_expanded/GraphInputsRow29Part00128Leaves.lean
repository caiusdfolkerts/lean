module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00128Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M056
public import InducedTerminalMatches.M057

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128
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
noncomputable def record003_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1821))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1822))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1823))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1824))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1825)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1826))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1827)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1828))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1829))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1830))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1831))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1832)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1833))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M057.r1834))))))
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 056 1821
cert_graph_leaf_checked_2 003 1 056 1822
cert_graph_leaf_checked_2 003 2 056 1823
cert_graph_leaf_checked_2 003 3 057 1824
cert_graph_leaf_checked_2 003 4 057 1825
cert_graph_leaf_checked_2 003 5 057 1826
cert_graph_leaf_checked_2 003 6 057 1827
cert_graph_leaf_checked_2 003 7 057 1828
cert_graph_leaf_checked_2 003 8 057 1829
cert_graph_leaf_checked_2 003 9 057 1830
cert_graph_leaf_checked_2 003 10 057 1831
cert_graph_leaf_checked_2 003 11 057 1832
cert_graph_leaf_checked_2 003 12 057 1833
cert_graph_leaf_checked_2 003 13 057 1834
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (Fin.cases record003_leaf_checked_1 (Fin.cases record003_leaf_checked_2 (Fin.cases record003_leaf_checked_3 (Fin.cases record003_leaf_checked_4 (Fin.cases record003_leaf_checked_5 (Fin.cases record003_leaf_checked_6 (Fin.cases record003_leaf_checked_7 (Fin.cases record003_leaf_checked_8 (Fin.cases record003_leaf_checked_9 (Fin.cases record003_leaf_checked_10 (Fin.cases record003_leaf_checked_11 (Fin.cases record003_leaf_checked_12 (Fin.cases record003_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128
