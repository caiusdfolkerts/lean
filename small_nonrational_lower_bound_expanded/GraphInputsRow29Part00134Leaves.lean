module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00134Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M058

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134
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
cert_graph_certificateTable 003 058 1861
cert_graph_certificates 003
cert_graph_leaf_checked_2 003 0 058 1861
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
cert_graph_certificateTable_8 009 058 058 058 1862 1863 1864 1865
cert_graph_certificates 009
cert_graph_leaf_checked_2 009 0 058 1862
cert_graph_leaf_checked_2 009 1 058 1863
cert_graph_leaf_checked_2 009 2 058 1864
cert_graph_leaf_checked_2 009 3 058 1865
cert_graph_leaf_certificates_checked_4 009

cert_graph_rawLeaves 010
cert_graph_raw_exact 010
noncomputable def record010_certificateTable : Table Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1866))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1867)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1868))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1869))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1870)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1871))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1872))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1873))))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1874))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1875))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M058.r1876))))))
cert_graph_certificates 010
cert_graph_leaf_checked_2 010 0 058 1866
cert_graph_leaf_checked_2 010 1 058 1867
cert_graph_leaf_checked_2 010 2 058 1868
cert_graph_leaf_checked_2 010 3 058 1869
cert_graph_leaf_checked_2 010 4 058 1870
cert_graph_leaf_checked_2 010 5 058 1871
cert_graph_leaf_checked_2 010 6 058 1872
cert_graph_leaf_checked_2 010 7 058 1873
cert_graph_leaf_checked_2 010 8 058 1874
cert_graph_leaf_checked_2 010 9 058 1875
cert_graph_leaf_checked_2 010 10 058 1876
theorem record010_leaf_certificates_checked : ∀ j : Fin record010.l,
    RawLeafCertificate.check record010.data.quota (record010_rawLeaves j)
      (record010_certificates j) = true :=
  (Fin.cases record010_leaf_checked_0 (Fin.cases record010_leaf_checked_1 (Fin.cases record010_leaf_checked_2 (Fin.cases record010_leaf_checked_3 (Fin.cases record010_leaf_checked_4 (Fin.cases record010_leaf_checked_5 (Fin.cases record010_leaf_checked_6 (Fin.cases record010_leaf_checked_7 (Fin.cases record010_leaf_checked_8 (Fin.cases record010_leaf_checked_9 (Fin.cases record010_leaf_checked_10 (fun j => Fin.elim0 j))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134
