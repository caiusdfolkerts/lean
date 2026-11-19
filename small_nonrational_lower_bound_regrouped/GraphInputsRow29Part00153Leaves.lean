module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00153Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M060

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153
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
cert_graph_certificateTable_5 006
cert_graph_certificates 006
cert_graph_leaf_checked_3 006
cert_graph_leaf_certificates_checked_7 006
#print axioms record006_leaf_certificates_checked

cert_graph_rawLeaves 007
cert_graph_raw_exact 007
cert_graph_certificateTable_5 007
cert_graph_certificates 007
cert_graph_leaf_checked_3 007
cert_graph_leaf_certificates_checked_7 007
#print axioms record007_leaf_certificates_checked

cert_graph_rawLeaves 008
cert_graph_raw_exact 008
noncomputable def record008_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1923))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1924))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1925))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1926))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1927)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1928))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1929)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1930))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1931))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1932))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1933))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1934)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1935))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M060.r1936))))))
cert_graph_certificates 008
cert_graph_leaf_checked_2 008 0 060 1923
cert_graph_leaf_checked_2 008 1 060 1924
cert_graph_leaf_checked_2 008 2 060 1925
cert_graph_leaf_checked_2 008 3 060 1926
cert_graph_leaf_checked_2 008 4 060 1927
cert_graph_leaf_checked_2 008 5 060 1928
cert_graph_leaf_checked_2 008 6 060 1929
cert_graph_leaf_checked_2 008 7 060 1930
cert_graph_leaf_checked_2 008 8 060 1931
cert_graph_leaf_checked_2 008 9 060 1932
cert_graph_leaf_checked_2 008 10 060 1933
cert_graph_leaf_checked_2 008 11 060 1934
cert_graph_leaf_checked_2 008 12 060 1935
cert_graph_leaf_checked_2 008 13 060 1936
theorem record008_leaf_certificates_checked : ∀ j : Fin record008.l,
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves j)
      (record008_certificates j) = true :=
  (Fin.cases record008_leaf_checked_0 (Fin.cases record008_leaf_checked_1 (Fin.cases record008_leaf_checked_2 (Fin.cases record008_leaf_checked_3 (Fin.cases record008_leaf_checked_4 (Fin.cases record008_leaf_checked_5 (Fin.cases record008_leaf_checked_6 (Fin.cases record008_leaf_checked_7 (Fin.cases record008_leaf_checked_8 (Fin.cases record008_leaf_checked_9 (Fin.cases record008_leaf_checked_10 (Fin.cases record008_leaf_checked_11 (Fin.cases record008_leaf_checked_12 (Fin.cases record008_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))
#print axioms record008_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153
