module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00142Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M059

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142
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
noncomputable def record001_certificateTable : Table Certificate :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1888))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1889))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1890))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1891))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1892))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1893)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1894))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1895))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1896))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1897))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1898)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1899))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1900))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1901))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1902))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1903))))
 (.branch 18
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1904))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1905)))
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1906))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1907)))))
 (.branch 23
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1908))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1909))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1910))))
 (.branch 25
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1911))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1912)))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1913))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1914)))))))
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 059 1888
cert_graph_leaf_checked_2 001 1 059 1889
cert_graph_leaf_checked_2 001 2 059 1890
cert_graph_leaf_checked_2 001 3 059 1891
cert_graph_leaf_checked_2 001 4 059 1892
cert_graph_leaf_checked_2 001 5 059 1893
cert_graph_leaf_checked_2 001 6 059 1894
cert_graph_leaf_checked_2 001 7 059 1895
cert_graph_leaf_checked_2 001 8 059 1896
cert_graph_leaf_checked_2 001 9 059 1897
cert_graph_leaf_checked_2 001 10 059 1898
cert_graph_leaf_checked_2 001 11 059 1899
cert_graph_leaf_checked_2 001 12 059 1900
cert_graph_leaf_checked_2 001 13 059 1901
cert_graph_leaf_checked_2 001 14 059 1902
cert_graph_leaf_checked_2 001 15 059 1903
cert_graph_leaf_checked_2 001 16 059 1904
cert_graph_leaf_checked_2 001 17 059 1905
cert_graph_leaf_checked_2 001 18 059 1906
cert_graph_leaf_checked_2 001 19 059 1907
cert_graph_leaf_checked_2 001 20 059 1908
cert_graph_leaf_checked_2 001 21 059 1909
cert_graph_leaf_checked_2 001 22 059 1910
cert_graph_leaf_checked_2 001 23 059 1911
cert_graph_leaf_checked_2 001 24 059 1912
cert_graph_leaf_checked_2 001 25 059 1913
cert_graph_leaf_checked_2 001 26 059 1914
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (Fin.cases record001_leaf_checked_18 (Fin.cases record001_leaf_checked_19 (Fin.cases record001_leaf_checked_20 (Fin.cases record001_leaf_checked_21 (Fin.cases record001_leaf_checked_22 (Fin.cases record001_leaf_checked_23 (Fin.cases record001_leaf_checked_24 (Fin.cases record001_leaf_checked_25 (Fin.cases record001_leaf_checked_26 (fun j => Fin.elim0 j))))))))))))))))))))))))))))

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
cert_graph_certificateTable_3 004 059 059 1915 1916
cert_graph_certificates 004
cert_graph_leaf_checked_2 004 0 059 1915
cert_graph_leaf_checked_2 004 1 059 1916
cert_graph_leaf_certificates_checked_9 004

cert_graph_rawLeaves 005
cert_graph_raw_exact 005
cert_graph_certificateTable_5 005
cert_graph_certificates 005
cert_graph_leaf_checked_3 005
cert_graph_leaf_certificates_checked_7 005
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142
