module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow29Part00117Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M056

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117
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
noncomputable def record008_certificateTable : Table Certificate :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1797))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1798)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1799))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1800))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1801))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1802)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1803))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1804))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1805))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1806))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1807)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1808))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1809))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1810))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1811)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1812))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1813))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M056.r1814)))))))
cert_graph_certificates 008
cert_graph_leaf_checked_2 008 0 056 1797
cert_graph_leaf_checked_2 008 1 056 1798
cert_graph_leaf_checked_2 008 2 056 1799
cert_graph_leaf_checked_2 008 3 056 1800
cert_graph_leaf_checked_2 008 4 056 1801
cert_graph_leaf_checked_2 008 5 056 1802
cert_graph_leaf_checked_2 008 6 056 1803
cert_graph_leaf_checked_2 008 7 056 1804
cert_graph_leaf_checked_2 008 8 056 1805
cert_graph_leaf_checked_2 008 9 056 1806
cert_graph_leaf_checked_2 008 10 056 1807
cert_graph_leaf_checked_2 008 11 056 1808
cert_graph_leaf_checked_2 008 12 056 1809
cert_graph_leaf_checked_2 008 13 056 1810
cert_graph_leaf_checked_2 008 14 056 1811
cert_graph_leaf_checked_2 008 15 056 1812
cert_graph_leaf_checked_2 008 16 056 1813
cert_graph_leaf_checked_2 008 17 056 1814
theorem record008_leaf_certificates_checked : ∀ j : Fin record008.l,
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves j)
      (record008_certificates j) = true :=
  (Fin.cases record008_leaf_checked_0 (Fin.cases record008_leaf_checked_1 (Fin.cases record008_leaf_checked_2 (Fin.cases record008_leaf_checked_3 (Fin.cases record008_leaf_checked_4 (Fin.cases record008_leaf_checked_5 (Fin.cases record008_leaf_checked_6 (Fin.cases record008_leaf_checked_7 (Fin.cases record008_leaf_checked_8 (Fin.cases record008_leaf_checked_9 (Fin.cases record008_leaf_checked_10 (Fin.cases record008_leaf_checked_11 (Fin.cases record008_leaf_checked_12 (Fin.cases record008_leaf_checked_13 (Fin.cases record008_leaf_checked_14 (Fin.cases record008_leaf_checked_15 (Fin.cases record008_leaf_checked_16 (Fin.cases record008_leaf_checked_17 (fun j => Fin.elim0 j)))))))))))))))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117
