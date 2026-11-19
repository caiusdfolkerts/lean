module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow29Case03786Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M066
public import InducedTerminalMatches.M067

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03786
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2142))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M066.r2143)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2144))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2145))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2146)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2147))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2148))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2149))))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2150))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2151))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2152))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2153))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2154)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2155))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2156))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2157)))))
 (.branch 19
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2158))
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2159))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2160))))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2161))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2162))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M067.r2163)))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
cert_graph_leaf_checked 0 066 2142
cert_graph_leaf_checked 1 066 2143
cert_graph_leaf_checked 2 067 2144
cert_graph_leaf_checked 3 067 2145
cert_graph_leaf_checked 4 067 2146
cert_graph_leaf_checked 5 067 2147
cert_graph_leaf_checked 6 067 2148
cert_graph_leaf_checked 7 067 2149
cert_graph_leaf_checked 8 067 2150
cert_graph_leaf_checked 9 067 2151
cert_graph_leaf_checked 10 067 2152
cert_graph_leaf_checked 11 067 2153
cert_graph_leaf_checked 12 067 2154
cert_graph_leaf_checked 13 067 2155
cert_graph_leaf_checked 14 067 2156
cert_graph_leaf_checked 15 067 2157
cert_graph_leaf_checked 16 067 2158
cert_graph_leaf_checked 17 067 2159
cert_graph_leaf_checked 18 067 2160
cert_graph_leaf_checked 19 067 2161
cert_graph_leaf_checked 20 067 2162
cert_graph_leaf_checked 21 067 2163
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (fun j => Fin.elim0 j)))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03786
