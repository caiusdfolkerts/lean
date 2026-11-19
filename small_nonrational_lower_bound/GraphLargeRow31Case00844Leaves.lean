module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow31Case00844Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M083
public import InducedTerminalMatches.M084

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2673))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2674))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2675))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2676))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2677)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2678))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2679)))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2680))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2681)))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2682))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2683))))
 (.branch 13
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2684))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2685)))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2686))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M083.r2687))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2688))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2689))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2690))))
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2691))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2692)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2693))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2694)))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2695))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2696)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2697))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2698))))
 (.branch 28
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2699))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2700)))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2701))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2702)))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
cert_graph_leaf_checked 0 083 2673
cert_graph_leaf_checked 1 083 2674
cert_graph_leaf_checked 2 083 2675
cert_graph_leaf_checked 3 083 2676
cert_graph_leaf_checked 4 083 2677
cert_graph_leaf_checked 5 083 2678
cert_graph_leaf_checked 6 083 2679
cert_graph_leaf_checked 7 083 2680
cert_graph_leaf_checked 8 083 2681
cert_graph_leaf_checked 9 083 2682
cert_graph_leaf_checked 10 083 2683
cert_graph_leaf_checked 11 083 2684
cert_graph_leaf_checked 12 083 2685
cert_graph_leaf_checked 13 083 2686
cert_graph_leaf_checked 14 083 2687
cert_graph_leaf_checked 15 084 2688
cert_graph_leaf_checked 16 084 2689
cert_graph_leaf_checked 17 084 2690
cert_graph_leaf_checked 18 084 2691
cert_graph_leaf_checked 19 084 2692
cert_graph_leaf_checked 20 084 2693
cert_graph_leaf_checked 21 084 2694
cert_graph_leaf_checked 22 084 2695
cert_graph_leaf_checked 23 084 2696
cert_graph_leaf_checked 24 084 2697
cert_graph_leaf_checked 25 084 2698
cert_graph_leaf_checked 26 084 2699
cert_graph_leaf_checked 27 084 2700
cert_graph_leaf_checked 28 084 2701
cert_graph_leaf_checked 29 084 2702
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
