module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow31Part00073Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M084
public import InducedTerminalMatches.M085

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

cert_graph_rawLeaves 000
cert_graph_raw_exact 000
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2708))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2709))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2710))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2711))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2712))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2713)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2714))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2715))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2716))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2717))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2718))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M084.r2719))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2720))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2721))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2722))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2723))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2724))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2725)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2726))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2727))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2728))))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2729))
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2730))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M085.r2731)))))))
cert_graph_certificates 000
cert_graph_leaf_checked_2 000 0 084 2708
cert_graph_leaf_checked_2 000 1 084 2709
cert_graph_leaf_checked_2 000 2 084 2710
cert_graph_leaf_checked_2 000 3 084 2711
cert_graph_leaf_checked_2 000 4 084 2712
cert_graph_leaf_checked_2 000 5 084 2713
cert_graph_leaf_checked_2 000 6 084 2714
cert_graph_leaf_checked_2 000 7 084 2715
cert_graph_leaf_checked_2 000 8 084 2716
cert_graph_leaf_checked_2 000 9 084 2717
cert_graph_leaf_checked_2 000 10 084 2718
cert_graph_leaf_checked_2 000 11 084 2719
cert_graph_leaf_checked_2 000 12 085 2720
cert_graph_leaf_checked_2 000 13 085 2721
cert_graph_leaf_checked_2 000 14 085 2722
cert_graph_leaf_checked_2 000 15 085 2723
cert_graph_leaf_checked_2 000 16 085 2724
cert_graph_leaf_checked_2 000 17 085 2725
cert_graph_leaf_checked_2 000 18 085 2726
cert_graph_leaf_checked_2 000 19 085 2727
cert_graph_leaf_checked_2 000 20 085 2728
cert_graph_leaf_checked_2 000 21 085 2729
cert_graph_leaf_checked_2 000 22 085 2730
cert_graph_leaf_checked_2 000 23 085 2731
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (fun j => Fin.elim0 j)))))))))))))))))))))))))

cert_graph_rawLeaves 001
cert_graph_raw_exact 001
cert_graph_certificateTable_2 001 085 085 085 085 2732 2733 2734 2735 2736 2737
cert_graph_certificates 001
cert_graph_leaf_checked_2 001 0 085 2732
cert_graph_leaf_checked_2 001 1 085 2733
cert_graph_leaf_checked_2 001 2 085 2734
cert_graph_leaf_checked_2 001 3 085 2735
cert_graph_leaf_checked_2 001 4 085 2736
cert_graph_leaf_checked_2 001 5 085 2737
cert_graph_leaf_certificates_checked_6 001

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
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073
