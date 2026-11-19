module
prelude
public meta import LowerSchemas.Leaves
public import GraphInputsRow26Part00011Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M028
public import InducedTerminalMatches.M029

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011
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
noncomputable def record005_certificateTable : Table Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0915))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0916))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0917))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0918))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0919)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0920))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0921)))))
 (.branch 10
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0922))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0923))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0924))))
 (.branch 12
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0925))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0926)))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M028.r0927))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M029.r0928))))))
cert_graph_certificates 005
cert_graph_leaf_checked_2 005 0 028 0915
cert_graph_leaf_checked_2 005 1 028 0916
cert_graph_leaf_checked_2 005 2 028 0917
cert_graph_leaf_checked_2 005 3 028 0918
cert_graph_leaf_checked_2 005 4 028 0919
cert_graph_leaf_checked_2 005 5 028 0920
cert_graph_leaf_checked_2 005 6 028 0921
cert_graph_leaf_checked_2 005 7 028 0922
cert_graph_leaf_checked_2 005 8 028 0923
cert_graph_leaf_checked_2 005 9 028 0924
cert_graph_leaf_checked_2 005 10 028 0925
cert_graph_leaf_checked_2 005 11 028 0926
cert_graph_leaf_checked_2 005 12 028 0927
cert_graph_leaf_checked_2 005 13 029 0928
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (Fin.cases record005_leaf_checked_3 (Fin.cases record005_leaf_checked_4 (Fin.cases record005_leaf_checked_5 (Fin.cases record005_leaf_checked_6 (Fin.cases record005_leaf_checked_7 (Fin.cases record005_leaf_checked_8 (Fin.cases record005_leaf_checked_9 (Fin.cases record005_leaf_checked_10 (Fin.cases record005_leaf_checked_11 (Fin.cases record005_leaf_checked_12 (Fin.cases record005_leaf_checked_13 (fun j => Fin.elim0 j)))))))))))))))

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
cert_graph_certificateTable 009 029 0929
cert_graph_certificates 009
cert_graph_leaf_checked_2 009 0 029 0929
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
cert_graph_certificateTable_5 018
cert_graph_certificates 018
cert_graph_leaf_checked_3 018
cert_graph_leaf_certificates_checked_7 018

cert_graph_rawLeaves 019
cert_graph_raw_exact 019
cert_graph_certificateTable_5 019
cert_graph_certificates 019
cert_graph_leaf_checked_3 019
cert_graph_leaf_certificates_checked_7 019

cert_graph_rawLeaves 020
cert_graph_raw_exact 020
cert_graph_certificateTable_5 020
cert_graph_certificates 020
cert_graph_leaf_checked_3 020
cert_graph_leaf_certificates_checked_7 020

cert_graph_rawLeaves 021
cert_graph_raw_exact 021
cert_graph_certificateTable_5 021
cert_graph_certificates 021
cert_graph_leaf_checked_3 021
cert_graph_leaf_certificates_checked_7 021

cert_graph_rawLeaves 022
cert_graph_raw_exact 022
cert_graph_certificateTable_5 022
cert_graph_certificates 022
cert_graph_leaf_checked_3 022
cert_graph_leaf_certificates_checked_7 022

cert_graph_rawLeaves 023
cert_graph_raw_exact 023
cert_graph_certificateTable_5 023
cert_graph_certificates 023
cert_graph_leaf_checked_3 023
cert_graph_leaf_certificates_checked_7 023

cert_graph_rawLeaves 024
cert_graph_raw_exact 024
cert_graph_certificateTable_5 024
cert_graph_certificates 024
cert_graph_leaf_checked_3 024
cert_graph_leaf_certificates_checked_7 024

cert_graph_rawLeaves 025
cert_graph_raw_exact 025
cert_graph_certificateTable_5 025
cert_graph_certificates 025
cert_graph_leaf_checked_3 025
cert_graph_leaf_certificates_checked_7 025

cert_graph_rawLeaves 026
cert_graph_raw_exact 026
cert_graph_certificateTable_5 026
cert_graph_certificates 026
cert_graph_leaf_checked_3 026
cert_graph_leaf_certificates_checked_7 026

cert_graph_rawLeaves 027
cert_graph_raw_exact 027
cert_graph_certificateTable_5 027
cert_graph_certificates 027
cert_graph_leaf_checked_3 027
cert_graph_leaf_certificates_checked_7 027

cert_graph_rawLeaves 028
cert_graph_raw_exact 028
cert_graph_certificateTable_5 028
cert_graph_certificates 028
cert_graph_leaf_checked_3 028
cert_graph_leaf_certificates_checked_7 028

cert_graph_rawLeaves 029
cert_graph_raw_exact 029
cert_graph_certificateTable_5 029
cert_graph_certificates 029
cert_graph_leaf_checked_3 029
cert_graph_leaf_certificates_checked_7 029
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011
