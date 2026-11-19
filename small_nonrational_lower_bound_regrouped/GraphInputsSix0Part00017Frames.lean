module
prelude
public meta import LowerSchemas.Frames
public meta import CertificateNumbers
public import GraphInputsSix0Part00017Data
public import RawFrameSupport
public import SharedFrameGroups065Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups072Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
cert_graph_frame_supported_4 000
cert_graph_frames_supported_2 000
#print axioms record000_frames_supported
cert_graph_frame_supported_4 001
cert_graph_frames_supported_2 001
#print axioms record001_frames_supported
cert_graph_frame_supported_4 002
cert_graph_frame_indices 002 001 1081 13 0
cert_graph_frame_graph 002 001 1081
cert_graph_frame_links 002 001 0000 1081 1 0 64 64
cert_graph_frame_links 002 001 0064 1081 1 64 118 54
cert_graph_frame_links_7 002 001 1081 1 118
cert_graph_frame_supported_3 002 001 1 1081
cert_graph_frame_indices 002 002 1026 11 1
cert_graph_frame_graph 002 002 1026
cert_graph_frame_links 002 002 0000 1026 2 0 64 64
cert_graph_frame_links 002 002 0064 1026 2 64 118 54
cert_graph_frame_links_7 002 002 1026 2 118
cert_graph_frame_supported_3 002 002 2 1026
cert_graph_frames_supported_17 002
#print axioms record002_frames_supported
cert_graph_frame_supported_4 003
cert_graph_frame_indices 003 001 1052 13 2
cert_graph_frame_graph 003 001 1052
cert_graph_frame_links 003 001 0000 1052 1 0 64 64
cert_graph_frame_links 003 001 0064 1052 1 64 124 60
cert_graph_frame_links_7 003 001 1052 1 124
cert_graph_frame_supported_3 003 001 1 1052
cert_graph_frame_indices 003 002 1081 13 3
cert_graph_frame_graph 003 002 1081
cert_graph_frame_links 003 002 0000 1081 2 0 64 64
cert_graph_frame_links 003 002 0064 1081 2 64 124 60
cert_graph_frame_links_7 003 002 1081 2 124
cert_graph_frame_supported_3 003 002 2 1081
cert_graph_frame_indices 003 003 1026 11 4
cert_graph_frame_graph 003 003 1026
cert_graph_frame_links 003 003 0000 1026 3 0 64 64
cert_graph_frame_links 003 003 0064 1026 3 64 124 60
cert_graph_frame_links_7 003 003 1026 3 124
cert_graph_frame_supported_3 003 003 3 1026
cert_graph_frame_indices 003 004 1031 10 5
cert_graph_frame_graph 003 004 1031
cert_graph_frame_links 003 004 0000 1031 4 0 64 64
cert_graph_frame_links 003 004 0064 1031 4 64 124 60
cert_graph_frame_links_7 003 004 1031 4 124
cert_graph_frame_supported_3 003 004 4 1031
cert_graph_frame_indices 003 005 0871 12 6
cert_graph_frame_graph 003 005 0871
cert_graph_frame_links 003 005 0000 0871 5 0 64 64
cert_graph_frame_links 003 005 0064 0871 5 64 124 60
cert_graph_frame_links_7 003 005 0871 5 124
cert_graph_frame_supported_3 003 005 5 0871
cert_graph_frame_indices 003 006 0826 11 7
cert_graph_frame_graph 003 006 0826
cert_graph_frame_links 003 006 0000 0826 6 0 64 64
cert_graph_frame_links 003 006 0064 0826 6 64 124 60
cert_graph_frame_links_7 003 006 0826 6 124
cert_graph_frame_supported_3 003 006 6 0826
cert_graph_frame_indices 003 007 0847 11 8
cert_graph_frame_graph 003 007 0847
cert_graph_frame_links 003 007 0000 0847 7 0 64 64
cert_graph_frame_links 003 007 0064 0847 7 64 124 60
cert_graph_frame_links_7 003 007 0847 7 124
cert_graph_frame_supported_3 003 007 7 0847
cert_graph_frame_indices 003 008 0803 7 9
cert_graph_frame_graph 003 008 0803
cert_graph_frame_links 003 008 0000 0803 8 0 64 64
cert_graph_frame_links 003 008 0064 0803 8 64 124 60
cert_graph_frame_links_7 003 008 0803 8 124
cert_graph_frame_supported_3 003 008 8 0803
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (Fin.cases (record003_frame006_supported hcells) (Fin.cases (record003_frame007_supported hcells) (Fin.cases (record003_frame008_supported hcells) (fun j => Fin.elim0 j))))))))))
#print axioms record003_frames_supported
cert_graph_frame_supported_4 004
cert_graph_frames_supported_2 004
#print axioms record004_frames_supported
cert_graph_frame_supported_4 005
cert_graph_frames_supported_2 005
#print axioms record005_frames_supported
cert_graph_frame_supported_4 006
cert_graph_frames_supported_2 006
#print axioms record006_frames_supported
cert_graph_frame_supported_4 007
cert_graph_frames_supported_2 007
#print axioms record007_frames_supported
cert_graph_frame_supported_4 008
cert_graph_frames_supported_2 008
#print axioms record008_frames_supported
cert_graph_frame_supported_4 009
cert_graph_frames_supported_2 009
#print axioms record009_frames_supported
cert_graph_frame_supported_4 010
cert_graph_frames_supported_2 010
#print axioms record010_frames_supported
cert_graph_frame_supported_4 011
cert_graph_frames_supported_2 011
#print axioms record011_frames_supported
cert_graph_frame_supported_4 012
cert_graph_frames_supported_2 012
#print axioms record012_frames_supported
cert_graph_frame_supported_4 013
cert_graph_frame_indices 013 001 0812 11 10
cert_graph_frame_graph 013 001 0812
cert_graph_frame_links 013 001 0000 0812 1 0 64 64
cert_graph_frame_links 013 001 0064 0812 1 64 114 50
cert_graph_frame_links_7 013 001 0812 1 114
cert_graph_frame_supported_3 013 001 1 0812
cert_graph_frames_supported_11 013
#print axioms record013_frames_supported
cert_graph_frame_supported_4 014
cert_graph_frame_indices 014 001 1115 13 11
cert_graph_frame_graph 014 001 1115
cert_graph_frame_links 014 001 0000 1115 1 0 64 64
cert_graph_frame_links 014 001 0064 1115 1 64 120 56
cert_graph_frame_links_7 014 001 1115 1 120
cert_graph_frame_supported_3 014 001 1 1115
cert_graph_frame_indices 014 002 0814 11 12
cert_graph_frame_graph 014 002 0814
cert_graph_frame_links 014 002 0000 0814 2 0 64 64
cert_graph_frame_links 014 002 0064 0814 2 64 120 56
cert_graph_frame_links_7 014 002 0814 2 120
cert_graph_frame_supported_3 014 002 2 0814
cert_graph_frame_indices 014 003 0813 11 13
cert_graph_frame_graph 014 003 0813
cert_graph_frame_links 014 003 0000 0813 3 0 64 64
cert_graph_frame_links 014 003 0064 0813 3 64 120 56
cert_graph_frame_links_7 014 003 0813 3 120
cert_graph_frame_supported_3 014 003 3 0813
cert_graph_frames_supported_13 014
#print axioms record014_frames_supported
cert_graph_frame_supported_4 015
cert_graph_frames_supported_2 015
#print axioms record015_frames_supported
cert_graph_frame_supported_4 016
cert_graph_frame_indices 016 001 0869 11 14
cert_graph_frame_graph 016 001 0869
cert_graph_frame_links 016 001 0000 0869 1 0 64 64
cert_graph_frame_links 016 001 0064 0869 1 64 110 46
cert_graph_frame_links_7 016 001 0869 1 110
cert_graph_frame_supported_3 016 001 1 0869
cert_graph_frames_supported_11 016
#print axioms record016_frames_supported
cert_graph_frame_supported_4 017
cert_graph_frame_indices 017 001 0871 12 15
cert_graph_frame_graph 017 001 0871
cert_graph_frame_links 017 001 0000 0871 1 0 64 64
cert_graph_frame_links 017 001 0064 0871 1 64 116 52
cert_graph_frame_links_7 017 001 0871 1 116
cert_graph_frame_supported_3 017 001 1 0871
cert_graph_frames_supported_11 017
#print axioms record017_frames_supported
cert_graph_frame_supported_4 018
cert_graph_frame_indices 018 001 1052 13 16
cert_graph_frame_graph 018 001 1052
cert_graph_frame_links 018 001 0000 1052 1 0 64 64
cert_graph_frame_links 018 001 0064 1052 1 64 110 46
cert_graph_frame_links_7 018 001 1052 1 110
cert_graph_frame_supported_3 018 001 1 1052
cert_graph_frames_supported_11 018
#print axioms record018_frames_supported
cert_graph_frame_supported_4 019
cert_graph_frame_indices 019 001 0820 11 17
cert_graph_frame_graph 019 001 0820
cert_graph_frame_links 019 001 0000 0820 1 0 64 64
cert_graph_frame_links 019 001 0064 0820 1 64 115 51
cert_graph_frame_links_7 019 001 0820 1 115
cert_graph_frame_supported_3 019 001 1 0820
cert_graph_frames_supported_11 019
#print axioms record019_frames_supported
cert_graph_frame_supported_4 020
cert_graph_frames_supported_2 020
#print axioms record020_frames_supported
cert_graph_frame_supported_4 021
cert_graph_frame_indices 021 001 0870 12 18
cert_graph_frame_graph 021 001 0870
cert_graph_frame_links 021 001 0000 0870 1 0 64 64
cert_graph_frame_links 021 001 0064 0870 1 64 109 45
cert_graph_frame_links_7 021 001 0870 1 109
cert_graph_frame_supported_3 021 001 1 0870
cert_graph_frames_supported_11 021
#print axioms record021_frames_supported
cert_graph_frame_supported_4 022
cert_graph_frames_supported_2 022
#print axioms record022_frames_supported
cert_graph_frame_supported_4 023
cert_graph_frames_supported_2 023
#print axioms record023_frames_supported
cert_graph_frame_supported_4 024
cert_graph_frames_supported_2 024
#print axioms record024_frames_supported
cert_graph_frame_supported_4 025
cert_graph_frames_supported_2 025
#print axioms record025_frames_supported
cert_graph_frame_supported_4 026
cert_graph_frames_supported_2 026
#print axioms record026_frames_supported
cert_graph_frame_supported_4 027
cert_graph_frames_supported_2 027
#print axioms record027_frames_supported
cert_graph_frame_supported_4 028
cert_graph_frames_supported_2 028
#print axioms record028_frames_supported
cert_graph_frame_supported_4 029
cert_graph_frames_supported_2 029
#print axioms record029_frames_supported
cert_graph_frame_supported_4 030
cert_graph_frames_supported_2 030
#print axioms record030_frames_supported
cert_graph_frame_supported_4 031
cert_graph_frames_supported_2 031
#print axioms record031_frames_supported
cert_graph_frame_supported_4 032
cert_graph_frames_supported_2 032
#print axioms record032_frames_supported
cert_graph_frame_supported_4 033
cert_graph_frame_indices 033 001 1110 13 19
cert_graph_frame_graph 033 001 1110
cert_graph_frame_links 033 001 0000 1110 1 0 64 64
cert_graph_frame_links 033 001 0064 1110 1 64 80 16
cert_graph_frame_links_7 033 001 1110 1 80
cert_graph_frame_supported_3 033 001 1 1110
cert_graph_frames_supported_11 033
#print axioms record033_frames_supported
cert_graph_frame_supported_4 034
cert_graph_frames_supported_2 034
#print axioms record034_frames_supported
cert_graph_frame_supported_4 035
cert_graph_frame_indices 035 001 1114 13 20
cert_graph_frame_graph 035 001 1114
cert_graph_frame_links 035 001 0000 1114 1 0 64 64
cert_graph_frame_links 035 001 0064 1114 1 64 113 49
cert_graph_frame_links_7 035 001 1114 1 113
cert_graph_frame_supported_3 035 001 1 1114
cert_graph_frames_supported_11 035
#print axioms record035_frames_supported
cert_graph_frame_supported_4 036
cert_graph_frames_supported_2 036
#print axioms record036_frames_supported
cert_graph_frame_supported_4 037
cert_graph_frame_indices 037 001 1114 13 21
cert_graph_frame_graph 037 001 1114
cert_graph_frame_links 037 001 0000 1114 1 0 64 64
cert_graph_frame_links 037 001 0064 1114 1 64 115 51
cert_graph_frame_links_7 037 001 1114 1 115
cert_graph_frame_supported_3 037 001 1 1114
cert_graph_frames_supported_11 037
#print axioms record037_frames_supported
cert_graph_frame_supported_4 038
cert_graph_frames_supported_2 038
#print axioms record038_frames_supported
cert_graph_frame_supported_4 039
cert_graph_frames_supported_2 039
#print axioms record039_frames_supported
cert_graph_frame_supported_4 040
cert_graph_frames_supported_2 040
#print axioms record040_frames_supported
cert_graph_frame_supported_4 041
cert_graph_frames_supported_2 041
#print axioms record041_frames_supported
cert_graph_frame_supported_4 042
cert_graph_frames_supported_2 042
#print axioms record042_frames_supported
cert_graph_frame_supported_4 043
cert_graph_frames_supported_2 043
#print axioms record043_frames_supported
cert_graph_frame_supported_4 044
cert_graph_frames_supported_2 044
#print axioms record044_frames_supported
cert_graph_frame_supported_4 045
cert_graph_frames_supported_2 045
#print axioms record045_frames_supported
cert_graph_frame_supported_4 046
cert_graph_frames_supported_2 046
#print axioms record046_frames_supported
cert_graph_frame_supported_4 047
cert_graph_frames_supported_2 047
#print axioms record047_frames_supported
cert_graph_frame_supported_4 048
cert_graph_frames_supported_2 048
#print axioms record048_frames_supported
cert_graph_frame_supported_4 049
cert_graph_frames_supported_2 049
#print axioms record049_frames_supported
cert_graph_frame_supported_4 050
cert_graph_frames_supported_2 050
#print axioms record050_frames_supported
cert_graph_frame_supported_4 051
cert_graph_frames_supported_2 051
#print axioms record051_frames_supported
cert_graph_frame_supported_4 052
cert_graph_frames_supported_2 052
#print axioms record052_frames_supported
cert_graph_frame_supported_4 053
cert_graph_frames_supported_2 053
#print axioms record053_frames_supported
cert_graph_frame_supported_4 054
cert_graph_frames_supported_2 054
#print axioms record054_frames_supported
cert_graph_frame_supported_4 055
cert_graph_frame_indices 055 001 1115 13 22
cert_graph_frame_graph 055 001 1115
cert_graph_frame_links 055 001 0000 1115 1 0 64 64
cert_graph_frame_links 055 001 0064 1115 1 64 91 27
cert_graph_frame_links_7 055 001 1115 1 91
cert_graph_frame_supported_3 055 001 1 1115
cert_graph_frame_indices 055 002 1110 13 23
cert_graph_frame_graph 055 002 1110
cert_graph_frame_links 055 002 0000 1110 2 0 64 64
cert_graph_frame_links 055 002 0064 1110 2 64 91 27
cert_graph_frame_links_7 055 002 1110 2 91
cert_graph_frame_supported_3 055 002 2 1110
cert_graph_frames_supported_17 055
#print axioms record055_frames_supported
cert_graph_frame_supported_4 056
cert_graph_frames_supported_2 056
#print axioms record056_frames_supported
cert_graph_frame_supported_4 057
cert_graph_frames_supported_2 057
#print axioms record057_frames_supported
cert_graph_frame_supported_4 058
cert_graph_frames_supported_2 058
#print axioms record058_frames_supported
cert_graph_frame_supported_4 059
cert_graph_frames_supported_2 059
#print axioms record059_frames_supported
cert_graph_frame_supported_4 060
cert_graph_frames_supported_2 060
#print axioms record060_frames_supported
cert_graph_frame_supported_4 061
cert_graph_frames_supported_2 061
#print axioms record061_frames_supported
cert_graph_frame_supported_4 062
cert_graph_frames_supported_2 062
#print axioms record062_frames_supported
cert_graph_frame_supported_4 063
cert_graph_frames_supported_2 063
#print axioms record063_frames_supported
cert_graph_frame_supported_4 064
cert_graph_frames_supported_2 064
#print axioms record064_frames_supported
cert_graph_frame_supported_4 065
cert_graph_frames_supported_2 065
#print axioms record065_frames_supported
cert_graph_frame_supported_4 066
cert_graph_frames_supported_2 066
#print axioms record066_frames_supported
cert_graph_frame_supported_4 067
cert_graph_frames_supported_2 067
#print axioms record067_frames_supported
cert_graph_frame_supported_4 068
cert_graph_frames_supported_2 068
#print axioms record068_frames_supported
cert_graph_frame_supported_4 069
cert_graph_frame_indices 069 001 1115 13 24
cert_graph_frame_graph 069 001 1115
cert_graph_frame_links 069 001 0000 1115 1 0 64 64
cert_graph_frame_links 069 001 0064 1115 1 64 108 44
cert_graph_frame_links_7 069 001 1115 1 108
cert_graph_frame_supported_3 069 001 1 1115
cert_graph_frames_supported_11 069
#print axioms record069_frames_supported
cert_graph_frame_supported_4 070
cert_graph_frames_supported_2 070
#print axioms record070_frames_supported
cert_graph_frame_supported_4 071
cert_graph_frames_supported_2 071
#print axioms record071_frames_supported
cert_graph_frame_supported_4 072
cert_graph_frames_supported_2 072
#print axioms record072_frames_supported
cert_graph_frame_supported_4 073
cert_graph_frames_supported_2 073
#print axioms record073_frames_supported
cert_graph_frame_supported_4 074
cert_graph_frames_supported_2 074
#print axioms record074_frames_supported
cert_graph_frame_supported_4 075
cert_graph_frames_supported_2 075
#print axioms record075_frames_supported
cert_graph_frame_supported_4 076
cert_graph_frames_supported_2 076
#print axioms record076_frames_supported
cert_graph_frame_supported_4 077
cert_graph_frames_supported_2 077
#print axioms record077_frames_supported
cert_graph_frame_supported_4 078
cert_graph_frames_supported_2 078
#print axioms record078_frames_supported
cert_graph_frame_supported_4 079
cert_graph_frames_supported_2 079
#print axioms record079_frames_supported
cert_graph_frame_supported_4 080
cert_graph_frames_supported_2 080
#print axioms record080_frames_supported
cert_graph_frame_supported_4 081
cert_graph_frame_indices 081 001 1081 13 25
cert_graph_frame_graph 081 001 1081
cert_graph_frame_links 081 001 0000 1081 1 0 64 64
cert_graph_frame_links 081 001 0064 1081 1 64 105 41
cert_graph_frame_links_7 081 001 1081 1 105
cert_graph_frame_supported_3 081 001 1 1081
cert_graph_frames_supported_11 081
#print axioms record081_frames_supported
cert_graph_frame_supported_4 082
cert_graph_frames_supported_2 082
#print axioms record082_frames_supported
cert_graph_frame_supported_4 083
cert_graph_frame_indices 083 001 1114 13 26
cert_graph_frame_graph 083 001 1114
cert_graph_frame_links 083 001 0000 1114 1 0 64 64
cert_graph_frame_links 083 001 0064 1114 1 64 96 32
cert_graph_frame_links_7 083 001 1114 1 96
cert_graph_frame_supported_3 083 001 1 1114
cert_graph_frame_indices 083 002 1081 13 27
cert_graph_frame_graph 083 002 1081
cert_graph_frame_links 083 002 0000 1081 2 0 64 64
cert_graph_frame_links 083 002 0064 1081 2 64 96 32
cert_graph_frame_links_7 083 002 1081 2 96
cert_graph_frame_supported_3 083 002 2 1081
cert_graph_frames_supported_17 083
#print axioms record083_frames_supported
cert_graph_frame_supported_4 084
cert_graph_frames_supported_2 084
#print axioms record084_frames_supported
cert_graph_frame_supported_4 085
cert_graph_frame_indices 085 001 0841 11 28
cert_graph_frame_graph 085 001 0841
cert_graph_frame_links 085 001 0000 0841 1 0 64 64
cert_graph_frame_links 085 001 0064 0841 1 64 104 40
cert_graph_frame_links_7 085 001 0841 1 104
cert_graph_frame_supported_3 085 001 1 0841
cert_graph_frames_supported_11 085
#print axioms record085_frames_supported
cert_graph_frame_supported_4 086
cert_graph_frames_supported_2 086
#print axioms record086_frames_supported
cert_graph_frame_supported_4 087
cert_graph_frames_supported_2 087
#print axioms record087_frames_supported
cert_graph_frame_supported_4 088
cert_graph_frames_supported_2 088
#print axioms record088_frames_supported
cert_graph_frame_supported_4 089
cert_graph_frames_supported_2 089
#print axioms record089_frames_supported
cert_graph_frame_supported_4 090
cert_graph_frame_indices 090 001 0847 11 29
cert_graph_frame_graph 090 001 0847
cert_graph_frame_links 090 001 0000 0847 1 0 64 64
cert_graph_frame_links 090 001 0064 0847 1 64 127 63
cert_graph_frame_links_7 090 001 0847 1 127
cert_graph_frame_supported_3 090 001 1 0847
cert_graph_frames_supported_11 090
#print axioms record090_frames_supported
cert_graph_frame_supported_4 091
cert_graph_frame_indices 091 001 1114 13 30
cert_graph_frame_graph 091 001 1114
cert_graph_frame_links 091 001 0000 1114 1 0 64 64
cert_graph_frame_links 091 001 0064 1114 1 64 113 49
cert_graph_frame_links_7 091 001 1114 1 113
cert_graph_frame_supported_3 091 001 1 1114
cert_graph_frames_supported_11 091
#print axioms record091_frames_supported
cert_graph_frame_supported_4 092
cert_graph_frame_indices 092 001 1114 13 31
cert_graph_frame_graph 092 001 1114
cert_graph_frame_links 092 001 0000 1114 1 0 64 64
cert_graph_frame_links 092 001 0064 1114 1 64 128 64
cert_graph_frame_links 092 001 0128 1114 1 128 132 4
cert_graph_frame_links_2 092 001 1114 1 132
cert_graph_frame_supported_3 092 001 1 1114
cert_graph_frame_indices 092 002 0847 11 32
cert_graph_frame_graph 092 002 0847
cert_graph_frame_links 092 002 0000 0847 2 0 64 64
cert_graph_frame_links 092 002 0064 0847 2 64 128 64
cert_graph_frame_links 092 002 0128 0847 2 128 132 4
cert_graph_frame_links_2 092 002 0847 2 132
cert_graph_frame_supported_3 092 002 2 0847
cert_graph_frame_indices 092 003 0845 11 33
cert_graph_frame_graph 092 003 0845
cert_graph_frame_links 092 003 0000 0845 3 0 64 64
cert_graph_frame_links 092 003 0064 0845 3 64 128 64
cert_graph_frame_links 092 003 0128 0845 3 128 132 4
cert_graph_frame_links_2 092 003 0845 3 132
cert_graph_frame_supported_3 092 003 3 0845
cert_graph_frames_supported_13 092
#print axioms record092_frames_supported
cert_graph_frame_supported_4 093
cert_graph_frames_supported_2 093
#print axioms record093_frames_supported
cert_graph_frame_supported_4 094
cert_graph_frames_supported_2 094
#print axioms record094_frames_supported
cert_graph_frame_supported_4 095
cert_graph_frames_supported_2 095
#print axioms record095_frames_supported
cert_graph_frame_supported_4 096
cert_graph_frames_supported_2 096
#print axioms record096_frames_supported
cert_graph_frame_supported_4 097
cert_graph_frames_supported_2 097
#print axioms record097_frames_supported
cert_graph_frame_supported_4 098
cert_graph_frames_supported_2 098
#print axioms record098_frames_supported
cert_graph_frame_supported_4 099
cert_graph_frame_indices 099 001 1110 13 34
cert_graph_frame_graph 099 001 1110
cert_graph_frame_links 099 001 0000 1110 1 0 64 64
cert_graph_frame_links 099 001 0064 1110 1 64 100 36
cert_graph_frame_links_7 099 001 1110 1 100
cert_graph_frame_supported_3 099 001 1 1110
cert_graph_frames_supported_11 099
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017
