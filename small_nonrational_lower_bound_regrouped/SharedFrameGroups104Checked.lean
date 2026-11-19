module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups104Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1053
cert_group_pairs 1053 00000 0 128 128
cert_group_pairs 1053 00128 128 130 2
cert_group_facts 1053 130
#print axioms group1053_facts
cert_group_header 1054
cert_group_pairs 1054 00000 0 128 128
cert_group_pairs 1054 00128 128 130 2
cert_group_facts 1054 130
#print axioms group1054_facts
cert_group_header 1055
cert_group_pairs 1055 00000 0 128 128
cert_group_pairs 1055 00128 128 176 48
cert_group_facts 1055 176
#print axioms group1055_facts
cert_group_header 1056
cert_group_pairs 1056 00000 0 128 128
cert_group_pairs 1056 00128 128 130 2
cert_group_facts 1056 130
#print axioms group1056_facts
cert_group_header 1057
cert_group_pairs 1057 00000 0 128 128
cert_group_pairs 1057 00128 128 246 118
cert_group_facts 1057 246
#print axioms group1057_facts
cert_group_header 1058
cert_group_pairs 1058 00000 0 128 128
cert_group_pairs 1058 00128 128 130 2
cert_group_facts 1058 130
#print axioms group1058_facts
cert_group_header 1059
cert_group_pairs 1059 00000 0 128 128
cert_group_pairs 1059 00128 128 256 128
cert_group_pairs 1059 00256 256 356 100
cert_group_facts_2 1059 356
#print axioms group1059_facts
cert_group_header 1060
cert_group_pairs 1060 00000 0 128 128
cert_group_pairs 1060 00128 128 256 128
cert_group_pairs 1060 00256 256 384 128
cert_group_pairs 1060 00384 384 512 128
cert_group_pairs 1060 00512 512 601 89
cert_group_facts_5 1060 601
#print axioms group1060_facts
cert_group_header 1061
cert_group_pairs 1061 00000 0 128 128
cert_group_pairs 1061 00128 128 130 2
cert_group_facts 1061 130
#print axioms group1061_facts
cert_group_header 1062
cert_group_pairs 1062 00000 0 128 128
cert_group_pairs 1062 00128 128 189 61
cert_group_facts 1062 189
#print axioms group1062_facts
cert_group_header 1063
cert_group_pairs 1063 00000 0 128 128
cert_group_pairs 1063 00128 128 151 23
cert_group_facts 1063 151
#print axioms group1063_facts
cert_group_header 1064
cert_group_pairs 1064 00000 0 128 128
cert_group_pairs 1064 00128 128 256 128
cert_group_pairs 1064 00256 256 384 128
cert_group_pairs 1064 00384 384 512 128
cert_group_pairs 1064 00512 512 640 128
cert_group_pairs 1064 00640 640 768 128
cert_group_pairs 1064 00768 768 896 128
cert_group_pairs 1064 00896 896 1024 128
cert_group_pairs 1064 01024 1024 1089 65
theorem group1064_facts : group1064.Facts FacetUniverses.FullSix0.cells :=
  group1064.facts_of_checks _ group1064_header (interval_append _ 0 512 1089 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1064_pairs_00000 group1064_pairs_00128) (interval_append _ 256 384 512 group1064_pairs_00256 group1064_pairs_00384)) (interval_append _ 512 768 1089 (interval_append _ 512 640 768 group1064_pairs_00512 group1064_pairs_00640) (interval_append _ 768 896 1089 group1064_pairs_00768 (interval_append _ 896 1024 1089 group1064_pairs_00896 group1064_pairs_01024))))
#print axioms group1064_facts
cert_group_header 1065
cert_group_pairs 1065 00000 0 128 128
cert_group_pairs 1065 00128 128 130 2
cert_group_facts 1065 130
#print axioms group1065_facts
cert_group_header 1066
cert_group_pairs 1066 00000 0 128 128
cert_group_pairs 1066 00128 128 246 118
cert_group_facts 1066 246
#print axioms group1066_facts
cert_group_header 1067
cert_group_pairs 1067 00000 0 128 128
cert_group_pairs 1067 00128 128 189 61
cert_group_facts 1067 189
#print axioms group1067_facts
end Papers.RationalityTen.SharedFrameCatalogue
