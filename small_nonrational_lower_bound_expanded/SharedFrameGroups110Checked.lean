module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups110Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1082
cert_group_pairs 1082 00000 0 128 128
cert_group_pairs 1082 00128 128 256 128
cert_group_pairs 1082 00256 256 346 90
cert_group_facts_2 1082 346
cert_group_header 1083
cert_group_pairs 1083 00000 0 128 128
cert_group_pairs 1083 00128 128 256 128
cert_group_pairs 1083 00256 256 384 128
cert_group_pairs 1083 00384 384 416 32
cert_group_facts_4 1083 416
cert_group_header 1084
cert_group_pairs 1084 00000 0 128 128
cert_group_pairs 1084 00128 128 155 27
cert_group_facts 1084 155
cert_group_header 1085
cert_group_pairs 1085 00000 0 128 128
cert_group_pairs 1085 00128 128 155 27
cert_group_facts 1085 155
cert_group_header 1086
cert_group_pairs 1086 00000 0 128 128
cert_group_pairs 1086 00128 128 256 128
cert_group_pairs 1086 00256 256 384 128
cert_group_pairs 1086 00384 384 475 91
cert_group_facts_4 1086 475
cert_group_header 1087
cert_group_pairs 1087 00000 0 104 104
cert_group_facts_6 1087
cert_group_header 1088
cert_group_pairs 1088 00000 0 128 128
cert_group_pairs 1088 00128 128 155 27
cert_group_facts 1088 155
cert_group_header 1089
cert_group_pairs 1089 00000 0 128 128
cert_group_pairs 1089 00128 128 256 128
cert_group_pairs 1089 00256 256 377 121
cert_group_facts_2 1089 377
cert_group_header 1090
cert_group_pairs 1090 00000 0 128 128
cert_group_pairs 1090 00128 128 137 9
cert_group_facts 1090 137
cert_group_header 1091
cert_group_pairs 1091 00000 0 128 128
cert_group_pairs 1091 00128 128 256 128
cert_group_pairs 1091 00256 256 384 128
cert_group_pairs 1091 00384 384 512 128
cert_group_pairs 1091 00512 512 640 128
cert_group_pairs 1091 00640 640 691 51
theorem group1091_facts : group1091.Facts FacetUniverses.FullSix0.cells :=
  group1091.facts_of_checks _ group1091_header (interval_append _ 0 384 691 (interval_append _ 0 128 384 group1091_pairs_00000 (interval_append _ 128 256 384 group1091_pairs_00128 group1091_pairs_00256)) (interval_append _ 384 512 691 group1091_pairs_00384 (interval_append _ 512 640 691 group1091_pairs_00512 group1091_pairs_00640)))
cert_group_header 1092
cert_group_pairs 1092 00000 0 128 128
cert_group_pairs 1092 00128 128 256 128
cert_group_pairs 1092 00256 256 384 128
cert_group_pairs 1092 00384 384 416 32
cert_group_facts_4 1092 416
cert_group_header 1093
cert_group_pairs 1093 00000 0 128 128
cert_group_pairs 1093 00128 128 182 54
cert_group_facts 1093 182
cert_group_header 1094
cert_group_pairs 1094 00000 0 128 128
cert_group_pairs 1094 00128 128 256 128
cert_group_pairs 1094 00256 256 384 128
cert_group_pairs 1094 00384 384 388 4
cert_group_facts_4 1094 388
end Papers.RationalityTen.SharedFrameCatalogue
