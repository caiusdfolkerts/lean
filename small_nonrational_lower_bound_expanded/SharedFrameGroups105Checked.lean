module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups105Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1068
cert_group_pairs 1068 00000 0 128 128
cert_group_pairs 1068 00128 128 256 128
cert_group_pairs 1068 00256 256 299 43
cert_group_facts_2 1068 299
cert_group_header 1069
cert_group_pairs 1069 00000 0 128 128
cert_group_pairs 1069 00128 128 256 128
cert_group_pairs 1069 00256 256 384 128
cert_group_pairs 1069 00384 384 512 128
cert_group_pairs 1069 00512 512 640 128
cert_group_pairs 1069 00640 640 768 128
cert_group_pairs 1069 00768 768 896 128
cert_group_pairs 1069 00896 896 1007 111
theorem group1069_facts : group1069.Facts FacetUniverses.FullSix0.cells :=
  group1069.facts_of_checks _ group1069_header (interval_append _ 0 512 1007 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1069_pairs_00000 group1069_pairs_00128) (interval_append _ 256 384 512 group1069_pairs_00256 group1069_pairs_00384)) (interval_append _ 512 768 1007 (interval_append _ 512 640 768 group1069_pairs_00512 group1069_pairs_00640) (interval_append _ 768 896 1007 group1069_pairs_00768 group1069_pairs_00896)))
cert_group_header 1070
cert_group_pairs 1070 00000 0 128 128
cert_group_pairs 1070 00128 128 165 37
cert_group_facts 1070 165
cert_group_header 1071
cert_group_pairs 1071 00000 0 128 128
cert_group_pairs 1071 00128 128 165 37
cert_group_facts 1071 165
cert_group_header 1072
cert_group_pairs 1072 00000 0 128 128
cert_group_pairs 1072 00128 128 165 37
cert_group_facts 1072 165
cert_group_header 1073
cert_group_pairs 1073 00000 0 128 128
cert_group_pairs 1073 00128 128 165 37
cert_group_facts 1073 165
cert_group_header 1074
cert_group_pairs 1074 00000 0 128 128
cert_group_pairs 1074 00128 128 256 128
cert_group_pairs 1074 00256 256 384 128
cert_group_pairs 1074 00384 384 512 128
cert_group_pairs 1074 00512 512 640 128
cert_group_pairs 1074 00640 640 768 128
cert_group_pairs 1074 00768 768 896 128
cert_group_pairs 1074 00896 896 1019 123
theorem group1074_facts : group1074.Facts FacetUniverses.FullSix0.cells :=
  group1074.facts_of_checks _ group1074_header (interval_append _ 0 512 1019 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1074_pairs_00000 group1074_pairs_00128) (interval_append _ 256 384 512 group1074_pairs_00256 group1074_pairs_00384)) (interval_append _ 512 768 1019 (interval_append _ 512 640 768 group1074_pairs_00512 group1074_pairs_00640) (interval_append _ 768 896 1019 group1074_pairs_00768 group1074_pairs_00896)))
end Papers.RationalityTen.SharedFrameCatalogue
