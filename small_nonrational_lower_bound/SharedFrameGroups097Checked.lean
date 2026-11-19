module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups097Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1031
cert_group_pairs 1031 00000 0 128 128
cert_group_pairs 1031 00128 128 256 128
cert_group_pairs 1031 00256 256 384 128
cert_group_pairs 1031 00384 384 512 128
cert_group_pairs 1031 00512 512 640 128
cert_group_pairs 1031 00640 640 768 128
cert_group_pairs 1031 00768 768 896 128
cert_group_pairs 1031 00896 896 925 29
theorem group1031_facts : group1031.Facts FacetUniverses.FullSix0.cells :=
  group1031.facts_of_checks _ group1031_header (interval_append _ 0 512 925 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1031_pairs_00000 group1031_pairs_00128) (interval_append _ 256 384 512 group1031_pairs_00256 group1031_pairs_00384)) (interval_append _ 512 768 925 (interval_append _ 512 640 768 group1031_pairs_00512 group1031_pairs_00640) (interval_append _ 768 896 925 group1031_pairs_00768 group1031_pairs_00896)))
#print axioms group1031_facts
cert_group_header 1032
cert_group_pairs 1032 00000 0 128 128
cert_group_pairs 1032 00128 128 256 128
cert_group_pairs 1032 00256 256 384 128
cert_group_pairs 1032 00384 384 412 28
cert_group_facts_4 1032 412
#print axioms group1032_facts
cert_group_header 1033
cert_group_pairs 1033 00000 0 128 128
cert_group_pairs 1033 00128 128 132 4
cert_group_facts 1033 132
#print axioms group1033_facts
cert_group_header 1034
cert_group_pairs 1034 00000 0 128 128
cert_group_pairs 1034 00128 128 256 128
cert_group_pairs 1034 00256 256 258 2
cert_group_facts_2 1034 258
#print axioms group1034_facts
cert_group_header 1035
cert_group_pairs 1035 00000 0 128 128
cert_group_pairs 1035 00128 128 132 4
cert_group_facts 1035 132
#print axioms group1035_facts
cert_group_header 1036
cert_group_pairs 1036 00000 0 128 128
cert_group_pairs 1036 00128 128 141 13
cert_group_facts 1036 141
#print axioms group1036_facts
cert_group_header 1037
cert_group_pairs 1037 00000 0 128 128
cert_group_pairs 1037 00128 128 139 11
cert_group_facts 1037 139
#print axioms group1037_facts
cert_group_header 1038
cert_group_pairs 1038 00000 0 128 128
cert_group_pairs 1038 00128 128 256 128
cert_group_pairs 1038 00256 256 333 77
cert_group_facts_2 1038 333
#print axioms group1038_facts
end Papers.RationalityTen.SharedFrameCatalogue
