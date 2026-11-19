module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups099Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1041
cert_group_pairs 1041 00000 0 128 128
cert_group_pairs 1041 00128 128 256 128
cert_group_pairs 1041 00256 256 384 128
cert_group_pairs 1041 00384 384 512 128
cert_group_pairs 1041 00512 512 640 128
cert_group_pairs 1041 00640 640 768 128
cert_group_pairs 1041 00768 768 896 128
cert_group_pairs 1041 00896 896 1024 128
cert_group_pairs 1041 01024 1024 1152 128
cert_group_pairs 1041 01152 1152 1280 128
cert_group_pairs 1041 01280 1280 1408 128
cert_group_pairs 1041 01408 1408 1536 128
cert_group_pairs 1041 01536 1536 1664 128
cert_group_pairs 1041 01664 1664 1792 128
cert_group_pairs 1041 01792 1792 1920 128
cert_group_pairs 1041 01920 1920 2048 128
cert_group_pairs 1041 02048 2048 2176 128
cert_group_pairs 1041 02176 2176 2304 128
cert_group_pairs 1041 02304 2304 2387 83
theorem group1041_facts : group1041.Facts FacetUniverses.FullSix0.cells :=
  group1041.facts_of_checks _ group1041_header (interval_append _ 0 1152 2387 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1041_pairs_00000 group1041_pairs_00128) (interval_append _ 256 384 512 group1041_pairs_00256 group1041_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group1041_pairs_00512 group1041_pairs_00640) (interval_append _ 768 896 1152 group1041_pairs_00768 (interval_append _ 896 1024 1152 group1041_pairs_00896 group1041_pairs_01024)))) (interval_append _ 1152 1792 2387 (interval_append _ 1152 1408 1792 (interval_append _ 1152 1280 1408 group1041_pairs_01152 group1041_pairs_01280) (interval_append _ 1408 1536 1792 group1041_pairs_01408 (interval_append _ 1536 1664 1792 group1041_pairs_01536 group1041_pairs_01664))) (interval_append _ 1792 2048 2387 (interval_append _ 1792 1920 2048 group1041_pairs_01792 group1041_pairs_01920) (interval_append _ 2048 2176 2387 group1041_pairs_02048 (interval_append _ 2176 2304 2387 group1041_pairs_02176 group1041_pairs_02304)))))
#print axioms group1041_facts
cert_group_header 1042
cert_group_pairs 1042 00000 0 120 120
cert_group_facts_6 1042
#print axioms group1042_facts
cert_group_header 1043
cert_group_pairs 1043 00000 0 98 98
cert_group_facts_6 1043
#print axioms group1043_facts
cert_group_header 1044
cert_group_pairs 1044 00000 0 128 128
cert_group_pairs 1044 00128 128 190 62
cert_group_facts 1044 190
#print axioms group1044_facts
cert_group_header 1045
cert_group_pairs 1045 00000 0 128 128
cert_group_pairs 1045 00128 128 256 128
cert_group_pairs 1045 00256 256 384 128
cert_group_pairs 1045 00384 384 512 128
cert_group_pairs 1045 00512 512 640 128
cert_group_pairs 1045 00640 640 768 128
cert_group_pairs 1045 00768 768 896 128
cert_group_pairs 1045 00896 896 1024 128
cert_group_pairs 1045 01024 1024 1064 40
theorem group1045_facts : group1045.Facts FacetUniverses.FullSix0.cells :=
  group1045.facts_of_checks _ group1045_header (interval_append _ 0 512 1064 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1045_pairs_00000 group1045_pairs_00128) (interval_append _ 256 384 512 group1045_pairs_00256 group1045_pairs_00384)) (interval_append _ 512 768 1064 (interval_append _ 512 640 768 group1045_pairs_00512 group1045_pairs_00640) (interval_append _ 768 896 1064 group1045_pairs_00768 (interval_append _ 896 1024 1064 group1045_pairs_00896 group1045_pairs_01024))))
#print axioms group1045_facts
end Papers.RationalityTen.SharedFrameCatalogue
