module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups075Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0864
cert_group_pairs 0864 00000 0 128 128
cert_group_pairs 0864 00128 128 256 128
cert_group_pairs 0864 00256 256 384 128
cert_group_pairs 0864 00384 384 512 128
cert_group_pairs 0864 00512 512 640 128
cert_group_pairs 0864 00640 640 768 128
cert_group_pairs 0864 00768 768 896 128
cert_group_pairs 0864 00896 896 1024 128
cert_group_pairs 0864 01024 1024 1152 128
cert_group_pairs 0864 01152 1152 1267 115
cert_group_facts_3 0864 1267
#print axioms group0864_facts
cert_group_header 0865
cert_group_pairs 0865 00000 0 128 128
cert_group_pairs 0865 00128 128 256 128
cert_group_pairs 0865 00256 256 384 128
cert_group_pairs 0865 00384 384 512 128
cert_group_pairs 0865 00512 512 640 128
cert_group_pairs 0865 00640 640 768 128
cert_group_pairs 0865 00768 768 896 128
cert_group_pairs 0865 00896 896 1024 128
cert_group_pairs 0865 01024 1024 1152 128
cert_group_pairs 0865 01152 1152 1280 128
cert_group_pairs 0865 01280 1280 1408 128
cert_group_pairs 0865 01408 1408 1536 128
cert_group_pairs 0865 01536 1536 1664 128
cert_group_pairs 0865 01664 1664 1792 128
cert_group_pairs 0865 01792 1792 1920 128
cert_group_pairs 0865 01920 1920 2048 128
cert_group_pairs 0865 02048 2048 2176 128
cert_group_pairs 0865 02176 2176 2304 128
cert_group_pairs 0865 02304 2304 2358 54
theorem group0865_facts : group0865.Facts FacetUniverses.FullSix0.cells :=
  group0865.facts_of_checks _ group0865_header (interval_append _ 0 1152 2358 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0865_pairs_00000 group0865_pairs_00128) (interval_append _ 256 384 512 group0865_pairs_00256 group0865_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group0865_pairs_00512 group0865_pairs_00640) (interval_append _ 768 896 1152 group0865_pairs_00768 (interval_append _ 896 1024 1152 group0865_pairs_00896 group0865_pairs_01024)))) (interval_append _ 1152 1792 2358 (interval_append _ 1152 1408 1792 (interval_append _ 1152 1280 1408 group0865_pairs_01152 group0865_pairs_01280) (interval_append _ 1408 1536 1792 group0865_pairs_01408 (interval_append _ 1536 1664 1792 group0865_pairs_01536 group0865_pairs_01664))) (interval_append _ 1792 2048 2358 (interval_append _ 1792 1920 2048 group0865_pairs_01792 group0865_pairs_01920) (interval_append _ 2048 2176 2358 group0865_pairs_02048 (interval_append _ 2176 2304 2358 group0865_pairs_02176 group0865_pairs_02304)))))
#print axioms group0865_facts
cert_group_header 0866
cert_group_pairs 0866 00000 0 128 128
cert_group_pairs 0866 00128 128 210 82
cert_group_facts 0866 210
#print axioms group0866_facts
cert_group_header 0867
cert_group_pairs 0867 00000 0 128 128
cert_group_pairs 0867 00128 128 153 25
cert_group_facts 0867 153
#print axioms group0867_facts
end Papers.RationalityTen.SharedFrameCatalogue
