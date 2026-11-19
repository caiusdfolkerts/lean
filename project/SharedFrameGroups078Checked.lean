module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups078Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0871
cert_group_pairs 0871 00000 0 128 128
cert_group_pairs 0871 00128 128 256 128
cert_group_pairs 0871 00256 256 384 128
cert_group_pairs 0871 00384 384 512 128
cert_group_pairs 0871 00512 512 640 128
cert_group_pairs 0871 00640 640 768 128
cert_group_pairs 0871 00768 768 896 128
cert_group_pairs 0871 00896 896 1024 128
cert_group_pairs 0871 01024 1024 1152 128
cert_group_pairs 0871 01152 1152 1280 128
cert_group_pairs 0871 01280 1280 1408 128
cert_group_pairs 0871 01408 1408 1536 128
cert_group_pairs 0871 01536 1536 1664 128
cert_group_pairs 0871 01664 1664 1792 128
cert_group_pairs 0871 01792 1792 1920 128
cert_group_pairs 0871 01920 1920 2048 128
cert_group_pairs 0871 02048 2048 2176 128
cert_group_pairs 0871 02176 2176 2304 128
cert_group_pairs 0871 02304 2304 2432 128
cert_group_pairs 0871 02432 2432 2560 128
cert_group_pairs 0871 02560 2560 2688 128
cert_group_pairs 0871 02688 2688 2816 128
cert_group_pairs 0871 02816 2816 2944 128
cert_group_pairs 0871 02944 2944 3072 128
cert_group_pairs 0871 03072 3072 3200 128
cert_group_pairs 0871 03200 3200 3328 128
cert_group_pairs 0871 03328 3328 3456 128
cert_group_pairs 0871 03456 3456 3584 128
cert_group_pairs 0871 03584 3584 3712 128
cert_group_pairs 0871 03712 3712 3819 107
theorem group0871_facts : group0871.Facts FacetUniverses.FullSix0.cells :=
  group0871.facts_of_checks _ group0871_header (interval_append _ 0 1920 3819 (interval_append _ 0 896 1920 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0871_pairs_00000 (interval_append _ 128 256 384 group0871_pairs_00128 group0871_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0871_pairs_00384 group0871_pairs_00512) (interval_append _ 640 768 896 group0871_pairs_00640 group0871_pairs_00768))) (interval_append _ 896 1408 1920 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0871_pairs_00896 group0871_pairs_01024) (interval_append _ 1152 1280 1408 group0871_pairs_01152 group0871_pairs_01280)) (interval_append _ 1408 1664 1920 (interval_append _ 1408 1536 1664 group0871_pairs_01408 group0871_pairs_01536) (interval_append _ 1664 1792 1920 group0871_pairs_01664 group0871_pairs_01792)))) (interval_append _ 1920 2816 3819 (interval_append _ 1920 2304 2816 (interval_append _ 1920 2048 2304 group0871_pairs_01920 (interval_append _ 2048 2176 2304 group0871_pairs_02048 group0871_pairs_02176)) (interval_append _ 2304 2560 2816 (interval_append _ 2304 2432 2560 group0871_pairs_02304 group0871_pairs_02432) (interval_append _ 2560 2688 2816 group0871_pairs_02560 group0871_pairs_02688))) (interval_append _ 2816 3328 3819 (interval_append _ 2816 3072 3328 (interval_append _ 2816 2944 3072 group0871_pairs_02816 group0871_pairs_02944) (interval_append _ 3072 3200 3328 group0871_pairs_03072 group0871_pairs_03200)) (interval_append _ 3328 3584 3819 (interval_append _ 3328 3456 3584 group0871_pairs_03328 group0871_pairs_03456) (interval_append _ 3584 3712 3819 group0871_pairs_03584 group0871_pairs_03712)))))
#print axioms group0871_facts
cert_group_header 0872
cert_group_pairs 0872 00000 0 111 111
cert_group_facts_6 0872
#print axioms group0872_facts
cert_group_header 0873
cert_group_pairs 0873 00000 0 111 111
cert_group_facts_6 0873
#print axioms group0873_facts
end Papers.RationalityTen.SharedFrameCatalogue
