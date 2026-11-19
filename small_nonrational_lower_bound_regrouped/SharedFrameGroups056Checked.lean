module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups056Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0661
cert_group_pairs 0661 00000 0 128 128
cert_group_pairs 0661 00128 128 256 128
cert_group_pairs 0661 00256 256 384 128
cert_group_pairs 0661 00384 384 512 128
cert_group_pairs 0661 00512 512 640 128
cert_group_pairs 0661 00640 640 768 128
cert_group_pairs 0661 00768 768 896 128
cert_group_pairs 0661 00896 896 1024 128
cert_group_pairs 0661 01024 1024 1152 128
cert_group_pairs 0661 01152 1152 1280 128
cert_group_pairs 0661 01280 1280 1408 128
cert_group_pairs 0661 01408 1408 1536 128
cert_group_pairs 0661 01536 1536 1664 128
cert_group_pairs 0661 01664 1664 1792 128
cert_group_pairs 0661 01792 1792 1920 128
cert_group_pairs 0661 01920 1920 2048 128
cert_group_pairs 0661 02048 2048 2176 128
cert_group_pairs 0661 02176 2176 2304 128
cert_group_pairs 0661 02304 2304 2432 128
cert_group_pairs 0661 02432 2432 2560 128
cert_group_pairs 0661 02560 2560 2688 128
cert_group_pairs 0661 02688 2688 2816 128
cert_group_pairs 0661 02816 2816 2944 128
cert_group_pairs 0661 02944 2944 3072 128
cert_group_pairs 0661 03072 3072 3200 128
cert_group_pairs 0661 03200 3200 3328 128
cert_group_pairs 0661 03328 3328 3456 128
cert_group_pairs 0661 03456 3456 3584 128
cert_group_pairs 0661 03584 3584 3652 68
theorem group0661_facts : group0661.Facts FacetUniverses.FullSix0.cells :=
  group0661.facts_of_checks _ group0661_header (interval_append _ 0 1792 3652 (interval_append _ 0 896 1792 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0661_pairs_00000 (interval_append _ 128 256 384 group0661_pairs_00128 group0661_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0661_pairs_00384 group0661_pairs_00512) (interval_append _ 640 768 896 group0661_pairs_00640 group0661_pairs_00768))) (interval_append _ 896 1280 1792 (interval_append _ 896 1024 1280 group0661_pairs_00896 (interval_append _ 1024 1152 1280 group0661_pairs_01024 group0661_pairs_01152)) (interval_append _ 1280 1536 1792 (interval_append _ 1280 1408 1536 group0661_pairs_01280 group0661_pairs_01408) (interval_append _ 1536 1664 1792 group0661_pairs_01536 group0661_pairs_01664)))) (interval_append _ 1792 2688 3652 (interval_append _ 1792 2176 2688 (interval_append _ 1792 1920 2176 group0661_pairs_01792 (interval_append _ 1920 2048 2176 group0661_pairs_01920 group0661_pairs_02048)) (interval_append _ 2176 2432 2688 (interval_append _ 2176 2304 2432 group0661_pairs_02176 group0661_pairs_02304) (interval_append _ 2432 2560 2688 group0661_pairs_02432 group0661_pairs_02560))) (interval_append _ 2688 3200 3652 (interval_append _ 2688 2944 3200 (interval_append _ 2688 2816 2944 group0661_pairs_02688 group0661_pairs_02816) (interval_append _ 2944 3072 3200 group0661_pairs_02944 group0661_pairs_03072)) (interval_append _ 3200 3456 3652 (interval_append _ 3200 3328 3456 group0661_pairs_03200 group0661_pairs_03328) (interval_append _ 3456 3584 3652 group0661_pairs_03456 group0661_pairs_03584)))))
#print axioms group0661_facts
cert_group_header 0662
cert_group_pairs 0662 00000 0 125 125
cert_group_facts_6 0662
#print axioms group0662_facts
cert_group_header 0663
cert_group_pairs 0663 00000 0 125 125
cert_group_facts_6 0663
#print axioms group0663_facts
cert_group_header 0664
cert_group_pairs 0664 00000 0 75 75
cert_group_facts_6 0664
#print axioms group0664_facts
cert_group_header 0665
cert_group_pairs 0665 00000 0 75 75
cert_group_facts_6 0665
#print axioms group0665_facts
end Papers.RationalityTen.SharedFrameCatalogue
