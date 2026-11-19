module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups068Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0820
cert_group_pairs 0820 00000 0 128 128
cert_group_pairs 0820 00128 128 256 128
cert_group_pairs 0820 00256 256 384 128
cert_group_pairs 0820 00384 384 512 128
cert_group_pairs 0820 00512 512 640 128
cert_group_pairs 0820 00640 640 768 128
cert_group_pairs 0820 00768 768 896 128
cert_group_pairs 0820 00896 896 1024 128
cert_group_pairs 0820 01024 1024 1152 128
cert_group_pairs 0820 01152 1152 1280 128
cert_group_pairs 0820 01280 1280 1408 128
cert_group_pairs 0820 01408 1408 1536 128
cert_group_pairs 0820 01536 1536 1565 29
theorem group0820_facts : group0820.Facts FacetUniverses.FullSix0.cells :=
  group0820.facts_of_checks _ group0820_header (interval_append _ 0 768 1565 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0820_pairs_00000 (interval_append _ 128 256 384 group0820_pairs_00128 group0820_pairs_00256)) (interval_append _ 384 512 768 group0820_pairs_00384 (interval_append _ 512 640 768 group0820_pairs_00512 group0820_pairs_00640))) (interval_append _ 768 1152 1565 (interval_append _ 768 896 1152 group0820_pairs_00768 (interval_append _ 896 1024 1152 group0820_pairs_00896 group0820_pairs_01024)) (interval_append _ 1152 1408 1565 (interval_append _ 1152 1280 1408 group0820_pairs_01152 group0820_pairs_01280) (interval_append _ 1408 1536 1565 group0820_pairs_01408 group0820_pairs_01536))))
cert_group_header 0821
cert_group_pairs 0821 00000 0 105 105
cert_group_facts_6 0821
cert_group_header 0822
cert_group_pairs 0822 00000 0 128 128
cert_group_pairs 0822 00128 128 256 128
cert_group_pairs 0822 00256 256 314 58
cert_group_facts_2 0822 314
cert_group_header 0823
cert_group_pairs 0823 00000 0 128 128
cert_group_pairs 0823 00128 128 221 93
cert_group_facts 0823 221
cert_group_header 0824
cert_group_pairs 0824 00000 0 128 128
cert_group_pairs 0824 00128 128 256 128
cert_group_pairs 0824 00256 256 384 128
cert_group_pairs 0824 00384 384 512 128
cert_group_pairs 0824 00512 512 640 128
cert_group_pairs 0824 00640 640 768 128
cert_group_pairs 0824 00768 768 896 128
cert_group_pairs 0824 00896 896 1024 128
cert_group_pairs 0824 01024 1024 1152 128
cert_group_pairs 0824 01152 1152 1280 128
cert_group_pairs 0824 01280 1280 1408 128
cert_group_pairs 0824 01408 1408 1536 128
cert_group_pairs 0824 01536 1536 1597 61
theorem group0824_facts : group0824.Facts FacetUniverses.FullSix0.cells :=
  group0824.facts_of_checks _ group0824_header (interval_append _ 0 768 1597 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0824_pairs_00000 (interval_append _ 128 256 384 group0824_pairs_00128 group0824_pairs_00256)) (interval_append _ 384 512 768 group0824_pairs_00384 (interval_append _ 512 640 768 group0824_pairs_00512 group0824_pairs_00640))) (interval_append _ 768 1152 1597 (interval_append _ 768 896 1152 group0824_pairs_00768 (interval_append _ 896 1024 1152 group0824_pairs_00896 group0824_pairs_01024)) (interval_append _ 1152 1408 1597 (interval_append _ 1152 1280 1408 group0824_pairs_01152 group0824_pairs_01280) (interval_append _ 1408 1536 1597 group0824_pairs_01408 group0824_pairs_01536))))
end Papers.RationalityTen.SharedFrameCatalogue
