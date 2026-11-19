module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups048Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0624
cert_group_pairs 0624 00000 0 105 105
cert_group_facts_6 0624
#print axioms group0624_facts
cert_group_header 0625
cert_group_pairs 0625 00000 0 128 128
cert_group_pairs 0625 00128 128 256 128
cert_group_pairs 0625 00256 256 384 128
cert_group_pairs 0625 00384 384 424 40
cert_group_facts_4 0625 424
#print axioms group0625_facts
cert_group_header 0626
cert_group_pairs 0626 00000 0 128 128
cert_group_pairs 0626 00128 128 162 34
cert_group_facts 0626 162
#print axioms group0626_facts
cert_group_header 0627
cert_group_pairs 0627 00000 0 128 128
cert_group_pairs 0627 00128 128 256 128
cert_group_pairs 0627 00256 256 384 128
cert_group_pairs 0627 00384 384 512 128
cert_group_pairs 0627 00512 512 640 128
cert_group_pairs 0627 00640 640 768 128
cert_group_pairs 0627 00768 768 896 128
cert_group_pairs 0627 00896 896 1024 128
cert_group_pairs 0627 01024 1024 1152 128
cert_group_pairs 0627 01152 1152 1280 128
cert_group_pairs 0627 01280 1280 1408 128
cert_group_pairs 0627 01408 1408 1536 128
cert_group_pairs 0627 01536 1536 1550 14
theorem group0627_facts : group0627.Facts FacetUniverses.FullSix0.cells :=
  group0627.facts_of_checks _ group0627_header (interval_append _ 0 768 1550 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0627_pairs_00000 (interval_append _ 128 256 384 group0627_pairs_00128 group0627_pairs_00256)) (interval_append _ 384 512 768 group0627_pairs_00384 (interval_append _ 512 640 768 group0627_pairs_00512 group0627_pairs_00640))) (interval_append _ 768 1152 1550 (interval_append _ 768 896 1152 group0627_pairs_00768 (interval_append _ 896 1024 1152 group0627_pairs_00896 group0627_pairs_01024)) (interval_append _ 1152 1408 1550 (interval_append _ 1152 1280 1408 group0627_pairs_01152 group0627_pairs_01280) (interval_append _ 1408 1536 1550 group0627_pairs_01408 group0627_pairs_01536))))
#print axioms group0627_facts
cert_group_header 0628
cert_group_pairs 0628 00000 0 128 128
cert_group_pairs 0628 00128 128 256 128
cert_group_pairs 0628 00256 256 384 128
cert_group_pairs 0628 00384 384 512 128
cert_group_pairs 0628 00512 512 640 128
cert_group_pairs 0628 00640 640 768 128
cert_group_pairs 0628 00768 768 896 128
cert_group_pairs 0628 00896 896 1024 128
cert_group_pairs 0628 01024 1024 1152 128
cert_group_pairs 0628 01152 1152 1280 128
cert_group_pairs 0628 01280 1280 1408 128
cert_group_pairs 0628 01408 1408 1504 96
theorem group0628_facts : group0628.Facts FacetUniverses.FullSix0.cells :=
  group0628.facts_of_checks _ group0628_header (interval_append _ 0 768 1504 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0628_pairs_00000 (interval_append _ 128 256 384 group0628_pairs_00128 group0628_pairs_00256)) (interval_append _ 384 512 768 group0628_pairs_00384 (interval_append _ 512 640 768 group0628_pairs_00512 group0628_pairs_00640))) (interval_append _ 768 1152 1504 (interval_append _ 768 896 1152 group0628_pairs_00768 (interval_append _ 896 1024 1152 group0628_pairs_00896 group0628_pairs_01024)) (interval_append _ 1152 1280 1504 group0628_pairs_01152 (interval_append _ 1280 1408 1504 group0628_pairs_01280 group0628_pairs_01408))))
#print axioms group0628_facts
cert_group_header 0629
cert_group_pairs 0629 00000 0 128 128
cert_group_pairs 0629 00128 128 153 25
cert_group_facts 0629 153
#print axioms group0629_facts
end Papers.RationalityTen.SharedFrameCatalogue
