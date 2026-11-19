module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups088Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0993
cert_group_pairs 0993 00000 0 128 128
cert_group_pairs 0993 00128 128 256 128
cert_group_pairs 0993 00256 256 384 128
cert_group_pairs 0993 00384 384 512 128
cert_group_pairs 0993 00512 512 640 128
cert_group_pairs 0993 00640 640 768 128
cert_group_pairs 0993 00768 768 896 128
cert_group_pairs 0993 00896 896 1024 128
cert_group_pairs 0993 01024 1024 1152 128
cert_group_pairs 0993 01152 1152 1280 128
cert_group_pairs 0993 01280 1280 1408 128
cert_group_pairs 0993 01408 1408 1536 128
cert_group_pairs 0993 01536 1536 1621 85
theorem group0993_facts : group0993.Facts FacetUniverses.FullSix0.cells :=
  group0993.facts_of_checks _ group0993_header (interval_append _ 0 768 1621 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0993_pairs_00000 (interval_append _ 128 256 384 group0993_pairs_00128 group0993_pairs_00256)) (interval_append _ 384 512 768 group0993_pairs_00384 (interval_append _ 512 640 768 group0993_pairs_00512 group0993_pairs_00640))) (interval_append _ 768 1152 1621 (interval_append _ 768 896 1152 group0993_pairs_00768 (interval_append _ 896 1024 1152 group0993_pairs_00896 group0993_pairs_01024)) (interval_append _ 1152 1408 1621 (interval_append _ 1152 1280 1408 group0993_pairs_01152 group0993_pairs_01280) (interval_append _ 1408 1536 1621 group0993_pairs_01408 group0993_pairs_01536))))
#print axioms group0993_facts
cert_group_header 0994
cert_group_pairs 0994 00000 0 128 128
cert_group_pairs 0994 00128 128 256 128
cert_group_pairs 0994 00256 256 384 128
cert_group_pairs 0994 00384 384 512 128
cert_group_pairs 0994 00512 512 640 128
cert_group_pairs 0994 00640 640 768 128
cert_group_pairs 0994 00768 768 896 128
cert_group_pairs 0994 00896 896 1024 128
cert_group_pairs 0994 01024 1024 1152 128
cert_group_pairs 0994 01152 1152 1280 128
cert_group_pairs 0994 01280 1280 1408 128
cert_group_pairs 0994 01408 1408 1416 8
theorem group0994_facts : group0994.Facts FacetUniverses.FullSix0.cells :=
  group0994.facts_of_checks _ group0994_header (interval_append _ 0 768 1416 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0994_pairs_00000 (interval_append _ 128 256 384 group0994_pairs_00128 group0994_pairs_00256)) (interval_append _ 384 512 768 group0994_pairs_00384 (interval_append _ 512 640 768 group0994_pairs_00512 group0994_pairs_00640))) (interval_append _ 768 1152 1416 (interval_append _ 768 896 1152 group0994_pairs_00768 (interval_append _ 896 1024 1152 group0994_pairs_00896 group0994_pairs_01024)) (interval_append _ 1152 1280 1416 group0994_pairs_01152 (interval_append _ 1280 1408 1416 group0994_pairs_01280 group0994_pairs_01408))))
#print axioms group0994_facts
end Papers.RationalityTen.SharedFrameCatalogue
