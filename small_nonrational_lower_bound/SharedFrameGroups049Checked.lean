module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups049Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0630
cert_group_pairs 0630 00000 0 128 128
cert_group_pairs 0630 00128 128 204 76
cert_group_facts 0630 204
#print axioms group0630_facts
cert_group_header 0631
cert_group_pairs 0631 00000 0 128 128
cert_group_pairs 0631 00128 128 192 64
cert_group_facts 0631 192
#print axioms group0631_facts
cert_group_header 0632
cert_group_pairs 0632 00000 0 128 128
cert_group_pairs 0632 00128 128 256 128
cert_group_pairs 0632 00256 256 384 128
cert_group_pairs 0632 00384 384 512 128
cert_group_pairs 0632 00512 512 640 128
cert_group_pairs 0632 00640 640 768 128
cert_group_pairs 0632 00768 768 896 128
cert_group_pairs 0632 00896 896 1024 128
cert_group_pairs 0632 01024 1024 1152 128
cert_group_pairs 0632 01152 1152 1280 128
cert_group_pairs 0632 01280 1280 1361 81
theorem group0632_facts : group0632.Facts FacetUniverses.FullSix0.cells :=
  group0632.facts_of_checks _ group0632_header (interval_append _ 0 640 1361 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0632_pairs_00000 group0632_pairs_00128) (interval_append _ 256 384 640 group0632_pairs_00256 (interval_append _ 384 512 640 group0632_pairs_00384 group0632_pairs_00512))) (interval_append _ 640 1024 1361 (interval_append _ 640 768 1024 group0632_pairs_00640 (interval_append _ 768 896 1024 group0632_pairs_00768 group0632_pairs_00896)) (interval_append _ 1024 1152 1361 group0632_pairs_01024 (interval_append _ 1152 1280 1361 group0632_pairs_01152 group0632_pairs_01280))))
#print axioms group0632_facts
cert_group_header 0633
cert_group_pairs 0633 00000 0 128 128
cert_group_pairs 0633 00128 128 256 128
cert_group_pairs 0633 00256 256 384 128
cert_group_pairs 0633 00384 384 512 128
cert_group_pairs 0633 00512 512 640 128
cert_group_pairs 0633 00640 640 768 128
cert_group_pairs 0633 00768 768 896 128
cert_group_pairs 0633 00896 896 1024 128
cert_group_pairs 0633 01024 1024 1152 128
cert_group_pairs 0633 01152 1152 1280 128
cert_group_pairs 0633 01280 1280 1408 128
cert_group_pairs 0633 01408 1408 1536 128
cert_group_pairs 0633 01536 1536 1608 72
theorem group0633_facts : group0633.Facts FacetUniverses.FullSix0.cells :=
  group0633.facts_of_checks _ group0633_header (interval_append _ 0 768 1608 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0633_pairs_00000 (interval_append _ 128 256 384 group0633_pairs_00128 group0633_pairs_00256)) (interval_append _ 384 512 768 group0633_pairs_00384 (interval_append _ 512 640 768 group0633_pairs_00512 group0633_pairs_00640))) (interval_append _ 768 1152 1608 (interval_append _ 768 896 1152 group0633_pairs_00768 (interval_append _ 896 1024 1152 group0633_pairs_00896 group0633_pairs_01024)) (interval_append _ 1152 1408 1608 (interval_append _ 1152 1280 1408 group0633_pairs_01152 group0633_pairs_01280) (interval_append _ 1408 1536 1608 group0633_pairs_01408 group0633_pairs_01536))))
#print axioms group0633_facts
end Papers.RationalityTen.SharedFrameCatalogue
