module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups038Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0545
cert_group_pairs 0545 00000 0 128 128
cert_group_pairs 0545 00128 128 256 128
cert_group_pairs 0545 00256 256 384 128
cert_group_pairs 0545 00384 384 512 128
cert_group_pairs 0545 00512 512 640 128
cert_group_pairs 0545 00640 640 768 128
cert_group_pairs 0545 00768 768 896 128
cert_group_pairs 0545 00896 896 1024 128
cert_group_pairs 0545 01024 1024 1152 128
cert_group_pairs 0545 01152 1152 1280 128
cert_group_pairs 0545 01280 1280 1408 128
cert_group_pairs 0545 01408 1408 1409 1
theorem group0545_facts : group0545.Facts FacetUniverses.FullSix0.cells :=
  group0545.facts_of_checks _ group0545_header (interval_append _ 0 768 1409 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0545_pairs_00000 (interval_append _ 128 256 384 group0545_pairs_00128 group0545_pairs_00256)) (interval_append _ 384 512 768 group0545_pairs_00384 (interval_append _ 512 640 768 group0545_pairs_00512 group0545_pairs_00640))) (interval_append _ 768 1152 1409 (interval_append _ 768 896 1152 group0545_pairs_00768 (interval_append _ 896 1024 1152 group0545_pairs_00896 group0545_pairs_01024)) (interval_append _ 1152 1280 1409 group0545_pairs_01152 (interval_append _ 1280 1408 1409 group0545_pairs_01280 group0545_pairs_01408))))
cert_group_header 0546
cert_group_pairs 0546 00000 0 128 128
cert_group_pairs 0546 00128 128 204 76
cert_group_facts 0546 204
cert_group_header 0547
cert_group_pairs 0547 00000 0 125 125
cert_group_facts_6 0547
cert_group_header 0548
cert_group_pairs 0548 00000 0 128 128
cert_group_pairs 0548 00128 128 137 9
cert_group_facts 0548 137
cert_group_header 0549
cert_group_pairs 0549 00000 0 128 128
cert_group_pairs 0549 00128 128 256 128
cert_group_pairs 0549 00256 256 384 128
cert_group_pairs 0549 00384 384 512 128
cert_group_pairs 0549 00512 512 640 128
cert_group_pairs 0549 00640 640 768 128
cert_group_pairs 0549 00768 768 896 128
cert_group_pairs 0549 00896 896 1024 128
cert_group_pairs 0549 01024 1024 1152 128
cert_group_pairs 0549 01152 1152 1280 128
cert_group_pairs 0549 01280 1280 1408 128
cert_group_pairs 0549 01408 1408 1426 18
theorem group0549_facts : group0549.Facts FacetUniverses.FullSix0.cells :=
  group0549.facts_of_checks _ group0549_header (interval_append _ 0 768 1426 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0549_pairs_00000 (interval_append _ 128 256 384 group0549_pairs_00128 group0549_pairs_00256)) (interval_append _ 384 512 768 group0549_pairs_00384 (interval_append _ 512 640 768 group0549_pairs_00512 group0549_pairs_00640))) (interval_append _ 768 1152 1426 (interval_append _ 768 896 1152 group0549_pairs_00768 (interval_append _ 896 1024 1152 group0549_pairs_00896 group0549_pairs_01024)) (interval_append _ 1152 1280 1426 group0549_pairs_01152 (interval_append _ 1280 1408 1426 group0549_pairs_01280 group0549_pairs_01408))))
end Papers.RationalityTen.SharedFrameCatalogue
