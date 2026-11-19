module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups037Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0543
cert_group_pairs 0543 00000 0 128 128
cert_group_pairs 0543 00128 128 256 128
cert_group_pairs 0543 00256 256 384 128
cert_group_pairs 0543 00384 384 512 128
cert_group_pairs 0543 00512 512 640 128
cert_group_pairs 0543 00640 640 768 128
cert_group_pairs 0543 00768 768 896 128
cert_group_pairs 0543 00896 896 1024 128
cert_group_pairs 0543 01024 1024 1152 128
cert_group_pairs 0543 01152 1152 1280 128
cert_group_pairs 0543 01280 1280 1408 128
cert_group_pairs 0543 01408 1408 1536 128
cert_group_pairs 0543 01536 1536 1664 128
cert_group_pairs 0543 01664 1664 1792 128
cert_group_pairs 0543 01792 1792 1856 64
theorem group0543_facts : group0543.Facts FacetUniverses.FullSix0.cells :=
  group0543.facts_of_checks _ group0543_header (interval_append _ 0 896 1856 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0543_pairs_00000 (interval_append _ 128 256 384 group0543_pairs_00128 group0543_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0543_pairs_00384 group0543_pairs_00512) (interval_append _ 640 768 896 group0543_pairs_00640 group0543_pairs_00768))) (interval_append _ 896 1408 1856 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0543_pairs_00896 group0543_pairs_01024) (interval_append _ 1152 1280 1408 group0543_pairs_01152 group0543_pairs_01280)) (interval_append _ 1408 1664 1856 (interval_append _ 1408 1536 1664 group0543_pairs_01408 group0543_pairs_01536) (interval_append _ 1664 1792 1856 group0543_pairs_01664 group0543_pairs_01792))))
#print axioms group0543_facts
cert_group_header 0544
cert_group_pairs 0544 00000 0 128 128
cert_group_pairs 0544 00128 128 256 128
cert_group_pairs 0544 00256 256 384 128
cert_group_pairs 0544 00384 384 512 128
cert_group_pairs 0544 00512 512 640 128
cert_group_pairs 0544 00640 640 768 128
cert_group_pairs 0544 00768 768 896 128
cert_group_pairs 0544 00896 896 1024 128
cert_group_pairs 0544 01024 1024 1152 128
cert_group_pairs 0544 01152 1152 1280 128
cert_group_pairs 0544 01280 1280 1408 128
cert_group_pairs 0544 01408 1408 1536 128
cert_group_pairs 0544 01536 1536 1664 128
cert_group_pairs 0544 01664 1664 1770 106
theorem group0544_facts : group0544.Facts FacetUniverses.FullSix0.cells :=
  group0544.facts_of_checks _ group0544_header (interval_append _ 0 896 1770 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0544_pairs_00000 (interval_append _ 128 256 384 group0544_pairs_00128 group0544_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0544_pairs_00384 group0544_pairs_00512) (interval_append _ 640 768 896 group0544_pairs_00640 group0544_pairs_00768))) (interval_append _ 896 1280 1770 (interval_append _ 896 1024 1280 group0544_pairs_00896 (interval_append _ 1024 1152 1280 group0544_pairs_01024 group0544_pairs_01152)) (interval_append _ 1280 1536 1770 (interval_append _ 1280 1408 1536 group0544_pairs_01280 group0544_pairs_01408) (interval_append _ 1536 1664 1770 group0544_pairs_01536 group0544_pairs_01664))))
#print axioms group0544_facts
end Papers.RationalityTen.SharedFrameCatalogue
