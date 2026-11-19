module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups052Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0646
cert_group_pairs 0646 00000 0 128 128
cert_group_pairs 0646 00128 128 256 128
cert_group_pairs 0646 00256 256 384 128
cert_group_pairs 0646 00384 384 512 128
cert_group_pairs 0646 00512 512 640 128
cert_group_pairs 0646 00640 640 768 128
cert_group_pairs 0646 00768 768 896 128
cert_group_pairs 0646 00896 896 1024 128
cert_group_pairs 0646 01024 1024 1152 128
cert_group_pairs 0646 01152 1152 1280 128
cert_group_pairs 0646 01280 1280 1408 128
cert_group_pairs 0646 01408 1408 1536 128
cert_group_pairs 0646 01536 1536 1664 128
cert_group_pairs 0646 01664 1664 1792 128
cert_group_pairs 0646 01792 1792 1920 128
cert_group_pairs 0646 01920 1920 1979 59
theorem group0646_facts : group0646.Facts FacetUniverses.FullSix0.cells :=
  group0646.facts_of_checks _ group0646_header (interval_append _ 0 1024 1979 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0646_pairs_00000 group0646_pairs_00128) (interval_append _ 256 384 512 group0646_pairs_00256 group0646_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0646_pairs_00512 group0646_pairs_00640) (interval_append _ 768 896 1024 group0646_pairs_00768 group0646_pairs_00896))) (interval_append _ 1024 1536 1979 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0646_pairs_01024 group0646_pairs_01152) (interval_append _ 1280 1408 1536 group0646_pairs_01280 group0646_pairs_01408)) (interval_append _ 1536 1792 1979 (interval_append _ 1536 1664 1792 group0646_pairs_01536 group0646_pairs_01664) (interval_append _ 1792 1920 1979 group0646_pairs_01792 group0646_pairs_01920))))
#print axioms group0646_facts
cert_group_header 0647
cert_group_pairs 0647 00000 0 128 128
cert_group_pairs 0647 00128 128 256 128
cert_group_pairs 0647 00256 256 294 38
cert_group_facts_2 0647 294
#print axioms group0647_facts
cert_group_header 0648
cert_group_pairs 0648 00000 0 128 128
cert_group_pairs 0648 00128 128 256 128
cert_group_facts 0648 256
#print axioms group0648_facts
cert_group_header 0649
cert_group_pairs 0649 00000 0 128 128
cert_group_pairs 0649 00128 128 253 125
cert_group_facts 0649 253
#print axioms group0649_facts
cert_group_header 0650
cert_group_pairs 0650 00000 0 128 128
cert_group_pairs 0650 00128 128 256 128
cert_group_pairs 0650 00256 256 274 18
cert_group_facts_2 0650 274
#print axioms group0650_facts
cert_group_header 0651
cert_group_pairs 0651 00000 0 128 128
cert_group_pairs 0651 00128 128 256 128
cert_group_pairs 0651 00256 256 362 106
cert_group_facts_2 0651 362
#print axioms group0651_facts
cert_group_header 0652
cert_group_pairs 0652 00000 0 128 128
cert_group_pairs 0652 00128 128 131 3
cert_group_facts 0652 131
#print axioms group0652_facts
cert_group_header 0653
cert_group_pairs 0653 00000 0 128 128
cert_group_pairs 0653 00128 128 232 104
cert_group_facts 0653 232
#print axioms group0653_facts
end Papers.RationalityTen.SharedFrameCatalogue
