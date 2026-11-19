module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups036Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0539
cert_group_pairs 0539 00000 0 128 128
cert_group_pairs 0539 00128 128 256 128
cert_group_pairs 0539 00256 256 384 128
cert_group_pairs 0539 00384 384 512 128
cert_group_pairs 0539 00512 512 640 128
cert_group_pairs 0539 00640 640 768 128
cert_group_pairs 0539 00768 768 896 128
cert_group_pairs 0539 00896 896 1024 128
cert_group_pairs 0539 01024 1024 1152 128
cert_group_pairs 0539 01152 1152 1280 128
cert_group_pairs 0539 01280 1280 1408 128
cert_group_pairs 0539 01408 1408 1536 128
cert_group_pairs 0539 01536 1536 1664 128
cert_group_pairs 0539 01664 1664 1792 128
cert_group_pairs 0539 01792 1792 1920 128
cert_group_pairs 0539 01920 1920 2038 118
theorem group0539_facts : group0539.Facts FacetUniverses.FullSix0.cells :=
  group0539.facts_of_checks _ group0539_header (interval_append _ 0 1024 2038 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0539_pairs_00000 group0539_pairs_00128) (interval_append _ 256 384 512 group0539_pairs_00256 group0539_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0539_pairs_00512 group0539_pairs_00640) (interval_append _ 768 896 1024 group0539_pairs_00768 group0539_pairs_00896))) (interval_append _ 1024 1536 2038 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0539_pairs_01024 group0539_pairs_01152) (interval_append _ 1280 1408 1536 group0539_pairs_01280 group0539_pairs_01408)) (interval_append _ 1536 1792 2038 (interval_append _ 1536 1664 1792 group0539_pairs_01536 group0539_pairs_01664) (interval_append _ 1792 1920 2038 group0539_pairs_01792 group0539_pairs_01920))))
#print axioms group0539_facts
cert_group_header 0540
cert_group_pairs 0540 00000 0 111 111
cert_group_facts_6 0540
#print axioms group0540_facts
cert_group_header 0541
cert_group_pairs 0541 00000 0 128 128
cert_group_pairs 0541 00128 128 215 87
cert_group_facts 0541 215
#print axioms group0541_facts
cert_group_header 0542
cert_group_pairs 0542 00000 0 128 128
cert_group_pairs 0542 00128 128 256 128
cert_group_pairs 0542 00256 256 311 55
cert_group_facts_2 0542 311
#print axioms group0542_facts
end Papers.RationalityTen.SharedFrameCatalogue
