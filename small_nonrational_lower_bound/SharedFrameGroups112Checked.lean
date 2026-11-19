module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups112Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1099
cert_group_pairs 1099 00000 0 128 128
cert_group_pairs 1099 00128 128 256 128
cert_group_pairs 1099 00256 256 384 128
cert_group_pairs 1099 00384 384 512 128
cert_group_pairs 1099 00512 512 640 128
cert_group_pairs 1099 00640 640 768 128
cert_group_pairs 1099 00768 768 896 128
cert_group_pairs 1099 00896 896 1024 128
cert_group_pairs 1099 01024 1024 1152 128
cert_group_pairs 1099 01152 1152 1280 128
cert_group_pairs 1099 01280 1280 1408 128
cert_group_pairs 1099 01408 1408 1536 128
cert_group_pairs 1099 01536 1536 1664 128
cert_group_pairs 1099 01664 1664 1792 128
cert_group_pairs 1099 01792 1792 1920 128
cert_group_pairs 1099 01920 1920 2020 100
theorem group1099_facts : group1099.Facts FacetUniverses.FullSix0.cells :=
  group1099.facts_of_checks _ group1099_header (interval_append _ 0 1024 2020 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1099_pairs_00000 group1099_pairs_00128) (interval_append _ 256 384 512 group1099_pairs_00256 group1099_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group1099_pairs_00512 group1099_pairs_00640) (interval_append _ 768 896 1024 group1099_pairs_00768 group1099_pairs_00896))) (interval_append _ 1024 1536 2020 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group1099_pairs_01024 group1099_pairs_01152) (interval_append _ 1280 1408 1536 group1099_pairs_01280 group1099_pairs_01408)) (interval_append _ 1536 1792 2020 (interval_append _ 1536 1664 1792 group1099_pairs_01536 group1099_pairs_01664) (interval_append _ 1792 1920 2020 group1099_pairs_01792 group1099_pairs_01920))))
#print axioms group1099_facts
end Papers.RationalityTen.SharedFrameCatalogue
