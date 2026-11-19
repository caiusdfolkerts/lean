module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups077Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0870
cert_group_pairs 0870 00000 0 128 128
cert_group_pairs 0870 00128 128 256 128
cert_group_pairs 0870 00256 256 384 128
cert_group_pairs 0870 00384 384 512 128
cert_group_pairs 0870 00512 512 640 128
cert_group_pairs 0870 00640 640 768 128
cert_group_pairs 0870 00768 768 896 128
cert_group_pairs 0870 00896 896 1024 128
cert_group_pairs 0870 01024 1024 1152 128
cert_group_pairs 0870 01152 1152 1280 128
cert_group_pairs 0870 01280 1280 1408 128
cert_group_pairs 0870 01408 1408 1536 128
cert_group_pairs 0870 01536 1536 1664 128
cert_group_pairs 0870 01664 1664 1792 128
cert_group_pairs 0870 01792 1792 1920 128
cert_group_pairs 0870 01920 1920 2048 128
cert_group_pairs 0870 02048 2048 2121 73
theorem group0870_facts : group0870.Facts FacetUniverses.FullSix0.cells :=
  group0870.facts_of_checks _ group0870_header (interval_append _ 0 1024 2121 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0870_pairs_00000 group0870_pairs_00128) (interval_append _ 256 384 512 group0870_pairs_00256 group0870_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0870_pairs_00512 group0870_pairs_00640) (interval_append _ 768 896 1024 group0870_pairs_00768 group0870_pairs_00896))) (interval_append _ 1024 1536 2121 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0870_pairs_01024 group0870_pairs_01152) (interval_append _ 1280 1408 1536 group0870_pairs_01280 group0870_pairs_01408)) (interval_append _ 1536 1792 2121 (interval_append _ 1536 1664 1792 group0870_pairs_01536 group0870_pairs_01664) (interval_append _ 1792 1920 2121 group0870_pairs_01792 (interval_append _ 1920 2048 2121 group0870_pairs_01920 group0870_pairs_02048)))))
end Papers.RationalityTen.SharedFrameCatalogue
