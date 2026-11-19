module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups053Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0654
cert_group_pairs 0654 00000 0 128 128
cert_group_pairs 0654 00128 128 256 128
cert_group_pairs 0654 00256 256 384 128
cert_group_pairs 0654 00384 384 512 128
cert_group_pairs 0654 00512 512 640 128
cert_group_pairs 0654 00640 640 768 128
cert_group_pairs 0654 00768 768 896 128
cert_group_pairs 0654 00896 896 1024 128
cert_group_pairs 0654 01024 1024 1152 128
cert_group_pairs 0654 01152 1152 1280 128
cert_group_pairs 0654 01280 1280 1408 128
cert_group_pairs 0654 01408 1408 1430 22
theorem group0654_facts : group0654.Facts FacetUniverses.FullSix0.cells :=
  group0654.facts_of_checks _ group0654_header (interval_append _ 0 768 1430 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0654_pairs_00000 (interval_append _ 128 256 384 group0654_pairs_00128 group0654_pairs_00256)) (interval_append _ 384 512 768 group0654_pairs_00384 (interval_append _ 512 640 768 group0654_pairs_00512 group0654_pairs_00640))) (interval_append _ 768 1152 1430 (interval_append _ 768 896 1152 group0654_pairs_00768 (interval_append _ 896 1024 1152 group0654_pairs_00896 group0654_pairs_01024)) (interval_append _ 1152 1280 1430 group0654_pairs_01152 (interval_append _ 1280 1408 1430 group0654_pairs_01280 group0654_pairs_01408))))
cert_group_header 0655
cert_group_pairs 0655 00000 0 128 128
cert_group_pairs 0655 00128 128 256 128
cert_group_pairs 0655 00256 256 384 128
cert_group_pairs 0655 00384 384 512 128
cert_group_pairs 0655 00512 512 640 128
cert_group_pairs 0655 00640 640 768 128
cert_group_pairs 0655 00768 768 896 128
cert_group_pairs 0655 00896 896 1024 128
cert_group_pairs 0655 01024 1024 1152 128
cert_group_pairs 0655 01152 1152 1280 128
cert_group_pairs 0655 01280 1280 1408 128
cert_group_pairs 0655 01408 1408 1536 128
cert_group_pairs 0655 01536 1536 1664 128
cert_group_pairs 0655 01664 1664 1792 128
cert_group_pairs 0655 01792 1792 1920 128
cert_group_pairs 0655 01920 1920 2048 128
cert_group_pairs 0655 02048 2048 2109 61
theorem group0655_facts : group0655.Facts FacetUniverses.FullSix0.cells :=
  group0655.facts_of_checks _ group0655_header (interval_append _ 0 1024 2109 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0655_pairs_00000 group0655_pairs_00128) (interval_append _ 256 384 512 group0655_pairs_00256 group0655_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0655_pairs_00512 group0655_pairs_00640) (interval_append _ 768 896 1024 group0655_pairs_00768 group0655_pairs_00896))) (interval_append _ 1024 1536 2109 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0655_pairs_01024 group0655_pairs_01152) (interval_append _ 1280 1408 1536 group0655_pairs_01280 group0655_pairs_01408)) (interval_append _ 1536 1792 2109 (interval_append _ 1536 1664 1792 group0655_pairs_01536 group0655_pairs_01664) (interval_append _ 1792 1920 2109 group0655_pairs_01792 (interval_append _ 1920 2048 2109 group0655_pairs_01920 group0655_pairs_02048)))))
cert_group_header 0656
cert_group_pairs 0656 00000 0 128 128
cert_group_pairs 0656 00128 128 256 128
cert_group_pairs 0656 00256 256 283 27
cert_group_facts_2 0656 283
cert_group_header 0657
cert_group_pairs 0657 00000 0 128 128
cert_group_pairs 0657 00128 128 213 85
cert_group_facts 0657 213
end Papers.RationalityTen.SharedFrameCatalogue
