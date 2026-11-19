module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups046Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0604
cert_group_pairs 0604 00000 0 128 128
cert_group_pairs 0604 00128 128 256 128
cert_group_pairs 0604 00256 256 384 128
cert_group_pairs 0604 00384 384 512 128
cert_group_pairs 0604 00512 512 640 128
cert_group_pairs 0604 00640 640 768 128
cert_group_pairs 0604 00768 768 896 128
cert_group_pairs 0604 00896 896 1024 128
cert_group_pairs 0604 01024 1024 1152 128
cert_group_pairs 0604 01152 1152 1245 93
cert_group_facts_3 0604 1245
cert_group_header 0605
cert_group_pairs 0605 00000 0 128 128
cert_group_pairs 0605 00128 128 256 128
cert_group_pairs 0605 00256 256 384 128
cert_group_pairs 0605 00384 384 512 128
cert_group_pairs 0605 00512 512 640 128
cert_group_pairs 0605 00640 640 768 128
cert_group_pairs 0605 00768 768 896 128
cert_group_pairs 0605 00896 896 988 92
theorem group0605_facts : group0605.Facts FacetUniverses.FullSix0.cells :=
  group0605.facts_of_checks _ group0605_header (interval_append _ 0 512 988 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0605_pairs_00000 group0605_pairs_00128) (interval_append _ 256 384 512 group0605_pairs_00256 group0605_pairs_00384)) (interval_append _ 512 768 988 (interval_append _ 512 640 768 group0605_pairs_00512 group0605_pairs_00640) (interval_append _ 768 896 988 group0605_pairs_00768 group0605_pairs_00896)))
cert_group_header 0606
cert_group_pairs 0606 00000 0 128 128
cert_group_pairs 0606 00128 128 256 128
cert_group_pairs 0606 00256 256 384 128
cert_group_pairs 0606 00384 384 512 128
cert_group_pairs 0606 00512 512 640 128
cert_group_pairs 0606 00640 640 768 128
cert_group_pairs 0606 00768 768 896 128
cert_group_pairs 0606 00896 896 1024 128
cert_group_pairs 0606 01024 1024 1152 128
cert_group_pairs 0606 01152 1152 1280 128
cert_group_pairs 0606 01280 1280 1408 128
cert_group_pairs 0606 01408 1408 1536 128
cert_group_pairs 0606 01536 1536 1537 1
theorem group0606_facts : group0606.Facts FacetUniverses.FullSix0.cells :=
  group0606.facts_of_checks _ group0606_header (interval_append _ 0 768 1537 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0606_pairs_00000 (interval_append _ 128 256 384 group0606_pairs_00128 group0606_pairs_00256)) (interval_append _ 384 512 768 group0606_pairs_00384 (interval_append _ 512 640 768 group0606_pairs_00512 group0606_pairs_00640))) (interval_append _ 768 1152 1537 (interval_append _ 768 896 1152 group0606_pairs_00768 (interval_append _ 896 1024 1152 group0606_pairs_00896 group0606_pairs_01024)) (interval_append _ 1152 1408 1537 (interval_append _ 1152 1280 1408 group0606_pairs_01152 group0606_pairs_01280) (interval_append _ 1408 1536 1537 group0606_pairs_01408 group0606_pairs_01536))))
cert_group_header 0607
cert_group_pairs 0607 00000 0 128 128
cert_group_pairs 0607 00128 128 158 30
cert_group_facts 0607 158
end Papers.RationalityTen.SharedFrameCatalogue
