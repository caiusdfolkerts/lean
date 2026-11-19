module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups045Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0599
cert_group_pairs 0599 00000 0 128 128
cert_group_pairs 0599 00128 128 256 128
cert_group_pairs 0599 00256 256 384 128
cert_group_pairs 0599 00384 384 512 128
cert_group_pairs 0599 00512 512 640 128
cert_group_pairs 0599 00640 640 768 128
cert_group_pairs 0599 00768 768 896 128
cert_group_pairs 0599 00896 896 1024 128
cert_group_pairs 0599 01024 1024 1049 25
theorem group0599_facts : group0599.Facts FacetUniverses.FullSix0.cells :=
  group0599.facts_of_checks _ group0599_header (interval_append _ 0 512 1049 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0599_pairs_00000 group0599_pairs_00128) (interval_append _ 256 384 512 group0599_pairs_00256 group0599_pairs_00384)) (interval_append _ 512 768 1049 (interval_append _ 512 640 768 group0599_pairs_00512 group0599_pairs_00640) (interval_append _ 768 896 1049 group0599_pairs_00768 (interval_append _ 896 1024 1049 group0599_pairs_00896 group0599_pairs_01024))))
cert_group_header 0600
cert_group_pairs 0600 00000 0 128 128
cert_group_pairs 0600 00128 128 256 128
cert_group_pairs 0600 00256 256 384 128
cert_group_pairs 0600 00384 384 512 128
cert_group_pairs 0600 00512 512 640 128
cert_group_pairs 0600 00640 640 768 128
cert_group_pairs 0600 00768 768 896 128
cert_group_pairs 0600 00896 896 1024 128
cert_group_pairs 0600 01024 1024 1152 128
cert_group_pairs 0600 01152 1152 1275 123
cert_group_facts_3 0600 1275
cert_group_header 0601
cert_group_pairs 0601 00000 0 128 128
cert_group_pairs 0601 00128 128 171 43
cert_group_facts 0601 171
cert_group_header 0602
cert_group_pairs 0602 00000 0 105 105
cert_group_facts_6 0602
cert_group_header 0603
cert_group_pairs 0603 00000 0 128 128
cert_group_pairs 0603 00128 128 256 128
cert_group_pairs 0603 00256 256 269 13
cert_group_facts_2 0603 269
end Papers.RationalityTen.SharedFrameCatalogue
