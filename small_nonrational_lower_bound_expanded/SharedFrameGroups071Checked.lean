module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups071Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0843
cert_group_pairs 0843 00000 0 128 128
cert_group_pairs 0843 00128 128 207 79
cert_group_facts 0843 207
cert_group_header 0844
cert_group_pairs 0844 00000 0 128 128
cert_group_pairs 0844 00128 128 246 118
cert_group_facts 0844 246
cert_group_header 0845
cert_group_pairs 0845 00000 0 128 128
cert_group_pairs 0845 00128 128 256 128
cert_group_pairs 0845 00256 256 384 128
cert_group_pairs 0845 00384 384 512 128
cert_group_pairs 0845 00512 512 640 128
cert_group_pairs 0845 00640 640 768 128
cert_group_pairs 0845 00768 768 896 128
cert_group_pairs 0845 00896 896 1024 128
cert_group_pairs 0845 01024 1024 1152 128
cert_group_pairs 0845 01152 1152 1280 128
cert_group_pairs 0845 01280 1280 1382 102
theorem group0845_facts : group0845.Facts FacetUniverses.FullSix0.cells :=
  group0845.facts_of_checks _ group0845_header (interval_append _ 0 640 1382 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0845_pairs_00000 group0845_pairs_00128) (interval_append _ 256 384 640 group0845_pairs_00256 (interval_append _ 384 512 640 group0845_pairs_00384 group0845_pairs_00512))) (interval_append _ 640 1024 1382 (interval_append _ 640 768 1024 group0845_pairs_00640 (interval_append _ 768 896 1024 group0845_pairs_00768 group0845_pairs_00896)) (interval_append _ 1024 1152 1382 group0845_pairs_01024 (interval_append _ 1152 1280 1382 group0845_pairs_01152 group0845_pairs_01280))))
cert_group_header 0846
cert_group_pairs 0846 00000 0 128 128
cert_group_pairs 0846 00128 128 256 128
cert_group_pairs 0846 00256 256 384 128
cert_group_pairs 0846 00384 384 512 128
cert_group_pairs 0846 00512 512 640 128
cert_group_pairs 0846 00640 640 768 128
cert_group_pairs 0846 00768 768 896 128
cert_group_pairs 0846 00896 896 1024 128
cert_group_pairs 0846 01024 1024 1152 128
cert_group_pairs 0846 01152 1152 1280 128
cert_group_pairs 0846 01280 1280 1328 48
theorem group0846_facts : group0846.Facts FacetUniverses.FullSix0.cells :=
  group0846.facts_of_checks _ group0846_header (interval_append _ 0 640 1328 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0846_pairs_00000 group0846_pairs_00128) (interval_append _ 256 384 640 group0846_pairs_00256 (interval_append _ 384 512 640 group0846_pairs_00384 group0846_pairs_00512))) (interval_append _ 640 1024 1328 (interval_append _ 640 768 1024 group0846_pairs_00640 (interval_append _ 768 896 1024 group0846_pairs_00768 group0846_pairs_00896)) (interval_append _ 1024 1152 1328 group0846_pairs_01024 (interval_append _ 1152 1280 1328 group0846_pairs_01152 group0846_pairs_01280))))
end Papers.RationalityTen.SharedFrameCatalogue
