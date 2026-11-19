module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups086Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0980
cert_group_pairs 0980 00000 0 128 128
cert_group_pairs 0980 00128 128 256 128
cert_group_facts 0980 256
cert_group_header 0981
cert_group_pairs 0981 00000 0 128 128
cert_group_pairs 0981 00128 128 256 128
cert_group_pairs 0981 00256 256 384 128
cert_group_pairs 0981 00384 384 512 128
cert_group_pairs 0981 00512 512 640 128
cert_group_pairs 0981 00640 640 768 128
cert_group_pairs 0981 00768 768 896 128
cert_group_pairs 0981 00896 896 1024 128
cert_group_pairs 0981 01024 1024 1152 128
cert_group_pairs 0981 01152 1152 1164 12
cert_group_facts_3 0981 1164
cert_group_header 0982
cert_group_pairs 0982 00000 0 128 128
cert_group_pairs 0982 00128 128 256 128
cert_group_pairs 0982 00256 256 384 128
cert_group_pairs 0982 00384 384 512 128
cert_group_pairs 0982 00512 512 640 128
cert_group_pairs 0982 00640 640 768 128
cert_group_pairs 0982 00768 768 896 128
cert_group_pairs 0982 00896 896 1024 128
cert_group_pairs 0982 01024 1024 1152 128
cert_group_pairs 0982 01152 1152 1280 128
cert_group_pairs 0982 01280 1280 1331 51
theorem group0982_facts : group0982.Facts FacetUniverses.FullSix0.cells :=
  group0982.facts_of_checks _ group0982_header (interval_append _ 0 640 1331 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0982_pairs_00000 group0982_pairs_00128) (interval_append _ 256 384 640 group0982_pairs_00256 (interval_append _ 384 512 640 group0982_pairs_00384 group0982_pairs_00512))) (interval_append _ 640 1024 1331 (interval_append _ 640 768 1024 group0982_pairs_00640 (interval_append _ 768 896 1024 group0982_pairs_00768 group0982_pairs_00896)) (interval_append _ 1024 1152 1331 group0982_pairs_01024 (interval_append _ 1152 1280 1331 group0982_pairs_01152 group0982_pairs_01280))))
end Papers.RationalityTen.SharedFrameCatalogue
