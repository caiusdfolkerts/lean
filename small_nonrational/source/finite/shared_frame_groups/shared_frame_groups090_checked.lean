module
prelude
public import SharedFrameGroups090Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group1000_header : group1000.headerCheck = true := by
  decide +kernel
theorem group1000_pairs_00000 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group1000_pairs_00128 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group1000_pairs_00256 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group1000_pairs_00384 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group1000_pairs_00512 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group1000_pairs_00640 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group1000_pairs_00768 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group1000_pairs_00896 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group1000_pairs_01024 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group1000_pairs_01152 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group1000_pairs_01280 :
    Interval (group1000.pairTest FacetUniverses.FullSix0.cells) 1280 1341 :=
  interval_of_check _ 1280 61 (by decide +kernel)
theorem group1000_facts : group1000.Facts FacetUniverses.FullSix0.cells :=
  group1000.facts_of_checks _ group1000_header (interval_append _ 0 640 1341 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1000_pairs_00000 group1000_pairs_00128) (interval_append _ 256 384 640 group1000_pairs_00256 (interval_append _ 384 512 640 group1000_pairs_00384 group1000_pairs_00512))) (interval_append _ 640 1024 1341 (interval_append _ 640 768 1024 group1000_pairs_00640 (interval_append _ 768 896 1024 group1000_pairs_00768 group1000_pairs_00896)) (interval_append _ 1024 1152 1341 group1000_pairs_01024 (interval_append _ 1152 1280 1341 group1000_pairs_01152 group1000_pairs_01280))))
#print axioms group1000_facts
end Papers.RationalityTen.SharedFrameCatalogue
