module
prelude
public import SharedFrameGroups048Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group0624_header : group0624.headerCheck = true := by
  decide +kernel
theorem group0624_pairs_00000 :
    Interval (group0624.pairTest FacetUniverses.FullSix0.cells) 0 105 :=
  interval_of_check _ 0 105 (by decide +kernel)
theorem group0624_facts : group0624.Facts FacetUniverses.FullSix0.cells :=
  group0624.facts_of_checks _ group0624_header group0624_pairs_00000
#print axioms group0624_facts
theorem group0625_header : group0625.headerCheck = true := by
  decide +kernel
theorem group0625_pairs_00000 :
    Interval (group0625.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0625_pairs_00128 :
    Interval (group0625.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0625_pairs_00256 :
    Interval (group0625.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group0625_pairs_00384 :
    Interval (group0625.pairTest FacetUniverses.FullSix0.cells) 384 424 :=
  interval_of_check _ 384 40 (by decide +kernel)
theorem group0625_facts : group0625.Facts FacetUniverses.FullSix0.cells :=
  group0625.facts_of_checks _ group0625_header (interval_append _ 0 256 424 (interval_append _ 0 128 256 group0625_pairs_00000 group0625_pairs_00128) (interval_append _ 256 384 424 group0625_pairs_00256 group0625_pairs_00384))
#print axioms group0625_facts
theorem group0626_header : group0626.headerCheck = true := by
  decide +kernel
theorem group0626_pairs_00000 :
    Interval (group0626.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0626_pairs_00128 :
    Interval (group0626.pairTest FacetUniverses.FullSix0.cells) 128 162 :=
  interval_of_check _ 128 34 (by decide +kernel)
theorem group0626_facts : group0626.Facts FacetUniverses.FullSix0.cells :=
  group0626.facts_of_checks _ group0626_header (interval_append _ 0 128 162 group0626_pairs_00000 group0626_pairs_00128)
#print axioms group0626_facts
theorem group0627_header : group0627.headerCheck = true := by
  decide +kernel
theorem group0627_pairs_00000 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0627_pairs_00128 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0627_pairs_00256 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group0627_pairs_00384 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group0627_pairs_00512 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group0627_pairs_00640 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group0627_pairs_00768 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group0627_pairs_00896 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group0627_pairs_01024 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group0627_pairs_01152 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group0627_pairs_01280 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group0627_pairs_01408 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 1408 1536 :=
  interval_of_check _ 1408 128 (by decide +kernel)
theorem group0627_pairs_01536 :
    Interval (group0627.pairTest FacetUniverses.FullSix0.cells) 1536 1550 :=
  interval_of_check _ 1536 14 (by decide +kernel)
theorem group0627_facts : group0627.Facts FacetUniverses.FullSix0.cells :=
  group0627.facts_of_checks _ group0627_header (interval_append _ 0 768 1550 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0627_pairs_00000 (interval_append _ 128 256 384 group0627_pairs_00128 group0627_pairs_00256)) (interval_append _ 384 512 768 group0627_pairs_00384 (interval_append _ 512 640 768 group0627_pairs_00512 group0627_pairs_00640))) (interval_append _ 768 1152 1550 (interval_append _ 768 896 1152 group0627_pairs_00768 (interval_append _ 896 1024 1152 group0627_pairs_00896 group0627_pairs_01024)) (interval_append _ 1152 1408 1550 (interval_append _ 1152 1280 1408 group0627_pairs_01152 group0627_pairs_01280) (interval_append _ 1408 1536 1550 group0627_pairs_01408 group0627_pairs_01536))))
#print axioms group0627_facts
theorem group0628_header : group0628.headerCheck = true := by
  decide +kernel
theorem group0628_pairs_00000 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0628_pairs_00128 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0628_pairs_00256 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group0628_pairs_00384 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group0628_pairs_00512 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group0628_pairs_00640 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group0628_pairs_00768 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group0628_pairs_00896 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group0628_pairs_01024 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group0628_pairs_01152 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group0628_pairs_01280 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group0628_pairs_01408 :
    Interval (group0628.pairTest FacetUniverses.FullSix0.cells) 1408 1504 :=
  interval_of_check _ 1408 96 (by decide +kernel)
theorem group0628_facts : group0628.Facts FacetUniverses.FullSix0.cells :=
  group0628.facts_of_checks _ group0628_header (interval_append _ 0 768 1504 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0628_pairs_00000 (interval_append _ 128 256 384 group0628_pairs_00128 group0628_pairs_00256)) (interval_append _ 384 512 768 group0628_pairs_00384 (interval_append _ 512 640 768 group0628_pairs_00512 group0628_pairs_00640))) (interval_append _ 768 1152 1504 (interval_append _ 768 896 1152 group0628_pairs_00768 (interval_append _ 896 1024 1152 group0628_pairs_00896 group0628_pairs_01024)) (interval_append _ 1152 1280 1504 group0628_pairs_01152 (interval_append _ 1280 1408 1504 group0628_pairs_01280 group0628_pairs_01408))))
#print axioms group0628_facts
theorem group0629_header : group0629.headerCheck = true := by
  decide +kernel
theorem group0629_pairs_00000 :
    Interval (group0629.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0629_pairs_00128 :
    Interval (group0629.pairTest FacetUniverses.FullSix0.cells) 128 153 :=
  interval_of_check _ 128 25 (by decide +kernel)
theorem group0629_facts : group0629.Facts FacetUniverses.FullSix0.cells :=
  group0629.facts_of_checks _ group0629_header (interval_append _ 0 128 153 group0629_pairs_00000 group0629_pairs_00128)
#print axioms group0629_facts
end Papers.RationalityTen.SharedFrameCatalogue
