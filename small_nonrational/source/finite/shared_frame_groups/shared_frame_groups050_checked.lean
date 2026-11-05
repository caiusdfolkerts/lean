module
prelude
public import SharedFrameGroups050Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem group0634_header : group0634.headerCheck = true := by
  decide +kernel
theorem group0634_pairs_00000 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0634_pairs_00128 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0634_pairs_00256 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group0634_pairs_00384 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 384 512 :=
  interval_of_check _ 384 128 (by decide +kernel)
theorem group0634_pairs_00512 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 512 640 :=
  interval_of_check _ 512 128 (by decide +kernel)
theorem group0634_pairs_00640 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 640 768 :=
  interval_of_check _ 640 128 (by decide +kernel)
theorem group0634_pairs_00768 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 768 896 :=
  interval_of_check _ 768 128 (by decide +kernel)
theorem group0634_pairs_00896 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 896 1024 :=
  interval_of_check _ 896 128 (by decide +kernel)
theorem group0634_pairs_01024 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1024 1152 :=
  interval_of_check _ 1024 128 (by decide +kernel)
theorem group0634_pairs_01152 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1152 1280 :=
  interval_of_check _ 1152 128 (by decide +kernel)
theorem group0634_pairs_01280 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1280 1408 :=
  interval_of_check _ 1280 128 (by decide +kernel)
theorem group0634_pairs_01408 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1408 1536 :=
  interval_of_check _ 1408 128 (by decide +kernel)
theorem group0634_pairs_01536 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1536 1664 :=
  interval_of_check _ 1536 128 (by decide +kernel)
theorem group0634_pairs_01664 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1664 1792 :=
  interval_of_check _ 1664 128 (by decide +kernel)
theorem group0634_pairs_01792 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1792 1920 :=
  interval_of_check _ 1792 128 (by decide +kernel)
theorem group0634_pairs_01920 :
    Interval (group0634.pairTest FacetUniverses.FullSix0.cells) 1920 2003 :=
  interval_of_check _ 1920 83 (by decide +kernel)
theorem group0634_facts : group0634.Facts FacetUniverses.FullSix0.cells :=
  group0634.facts_of_checks _ group0634_header (interval_append _ 0 1024 2003 (interval_append _ 0 512 1024 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0634_pairs_00000 group0634_pairs_00128) (interval_append _ 256 384 512 group0634_pairs_00256 group0634_pairs_00384)) (interval_append _ 512 768 1024 (interval_append _ 512 640 768 group0634_pairs_00512 group0634_pairs_00640) (interval_append _ 768 896 1024 group0634_pairs_00768 group0634_pairs_00896))) (interval_append _ 1024 1536 2003 (interval_append _ 1024 1280 1536 (interval_append _ 1024 1152 1280 group0634_pairs_01024 group0634_pairs_01152) (interval_append _ 1280 1408 1536 group0634_pairs_01280 group0634_pairs_01408)) (interval_append _ 1536 1792 2003 (interval_append _ 1536 1664 1792 group0634_pairs_01536 group0634_pairs_01664) (interval_append _ 1792 1920 2003 group0634_pairs_01792 group0634_pairs_01920))))
#print axioms group0634_facts
theorem group0635_header : group0635.headerCheck = true := by
  decide +kernel
theorem group0635_pairs_00000 :
    Interval (group0635.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0635_pairs_00128 :
    Interval (group0635.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0635_pairs_00256 :
    Interval (group0635.pairTest FacetUniverses.FullSix0.cells) 256 370 :=
  interval_of_check _ 256 114 (by decide +kernel)
theorem group0635_facts : group0635.Facts FacetUniverses.FullSix0.cells :=
  group0635.facts_of_checks _ group0635_header (interval_append _ 0 128 370 group0635_pairs_00000 (interval_append _ 128 256 370 group0635_pairs_00128 group0635_pairs_00256))
#print axioms group0635_facts
theorem group0636_header : group0636.headerCheck = true := by
  decide +kernel
theorem group0636_pairs_00000 :
    Interval (group0636.pairTest FacetUniverses.FullSix0.cells) 0 122 :=
  interval_of_check _ 0 122 (by decide +kernel)
theorem group0636_facts : group0636.Facts FacetUniverses.FullSix0.cells :=
  group0636.facts_of_checks _ group0636_header group0636_pairs_00000
#print axioms group0636_facts
theorem group0637_header : group0637.headerCheck = true := by
  decide +kernel
theorem group0637_pairs_00000 :
    Interval (group0637.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0637_pairs_00128 :
    Interval (group0637.pairTest FacetUniverses.FullSix0.cells) 128 164 :=
  interval_of_check _ 128 36 (by decide +kernel)
theorem group0637_facts : group0637.Facts FacetUniverses.FullSix0.cells :=
  group0637.facts_of_checks _ group0637_header (interval_append _ 0 128 164 group0637_pairs_00000 group0637_pairs_00128)
#print axioms group0637_facts
theorem group0638_header : group0638.headerCheck = true := by
  decide +kernel
theorem group0638_pairs_00000 :
    Interval (group0638.pairTest FacetUniverses.FullSix0.cells) 0 104 :=
  interval_of_check _ 0 104 (by decide +kernel)
theorem group0638_facts : group0638.Facts FacetUniverses.FullSix0.cells :=
  group0638.facts_of_checks _ group0638_header group0638_pairs_00000
#print axioms group0638_facts
theorem group0639_header : group0639.headerCheck = true := by
  decide +kernel
theorem group0639_pairs_00000 :
    Interval (group0639.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0639_pairs_00128 :
    Interval (group0639.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0639_pairs_00256 :
    Interval (group0639.pairTest FacetUniverses.FullSix0.cells) 256 384 :=
  interval_of_check _ 256 128 (by decide +kernel)
theorem group0639_pairs_00384 :
    Interval (group0639.pairTest FacetUniverses.FullSix0.cells) 384 452 :=
  interval_of_check _ 384 68 (by decide +kernel)
theorem group0639_facts : group0639.Facts FacetUniverses.FullSix0.cells :=
  group0639.facts_of_checks _ group0639_header (interval_append _ 0 256 452 (interval_append _ 0 128 256 group0639_pairs_00000 group0639_pairs_00128) (interval_append _ 256 384 452 group0639_pairs_00256 group0639_pairs_00384))
#print axioms group0639_facts
theorem group0640_header : group0640.headerCheck = true := by
  decide +kernel
theorem group0640_pairs_00000 :
    Interval (group0640.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0640_pairs_00128 :
    Interval (group0640.pairTest FacetUniverses.FullSix0.cells) 128 202 :=
  interval_of_check _ 128 74 (by decide +kernel)
theorem group0640_facts : group0640.Facts FacetUniverses.FullSix0.cells :=
  group0640.facts_of_checks _ group0640_header (interval_append _ 0 128 202 group0640_pairs_00000 group0640_pairs_00128)
#print axioms group0640_facts
theorem group0641_header : group0641.headerCheck = true := by
  decide +kernel
theorem group0641_pairs_00000 :
    Interval (group0641.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0641_pairs_00128 :
    Interval (group0641.pairTest FacetUniverses.FullSix0.cells) 128 194 :=
  interval_of_check _ 128 66 (by decide +kernel)
theorem group0641_facts : group0641.Facts FacetUniverses.FullSix0.cells :=
  group0641.facts_of_checks _ group0641_header (interval_append _ 0 128 194 group0641_pairs_00000 group0641_pairs_00128)
#print axioms group0641_facts
theorem group0642_header : group0642.headerCheck = true := by
  decide +kernel
theorem group0642_pairs_00000 :
    Interval (group0642.pairTest FacetUniverses.FullSix0.cells) 0 128 :=
  interval_of_check _ 0 128 (by decide +kernel)
theorem group0642_pairs_00128 :
    Interval (group0642.pairTest FacetUniverses.FullSix0.cells) 128 256 :=
  interval_of_check _ 128 128 (by decide +kernel)
theorem group0642_pairs_00256 :
    Interval (group0642.pairTest FacetUniverses.FullSix0.cells) 256 286 :=
  interval_of_check _ 256 30 (by decide +kernel)
theorem group0642_facts : group0642.Facts FacetUniverses.FullSix0.cells :=
  group0642.facts_of_checks _ group0642_header (interval_append _ 0 128 286 group0642_pairs_00000 (interval_append _ 128 256 286 group0642_pairs_00128 group0642_pairs_00256))
#print axioms group0642_facts
end Papers.RationalityTen.SharedFrameCatalogue
