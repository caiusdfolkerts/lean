module
prelude
import GraphInputsRow31Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0800
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 2418470355200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 2521554812928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record001_result⟩)
 (.leaf ⟨(31, 2530543173760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 2534838124672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record003_result⟩)
 (.leaf ⟨(31, 2569196814464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 2637916291136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record005_result⟩)
 (.leaf ⟨(31, 2933601140992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(31, 2933873770496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 3118284701952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record008_result⟩)
 (.leaf ⟨(31, 3118951563904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 3118953693184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record010_result⟩)
 (.leaf ⟨(31, 3187671040576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 3208751611904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record012_result⟩)
 (.leaf ⟨(31, 3240963866624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25574 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 25574 25588 :=
  block_of_table results 25574 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0800
