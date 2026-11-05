module
prelude
import GraphInputsRow31Part00109Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0897
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 25125583847424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record000_result⟩)
 (.leaf ⟨(31, 25126112329728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 25134169587712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record002_result⟩)
 (.leaf ⟨(31, 25142738681856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 25153614446592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record004_result⟩)
 (.leaf ⟨(31, 25177098289668), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 25177167495168), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 25190260015104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record007_result⟩)
 (.leaf ⟨(31, 25199109996544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 25211592245248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record009_result⟩)
 (.leaf ⟨(31, 25327560622336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 25396418510848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record011_result⟩)
 (.leaf ⟨(31, 25405276815360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(31, 25413598314496), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record013_result⟩)
 (.leaf ⟨(31, 25414126796800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record014_result⟩))
 (.branch 16
 (.leaf ⟨(31, 25417759064064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 25465003769856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record016_result⟩)
 (.leaf ⟨(31, 25482183573504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00109.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26407 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 26407 26425 :=
  block_of_table results 26407 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0897
