module
prelude
import GraphInputsRow29Part00218Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0652
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 29693928018048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 29725620207872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record001_result⟩)
 (.leaf ⟨(29, 29725628596224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 29726140010624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record003_result⟩)
 (.leaf ⟨(29, 29727213486720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 29731242180608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record005_result⟩)
 (.leaf ⟨(29, 29757832462592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00218.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23121 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23121 23128 :=
  block_of_table results 23121 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0652
