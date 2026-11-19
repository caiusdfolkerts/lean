module
prelude
import GraphInputsRow24Part00095Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0211
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25160489115712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record000_result⟩)
 (.leaf ⟨(24, 25161596142144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25177115598912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record002_result⟩)
 (.leaf ⟨(24, 25177149685760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 25177151766528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record004_result⟩)
 (.leaf ⟨(24, 25177184796672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 25178172170304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 25178239287296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record007_result⟩)
 (.leaf ⟨(24, 25178241368064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10829 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 10829 10838 :=
  block_of_table results 10829 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0211
