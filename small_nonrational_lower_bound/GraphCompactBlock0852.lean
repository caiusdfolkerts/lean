module
prelude
import GraphInputsRow31Part00064Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0852
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 13013751070720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record000_result⟩)
 (.leaf ⟨(31, 13056719487232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 13125441093632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 13134035156992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record003_result⟩)
 (.leaf ⟨(31, 13134563639296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 13142620897280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record005_result⟩)
 (.leaf ⟨(31, 13151189991424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 13234207785216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 13234216173568), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record008_result⟩)
 (.leaf ⟨(31, 13234674368768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25979 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25979 25989 :=
  block_of_table results 25979 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0852
