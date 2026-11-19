module
prelude
import GraphInputsRow31Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0811
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 5585203396864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record000_result⟩)
 (.leaf ⟨(31, 5607356694784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 5620640055296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 5652739530816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record003_result⟩)
 (.leaf ⟨(31, 5653865168897), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 5687100833793), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record005_result⟩)
 (.leaf ⟨(31, 5791306235904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 5791496028416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 5829075927808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record008_result⟩)
 (.leaf ⟨(31, 5829088509952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 5833373057024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record010_result⟩)
 (.leaf ⟨(31, 5882234601472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 5899414405120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 5935714074880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record013_result⟩)
 (.leaf ⟨(31, 6087319290112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(31, 6087856160768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 6094600601856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record016_result⟩)
 (.leaf ⟨(31, 6100065779968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(31, 6100338409472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record018_result⟩)
 (.branch 20
 (.leaf ⟨(31, 6100602650624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record019_result⟩)
 (.leaf ⟨(31, 6100610973696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00023.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25677 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 25677 25698 :=
  block_of_table results 25677 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0811
