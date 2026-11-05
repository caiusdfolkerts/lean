module
prelude
import GraphInputsRow31Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0834
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 8943540650240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 8952126390528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record001_result⟩)
 (.leaf ⟨(31, 8952399020160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 8979042336768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 8987628077056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record004_result⟩)
 (.leaf ⟨(31, 8988036972544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 9015942717696), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 9125465456768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record007_result⟩)
 (.leaf ⟨(31, 9424571793664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 9424580182016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record009_result⟩)
 (.leaf ⟨(31, 9475515744256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 9493297561600), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record011_result⟩)
 (.leaf ⟨(31, 9494601990144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25858 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 25858 25871 :=
  block_of_table results 25858 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0834
