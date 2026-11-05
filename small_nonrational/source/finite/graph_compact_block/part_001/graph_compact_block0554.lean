module
prelude
import GraphInputsRow29Part00120Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0554
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 20690539413504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 20694295412992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record001_result⟩)
 (.leaf ⟨(29, 20694572204032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 20694638264320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 20694832283648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record004_result⟩)
 (.leaf ⟨(29, 20702885347456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 20710366920832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 20711611564032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record007_result⟩)
 (.leaf ⟨(29, 20723238207744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 20723506675712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 20723514998784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record010_result⟩)
 (.leaf ⟨(29, 20723775078400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22235 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 22235 22247 :=
  block_of_table results 22235 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0554
