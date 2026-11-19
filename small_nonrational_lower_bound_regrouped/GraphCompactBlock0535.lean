module
prelude
import GraphInputsRow29Part00101Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0535
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 17235980582912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 17236509065216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record001_result⟩)
 (.leaf ⟨(29, 17248609698048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 17274358661120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 17292083593216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record004_result⟩)
 (.leaf ⟨(29, 17309255073792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 17317602004992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 17326183874560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record007_result⟩)
 (.leaf ⟨(29, 17326451720720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 17457033052160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 17480516895236), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record010_result⟩)
 (.leaf ⟨(29, 17493678620672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21946 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 21946 21958 :=
  block_of_table results 21946 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0535
