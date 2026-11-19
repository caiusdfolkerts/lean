module
prelude
import GraphInputsRow29Part00065Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0499
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 12000541605888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record000_result⟩)
 (.leaf ⟨(29, 12000694403072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12000698564608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12000810008576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record003_result⟩)
 (.leaf ⟨(29, 12004433756416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 12005238899200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 12008747466880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record006_result⟩)
 (.leaf ⟨(29, 12009131507712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 12013023690880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 12017318641792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record009_result⟩)
 (.leaf ⟨(29, 12021613625344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00065.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21416 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 21416 21427 :=
  block_of_table results 21416 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0499
