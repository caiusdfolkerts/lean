module
prelude
import GraphInputsRow29Part00144Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0578
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24303879913472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record000_result⟩)
 (.leaf ⟨(29, 24305828167680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24312333468288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 24335847268416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record003_result⟩)
 (.leaf ⟨(29, 24336903839808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 24345352093952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 24345361522688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record006_result⟩)
 (.leaf ⟨(29, 24345754746944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 24372473495552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 24380786671616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record009_result⟩)
 (.leaf ⟨(29, 24380794994688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22559 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22559 22570 :=
  block_of_table results 22559 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0578
