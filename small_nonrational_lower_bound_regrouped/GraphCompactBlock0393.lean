module
prelude
import GraphInputsRow26Part00077Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0393
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 32788335558656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 32788351033344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record001_result⟩)
 (.leaf ⟨(26, 32788854219008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 32789458059776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record003_result⟩)
 (.leaf ⟨(26, 32804960342048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 32804977516544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record005_result⟩)
 (.leaf ⟨(26, 32805011587072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 32806034087936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record007_result⟩)
 (.leaf ⟨(26, 32806101188608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 32813567213824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record009_result⟩)
 (.leaf ⟨(26, 32813835681792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 32813844004864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record011_result⟩)
 (.leaf ⟨(26, 32814355712000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 32822140209408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record013_result⟩)
 (.leaf ⟨(26, 32822677080064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00077.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17484 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 17484 17499 :=
  block_of_table results 17484 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0393
