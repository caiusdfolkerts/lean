module
prelude
import GraphInputsRow29Part00232Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0666
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 30942364180480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record000_result⟩)
 (.leaf ⟨(29, 30942421852416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30942824505408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 30943495069952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record003_result⟩)
 (.leaf ⟨(29, 30943897722944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 30946045206560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record005_result⟩)
 (.leaf ⟨(29, 30969467830272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 30969532777216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 30977854276352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record008_result⟩)
 (.leaf ⟨(29, 30978256929344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 30980404412960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record010_result⟩)
 (.leaf ⟨(29, 31014027034880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 31014765207552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 31063514550304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record013_result⟩)
 (.leaf ⟨(29, 31063910912032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 31065793105952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record015_result⟩)
 (.leaf ⟨(29, 31065842651168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 31072344088832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 31099390558208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record018_result⟩)
 (.leaf ⟨(29, 31244345671680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23261 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 23261 23281 :=
  block_of_table results 23261 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0666
