module
prelude
import GraphInputsRow29Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0437
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 1042135679232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 1174210183424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record001_result⟩)
 (.leaf ⟨(29, 1174283583520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 1209716998400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record003_result⟩)
 (.leaf ⟨(29, 1214009868544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 1222331367680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record005_result⟩)
 (.leaf ⟨(29, 1255818756160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 1323413110848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record007_result⟩)
 (.leaf ⟨(29, 1347147596032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 1364327464960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record009_result⟩)
 (.leaf ⟨(29, 1422317944832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 1422452080896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record011_result⟩)
 (.leaf ⟨(29, 1469696712768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 1484318114048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record013_result⟩)
 (.leaf ⟨(29, 1507739107328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20508 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 20508 20523 :=
  block_of_table results 20508 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0437
