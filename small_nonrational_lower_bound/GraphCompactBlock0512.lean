module
prelude
import GraphInputsRow29Part00078Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0512
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 12786403442944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12786411831296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record001_result⟩)
 (.leaf ⟨(29, 12786683875328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 12790976745472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 12791083962624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record004_result⟩)
 (.leaf ⟨(29, 12792293818368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 12795513470976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 12799405461760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record007_result⟩)
 (.leaf ⟨(29, 12799556731008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 12799562485760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record009_result⟩)
 (.leaf ⟨(29, 12799673897088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 12800478937856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record011_result⟩)
 (.leaf ⟨(29, 12800747373184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(29, 12804102816272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 12864240746496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record014_result⟩)
 (.leaf ⟨(29, 12923842363648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(29, 12923854393344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record016_result⟩)
 (.leaf ⟨(29, 12924110798976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record017_result⟩))
 (.branch 19
 (.leaf ⟨(29, 12928147263488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_result⟩)
 (.leaf ⟨(29, 12928405749888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(29, 12928411504640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record020_result⟩)
 (.branch 22
 (.leaf ⟨(29, 12932951835152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record021_result⟩)
 (.leaf ⟨(29, 12936844415104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 12937917891200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record023_result⟩)
 (.leaf ⟨(29, 13125437128960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 13125705596928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record025_result⟩)
 (.leaf ⟨(29, 13125713920000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21554 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 21554 21581 :=
  block_of_table results 21554 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0512
