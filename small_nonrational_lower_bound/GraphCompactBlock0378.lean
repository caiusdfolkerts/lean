module
prelude
import GraphInputsRow26Part00062Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0378
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 29292802097280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record000_result⟩)
 (.leaf ⟨(26, 29353284009984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 29357519142912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 29412024434704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record003_result⟩)
 (.leaf ⟨(26, 29412225736720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 29414222104592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 29414238749200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record006_result⟩)
 (.leaf ⟨(26, 29515036395520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 29549426655360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 29549426688000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record009_result⟩)
 (.leaf ⟨(26, 29549428476032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 29549481953288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 29550518077568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_result⟩)
 (.leaf ⟨(26, 29550518110208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 29550522139656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 29550538915841), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record015_result⟩)
 (.leaf ⟨(26, 29583753742464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 29583753775104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 29583873280008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record018_result⟩)
 (.leaf ⟨(26, 29583873410056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 29583890186241), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 29687974281344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record021_result⟩)
 (.leaf ⟨(26, 29688047624320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17091 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 17091 17114 :=
  block_of_table results 17091 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0378
