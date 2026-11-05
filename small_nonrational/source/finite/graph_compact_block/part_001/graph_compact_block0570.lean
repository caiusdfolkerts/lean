module
prelude
import GraphInputsRow29Part00136Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0570
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 23383288848384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 23383485988864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record001_result⟩)
 (.leaf ⟨(29, 23383682072640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 23386902765632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 23412537819904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record004_result⟩)
 (.leaf ⟨(29, 23418445529344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 23418713997312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 23419116601344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record007_result⟩)
 (.leaf ⟨(29, 23420525904128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 23421263036416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 23424820855040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record010_result⟩)
 (.leaf ⟨(29, 23469987266816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 23474420645888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 23474957451264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record013_result⟩)
 (.leaf ⟨(29, 23478581395456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 23479118200832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 23487167135744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record016_result⟩)
 (.leaf ⟨(29, 23487836061696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 23493540380672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 23495761199104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_result⟩)
 (.leaf ⟨(29, 23496289681408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(29, 23538704646400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 23543005904896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record022_result⟩)
 (.leaf ⟨(29, 23543542710272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22457 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 22457 22481 :=
  block_of_table results 22457 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0570
