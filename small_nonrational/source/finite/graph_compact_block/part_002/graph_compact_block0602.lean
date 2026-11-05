module
prelude
import GraphInputsRow29Part00168Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0602
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 25574418432256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25575054393344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record001_result⟩)
 (.leaf ⟨(29, 25576564867328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 25582106574848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record003_result⟩)
 (.leaf ⟨(29, 25582236614656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 25582302674944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record005_result⟩)
 (.leaf ⟨(29, 25583375892480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 25589449769024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 25610890133760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record008_result⟩)
 (.leaf ⟨(29, 25611561075200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 25623775035456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record010_result⟩)
 (.leaf ⟨(29, 25642097770496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 25658134765632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record012_result⟩)
 (.leaf ⟨(29, 25659277574144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22747 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 22747 22761 :=
  block_of_table results 22747 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0602
