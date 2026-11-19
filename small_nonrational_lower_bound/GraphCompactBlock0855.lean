module
prelude
import GraphInputsRow31Part00067Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0855
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 13281453473792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 13289434652704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record001_result⟩)
 (.leaf ⟨(31, 13308761473792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 13316818796800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 13317355667456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record004_result⟩)
 (.leaf ⟨(31, 13317363990528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 13323793859104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 13338826776832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record007_result⟩)
 (.leaf ⟨(31, 13341444604160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 13341452992512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record009_result⟩)
 (.leaf ⟨(31, 13341856636928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 13341914308864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record011_result⟩)
 (.leaf ⟨(31, 13342987526400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26001 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 26001 26014 :=
  block_of_table results 26001 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0855
