module
prelude
import GraphInputsRow29Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0454
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 4438458728480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record000_result⟩)
 (.leaf ⟨(29, 4451073097760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 4451276521536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 4472479777024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record003_result⟩)
 (.leaf ⟨(29, 4472751357984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 4476640526592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 4477044228128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record006_result⟩)
 (.leaf ⟨(29, 4485226266880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 4485233606688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 4485364629760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record009_result⟩)
 (.leaf ⟨(29, 4485365727264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(29, 4485629968416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 4521136848896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record012_result⟩)
 (.leaf ⟨(29, 4553943646464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(29, 4587588255808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 4658498142464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record015_result⟩)
 (.leaf ⟨(29, 4729442672768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(29, 4787347161344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 4953754140704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record018_result⟩)
 (.leaf ⟨(29, 4958047010848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(29, 4966632751136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record020_result⟩)
 (.branch 22
 (.leaf ⟨(29, 5025405935872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record021_result⟩)
 (.leaf ⟨(29, 5025674395680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20788 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 20788 20811 :=
  block_of_table results 20788 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0454
