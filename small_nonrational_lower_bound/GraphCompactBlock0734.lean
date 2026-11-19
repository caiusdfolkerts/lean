module
prelude
import GraphInputsRow30Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0734
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 4451270181120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record000_result⟩)
 (.leaf ⟨(30, 4485233606688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 4485364629760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 4485365727264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record003_result⟩)
 (.leaf ⟨(30, 4485629968416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 4521136848896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 4553943646464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record006_result⟩)
 (.leaf ⟨(30, 4658498142464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 4691384647936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 4691385745440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record009_result⟩)
 (.leaf ⟨(30, 4691788349472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 4953754140704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record011_result⟩)
 (.leaf ⟨(30, 4958047010848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 4966632751136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 5025405935872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record014_result⟩)
 (.leaf ⟨(30, 5025674395680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(30, 5089830445312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 5102983757856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record017_result⟩)
 (.leaf ⟨(30, 5104109453312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(30, 5123505979392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 5138460737792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record020_result⟩)
 (.leaf ⟨(30, 5140677459968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23832 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 23832 23854 :=
  block_of_table results 23832 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0734
