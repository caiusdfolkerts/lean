module
prelude
import GraphInputsRow23Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0100
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 28797288087552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 28830123229184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record001_result⟩)
 (.leaf ⟨(23, 28830131552256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(23, 28830523752448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record003_result⟩)
 (.leaf ⟨(23, 28830527913984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record004_result⟩))
 (.branch 6
 (.leaf ⟨(23, 28830639357952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record005_result⟩)
 (.leaf ⟨(23, 28838968950784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(23, 28845018202240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record007_result⟩)
 (.branch 9
 (.leaf ⟨(23, 28845201981440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record008_result⟩)
 (.leaf ⟨(23, 28866766704672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(23, 28868824563840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record010_result⟩)
 (.leaf ⟨(23, 28868958765184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record011_result⟩))
 (.branch 13
 (.leaf ⟨(23, 28868964519936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record012_result⟩)
 (.leaf ⟨(23, 28900165976064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(23, 28900170137600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record014_result⟩)
 (.branch 16
 (.leaf ⟨(23, 28901977915520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record015_result⟩)
 (.leaf ⟨(23, 28902114230272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(23, 28902246350848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record017_result⟩)
 (.leaf ⟨(23, 28902250512384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record018_result⟩))
 (.branch 20
 (.leaf ⟨(23, 28909459488896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record019_result⟩)
 (.leaf ⟨(23, 28934458605568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 28967425835136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record021_result⟩)
 (.leaf ⟨(23, 28967562149888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 28967694270464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record023_result⟩)
 (.leaf ⟨(23, 28967698432000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(23, 28967809875968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record025_result⟩)
 (.leaf ⟨(23, 28971702059136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record026_result⟩))
 (.branch 28
 (.leaf ⟨(23, 28973867221120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record027_result⟩)
 (.leaf ⟨(23, 28974051000320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7338 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 7338 7367 :=
  block_of_table results 7338 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0100
