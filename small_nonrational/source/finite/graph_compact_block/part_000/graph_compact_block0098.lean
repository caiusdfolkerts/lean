module
prelude
import GraphInputsRow23Part00020Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0098
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 27267812065280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record000_result⟩)
 (.leaf ⟨(23, 27268080467968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 27354179076096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record002_result⟩)
 (.branch 4
 (.leaf ⟨(23, 27386877870336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record003_result⟩)
 (.leaf ⟨(23, 27387414740992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(23, 27493740322944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record005_result⟩)
 (.leaf ⟨(23, 27561367707776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record006_result⟩))
 (.branch 8
 (.leaf ⟨(23, 27566980219136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record007_result⟩)
 (.branch 9
 (.leaf ⟨(23, 27602290999296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record008_result⟩)
 (.leaf ⟨(23, 27602414796800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(23, 27671000055808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record010_result⟩)
 (.leaf ⟨(23, 27685428412672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record011_result⟩))
 (.branch 13
 (.leaf ⟨(23, 27747774693376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 27748443619328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record013_result⟩)
 (.leaf ⟨(23, 27756368756736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(23, 27756897239040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 27802602635264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record016_result⟩)
 (.leaf ⟨(23, 27941320785920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(23, 27945341091840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 27947421466624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record019_result⟩)
 (.leaf ⟨(23, 28076495339521), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7272 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 7272 7293 :=
  block_of_table results 7272 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0098
