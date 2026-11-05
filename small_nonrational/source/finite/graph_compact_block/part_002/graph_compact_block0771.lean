module
prelude
import GraphInputsRow30Part00043Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0771
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 27130645708800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record000_result⟩)
 (.leaf ⟨(30, 27130909949952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 27217505554464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 27224254726272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record003_result⟩)
 (.leaf ⟨(30, 27251301187584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 27257542311936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 27258582499328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record006_result⟩)
 (.leaf ⟨(30, 27267812065280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 27268080467968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 27354179076096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record009_result⟩)
 (.leaf ⟨(30, 27387414740992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(30, 27602290999296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 27748443619328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record012_result⟩)
 (.leaf ⟨(30, 27756368756736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(30, 27756897239040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 27802602635264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record015_result⟩)
 (.leaf ⟨(30, 27941320785920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(30, 28072061702400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 28076495339521), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record018_result⟩)
 (.leaf ⟨(30, 28082253594624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(30, 28300344819712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record020_result⟩)
 (.branch 22
 (.leaf ⟨(30, 28308666318848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record021_result⟩)
 (.leaf ⟨(30, 28315126087808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00043.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24990 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 24990 25013 :=
  block_of_table results 24990 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0771
