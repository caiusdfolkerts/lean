module
prelude
import GraphInputsRow30Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0772
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 28453495635968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record000_result⟩)
 (.leaf ⟨(30, 28488811675648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 28493484392448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 28531543244800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record003_result⟩)
 (.leaf ⟨(30, 28592851394688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 28627244711936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record005_result⟩)
 (.leaf ⟨(30, 28627837141120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 28631537582080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 28640119128192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record008_result⟩)
 (.leaf ⟨(30, 28640123322368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 28640319389824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record010_result⟩)
 (.leaf ⟨(30, 28660606705920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 28660610900096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 28700114452736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record013_result⟩)
 (.leaf ⟨(30, 28708704387200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 28717294321664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record015_result⟩)
 (.leaf ⟨(30, 28717430603776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 28743199391744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 28781855113216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record018_result⟩)
 (.leaf ⟨(30, 28797288087552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 28830131552256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record020_result⟩)
 (.leaf ⟨(30, 28830523752448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 28830527913984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record022_result⟩)
 (.branch 24
 (.leaf ⟨(30, 28845018202240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record023_result⟩)
 (.leaf ⟨(30, 28845201981440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 28866766704672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record025_result⟩)
 (.leaf ⟨(30, 28868824563840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 28868958765184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 28868964519936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record028_result⟩)
 (.leaf ⟨(30, 28899897540736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 28900165976064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record030_result⟩)
 (.leaf ⟨(30, 28900170137600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 28901977915520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 28902114230272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record033_result⟩)
 (.leaf ⟨(30, 28902246350848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(30, 28902250512384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record035_result⟩)
 (.leaf ⟨(30, 28909459488896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record036_result⟩))
 (.branch 38
 (.leaf ⟨(30, 28934458605568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 28967694270464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record038_result⟩)
 (.leaf ⟨(30, 28967698432000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00044.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25013 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 25013 25053 :=
  block_of_table results 25013 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0772
