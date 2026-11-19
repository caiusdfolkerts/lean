module
prelude
import GraphInputsRow25Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0308
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 27756897239040), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 27802602635264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record001_result⟩)
 (.leaf ⟨(25, 27941320785920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(25, 28072061702400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record003_result⟩)
 (.leaf ⟨(25, 28076495339521), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record004_result⟩))
 (.branch 6
 (.leaf ⟨(25, 28082253594624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record005_result⟩)
 (.leaf ⟨(25, 28300344819712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(25, 28308666318848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record007_result⟩)
 (.leaf ⟨(25, 28315126087808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record008_result⟩))
 (.branch 10
 (.leaf ⟨(25, 28453495635968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record009_result⟩)
 (.leaf ⟨(25, 28488811675648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(25, 28493484392448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record011_result⟩)
 (.leaf ⟨(25, 28531543244800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record012_result⟩))
 (.branch 14
 (.leaf ⟨(25, 28592851394688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record013_result⟩)
 (.leaf ⟨(25, 28627244711936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(25, 28627837141120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record015_result⟩)
 (.leaf ⟨(25, 28631537582080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record016_result⟩))
 (.branch 18
 (.leaf ⟨(25, 28640119128192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record017_result⟩)
 (.leaf ⟨(25, 28640123322368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(25, 28640319389824), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record019_result⟩)
 (.leaf ⟨(25, 28660606705920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record020_result⟩))
 (.branch 22
 (.leaf ⟨(25, 28660610900096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record021_result⟩)
 (.leaf ⟨(25, 28700114452736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(25, 28708704387200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record023_result⟩)
 (.leaf ⟨(25, 28717294321664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record024_result⟩))
 (.branch 26
 (.leaf ⟨(25, 28717430603776), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record025_result⟩)
 (.leaf ⟨(25, 28743199391744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(25, 28781855113216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record027_result⟩)
 (.leaf ⟨(25, 28797288087552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record028_result⟩))
 (.branch 30
 (.leaf ⟨(25, 28830131552256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record029_result⟩)
 (.leaf ⟨(25, 28830523752448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record030_result⟩))))))
 (.branch 46
 (.branch 38
 (.branch 34
 (.branch 32
 (.leaf ⟨(25, 28830527913984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 28845018202240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record032_result⟩)
 (.leaf ⟨(25, 28845201981440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(25, 28866766704672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record034_result⟩)
 (.leaf ⟨(25, 28868824563840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record035_result⟩))
 (.branch 37
 (.leaf ⟨(25, 28868958765184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record036_result⟩)
 (.leaf ⟨(25, 28868964519936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record037_result⟩))))
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(25, 28899897540736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record038_result⟩)
 (.leaf ⟨(25, 28900165976064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record039_result⟩))
 (.branch 41
 (.leaf ⟨(25, 28900170137600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record040_result⟩)
 (.leaf ⟨(25, 28901977915520), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(25, 28902114230272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record042_result⟩)
 (.leaf ⟨(25, 28902246350848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record043_result⟩))
 (.branch 45
 (.leaf ⟨(25, 28902250512384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record044_result⟩)
 (.leaf ⟨(25, 28909459488896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record045_result⟩)))))
 (.branch 54
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 28934458605568), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record046_result⟩)
 (.leaf ⟨(25, 28967694270464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 28967698432000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record048_result⟩)
 (.leaf ⟨(25, 28973867221120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(25, 28974051000320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record050_result⟩)
 (.leaf ⟨(25, 28974137737216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record051_result⟩))
 (.branch 53
 (.leaf ⟨(25, 29038475509760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record052_result⟩)
 (.leaf ⟨(25, 29070572158976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record053_result⟩))))
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf ⟨(25, 29140459749376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record054_result⟩)
 (.leaf ⟨(25, 29140694601728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record055_result⟩))
 (.branch 57
 (.leaf ⟨(25, 29141085208704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record056_result⟩)
 (.leaf ⟨(25, 29144306421888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record057_result⟩)))
 (.branch 60
 (.branch 59
 (.leaf ⟨(25, 29146935726080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record058_result⟩)
 (.leaf ⟨(25, 29147027013632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record059_result⟩))
 (.branch 61
 (.leaf ⟨(25, 29147293302912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record060_result⟩)
 (.leaf ⟨(25, 29147295416320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00018.record061_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13580 + i))) 0 62 :=
  interval_of_check _ 0 62 (by decide +kernel)

public theorem complete : Block 13580 13642 :=
  block_of_table results 13580 62 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0308
