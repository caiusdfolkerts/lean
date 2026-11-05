module
prelude
import GraphInputsRow24Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0127
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 7003615265408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record000_result⟩)
 (.leaf ⟨(24, 7003883700736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 7033120129024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record002_result⟩)
 (.leaf ⟨(24, 7033186189312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 7046055362816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record004_result⟩)
 (.leaf ⟨(24, 7046575425664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 7055167471616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record006_result⟩)
 (.leaf ⟨(24, 7061138049152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 7072076791808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_result⟩)
 (.leaf ⟨(24, 7072605274112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 7073880375552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record010_result⟩)
 (.leaf ⟨(24, 7074016722944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 7074025046016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_result⟩)
 (.leaf ⟨(24, 7074148843520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 7074157166592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record014_result⟩)
 (.leaf ⟨(24, 7074617507840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 7089460101120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record016_result⟩)
 (.leaf ⟨(24, 7150359380224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 7150627815552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record018_result⟩)
 (.leaf ⟨(24, 7165425319952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 7186046615568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record020_result⟩)
 (.leaf ⟨(24, 7187371950336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 7190339485712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record022_result⟩)
 (.leaf ⟨(24, 7191532765184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 7207773016128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record024_result⟩)
 (.leaf ⟨(24, 7218258870288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 7276492488705), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record026_result⟩)
 (.leaf ⟨(24, 7286572024064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 7286976249872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record028_result⟩)
 (.leaf ⟨(24, 7302732152832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 7303336042560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 7304409780288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record031_result⟩)
 (.leaf ⟨(24, 7340916998145), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record032_result⟩)))))))
 (.branch 49
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 7375276744704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record033_result⟩)
 (.leaf ⟨(24, 7424014647312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 7424146767888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record035_result⟩)
 (.leaf ⟨(24, 7426557444112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(24, 7448724275200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record037_result⟩)
 (.leaf ⟨(24, 7449118523520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record038_result⟩))
 (.branch 40
 (.leaf ⟨(24, 7518138925568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record039_result⟩)
 (.leaf ⟨(24, 7525076664320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record040_result⟩))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf ⟨(24, 7551374590464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record041_result⟩)
 (.leaf ⟨(24, 7560310587648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record042_result⟩))
 (.branch 44
 (.leaf ⟨(24, 7560310652928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record043_result⟩)
 (.leaf ⟨(24, 7560372486400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(24, 7560376647936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record045_result⟩)
 (.leaf ⟨(24, 7560376713216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record046_result⟩))
 (.branch 48
 (.leaf ⟨(24, 7560430094592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record047_result⟩)
 (.leaf ⟨(24, 7560773074944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record048_result⟩)))))
 (.branch 57
 (.branch 53
 (.branch 51
 (.branch 50
 (.leaf ⟨(24, 7560776196096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record049_result⟩)
 (.leaf ⟨(24, 7560830650496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record050_result⟩))
 (.branch 52
 (.leaf ⟨(24, 7562778968064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record051_result⟩)
 (.leaf ⟨(24, 7563047337985), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record052_result⟩)))
 (.branch 55
 (.branch 54
 (.leaf ⟨(24, 7563181572096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record053_result⟩)
 (.leaf ⟨(24, 7563550656768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record054_result⟩))
 (.branch 56
 (.leaf ⟨(24, 7563724259584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record055_result⟩)
 (.leaf ⟨(24, 7563731607552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record056_result⟩))))
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(24, 7563992662272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record057_result⟩)
 (.leaf ⟨(24, 7563992727552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_result⟩))
 (.branch 60
 (.leaf ⟨(24, 7563995848704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record059_result⟩)
 (.leaf ⟨(24, 7565127712769), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(24, 7569422696448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record061_result⟩)
 (.leaf ⟨(24, 7576433461376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record062_result⟩))
 (.branch 64
 (.leaf ⟨(24, 7576495327488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record063_result⟩)
 (.branch 65
 (.leaf ⟨(24, 7576499521664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record064_result⟩)
 (.leaf ⟨(24, 7576877580288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record065_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8317 + i))) 0 66 :=
  interval_of_check _ 0 66 (by decide +kernel)

public theorem complete : Block 8317 8383 :=
  block_of_table results 8317 66 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0127
