module
prelude
import GraphInputsRow30Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0731
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 1920387448832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record000_result⟩)
 (.leaf ⟨(30, 1920395771904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 1972073660417), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record002_result⟩)
 (.leaf ⟨(30, 1980663627776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 1980787360000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record004_result⟩)
 (.leaf ⟨(30, 1996492964096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 1996501352448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record006_result⟩)
 (.leaf ⟨(30, 1996893487360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 1999621914624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record008_result⟩)
 (.leaf ⟨(30, 2002940657664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 2003134611712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record010_result⟩)
 (.leaf ⟨(30, 2004013875200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 2004174799104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record012_result⟩)
 (.leaf ⟨(30, 2015157551105), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 2019442065664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 2019452518401), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record015_result⟩)
 (.leaf ⟨(30, 2019777609984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 2019913957376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record017_result⟩)
 (.leaf ⟨(30, 2019922280448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 2020318642176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record019_result⟩)
 (.leaf ⟨(30, 2031817392128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 2032325132544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record021_result⟩)
 (.leaf ⟨(30, 2032337422336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 2036370276608), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record023_result⟩)
 (.leaf ⟨(30, 2036374503424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 2036498171904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record025_result⟩)
 (.leaf ⟨(30, 2040914772736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 2049517289472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record027_result⟩)
 (.leaf ⟨(30, 2057289498880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(30, 2057557966848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record029_result⟩)
 (.leaf ⟨(30, 2057566289920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record030_result⟩))
 (.branch 32
 (.leaf ⟨(30, 2058094641664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 2058103029760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record032_result⟩)
 (.leaf ⟨(30, 2100910391552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(30, 2118094225408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record034_result⟩)
 (.leaf ⟨(30, 2132606517504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record035_result⟩))
 (.branch 37
 (.leaf ⟨(30, 2132614905856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record036_result⟩)
 (.leaf ⟨(30, 2132854243584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(30, 2133007040768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record038_result⟩)
 (.leaf ⟨(30, 2133011267584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record039_result⟩))
 (.branch 41
 (.leaf ⟨(30, 2133122646272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record040_result⟩)
 (.leaf ⟨(30, 2133134936064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(30, 2137551536896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record042_result⟩)
 (.leaf ⟨(30, 2143792661248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record043_result⟩))
 (.branch 45
 (.leaf ⟨(30, 2147697559552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record044_result⟩)
 (.leaf ⟨(30, 2147895740416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(30, 2149769609472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record046_result⟩)
 (.leaf ⟨(30, 2150306480128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(30, 2150314803200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record048_result⟩)
 (.branch 50
 (.leaf ⟨(30, 2446399176704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record049_result⟩)
 (.leaf ⟨(30, 2454712287488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record050_result⟩))))))
 (.branch 59
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(30, 2455249158144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record051_result⟩)
 (.leaf ⟨(30, 2455257481216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record052_result⟩))
 (.branch 54
 (.leaf ⟨(30, 2459277787136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record053_result⟩)
 (.leaf ⟨(30, 2521559040000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(30, 2521829490816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record055_result⟩)
 (.leaf ⟨(30, 2588126806016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record056_result⟩))
 (.branch 58
 (.leaf ⟨(30, 2686843944960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record057_result⟩)
 (.leaf ⟨(30, 2793211494656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record058_result⟩))))
 (.branch 63
 (.branch 61
 (.branch 60
 (.leaf ⟨(30, 2796438950144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record059_result⟩)
 (.leaf ⟨(30, 2828651204864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record060_result⟩))
 (.branch 62
 (.leaf ⟨(30, 2905954324736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record061_result⟩)
 (.leaf ⟨(30, 2968439029760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record062_result⟩)))
 (.branch 65
 (.branch 64
 (.leaf ⟨(30, 2974948556800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record063_result⟩)
 (.leaf ⟨(30, 2975072289024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record064_result⟩))
 (.branch 66
 (.leaf ⟨(30, 3034803343616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(30, 3080298987648), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record066_result⟩)
 (.leaf ⟨(30, 3102382030848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00003.record067_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23662 + i))) 0 68 :=
  interval_of_check _ 0 68 (by decide +kernel)

public theorem complete : Block 23662 23730 :=
  block_of_table results 23662 68 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0731
