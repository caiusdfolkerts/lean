module
prelude
import GraphInputsRow24Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0119
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 31
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 1507602956288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 1507739107584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record001_result⟩)
 (.leaf ⟨(24, 1507747495936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 1508148019200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record003_result⟩)
 (.leaf ⟨(24, 1535621759232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 1736855093376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record005_result⟩)
 (.leaf ⟨(24, 1874294046720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 1876510703616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record007_result⟩)
 (.leaf ⟨(24, 1876766491392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 1876774879744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record009_result⟩)
 (.leaf ⟨(24, 1972073758720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 1981468966912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record011_result⟩)
 (.leaf ⟨(24, 1981737369600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 1981861101824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record013_result⟩)
 (.leaf ⟨(24, 1981997449216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 1982005772288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_result⟩)
 (.leaf ⟨(24, 1986030239744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 2003143065600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record017_result⟩)
 (.leaf ⟨(24, 2011735015552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 2016290078720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record019_result⟩)
 (.leaf ⟨(24, 2016298401792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 2018688204800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record021_result⟩)
 (.leaf ⟨(24, 2018787229952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 2018787295232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record023_result⟩)
 (.leaf ⟨(24, 2019777806336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 2020314480896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record025_result⟩)
 (.leaf ⟨(24, 2020322869248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 2020450828288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record027_result⟩)
 (.leaf ⟨(24, 2020459151360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 2032085860352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record029_result⟩)
 (.leaf ⟨(24, 2036378730496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record030_result⟩))))))
 (.branch 47
 (.branch 39
 (.branch 35
 (.branch 33
 (.branch 32
 (.leaf ⟨(24, 2040927420416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record031_result⟩)
 (.leaf ⟨(24, 2044964470784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record032_result⟩))
 (.branch 34
 (.leaf ⟨(24, 2049517289473), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record033_result⟩)
 (.leaf ⟨(24, 2053801804032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 2057293726720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record035_result⟩)
 (.leaf ⟨(24, 2057557967104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 2057566355456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record037_result⟩)
 (.leaf ⟨(24, 2057834758144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record038_result⟩))))
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ⟨(24, 2057838789632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_result⟩)
 (.leaf ⟨(24, 2058094641920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record040_result⟩))
 (.branch 42
 (.leaf ⟨(24, 2058098900992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record041_result⟩)
 (.leaf ⟨(24, 2058107224064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(24, 2067567509760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record043_result⟩)
 (.leaf ⟨(24, 2100803174656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record044_result⟩))
 (.branch 46
 (.leaf ⟨(24, 2109512679424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record045_result⟩)
 (.leaf ⟨(24, 2113805486208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record046_result⟩)))))
 (.branch 55
 (.branch 51
 (.branch 49
 (.branch 48
 (.leaf ⟨(24, 2118226313472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record047_result⟩)
 (.leaf ⟨(24, 2118236782592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record048_result⟩))
 (.branch 50
 (.leaf ⟨(24, 2126147289344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record049_result⟩)
 (.leaf ⟨(24, 2126684160000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(24, 2126692483072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record051_result⟩)
 (.leaf ⟨(24, 2126816280576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record052_result⟩))
 (.branch 54
 (.leaf ⟨(24, 2126956724224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record053_result⟩)
 (.leaf ⟨(24, 2148046749824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record054_result⟩))))
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf ⟨(24, 2148098115712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record055_result⟩)
 (.leaf ⟨(24, 2150314803201), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record056_result⟩))
 (.branch 58
 (.leaf ⟨(24, 2150438568192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record057_result⟩)
 (.leaf ⟨(24, 2150449037312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record058_result⟩)))
 (.branch 61
 (.branch 60
 (.leaf ⟨(24, 2313253126400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record059_result⟩)
 (.leaf ⟨(24, 2420321091840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record060_result⟩))
 (.branch 62
 (.leaf ⟨(24, 2420325253376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record061_result⟩)
 (.leaf ⟨(24, 2420325318656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7872 + i))) 0 63 :=
  interval_of_check _ 0 63 (by decide +kernel)

public theorem complete : Block 7872 7935 :=
  block_of_table results 7872 63 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0119
