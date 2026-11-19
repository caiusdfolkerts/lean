module
prelude
import GraphInputsSix0Part00076Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1041
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 29145958735888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 29147029061888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record001_result⟩)
 (.leaf ⟨(32, 29147063652608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(32, 29171573424144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record003_result⟩)
 (.leaf ⟨(32, 29171707625488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record004_result⟩))
 (.branch 6
 (.leaf ⟨(32, 29171711787024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record005_result⟩)
 (.leaf ⟨(32, 29175985670160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(32, 29180146419728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record007_result⟩)
 (.branch 9
 (.leaf ⟨(32, 29180297756928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record008_result⟩)
 (.leaf ⟨(32, 29180299317504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(32, 29181490561024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record010_result⟩)
 (.leaf ⟨(32, 29215783190528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record011_result⟩))
 (.branch 13
 (.leaf ⟨(32, 29274583433232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record012_result⟩)
 (.leaf ⟨(32, 29274585514000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(32, 29274589675536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record014_result⟩)
 (.branch 16
 (.leaf ⟨(32, 29274790977552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record015_result⟩)
 (.leaf ⟨(32, 29276783183888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(32, 29276936081664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record017_result⟩)
 (.leaf ⟨(32, 29283156428816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record018_result⟩))
 (.branch 20
 (.leaf ⟨(32, 29283375386880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record019_result⟩)
 (.leaf ⟨(32, 29284368449536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 29284463821056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record021_result⟩)
 (.leaf ⟨(32, 29287785177344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 29292802097280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record023_result⟩)
 (.leaf ⟨(32, 29322144383744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(32, 29353284009984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record025_result⟩)
 (.leaf ⟨(32, 29357519142912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record026_result⟩))
 (.branch 28
 (.leaf ⟨(32, 29388724764672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record027_result⟩)
 (.leaf ⟨(32, 29412024434704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record028_result⟩))))))
 (.branch 44
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(32, 29412225736720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record029_result⟩)
 (.branch 31
 (.leaf ⟨(32, 29414222104592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record030_result⟩)
 (.leaf ⟨(32, 29414238749200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(32, 29515032461440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record032_result⟩)
 (.leaf ⟨(32, 29515036362880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record033_result⟩))
 (.branch 35
 (.leaf ⟨(32, 29515036395520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record034_result⟩)
 (.leaf ⟨(32, 29515288021000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record035_result⟩))))
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf ⟨(32, 29515288151048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record036_result⟩)
 (.leaf ⟨(32, 29515304927233), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record037_result⟩))
 (.branch 39
 (.leaf ⟨(32, 29549426655360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record038_result⟩)
 (.leaf ⟨(32, 29549426688000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record039_result⟩)))
 (.branch 42
 (.branch 41
 (.leaf ⟨(32, 29549428476032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record040_result⟩)
 (.leaf ⟨(32, 29549481953288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record041_result⟩))
 (.branch 43
 (.leaf ⟨(32, 29550518077568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record042_result⟩)
 (.leaf ⟨(32, 29550518110208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record043_result⟩)))))
 (.branch 51
 (.branch 47
 (.branch 45
 (.leaf ⟨(32, 29550522139656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record044_result⟩)
 (.branch 46
 (.leaf ⟨(32, 29550538915841), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record045_result⟩)
 (.leaf ⟨(32, 29583751921792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(32, 29583751954432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record047_result⟩)
 (.leaf ⟨(32, 29583753742464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record048_result⟩))
 (.branch 50
 (.leaf ⟨(32, 29583753775104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record049_result⟩)
 (.leaf ⟨(32, 29583757804552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record050_result⟩))))
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(32, 29583873280008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record051_result⟩)
 (.leaf ⟨(32, 29583873410056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record052_result⟩))
 (.branch 54
 (.leaf ⟨(32, 29583890186241), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record053_result⟩)
 (.leaf ⟨(32, 29687941251200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(32, 29687974281344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record055_result⟩)
 (.leaf ⟨(32, 29688041382016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record056_result⟩))
 (.branch 58
 (.leaf ⟨(32, 29688047624320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record057_result⟩)
 (.leaf ⟨(32, 29689115119744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076.record058_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34213 + i))) 0 59 :=
  interval_of_check _ 0 59 (by decide +kernel)

public theorem complete : Block 34213 34272 :=
  block_of_table results 34213 59 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1041
