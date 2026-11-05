module
prelude
import GraphInputsRow26Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0338
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 14604525650048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 14605598867584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record001_result⟩)
 (.leaf ⟨(26, 14613169061888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 14623424282880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 14623428509696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record004_result⟩)
 (.leaf ⟨(26, 14623432671232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 14623436702720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 14623568823296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record007_result⟩)
 (.leaf ⟨(26, 14623692555008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 14623826919552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 14623833064448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record010_result⟩)
 (.leaf ⟨(26, 14623960990336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 14630070059008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 14630606864384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record013_result⟩)
 (.leaf ⟨(26, 14678868623360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 14683029372928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 14699664048128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record016_result⟩)
 (.leaf ⟨(26, 14699936612352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 14701744422912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 14702016987136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record019_result⟩)
 (.leaf ⟨(26, 14702479409152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 14709805826048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record021_result⟩)
 (.leaf ⟨(26, 14716245131264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 14724566630400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record023_result⟩)
 (.leaf ⟨(26, 14733988134912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record024_result⟩))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(26, 14747445559296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 14749480796160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record026_result⟩)
 (.leaf ⟨(26, 14768387784704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(26, 14768782065664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 14781738188800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record029_result⟩)
 (.leaf ⟨(26, 14781746511872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(26, 14786039382016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 14794625122304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record032_result⟩)
 (.leaf ⟨(26, 14805357297664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(26, 14883944988928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record034_result⟩)
 (.leaf ⟨(26, 14883953377280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record035_result⟩))
 (.branch 37
 (.leaf ⟨(26, 14891457511680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record036_result⟩)
 (.leaf ⟨(26, 14896435625984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record037_result⟩)))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf ⟨(26, 14922406756352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 14922596548864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record039_result⟩)
 (.leaf ⟨(26, 14931197960192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(26, 14932259668224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 14932271697920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record042_result⟩)
 (.leaf ⟨(26, 14938702094592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record043_result⟩))))
 (.branch 47
 (.branch 45
 (.leaf ⟨(26, 14988094275840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record044_result⟩)
 (.branch 46
 (.leaf ⟨(26, 14999313514496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record045_result⟩)
 (.leaf ⟨(26, 14999783219200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(26, 15000856956928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record047_result⟩)
 (.leaf ⟨(26, 15003126604032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record048_result⟩))
 (.branch 50
 (.leaf ⟨(26, 15068435578880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record049_result⟩)
 (.leaf ⟨(26, 15068625436672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00022.record050_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15226 + i))) 0 51 :=
  interval_of_check _ 0 51 (by decide +kernel)

public theorem complete : Block 15226 15277 :=
  block_of_table results 15226 51 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0338
