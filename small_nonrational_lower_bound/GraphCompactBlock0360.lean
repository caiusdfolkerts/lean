module
prelude
import GraphInputsRow26Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0360
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 29
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 23932977545217), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 23941792940032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record001_result⟩)
 (.leaf ⟨(26, 23971286384896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 23971554852864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record003_result⟩)
 (.leaf ⟨(26, 23971563175936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 23972091527680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record005_result⟩)
 (.leaf ⟨(26, 23986993954816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(26, 23989074329600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 23990114516992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record008_result⟩)
 (.leaf ⟨(26, 24005717327872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 24005989892096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record010_result⟩)
 (.leaf ⟨(26, 24006452314112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 24022309994496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record012_result⟩)
 (.leaf ⟨(26, 24024176459776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(26, 24034913945600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 24052985036800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record015_result⟩)
 (.leaf ⟨(26, 24053453701120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 24053494857984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record017_result⟩)
 (.leaf ⟨(26, 24053505067008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 24054124314624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record019_result⟩)
 (.leaf ⟨(26, 24054520676352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 24054526918656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record021_result⟩)
 (.leaf ⟨(26, 24054535045376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 24054545254400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record023_result⟩)
 (.leaf ⟨(26, 24055709172480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 24069097668864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record025_result⟩)
 (.leaf ⟨(26, 24069107877888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 24069206968320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record027_result⟩)
 (.leaf ⟨(26, 24069550907456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record028_result⟩))))))
 (.branch 43
 (.branch 36
 (.branch 32
 (.branch 30
 (.leaf ⟨(26, 24069551964160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 24069567422528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record030_result⟩)
 (.leaf ⟨(26, 24070674448960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record031_result⟩)))
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 24086336307200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record032_result⟩)
 (.leaf ⟨(26, 24086730522880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 24086738911232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record034_result⟩)
 (.leaf ⟨(26, 24086740731904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 24086847949056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 24091016955904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record037_result⟩)
 (.leaf ⟨(26, 24091025212160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record038_result⟩)))
 (.branch 41
 (.branch 40
 (.leaf ⟨(26, 24103499204608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record039_result⟩)
 (.leaf ⟨(26, 24103893469248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record040_result⟩))
 (.branch 42
 (.leaf ⟨(26, 24103910113856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record041_result⟩)
 (.leaf ⟨(26, 24104027554312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record042_result⟩)))))
 (.branch 50
 (.branch 46
 (.branch 44
 (.leaf ⟨(26, 24194801803392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 24195198165120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record044_result⟩)
 (.leaf ⟨(26, 24199496286240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(26, 24208083017856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record046_result⟩)
 (.leaf ⟨(26, 24208086188064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record047_result⟩))
 (.branch 49
 (.leaf ⟨(26, 24228473102464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record048_result⟩)
 (.leaf ⟨(26, 24229396381952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record049_result⟩))))
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf ⟨(26, 24233491136512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record050_result⟩)
 (.leaf ⟨(26, 24233889513728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record051_result⟩))
 (.branch 53
 (.leaf ⟨(26, 24233889579008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record052_result⟩)
 (.leaf ⟨(26, 24233895804992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record053_result⟩)))
 (.branch 56
 (.branch 55
 (.leaf ⟨(26, 24236912546048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record054_result⟩)
 (.leaf ⟨(26, 24260282753152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record055_result⟩))
 (.branch 57
 (.leaf ⟨(26, 24267127832608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record056_result⟩)
 (.leaf ⟨(26, 24293478203400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16376 + i))) 0 58 :=
  interval_of_check _ 0 58 (by decide +kernel)

public theorem complete : Block 16376 16434 :=
  block_of_table results 16376 58 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0360
