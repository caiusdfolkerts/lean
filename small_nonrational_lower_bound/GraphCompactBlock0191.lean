module
prelude
import GraphInputsRow24Part00075Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0191
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 24052976648448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record000_result⟩)
 (.leaf ⟨(24, 24052985036800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24053445312768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record002_result⟩)
 (.leaf ⟨(24, 24053447458816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 24053453701120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record004_result⟩)
 (.leaf ⟨(24, 24053494857984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 24053505067008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24054124314624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record007_result⟩)
 (.leaf ⟨(24, 24054132441344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 24054520676352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record009_result⟩)
 (.leaf ⟨(24, 24054526918656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 24054535045376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 24054545254400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record012_result⟩)
 (.leaf ⟨(24, 24055709172480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 24069097668864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record014_result⟩)
 (.leaf ⟨(24, 24069107877888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 24069206968320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 24069550907456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record017_result⟩)
 (.leaf ⟨(24, 24069551964160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 24069567422528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record019_result⟩)
 (.leaf ⟨(24, 24070674448960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 24086327918848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 24086336307200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record022_result⟩)
 (.leaf ⟨(24, 24086730522880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 24086738911232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record024_result⟩)
 (.leaf ⟨(24, 24086740731904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 24086847949056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 24091008567552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record027_result⟩)
 (.leaf ⟨(24, 24091016955904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 24091025212160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record029_result⟩)
 (.leaf ⟨(24, 24103499204608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 24103893469248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 24104027554312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record032_result⟩)
 (.leaf ⟨(24, 24192588267648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(24, 24193050689664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record034_result⟩)
 (.leaf ⟨(24, 24199232045088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record035_result⟩))
 (.branch 37
 (.leaf ⟨(24, 24199496286240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 24208083017856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record037_result⟩)
 (.leaf ⟨(24, 24228473102464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00075.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10483 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 10483 10522 :=
  block_of_table results 10483 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0191
