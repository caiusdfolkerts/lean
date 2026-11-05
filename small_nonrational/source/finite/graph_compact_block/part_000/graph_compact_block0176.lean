module
prelude
import GraphInputsRow24Part00060Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0176
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 21921798570240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 21921806958592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record001_result⟩)
 (.leaf ⟨(24, 21921808779264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 21921915996416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 21922318649408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record004_result⟩)
 (.leaf ⟨(24, 21925963300864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 21926076614912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 21926085003264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record007_result⟩)
 (.leaf ⟨(24, 21926093259520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 21926613352968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_result⟩)
 (.leaf ⟨(24, 21930245752832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 21930640017472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record011_result⟩)
 (.leaf ⟨(24, 21930656662080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 21930774102536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 21951577850372), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record014_result⟩)
 (.leaf ⟨(24, 21951577981952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 22034866323712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 22034870534208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record017_result⟩)
 (.leaf ⟨(24, 22065970249984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 22068960772352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 22069230272544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record020_result⟩)
 (.leaf ⟨(24, 22077546512640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 22077550674176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record022_result⟩)
 (.leaf ⟨(24, 22077550723136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 22077551771680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record024_result⟩)
 (.leaf ⟨(24, 22100031275264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(24, 22100437926144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 22102196437248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record027_result⟩)
 (.leaf ⟨(24, 22102460678400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(24, 22102464839936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 22104665768192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record030_result⟩)
 (.leaf ⟨(24, 22104730796288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(24, 22113052295424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 22137948684352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record033_result⟩)
 (.leaf ⟨(24, 22137949732896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 22146270183488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record035_result⟩)
 (.leaf ⟨(24, 22146271232032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 22146535473184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record037_result⟩)
 (.leaf ⟨(24, 22146538586176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 22173383147776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 22181968888064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record040_result⟩)
 (.leaf ⟨(24, 22181975179328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(24, 22242094285056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record042_result⟩)
 (.leaf ⟨(24, 22250684186880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record043_result⟩))
 (.branch 45
 (.leaf ⟨(24, 22250694656000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record044_result⟩)
 (.leaf ⟨(24, 22259274153984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(24, 22283704942656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record046_result⟩)
 (.branch 48
 (.leaf ⟨(24, 22320083140608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record047_result⟩)
 (.leaf ⟨(24, 22323203702784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(24, 22379264803072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record049_result⟩)
 (.leaf ⟨(24, 22379533205760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record050_result⟩))
 (.branch 52
 (.leaf ⟨(24, 22379543674880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record051_result⟩)
 (.leaf ⟨(24, 22396444672000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10077 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 10077 10130 :=
  block_of_table results 10077 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0176
