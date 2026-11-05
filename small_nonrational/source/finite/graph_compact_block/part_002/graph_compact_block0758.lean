module
prelude
import GraphInputsRow30Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0758
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 16770259750912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 16776699056128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record001_result⟩)
 (.leaf ⟨(30, 16778692984832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 16784933785728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 16906134257920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record004_result⟩)
 (.leaf ⟨(30, 16908350980096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 16908623544320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 16909019906048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record007_result⟩)
 (.leaf ⟨(30, 16914724225024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 16915261030400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 16930795700224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record010_result⟩)
 (.leaf ⟨(30, 16931904028672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 16932036149248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 16943667019776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record013_result⟩)
 (.leaf ⟨(30, 16943939584000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 16944451551232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 16948496695296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record016_result⟩)
 (.leaf ⟨(30, 16948612300800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 16969415917568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 16975996715008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record019_result⟩)
 (.leaf ⟨(30, 16985119260672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 16986671153152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record021_result⟩)
 (.leaf ⟨(30, 17003842633728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 17042481381632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record023_result⟩)
 (.leaf ⟨(30, 17042481446912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record024_result⟩))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(30, 17042485022976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record025_result⟩)
 (.branch 27
 (.leaf ⟨(30, 17042485088256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record026_result⟩)
 (.leaf ⟨(30, 17042493147152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(30, 17042724098064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record028_result⟩)
 (.branch 30
 (.leaf ⟨(30, 17042724358160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record029_result⟩)
 (.leaf ⟨(30, 17043558564352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(30, 17043566886913), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 17043780929552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record032_result⟩)
 (.leaf ⟨(30, 17043798097921), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(30, 17043798163456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record034_result⟩)
 (.leaf ⟨(30, 17044058177792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record035_result⟩))
 (.branch 37
 (.leaf ⟨(30, 17044066566144), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record036_result⟩)
 (.leaf ⟨(30, 17044070207488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record037_result⟩)))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf ⟨(30, 17051062241296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record038_result⟩)
 (.branch 40
 (.leaf ⟨(30, 17051574341888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record039_result⟩)
 (.leaf ⟨(30, 17051582730240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(30, 17051590856960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record041_result⟩)
 (.branch 43
 (.leaf ⟨(30, 17052131721472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record042_result⟩)
 (.leaf ⟨(30, 17052404350976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record043_result⟩))))
 (.branch 47
 (.branch 45
 (.leaf ⟨(30, 17052639301632), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record044_result⟩)
 (.branch 46
 (.leaf ⟨(30, 17052664333056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record045_result⟩)
 (.leaf ⟨(30, 17052668592128), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(30, 17052676915200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record047_result⟩)
 (.leaf ⟨(30, 17052899803136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record048_result⟩))
 (.branch 50
 (.leaf ⟨(30, 17060164276352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record049_result⟩)
 (.leaf ⟨(30, 17060180791424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030.record050_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24508 + i))) 0 51 :=
  interval_of_check _ 0 51 (by decide +kernel)

public theorem complete : Block 24508 24559 :=
  block_of_table results 24508 51 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0758
