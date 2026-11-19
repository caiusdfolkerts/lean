module
prelude
import GraphInputsRow30Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0759
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 17060415672336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record000_result⟩)
 (.leaf ⟨(30, 17061254267520), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 17061489148432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 17068234146048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record003_result⟩)
 (.leaf ⟨(30, 17069005869056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 17081357631744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 17112496144640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record006_result⟩)
 (.leaf ⟨(30, 17121090273280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 17121627078656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 17136957325312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record009_result⟩)
 (.leaf ⟨(30, 17137725341696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(30, 17154376269824), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 17179886358784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record012_result⟩)
 (.leaf ⟨(30, 17180431486976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(30, 17188476485888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 17189013356544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record015_result⟩)
 (.leaf ⟨(30, 17189021679616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(30, 17190078251008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 17190212337664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record018_result⟩)
 (.leaf ⟨(30, 17197586057232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(30, 17197602701840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record020_result⟩)
 (.branch 22
 (.leaf ⟨(30, 17197854625792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record021_result⟩)
 (.leaf ⟨(30, 17198122959104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(30, 17198261272576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record023_result⟩)
 (.leaf ⟨(30, 17198533836800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record024_result⟩))
 (.branch 26
 (.leaf ⟨(30, 17198928101888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record025_result⟩)
 (.branch 27
 (.leaf ⟨(30, 17201381834752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record026_result⟩)
 (.leaf ⟨(30, 17202149851136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(30, 17205639123200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record028_result⟩)
 (.branch 30
 (.leaf ⟨(30, 17218800779264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record029_result⟩)
 (.leaf ⟨(30, 17227659083776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(30, 17235980582912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 17292083593216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record032_result⟩)
 (.leaf ⟨(30, 17317602004992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(30, 17326451720720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record034_result⟩)
 (.branch 36
 (.leaf ⟨(30, 17480516895236), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record035_result⟩)
 (.leaf ⟨(30, 17523487604736), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(30, 17532081668096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 17532610150400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record038_result⟩)
 (.leaf ⟨(30, 17549236502528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(30, 17595514306944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record040_result⟩)
 (.branch 42
 (.leaf ⟨(30, 17595578286464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_result⟩)
 (.leaf ⟨(30, 17595580367232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(30, 17595714584896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record043_result⟩)
 (.branch 45
 (.leaf ⟨(30, 17595718746432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record044_result⟩)
 (.leaf ⟨(30, 17631130755392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24559 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 24559 24605 :=
  block_of_table results 24559 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0759
