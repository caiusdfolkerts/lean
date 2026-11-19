module
prelude
import GraphInputsRow29Part00099Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0533
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 17044070207488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record000_result⟩)
 (.leaf ⟨(29, 17051062241296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 17051574341888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 17051582730240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record003_result⟩)
 (.leaf ⟨(29, 17051590856960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 17052131721472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record005_result⟩)
 (.leaf ⟨(29, 17052404350976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 17052639301632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 17052664333056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record008_result⟩)
 (.leaf ⟨(29, 17052668592128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 17052676915200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_result⟩)
 (.leaf ⟨(29, 17052899803136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 17059912356096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 17060164276352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record013_result⟩)
 (.leaf ⟨(29, 17060180791424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(29, 17060415672336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record015_result⟩)
 (.leaf ⟨(29, 17061254267520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record016_result⟩))
 (.branch 18
 (.leaf ⟨(29, 17061489148432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record017_result⟩)
 (.branch 19
 (.leaf ⟨(29, 17068234146048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record018_result⟩)
 (.leaf ⟨(29, 17069005869056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(29, 17081357631744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record020_result⟩)
 (.leaf ⟨(29, 17112496144640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record021_result⟩))
 (.branch 23
 (.leaf ⟨(29, 17121090273280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record022_result⟩)
 (.branch 24
 (.leaf ⟨(29, 17121627078656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_result⟩)
 (.leaf ⟨(29, 17136957325312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(29, 17137725341696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record025_result⟩)
 (.leaf ⟨(29, 17154376269824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record026_result⟩))
 (.branch 28
 (.leaf ⟨(29, 17171556073472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record027_result⟩)
 (.branch 29
 (.leaf ⟨(29, 17180431486976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record028_result⟩)
 (.leaf ⟨(29, 17181081403648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(29, 17188476485888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record030_result⟩)
 (.leaf ⟨(29, 17189013356544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record031_result⟩))
 (.branch 33
 (.leaf ⟨(29, 17189021679616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record032_result⟩)
 (.branch 34
 (.leaf ⟨(29, 17190078251008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record033_result⟩)
 (.leaf ⟨(29, 17190212337664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(29, 17192796094464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record035_result⟩)
 (.branch 37
 (.leaf ⟨(29, 17197586057232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record036_result⟩)
 (.leaf ⟨(29, 17197602701840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(29, 17197854625792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record038_result⟩)
 (.branch 40
 (.leaf ⟨(29, 17198122959104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record039_result⟩)
 (.leaf ⟨(29, 17198261272576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21898 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 21898 21939 :=
  block_of_table results 21898 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0533
