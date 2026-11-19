module
prelude
import GraphInputsRow16Part00015Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0015
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 17203802406912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 17207451451392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record001_result⟩)
 (.leaf ⟨(16, 17215457919232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 17215466307584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 17215598428160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record004_result⟩)
 (.leaf ⟨(16, 17215858442496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 17215862669312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 17215986337792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record007_result⟩)
 (.leaf ⟨(16, 17218809692416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(16, 17218818080768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record009_result⟩)
 (.branch 11
 (.leaf ⟨(16, 17219078095104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record010_result⟩)
 (.leaf ⟨(16, 17219082321920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(16, 17219090124800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 17219094610176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record013_result⟩)
 (.leaf ⟨(16, 17219106899968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(16, 17219329462528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 17220402938624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record016_result⟩)
 (.leaf ⟨(16, 17222986957056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(16, 17223375192064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 17223382994944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record019_result⟩)
 (.leaf ⟨(16, 17223399770112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(16, 17227131191552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 17227668062208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record022_result⟩)
 (.leaf ⟨(16, 17227676385280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(16, 17228724633600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record024_result⟩)
 (.branch 26
 (.leaf ⟨(16, 17228732956672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record025_result⟩)
 (.leaf ⟨(16, 17231576858880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(16, 17231589148672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 17231985510400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record028_result⟩)
 (.leaf ⟨(16, 17235721093376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(16, 17235758350336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 17235766673408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record031_result⟩)
 (.leaf ⟨(16, 17235989561344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(16, 17235997884416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record033_result⟩)
 (.branch 35
 (.leaf ⟨(16, 17236509331456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record034_result⟩)
 (.leaf ⟨(16, 17236526366720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(16, 17236777664768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 17237046132736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record037_result⟩)
 (.leaf ⟨(16, 17237054455808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(16, 17237582807552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record039_result⟩)
 (.branch 41
 (.leaf ⟨(16, 17244327444480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record040_result⟩)
 (.leaf ⟨(16, 17244335767552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 17244830699520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 17244864119296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record043_result⟩)
 (.leaf ⟨(16, 17320837709824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(16, 17327277015040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record045_result⟩)
 (.branch 47
 (.leaf ⟨(16, 17329431773184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_result⟩)
 (.leaf ⟨(16, 17329522540544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record047_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (980 + i))) 0 48 :=
  interval_of_check _ 0 48 (by decide +kernel)

public theorem complete : Block 980 1028 :=
  block_of_table results 980 48 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0015
