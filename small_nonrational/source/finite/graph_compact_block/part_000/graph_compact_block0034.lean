module
prelude
import GraphInputsRow16Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0034
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 31494101803008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record000_result⟩)
 (.leaf ⟨(16, 31494358761472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 31494367084544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record002_result⟩)
 (.leaf ⟨(16, 31494861496320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 31494862536704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record004_result⟩)
 (.leaf ⟨(16, 31496170668288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 31496174895104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 31496182177792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record007_result⟩)
 (.leaf ⟨(16, 31496380358656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 31496405000448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record009_result⟩)
 (.leaf ⟨(16, 31496908840960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 31496941871104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record011_result⟩)
 (.branch 13
 (.leaf ⟨(16, 31496942911488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record012_result⟩)
 (.leaf ⟨(16, 31509110128896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(16, 31509114290432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record014_result⟩)
 (.leaf ⟨(16, 31509114355712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record015_result⟩))
 (.branch 17
 (.leaf ⟨(16, 31509516959744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record016_result⟩)
 (.branch 18
 (.leaf ⟨(16, 31511707418880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record017_result⟩)
 (.leaf ⟨(16, 31512469184768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 31512469250048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record019_result⟩)
 (.leaf ⟨(16, 31512733491200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 31520816431360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record021_result⟩)
 (.leaf ⟨(16, 31520824819712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 31520874364928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record023_result⟩)
 (.leaf ⟨(16, 31521327554560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 31521914421248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record025_result⟩)
 (.branch 27
 (.leaf ⟨(16, 31522385036288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record026_result⟩)
 (.leaf ⟨(16, 31528415559936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(16, 31528419786752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record028_result⟩)
 (.leaf ⟨(16, 31528427979776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record029_result⟩))
 (.branch 31
 (.leaf ⟨(16, 31529406333184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 31529410560000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record031_result⟩)
 (.leaf ⟨(16, 31529417842688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(16, 31529460105216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record033_result⟩)
 (.leaf ⟨(16, 31529640665344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record034_result⟩))
 (.branch 36
 (.leaf ⟨(16, 31529649053696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 31530177536000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record036_result⟩)
 (.leaf ⟨(16, 31530178576384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00034.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1900 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 1900 1938 :=
  block_of_table results 1900 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0034
