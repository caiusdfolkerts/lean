module
prelude
import GraphInputsRow16Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0022
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 24005717458944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 24005922922496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record001_result⟩)
 (.leaf ⟨(16, 24005923832832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 24019759857920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record003_result⟩)
 (.leaf ⟨(16, 24020275986688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 24021353693184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record005_result⟩)
 (.leaf ⟨(16, 24024474255360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 24025250201600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 24025787006976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record008_result⟩)
 (.leaf ⟨(16, 24041348071424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 24041356394496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record010_result⟩)
 (.leaf ⟨(16, 24042430005248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 24042958487552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record012_result⟩)
 (.leaf ⟨(16, 24238416265216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 24251301117952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 24270634762240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record015_result⟩)
 (.leaf ⟨(16, 24299123540224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 24302823997440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record017_result⟩)
 (.leaf ⟨(16, 24306965840128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 24315225505792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record019_result⟩)
 (.leaf ⟨(16, 24319250087936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 24319455551488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 24339211632896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record022_result⟩)
 (.leaf ⟨(16, 24339213778944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 24339220021248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record024_result⟩)
 (.leaf ⟨(16, 24347268956160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 24349349265664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record026_result⟩)
 (.leaf ⟨(16, 24350117347328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(16, 24382582915072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 24382584930560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record029_result⟩)
 (.leaf ⟨(16, 24382584995840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 24383674597376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record031_result⟩)
 (.leaf ⟨(16, 24383874663680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 24383880044608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record033_result⟩)
 (.leaf ⟨(16, 24383880060928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 24384477594112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 24398847312128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record036_result⟩)
 (.leaf ⟨(16, 24418165227776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 24432082977024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record038_result⟩)
 (.leaf ⟨(16, 24453530681600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 24453601886208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record040_result⟩)
 (.leaf ⟨(16, 24471957160192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 24476117909760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 24476382150912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record043_result⟩)
 (.leaf ⟨(16, 24476384296960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(16, 24476390539264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record045_result⟩)
 (.leaf ⟨(16, 24476786900992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record046_result⟩))
 (.branch 48
 (.leaf ⟨(16, 24548054434048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record047_result⟩)
 (.leaf ⟨(16, 24608838795264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(16, 24612998488128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record049_result⟩)
 (.branch 51
 (.leaf ⟨(16, 24612999544832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record050_result⟩)
 (.leaf ⟨(16, 24711299923968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(16, 24778954014976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record052_result⟩)
 (.leaf ⟨(16, 24778954080256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record053_result⟩))
 (.branch 55
 (.leaf ⟨(16, 24779081974016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record054_result⟩)
 (.leaf ⟨(16, 24779152195840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00022.record055_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1363 + i))) 0 56 :=
  interval_of_check _ 0 56 (by decide +kernel)

public theorem complete : Block 1363 1419 :=
  block_of_table results 1363 56 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0022
