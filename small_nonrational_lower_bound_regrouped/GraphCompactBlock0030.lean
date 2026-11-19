module
prelude
import GraphInputsRow16Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0030
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 28266325016576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 28266522091776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record001_result⟩)
 (.leaf ⟨(16, 28273804509184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 28273811791872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 28278627024896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record004_result⟩)
 (.leaf ⟨(16, 28280615141632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 28280767938816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 28280772165632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record007_result⟩)
 (.leaf ⟨(16, 28280883544320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 28280895834112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record009_result⟩)
 (.leaf ⟨(16, 28281424380160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 28282636666880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record011_result⟩)
 (.leaf ⟨(16, 28298604249088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(16, 28298876813312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record013_result⟩)
 (.branch 15
 (.leaf ⟨(16, 28326820380672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record014_result⟩)
 (.leaf ⟨(16, 28326828703744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 28352494764032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record016_result⟩)
 (.leaf ⟨(16, 28362219782144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 28385728798976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_result⟩)
 (.leaf ⟨(16, 28389840783616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(16, 28394314539264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record020_result⟩)
 (.branch 22
 (.leaf ⟨(16, 28417942683648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record021_result⟩)
 (.leaf ⟨(16, 28427725832192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(16, 28555493048320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record023_result⟩)
 (.leaf ⟨(16, 28627372654848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record024_result⟩))
 (.branch 26
 (.leaf ⟨(16, 28665892094208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record025_result⟩)
 (.leaf ⟨(16, 28700454166784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record026_result⟩))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf ⟨(16, 28704682082304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 28736991854592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record028_result⟩)
 (.leaf ⟨(16, 28807626031104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 28807823106304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record030_result⟩)
 (.leaf ⟨(16, 28807890272256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 28807898595328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record032_result⟩)
 (.leaf ⟨(16, 28808600158208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record033_result⟩))))
 (.branch 37
 (.branch 35
 (.leaf ⟨(16, 28808666218496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record034_result⟩)
 (.branch 36
 (.leaf ⟨(16, 28832406970624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record035_result⟩)
 (.leaf ⟨(16, 28834604843008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(16, 28842991484928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record037_result⟩)
 (.leaf ⟨(16, 28867902881792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record038_result⟩))
 (.branch 40
 (.leaf ⟨(16, 29182564241664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record039_result⟩)
 (.leaf ⟨(16, 29215749579008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record040_result⟩)))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf ⟨(16, 29250142928896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record041_result⟩)
 (.branch 43
 (.leaf ⟨(16, 29288893054976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record042_result⟩)
 (.leaf ⟨(16, 29288901378048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(16, 29312487063552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record044_result⟩)
 (.leaf ⟨(16, 29314567438336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record045_result⟩))
 (.branch 47
 (.leaf ⟨(16, 29318728187904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record046_result⟩)
 (.leaf ⟨(16, 29323293622272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record047_result⟩))))
 (.branch 51
 (.branch 49
 (.leaf ⟨(16, 29324292456448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record048_result⟩)
 (.branch 50
 (.leaf ⟨(16, 29344581820672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record049_result⟩)
 (.leaf ⟨(16, 29344632146176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(16, 29356157108224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record051_result⟩)
 (.leaf ⟨(16, 29357246709760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record052_result⟩))
 (.branch 54
 (.leaf ⟨(16, 29380015357952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record053_result⟩)
 (.leaf ⟨(16, 29386454663168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record054_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1711 + i))) 0 55 :=
  interval_of_check _ 0 55 (by decide +kernel)

public theorem complete : Block 1711 1766 :=
  block_of_table results 1711 55 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0030
