module
prelude
import GraphInputsRow23Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0099
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 28082245271552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record000_result⟩)
 (.leaf ⟨(23, 28082253594624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 28082377392128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record002_result⟩)
 (.branch 4
 (.leaf ⟨(23, 28154324320256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record003_result⟩)
 (.leaf ⟨(23, 28193576779776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(23, 28193585102848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record005_result⟩)
 (.branch 7
 (.leaf ⟨(23, 28195118661632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record006_result⟩)
 (.leaf ⟨(23, 28231625343488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(23, 28299816337408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record008_result⟩)
 (.branch 10
 (.leaf ⟨(23, 28300344819712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record009_result⟩)
 (.leaf ⟨(23, 28308666318848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(23, 28315126087808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record011_result⟩)
 (.leaf ⟨(23, 28453495635968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record012_result⟩))
 (.branch 14
 (.leaf ⟨(23, 28488811675648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record013_result⟩)
 (.branch 15
 (.leaf ⟨(23, 28492831981568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record014_result⟩)
 (.leaf ⟨(23, 28493484392448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(23, 28531543244800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record016_result⟩)
 (.branch 18
 (.leaf ⟨(23, 28592851394688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record017_result⟩)
 (.leaf ⟨(23, 28592983515264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(23, 28593247756416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record019_result⟩)
 (.branch 21
 (.leaf ⟨(23, 28625296457728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record020_result⟩)
 (.leaf ⟨(23, 28627236323584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(23, 28627244711936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record022_result⟩)
 (.leaf ⟨(23, 28627368444160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record023_result⟩))
 (.branch 25
 (.leaf ⟨(23, 28627372670976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record024_result⟩)
 (.branch 26
 (.leaf ⟨(23, 28627376832512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record025_result⟩)
 (.leaf ⟨(23, 28627636879488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(23, 28627837141120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record027_result⟩)
 (.branch 29
 (.leaf ⟨(23, 28628519751680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record028_result⟩)
 (.leaf ⟨(23, 28628776157312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(23, 28628910358656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record030_result⟩)
 (.branch 32
 (.leaf ⟨(23, 28631537582080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record031_result⟩)
 (.leaf ⟨(23, 28640119128192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(23, 28640123322368), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record033_result⟩)
 (.branch 35
 (.leaf ⟨(23, 28640319389824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record034_result⟩)
 (.leaf ⟨(23, 28660606705920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(23, 28660610900096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record036_result⟩)
 (.branch 38
 (.leaf ⟨(23, 28667363737728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record037_result⟩)
 (.leaf ⟨(23, 28700114452736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(23, 28708704387200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record039_result⟩)
 (.branch 41
 (.leaf ⟨(23, 28717294321664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record040_result⟩)
 (.leaf ⟨(23, 28717430603776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(23, 28743199391744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record042_result⟩)
 (.branch 44
 (.leaf ⟨(23, 28770243248128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record043_result⟩)
 (.leaf ⟨(23, 28781855113216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00021.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7293 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 7293 7338 :=
  block_of_table results 7293 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0099
