module
prelude
import GraphInputsRow29Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0443
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 2147895740416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 2149769609472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record001_result⟩)
 (.leaf ⟨(29, 2150306480128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 2150314803200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record003_result⟩)
 (.leaf ⟨(29, 2313248899328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 2418750267648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record005_result⟩)
 (.leaf ⟨(29, 2427340202112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 2446390788352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record007_result⟩)
 (.leaf ⟨(29, 2446399176704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 2454712287488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record009_result⟩)
 (.leaf ⟨(29, 2455249158144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 2455257481216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record011_result⟩)
 (.leaf ⟨(29, 2459277787136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 2521559040000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record013_result⟩)
 (.leaf ⟨(29, 2521829490816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 2588126806016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 2686843944960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record016_result⟩)
 (.leaf ⟨(29, 2793211494656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(29, 2796438950144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record018_result⟩)
 (.leaf ⟨(29, 2827504124160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record019_result⟩))
 (.branch 21
 (.leaf ⟨(29, 2828651204864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record020_result⟩)
 (.leaf ⟨(29, 2865552752896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 2865561141248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record022_result⟩)
 (.leaf ⟨(29, 2874142654720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 2874151043072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record024_result⟩)
 (.leaf ⟨(29, 2878435524864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(29, 2893075714304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record026_result⟩)
 (.leaf ⟨(29, 2896089383168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record027_result⟩))
 (.branch 29
 (.leaf ⟨(29, 2897368584448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record028_result⟩)
 (.leaf ⟨(29, 2905954324736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00009.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20630 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 20630 20660 :=
  block_of_table results 20630 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0443
