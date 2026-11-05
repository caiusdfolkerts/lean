module
prelude
import GraphInputsRow29Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0485
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 9803401330944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record000_result⟩)
 (.leaf ⟨(29, 9811991232768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 9812660224000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 9820581199872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record003_result⟩)
 (.leaf ⟨(29, 9820853764096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 9821118005248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record005_result⟩)
 (.leaf ⟨(29, 9933594624256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 9935679225856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 9936822079744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record008_result⟩)
 (.leaf ⟨(29, 9939839910144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 9941114949888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record010_result⟩)
 (.leaf ⟨(29, 9943261384960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 9970309431552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 9970309496832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record013_result⟩)
 (.leaf ⟨(29, 9970510733568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 9974602366976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 9974671483136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record016_result⟩)
 (.leaf ⟨(29, 10010104954881), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(29, 10055202115616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 10072977637632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record019_result⟩)
 (.leaf ⟨(29, 10090165829632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21249 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 21249 21270 :=
  block_of_table results 21249 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0485
