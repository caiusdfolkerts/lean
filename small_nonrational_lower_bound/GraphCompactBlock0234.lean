module
prelude
import GraphInputsRow24Part00118Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0234
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 28256624509184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record000_result⟩)
 (.leaf ⟨(24, 28257739145216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 28258275950592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record002_result⟩)
 (.leaf ⟨(24, 28262027788544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 28262362316800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record004_result⟩)
 (.leaf ⟨(24, 28262568820736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 28265214411008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record006_result⟩)
 (.leaf ⟨(24, 28265985613824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 28266597449728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record008_result⟩)
 (.leaf ⟨(24, 28273804378112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 28273878761472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record010_result⟩)
 (.leaf ⟨(24, 28274341183488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 28282380681472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record012_result⟩)
 (.leaf ⟨(24, 28282653310976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 28282917552128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 28282925875200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record015_result⟩)
 (.leaf ⟨(24, 28283165278208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 28290949775616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record017_result⟩)
 (.leaf ⟨(24, 28295263453440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 28295647526912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record019_result⟩)
 (.leaf ⟨(24, 28295804485632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 28297530507264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record021_result⟩)
 (.leaf ⟨(24, 28299539677440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 28300344820224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record023_result⟩)
 (.leaf ⟨(24, 28308129644544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 28308666449920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record025_result⟩)
 (.leaf ⟨(24, 28391211335680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 28424496545792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record027_result⟩)
 (.leaf ⟨(24, 28451027353600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 28451231776768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record029_result⟩)
 (.leaf ⟨(24, 28451272933632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 28451283142656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 28452298752000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record032_result⟩)
 (.leaf ⟨(24, 28452304994304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00118.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11337 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 11337 11371 :=
  block_of_table results 11337 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0234
