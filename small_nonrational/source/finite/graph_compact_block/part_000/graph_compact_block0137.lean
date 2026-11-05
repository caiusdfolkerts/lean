module
prelude
import GraphInputsRow24Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0137
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 12465138204672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 12465142236160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_result⟩)
 (.leaf ⟨(24, 12465270162048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 12465340417024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 12508172681472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record004_result⟩)
 (.leaf ⟨(24, 12508230322304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 12510575001600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 12512655376384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record007_result⟩)
 (.leaf ⟨(24, 12517012160768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 12524295555200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_result⟩)
 (.leaf ⟨(24, 12545891041280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 12550297370880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record011_result⟩)
 (.leaf ⟨(24, 12554592060160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 12575750521088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 12575750586368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record014_result⟩)
 (.leaf ⟨(24, 12575752667136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 12575754422528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 12575756796032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record017_result⟩)
 (.leaf ⟨(24, 12575756828672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 12575878154248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 12575952603392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record020_result⟩)
 (.leaf ⟨(24, 12575958130688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 12576221038720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record022_result⟩)
 (.leaf ⟨(24, 12577950271744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 12577950337024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record024_result⟩)
 (.leaf ⟨(24, 12577954465920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8854 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 8854 8880 :=
  block_of_table results 8854 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0137
