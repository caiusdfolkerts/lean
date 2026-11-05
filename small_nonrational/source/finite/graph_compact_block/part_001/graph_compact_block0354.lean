module
prelude
import GraphInputsRow26Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0354
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 21119497175296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record000_result⟩)
 (.leaf ⟨(26, 21119633522688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 21119641845760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record002_result⟩)
 (.leaf ⟨(26, 21119765643264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 21119773966336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record004_result⟩)
 (.leaf ⟨(26, 21120234307584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 21123934715904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record006_result⟩)
 (.leaf ⟨(26, 21124395057152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 21127515619328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record008_result⟩)
 (.leaf ⟨(26, 21235546226944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 21235603867776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record010_result⟩)
 (.leaf ⟨(26, 21244385706240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 21256936259584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record012_result⟩)
 (.leaf ⟨(26, 21257068216960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 21316594311232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 21333137178688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record015_result⟩)
 (.leaf ⟨(26, 21333205336064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 21333271396352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record017_result⟩)
 (.leaf ⟨(26, 21333273477120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 21342105634816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record019_result⟩)
 (.leaf ⟨(26, 21367596662784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 21367598743552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record021_result⟩)
 (.leaf ⟨(26, 21374057873664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 21374062100480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record023_result⟩)
 (.leaf ⟨(26, 21374068342784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 21374192075008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record025_result⟩)
 (.leaf ⟨(26, 21374200463360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 21374307680512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record027_result⟩)
 (.leaf ⟨(26, 21374317889536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(26, 21374710333504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record029_result⟩)
 (.leaf ⟨(26, 21376253853952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record030_result⟩))
 (.branch 32
 (.leaf ⟨(26, 21376266143744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 21376338510080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record032_result⟩)
 (.leaf ⟨(26, 21376340656128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00038.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16037 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 16037 16071 :=
  block_of_table results 16037 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0354
