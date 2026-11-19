module
prelude
import GraphInputsRow29Part00098Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0532
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 16980430028800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record000_result⟩)
 (.leaf ⟨(29, 16985119260672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 16986671153152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record002_result⟩)
 (.leaf ⟨(29, 17003842633728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 17042481381632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record004_result⟩)
 (.leaf ⟨(29, 17042481446912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 17042485022976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record006_result⟩)
 (.leaf ⟨(29, 17042485088256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 17042493147152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record008_result⟩)
 (.leaf ⟨(29, 17042724098064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 17042724358160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record010_result⟩)
 (.leaf ⟨(29, 17043558564352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 17043780929552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record012_result⟩)
 (.leaf ⟨(29, 17043798097921), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 17043798163456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 17044058177792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record015_result⟩)
 (.leaf ⟨(29, 17044066566144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21881 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 21881 21898 :=
  block_of_table results 21881 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0532
