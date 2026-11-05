module
prelude
import GraphInputsRow29Part00048Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0482
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 8265171763200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 8265262465280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record001_result⟩)
 (.leaf ⟨(29, 8265274494976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 8268617879808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 8315350552832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record004_result⟩)
 (.leaf ⟨(29, 8324192012304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 8324209180673), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 8324209246208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record007_result⟩)
 (.leaf ⟨(29, 8325265752065), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 8325265817600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 8332513511440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record010_result⟩)
 (.leaf ⟨(29, 8332790759680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(29, 8332799148032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record012_result⟩)
 (.branch 14
 (.leaf ⟨(29, 8332802789376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record013_result⟩)
 (.leaf ⟨(29, 8334115603200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(29, 8334119862272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 8334128185344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record016_result⟩)
 (.leaf ⟨(29, 8340864303360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(29, 8341632385024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record018_result⟩)
 (.branch 20
 (.leaf ⟨(29, 8402713444352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record019_result⟩)
 (.leaf ⟨(29, 8402837241856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(29, 8406056894464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 8409581682944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record022_result⟩)
 (.leaf ⟨(29, 8474784169984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21134 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 21134 21158 :=
  block_of_table results 21134 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0482
