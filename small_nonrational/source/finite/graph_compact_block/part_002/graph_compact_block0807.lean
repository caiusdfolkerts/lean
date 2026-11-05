module
prelude
import GraphInputsRow31Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0807
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 4691518832896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record000_result⟩)
 (.leaf ⟨(31, 4720572825856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 4720841228544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 4720852738048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record003_result⟩)
 (.leaf ⟨(31, 4727016292608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 4727020519424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record005_result⟩)
 (.leaf ⟨(31, 4727429414912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 5026529476864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 5026793718016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record008_result⟩)
 (.leaf ⟨(31, 5026802106368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 5026991898880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record010_result⟩)
 (.leaf ⟨(31, 5035581800704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 5035593310208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 5043097444608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record013_result⟩)
 (.leaf ⟨(31, 5060029382912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(31, 5077456651008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record015_result⟩)
 (.leaf ⟨(31, 5103898657024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record016_result⟩))
 (.branch 18
 (.leaf ⟨(31, 5104100999424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record017_result⟩)
 (.branch 19
 (.leaf ⟨(31, 5104105226240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record018_result⟩)
 (.leaf ⟨(31, 5104167059712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00019.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25639 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 25639 25659 :=
  block_of_table results 25639 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0807
