module
prelude
import GraphInputsRow26Part00068Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0384
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 31570266161152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record000_result⟩)
 (.leaf ⟨(26, 31570728583168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 31579304951808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 31579313274880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record003_result⟩)
 (.leaf ⟨(26, 31579552677888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 31585744257024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 31585752580096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record006_result⟩)
 (.leaf ⟨(26, 31585793802240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 31593797288192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 31594115301376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record009_result⟩)
 (.leaf ⟨(26, 31594338320384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 31594585006080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 31596732219904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record012_result⟩)
 (.leaf ⟨(26, 31602369503488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 31604517044224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 31605053849600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record015_result⟩)
 (.leaf ⟨(26, 31655386480640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 31689679110144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 31722914775040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record018_result⟩)
 (.leaf ⟨(26, 31722964320256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 31751688716544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 31751825063936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record021_result⟩)
 (.leaf ⟨(26, 31751833387008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17296 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 17296 17319 :=
  block_of_table results 17296 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0384
