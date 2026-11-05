module
prelude
import GraphInputsRow30Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0766
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 24276644143104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 24293610389760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record001_result⟩)
 (.leaf ⟨(30, 24299587043328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 24299595366400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 24303756115968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record004_result⟩)
 (.leaf ⟨(30, 24437030125568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 24449908736000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 24457833873408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record007_result⟩)
 (.leaf ⟨(30, 24458362355712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 24470778052864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 24477824458816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record010_result⟩)
 (.leaf ⟨(30, 24482591834112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 24504067751936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 24512184729600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record013_result⟩)
 (.leaf ⟨(30, 24521247555584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 24584594423808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 24591103819776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record016_result⟩)
 (.leaf ⟨(30, 24642513338368), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 24642785902592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 24643182264320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record019_result⟩)
 (.leaf ⟨(30, 24646806208512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(30, 24647343013888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 24648886583296), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record022_result⟩)
 (.leaf ⟨(30, 24655664513024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00038.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24814 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 24814 24838 :=
  block_of_table results 24814 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0766
