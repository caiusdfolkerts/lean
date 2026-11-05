module
prelude
import GraphInputsRow26Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0361
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 24319384158208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record000_result⟩)
 (.leaf ⟨(26, 24319392481280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 24319516278784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 24333351129344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record003_result⟩)
 (.leaf ⟨(26, 24333549310208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 24333753782336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record005_result⟩)
 (.leaf ⟨(26, 24345152880896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 24345152946176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 24345155026944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record008_result⟩)
 (.leaf ⟨(26, 24345558655040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 24346632392768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record010_result⟩)
 (.leaf ⟨(26, 24367033548800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 24367039791104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 24375619289088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record013_result⟩)
 (.leaf ⟨(26, 24375627612160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 24380794994689), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 24383808667648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record016_result⟩)
 (.leaf ⟨(26, 24383816990720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(26, 24383949111296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 24384477593600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record019_result⟩)
 (.leaf ⟨(26, 24388101537792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 24388109860864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record021_result⟩)
 (.leaf ⟨(26, 24388504141824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 24391690764288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 24399241576704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record024_result⟩)
 (.leaf ⟨(26, 24399252045824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 24405691351040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record026_result⟩)
 (.leaf ⟨(26, 24414012850176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 24415884574976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 24416020922368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record029_result⟩)
 (.leaf ⟨(26, 24423434354688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(26, 24423442677760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record031_result⟩)
 (.leaf ⟨(26, 24432217227264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record032_result⟩))
 (.branch 34
 (.leaf ⟨(26, 24432487710720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 24432592847104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record034_result⟩)
 (.leaf ⟨(26, 24432605136896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 24436891779072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 24438920773632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record037_result⟩)
 (.leaf ⟨(26, 24438927015936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 24438968172800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 24438978381824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record040_result⟩)
 (.leaf ⟨(26, 24443262862080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00045.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16434 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 16434 16476 :=
  block_of_table results 16434 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0361
