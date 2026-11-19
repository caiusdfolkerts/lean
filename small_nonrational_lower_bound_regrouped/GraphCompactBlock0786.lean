module
prelude
import GraphInputsRow30Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0786
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 34498268905472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record000_result⟩)
 (.leaf ⟨(30, 34498337046528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 34498452652032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 34500398694400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record003_result⟩)
 (.leaf ⟨(30, 34531537193024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(30, 34531554115584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record005_result⟩)
 (.leaf ⟨(30, 34531688316928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record006_result⟩))
 (.branch 8
 (.leaf ⟨(30, 34535832160256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 34634633709584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record008_result⟩)
 (.leaf ⟨(30, 34634633713664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 34634666873088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record010_result⟩)
 (.leaf ⟨(30, 34634667393025), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 34634667458560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 34634675261440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record013_result⟩)
 (.leaf ⟨(30, 34635170189328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(30, 34635725701376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record015_result⟩)
 (.leaf ⟨(30, 34635752931328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_result⟩))
 (.branch 18
 (.leaf ⟨(30, 34635759255808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record017_result⟩)
 (.branch 19
 (.leaf ⟨(30, 34635975819264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record018_result⟩)
 (.leaf ⟨(30, 34635984142336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(30, 34636243665424), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record020_result⟩)
 (.leaf ⟨(30, 34636495589376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_result⟩))
 (.branch 23
 (.leaf ⟨(30, 34640022798336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record022_result⟩)
 (.branch 24
 (.leaf ⟨(30, 34640295362560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record023_result⟩)
 (.leaf ⟨(30, 34640790814720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(30, 34643223515392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record025_result⟩)
 (.leaf ⟨(30, 34643760386048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record026_result⟩))
 (.branch 28
 (.leaf ⟨(30, 34643776901120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 34644280086784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record028_result⟩)
 (.leaf ⟨(30, 34644850377216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(30, 34647535321088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record030_result⟩)
 (.leaf ⟨(30, 34660386213904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record031_result⟩))
 (.branch 33
 (.leaf ⟨(30, 34670188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record032_result⟩)
 (.branch 34
 (.leaf ⟨(30, 34674621546496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record033_result⟩)
 (.leaf ⟨(30, 34675150028800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(30, 34681902858240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_result⟩)
 (.branch 37
 (.leaf ⟨(30, 34703353086208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record036_result⟩)
 (.leaf ⟨(30, 34711943053312), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(30, 34712479858688), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record038_result⟩)
 (.branch 40
 (.leaf ⟨(30, 34712999624704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record039_result⟩)
 (.leaf ⟨(30, 34729105690624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25389 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 25389 25430 :=
  block_of_table results 25389 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0786
