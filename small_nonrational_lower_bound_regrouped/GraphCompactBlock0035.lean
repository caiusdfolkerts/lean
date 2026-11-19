module
prelude
import GraphInputsRow16Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0035
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 31530495934720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record000_result⟩)
 (.leaf ⟨(16, 31530500161536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 31530508354560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 31530697236736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record003_result⟩)
 (.leaf ⟨(16, 31530705625088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 31530706535424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record005_result⟩)
 (.leaf ⟨(16, 31531301077504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 31543872528384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 31544681504768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record008_result⟩)
 (.leaf ⟨(16, 31544949907456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 31551385051136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record010_result⟩)
 (.leaf ⟨(16, 31553531420928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 31561852920064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 31562389790720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record013_result⟩)
 (.leaf ⟨(16, 31562390831104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 31568069402624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record015_result⟩)
 (.leaf ⟨(16, 31568095150080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 31568102432768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record017_result⟩)
 (.branch 19
 (.leaf ⟨(16, 31570191908864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record018_result⟩)
 (.leaf ⟨(16, 31570199191552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 31570200101888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record020_result⟩)
 (.leaf ⟨(16, 31570233132032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 31570695554048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record022_result⟩)
 (.branch 24
 (.leaf ⟨(16, 31616635248896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record023_result⟩)
 (.leaf ⟨(16, 31618782789632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 31622877478912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record025_result⟩)
 (.leaf ⟨(16, 31622943539200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 31623075659776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 31623173644544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record028_result⟩)
 (.leaf ⟨(16, 31623207780352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 31623216103424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record030_result⟩)
 (.leaf ⟨(16, 31625023913984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 31625220989184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record032_result⟩)
 (.branch 34
 (.leaf ⟨(16, 31625254019328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record033_result⟩)
 (.leaf ⟨(16, 31649903943936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record034_result⟩))))
 (.branch 37
 (.branch 36
 (.leaf ⟨(16, 31649921239296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record035_result⟩)
 (.leaf ⟨(16, 31654081988864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record036_result⟩))
 (.branch 38
 (.leaf ⟨(16, 31658259578880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record037_result⟩)
 (.branch 39
 (.leaf ⟨(16, 31659349180416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record038_result⟩)
 (.leaf ⟨(16, 31659555554304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00035.record039_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1938 + i))) 0 40 :=
  interval_of_check _ 0 40 (by decide +kernel)

public theorem complete : Block 1938 1978 :=
  block_of_table results 1938 40 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0035
