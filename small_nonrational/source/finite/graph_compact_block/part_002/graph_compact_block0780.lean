module
prelude
import GraphInputsRow30Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0780
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 30942824505408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record000_result⟩)
 (.leaf ⟨(30, 30943897722944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 30946045206560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record002_result⟩)
 (.leaf ⟨(30, 30969467830272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 30978256929344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record004_result⟩)
 (.leaf ⟨(30, 30980404412960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 31014765207552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 31063910912032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record007_result⟩)
 (.leaf ⟨(30, 31065793105952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 31065842651168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record009_result⟩)
 (.leaf ⟨(30, 31099390558208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 31244345671680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 31336132608032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record012_result⟩)
 (.leaf ⟨(30, 31336136249376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(30, 31337209725472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record014_result⟩)
 (.leaf ⟨(30, 31337449267456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record015_result⟩))
 (.branch 17
 (.leaf ⟨(30, 31337717702784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 31346328084480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record017_result⟩)
 (.leaf ⟨(30, 31414808543232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(30, 31415072784384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record019_result⟩)
 (.leaf ⟨(30, 31415081107456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record020_result⟩))
 (.branch 22
 (.leaf ⟨(30, 31415270965248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 31430605308160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record022_result⟩)
 (.leaf ⟨(30, 31431376510976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 31448316772352), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record024_result⟩)
 (.leaf ⟨(30, 31450711719936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 31465001779200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record026_result⟩)
 (.branch 28
 (.leaf ⟨(30, 31465736765440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record027_result⟩)
 (.leaf ⟨(30, 31474082648096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(30, 31491505786912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record029_result⟩)
 (.leaf ⟨(30, 31492579263008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record030_result⟩))
 (.branch 32
 (.leaf ⟨(30, 31495801020416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 31519296978944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record032_result⟩)
 (.leaf ⟨(30, 31527345913856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(30, 31527618478080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record034_result⟩)
 (.leaf ⟨(30, 31530161274880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record035_result⟩))
 (.branch 37
 (.leaf ⟨(30, 31568077848576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 31587882237952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record037_result⟩)
 (.leaf ⟨(30, 31596203737088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00052.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25202 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 25202 25241 :=
  block_of_table results 25202 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0780
