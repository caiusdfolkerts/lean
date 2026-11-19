module
prelude
import GraphInputsRow30Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0782
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 32335217033216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 32351841304576), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record001_result⟩)
 (.leaf ⟨(30, 32476135161856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 32488344846336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 32488617410560), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record004_result⟩)
 (.leaf ⟨(30, 32492233424896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 32514051735552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 32514588540928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record007_result⟩)
 (.leaf ⟨(30, 32522637475840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 32522910040064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 32523372462080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record010_result⟩)
 (.leaf ⟨(30, 32524445679616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 32530116968448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 32642900754432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record013_result⟩)
 (.leaf ⟨(30, 32645517934592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 32660080558080), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 32693316222976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record016_result⟩)
 (.leaf ⟨(30, 32693844705280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 32711613907200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 32716951191552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record019_result⟩)
 (.leaf ⟨(30, 32717719207936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 32723390496768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record021_result⟩)
 (.leaf ⟨(30, 32729128239104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 32730201456640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record023_result⟩)
 (.leaf ⟨(30, 32780335513600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00054.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25280 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 25280 25305 :=
  block_of_table results 25280 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0782
