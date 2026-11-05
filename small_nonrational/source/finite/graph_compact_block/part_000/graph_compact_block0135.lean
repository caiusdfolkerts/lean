module
prelude
import GraphInputsRow24Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0135
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 11422572544000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record000_result⟩)
 (.leaf ⟨(24, 11422576705536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 11422671634432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 11423037014144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record003_result⟩)
 (.leaf ⟨(24, 11431158251648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 11431162445824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 11431261536256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record006_result⟩)
 (.leaf ⟨(24, 11434481188864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 11435521376256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 11444097679616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record009_result⟩)
 (.leaf ⟨(24, 11444097744896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 11444103954560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 11444231946240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record012_result⟩)
 (.leaf ⟨(24, 11444349307136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 11444500316288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 11444500348928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record015_result⟩)
 (.leaf ⟨(24, 11446244179968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 11446301755520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 11446376235264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record018_result⟩)
 (.leaf ⟨(24, 11446376300544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 11446378381312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 11446379421696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record021_result⟩)
 (.leaf ⟨(24, 11446429681920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record022_result⟩))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf ⟨(24, 11446644670592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 11446646751360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record024_result⟩)
 (.leaf ⟨(24, 11446646784000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record025_result⟩)))
 (.branch 27
 (.leaf ⟨(24, 11448650563585), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 11450590431488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record027_result⟩)
 (.leaf ⟨(24, 11450939621504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record028_result⟩))))
 (.branch 32
 (.branch 30
 (.leaf ⟨(24, 11450939654144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 11459180365952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record030_result⟩)
 (.leaf ⟨(24, 11471924904064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record031_result⟩)))
 (.branch 33
 (.leaf ⟨(24, 11471927017472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 11471931048960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record033_result⟩)
 (.leaf ⟨(24, 11472058974848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record034_result⟩)))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf ⟨(24, 11472129229824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 11478859006080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record036_result⟩)
 (.leaf ⟨(24, 11709726081152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(24, 11846896599168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 11958352904448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record039_result⟩)
 (.leaf ⟨(24, 11958352969728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record040_result⟩))))
 (.branch 44
 (.branch 42
 (.leaf ⟨(24, 11958359179392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record041_result⟩)
 (.branch 43
 (.leaf ⟨(24, 11958551150592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record042_result⟩)
 (.leaf ⟨(24, 11958553231360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record043_result⟩)))
 (.branch 45
 (.leaf ⟨(24, 11958604531968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record044_result⟩)
 (.branch 46
 (.leaf ⟨(24, 11958821601408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record045_result⟩)
 (.leaf ⟨(24, 11958821634048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00019.record046_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8757 + i))) 0 47 :=
  interval_of_check _ 0 47 (by decide +kernel)

public theorem complete : Block 8757 8804 :=
  block_of_table results 8757 47 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0135
