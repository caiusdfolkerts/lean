module
prelude
import GraphInputsRow24Part00110Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0226
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27532026019840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record000_result⟩)
 (.leaf ⟨(24, 27532028035328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27532160155904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27532160221184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record003_result⟩)
 (.leaf ⟨(24, 27532424462336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 27532430688320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record005_result⟩)
 (.leaf ⟨(24, 27532497788992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 27533300994304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27535447429376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record008_result⟩)
 (.leaf ⟨(24, 27540745896192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 27566518845696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record010_result⟩)
 (.leaf ⟨(24, 27575104585984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 27597719273728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 27618051162112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record013_result⟩)
 (.leaf ⟨(24, 27618059485184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 27632288665664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record015_result⟩)
 (.leaf ⟨(24, 27636581535808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 27643689844992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 27643689910272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record018_result⟩)
 (.leaf ⟨(24, 27663215427840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 27663223816192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record020_result⟩)
 (.leaf ⟨(24, 27663483830528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 27663494299648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record022_result⟩)
 (.branch 24
 (.leaf ⟨(24, 27663618031872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record023_result⟩)
 (.leaf ⟨(24, 27665163682048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 27665172070400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record025_result⟩)
 (.leaf ⟨(24, 27665295802624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 27665304190976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 27665564205312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record028_result⟩)
 (.leaf ⟨(24, 27665568432128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 27665574674432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record030_result⟩)
 (.leaf ⟨(24, 27665764466944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 27669859156224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 27669867544576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record033_result⟩)
 (.leaf ⟨(24, 27669925216512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(24, 27671536926976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 27672073797632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record036_result⟩)
 (.leaf ⟨(24, 27672082120704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(24, 27674154172416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 27678246715648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record039_result⟩)
 (.leaf ⟨(24, 27678453284864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00110.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11175 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 11175 11216 :=
  block_of_table results 11175 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0226
