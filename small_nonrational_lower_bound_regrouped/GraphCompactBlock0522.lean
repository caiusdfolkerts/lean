module
prelude
import GraphInputsRow29Part00088Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0522
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 15312363716608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record000_result⟩)
 (.leaf ⟨(29, 15320685215744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 15326867685376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 15335725989888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record003_result⟩)
 (.leaf ⟨(29, 15344047489024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 15350288613376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 15394526543904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record006_result⟩)
 (.leaf ⟨(29, 15399114514560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 15403138949376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 15403407384704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record009_result⟩)
 (.leaf ⟨(29, 15411993124992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 15437792313600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record011_result⟩)
 (.leaf ⟨(29, 15446113812736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 15446382248064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 15471034769536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record014_result⟩)
 (.leaf ⟨(29, 15472091340928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(29, 15535190843648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 15550533615744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record017_result⟩)
 (.leaf ⟨(29, 15576506368000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(29, 15613012541440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 15672633462816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record020_result⟩)
 (.leaf ⟨(29, 15677190574112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00088.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21742 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 21742 21764 :=
  block_of_table results 21742 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0522
