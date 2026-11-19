module
prelude
import GraphInputsRow24Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0161
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 18954497048832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record000_result⟩)
 (.leaf ⟨(24, 18955976638720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 18956249268224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record002_result⟩)
 (.leaf ⟨(24, 18956513509376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 18956521832448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record004_result⟩)
 (.leaf ⟨(24, 18956645629952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 18956786073600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record006_result⟩)
 (.leaf ⟨(24, 18960806379520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 18960814702592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record008_result⟩)
 (.leaf ⟨(24, 18962349883648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 18962886754304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record010_result⟩)
 (.leaf ⟨(24, 18962895077376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 18974262722816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record012_result⟩)
 (.leaf ⟨(24, 19006515872000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 19014503899200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record014_result⟩)
 (.leaf ⟨(24, 19023695740928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 19038728126720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record016_result⟩)
 (.leaf ⟨(24, 19041947779328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 19059028557824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record018_result⟩)
 (.leaf ⟨(24, 19059127648256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 19071963791616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record020_result⟩)
 (.leaf ⟨(24, 19072483854464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 19074506588416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record022_result⟩)
 (.leaf ⟨(24, 19076504158464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 19076512546816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record024_result⟩)
 (.leaf ⟨(24, 19080797028608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 19080805416960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record026_result⟩)
 (.leaf ⟨(24, 19083346067712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 19087046477952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record028_result⟩)
 (.leaf ⟨(24, 19089386930432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 19089391157248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 19089397399552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record031_result⟩)
 (.leaf ⟨(24, 19093419884544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00045.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9599 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 9599 9632 :=
  block_of_table results 9599 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0161
