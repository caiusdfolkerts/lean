module
prelude
import GraphInputsRow24Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0169
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 19740015724544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record000_result⟩)
 (.leaf ⟨(24, 19740228599808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 19740279965696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 19742219830016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record003_result⟩)
 (.leaf ⟨(24, 19742622483008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 19831283859584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 19835444609152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record006_result⟩)
 (.leaf ⟨(24, 19844030349440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 19878389039232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 19908861657088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record009_result⟩)
 (.leaf ⟨(24, 19917042647296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 19917051035648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record011_result⟩)
 (.leaf ⟨(24, 19917174767872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 19917178994688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 19917183156224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record014_result⟩)
 (.leaf ⟨(24, 19917249216512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 19917443203200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 19917643464832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record017_result⟩)
 (.leaf ⟨(24, 19921343905792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 19938725150752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 19947106418816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record020_result⟩)
 (.leaf ⟨(24, 19974158565632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 19985768415232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record022_result⟩)
 (.leaf ⟨(24, 20000800801024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 20017980669952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 20034036465920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record025_result⟩)
 (.leaf ⟨(24, 20034556528768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(24, 20036636903552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 20042878091264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record028_result⟩)
 (.leaf ⟨(24, 20047435202560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(24, 20047443525632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 20047707766784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record031_result⟩)
 (.leaf ⟨(24, 20049119152256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 20062129946624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record033_result⟩)
 (.leaf ⟨(24, 20106027499648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 20123198980224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 20123203174400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record036_result⟩)
 (.leaf ⟨(24, 20130682667008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(24, 20138235560192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 20138239754368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record039_result⟩)
 (.leaf ⟨(24, 20140381995264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(24, 20141459406976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record041_result⟩)
 (.branch 43
 (.leaf ⟨(24, 20144674865408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record042_result⟩)
 (.leaf ⟨(24, 20149950251008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00053.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9814 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 9814 9858 :=
  block_of_table results 9814 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0169
