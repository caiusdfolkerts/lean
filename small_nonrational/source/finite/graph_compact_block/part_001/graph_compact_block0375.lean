module
prelude
import GraphInputsRow26Part00059Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0375
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 28080790388736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 28080791884032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record001_result⟩)
 (.leaf ⟨(26, 28081054629888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 28081179854864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record003_result⟩)
 (.leaf ⟨(26, 28116143636480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 28152046813184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record005_result⟩)
 (.leaf ⟨(26, 28177428648192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(26, 28177699180608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 28193585102849), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record008_result⟩)
 (.leaf ⟨(26, 28247601512448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 28247609835520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record010_result⟩)
 (.leaf ⟨(26, 28249690210304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 28249880068096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record012_result⟩)
 (.leaf ⟨(26, 28265214411008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(26, 28265985613824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 28266597449728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record015_result⟩)
 (.leaf ⟨(26, 28273804378112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 28273878761472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record017_result⟩)
 (.leaf ⟨(26, 28274341183488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 28282925875200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record019_result⟩)
 (.leaf ⟨(26, 28308666449920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(26, 28391211335680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 28451231776768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record022_result⟩)
 (.leaf ⟨(26, 28451283142656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 28452298752000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record024_result⟩)
 (.leaf ⟨(26, 28452304994304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 28452323330048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record026_result⟩)
 (.leaf ⟨(26, 28458554245376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(26, 28458564454400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 28484518807552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record029_result⟩)
 (.leaf ⟨(26, 28492955781120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(26, 28493484130824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record031_result⟩)
 (.leaf ⟨(26, 28523164139520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record032_result⟩))
 (.branch 34
 (.leaf ⟨(26, 28523213684736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record033_result⟩)
 (.leaf ⟨(26, 28590630584448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 28623963259008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 28623965339776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record036_result⟩)
 (.leaf ⟨(26, 28623966928912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(26, 28623969501312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record038_result⟩)
 (.leaf ⟨(26, 28626251178112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record039_result⟩))
 (.branch 41
 (.leaf ⟨(26, 28636192194688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record040_result⟩)
 (.leaf ⟨(26, 28644513693824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 28716202737792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 28717292339328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record043_result⟩)
 (.leaf ⟨(26, 28717294452736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 28717298484224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record045_result⟩)
 (.leaf ⟨(26, 28764811624448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 28773397364736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record047_result⟩)
 (.leaf ⟨(26, 28781718962176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(26, 28796163473536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record049_result⟩)
 (.branch 51
 (.leaf ⟨(26, 28830106585088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record050_result⟩)
 (.leaf ⟨(26, 28845069699200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 28864483999760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record052_result⟩)
 (.leaf ⟨(26, 28865508425856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 28865572405376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record054_result⟩)
 (.leaf ⟨(26, 28865574486144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00059.record055_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16963 + i))) 0 56 :=
  interval_of_check _ 0 56 (by decide +kernel)

public theorem complete : Block 16963 17019 :=
  block_of_table results 16963 56 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0375
