module
prelude
import GraphInputsRow26Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0316
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 114426986880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 247306748160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record001_result⟩)
 (.leaf ⟨(26, 255764529408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 256165052672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 256165117952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record004_result⟩)
 (.leaf ⟨(26, 256293011712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 256301400064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 264354431232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record007_result⟩)
 (.leaf ⟨(26, 264482390272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 264486551808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record009_result⟩)
 (.leaf ⟨(26, 264486617088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 265015034112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record011_result⟩)
 (.leaf ⟨(26, 265019260928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(26, 265027584000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 268647301376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record014_result⟩)
 (.leaf ⟨(26, 384741507328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(26, 389036458240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 476945875200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record017_result⟩)
 (.leaf ⟨(26, 589830390144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(26, 662844834048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 665329893632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record020_result⟩)
 (.leaf ⟨(26, 665329958912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 665589973248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record022_result⟩)
 (.leaf ⟨(26, 665598361600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 680020476160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record024_result⟩)
 (.leaf ⟨(26, 680024637696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(26, 680024702976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record026_result⟩)
 (.branch 28
 (.leaf ⟨(26, 680553120000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record027_result⟩)
 (.leaf ⟨(26, 680557346816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(26, 680565669888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 736127648000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record030_result⟩)
 (.leaf ⟨(26, 736127713280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(26, 736255607040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 736263995392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record033_result⟩)
 (.leaf ⟨(26, 737295794432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(26, 737304182784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record035_result⟩)
 (.leaf ⟨(26, 742368837632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record036_result⟩))
 (.branch 38
 (.leaf ⟨(26, 742897254656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record037_result⟩)
 (.leaf ⟨(26, 742901481472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record038_result⟩)))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 744317026560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 744317091840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record040_result⟩)
 (.leaf ⟨(26, 744977629440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 744981856256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 744990179328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record043_result⟩)
 (.leaf ⟨(26, 746017816832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record044_result⟩))))
 (.branch 48
 (.branch 46
 (.leaf ⟨(26, 748609896704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record045_result⟩)
 (.branch 47
 (.leaf ⟨(26, 751726297344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record046_result⟩)
 (.leaf ⟨(26, 751730524160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 751792357632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record048_result⟩)
 (.leaf ⟨(26, 751796519168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 751796584448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record050_result⟩)
 (.leaf ⟨(26, 751829549312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00000.record051_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14016 + i))) 0 52 :=
  interval_of_check _ 0 52 (by decide +kernel)

public theorem complete : Block 14016 14068 :=
  block_of_table results 14016 52 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0316
