module
prelude
import GraphInputsRow19Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0063
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 24616674788608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record000_result⟩)
 (.leaf ⟨(19, 24616680706048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 24616716206081), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record002_result⟩)
 (.branch 4
 (.leaf ⟨(19, 24617143501888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record003_result⟩)
 (.leaf ⟨(19, 24621319987264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(19, 24621321043968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record005_result⟩)
 (.leaf ⟨(19, 24627395960896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record006_result⟩))
 (.branch 8
 (.leaf ⟨(19, 24627427950656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record007_result⟩)
 (.branch 9
 (.leaf ⟨(19, 24627428991040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record008_result⟩)
 (.leaf ⟨(19, 24627429007360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(19, 24629525766144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record010_result⟩)
 (.leaf ⟨(19, 24629559316480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record011_result⟩))
 (.branch 13
 (.leaf ⟨(19, 24711299923968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 24778954080256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record013_result⟩)
 (.leaf ⟨(19, 24779012768516), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(19, 24779152195840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 24822261252352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record016_result⟩)
 (.leaf ⟨(19, 24822272761856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(19, 24838106783744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 24845718978816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record019_result⟩)
 (.leaf ⟨(19, 24845727367168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record020_result⟩))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 24849351180289), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record021_result⟩)
 (.leaf ⟨(19, 24849351184384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 24850424922112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record023_result⟩)
 (.branch 25
 (.leaf ⟨(19, 24851968491520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record024_result⟩)
 (.leaf ⟨(19, 24852166672384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record025_result⟩))))
 (.branch 29
 (.branch 27
 (.leaf ⟨(19, 24852360626432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record026_result⟩)
 (.branch 28
 (.leaf ⟨(19, 24853231501568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record027_result⟩)
 (.leaf ⟨(19, 24855580279040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(19, 24857161040128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record029_result⟩)
 (.branch 31
 (.leaf ⟨(19, 24857433669632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record030_result⟩)
 (.leaf ⟨(19, 24857697910784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record031_result⟩)))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf ⟨(19, 24857706233856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record032_result⟩)
 (.leaf ⟨(19, 24857929121792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record033_result⟩))
 (.branch 35
 (.leaf ⟨(19, 24860686352384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 24869003624704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record035_result⟩)
 (.leaf ⟨(19, 24869139972096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record036_result⟩))))
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 24869148295168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 24870043812096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record038_result⟩)
 (.leaf ⟨(19, 24870180159488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 24870188482560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 24870411370496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record041_result⟩)
 (.leaf ⟨(19, 24870948175872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record042_result⟩)))))))
 (.branch 64
 (.branch 53
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf ⟨(19, 24903336222720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record043_result⟩)
 (.leaf ⟨(19, 24933572804608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record044_result⟩))
 (.branch 46
 (.leaf ⟨(19, 24934604668928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record045_result⟩)
 (.branch 47
 (.leaf ⟨(19, 24934612992000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record046_result⟩)
 (.leaf ⟨(19, 24946404262144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record047_result⟩))))
 (.branch 50
 (.branch 49
 (.leaf ⟨(19, 24965776736256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record048_result⟩)
 (.leaf ⟨(19, 24966696304896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record049_result⟩))
 (.branch 51
 (.leaf ⟨(19, 24966700531712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 24966707814400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record051_result⟩)
 (.leaf ⟨(19, 24966939025408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record052_result⟩)))))
 (.branch 58
 (.branch 55
 (.branch 54
 (.leaf ⟨(19, 24966955540480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record053_result⟩)
 (.leaf ⟨(19, 24967790133248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record054_result⟩))
 (.branch 56
 (.leaf ⟨(19, 24967995596800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record055_result⟩)
 (.branch 57
 (.leaf ⟨(19, 24981832532224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record056_result⟩)
 (.leaf ⟨(19, 24981840920576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record057_result⟩))))
 (.branch 61
 (.branch 59
 (.leaf ⟨(19, 25003420745728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record058_result⟩)
 (.branch 60
 (.leaf ⟨(19, 25003429068800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record059_result⟩)
 (.leaf ⟨(19, 25028017029376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record060_result⟩)))
 (.branch 62
 (.leaf ⟨(19, 25053959880704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record061_result⟩)
 (.branch 63
 (.leaf ⟨(19, 25117260253440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record062_result⟩)
 (.leaf ⟨(19, 25119407800320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record063_result⟩))))))
 (.branch 75
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf ⟨(19, 25121536477440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record064_result⟩)
 (.leaf ⟨(19, 25125697227008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record065_result⟩))
 (.branch 67
 (.leaf ⟨(19, 25129190948864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record066_result⟩)
 (.branch 68
 (.leaf ⟨(19, 25151622361152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record067_result⟩)
 (.leaf ⟨(19, 25152471599360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record068_result⟩))))
 (.branch 72
 (.branch 70
 (.leaf ⟨(19, 25152473729088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record069_result⟩)
 (.branch 71
 (.leaf ⟨(19, 25152477890624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record070_result⟩)
 (.leaf ⟨(19, 25152490373696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record071_result⟩)))
 (.branch 73
 (.leaf ⟨(19, 25153511786752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record072_result⟩)
 (.branch 74
 (.leaf ⟨(19, 25153752944648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record073_result⟩)
 (.leaf ⟨(19, 25157972820224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record074_result⟩)))))
 (.branch 80
 (.branch 77
 (.branch 76
 (.leaf ⟨(19, 25159994069000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record075_result⟩)
 (.leaf ⟨(19, 25177115746304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record076_result⟩))
 (.branch 78
 (.leaf ⟨(19, 25177116266496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record077_result⟩)
 (.branch 79
 (.leaf ⟨(19, 25177116640320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record078_result⟩)
 (.leaf ⟨(19, 25177166185536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record079_result⟩))))
 (.branch 83
 (.branch 81
 (.leaf ⟨(19, 25177184796673), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record080_result⟩)
 (.branch 82
 (.leaf ⟨(19, 25185841611008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record081_result⟩)
 (.leaf ⟨(19, 25191262519296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(19, 25256710438912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record083_result⟩)
 (.branch 85
 (.leaf ⟨(19, 25256718761984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record084_result⟩)
 (.leaf ⟨(19, 25260871188480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00023.record085_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4356 + i))) 0 86 :=
  interval_of_check _ 0 86 (by decide +kernel)

public theorem complete : Block 4356 4442 :=
  block_of_table results 4356 86 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0063
