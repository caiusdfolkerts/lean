module
prelude
import GraphInputsRow30Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0732
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 3135617695744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 3140430659584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record001_result⟩)
 (.leaf ⟨(30, 3140438982656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 3149020561408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 3152644440320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record004_result⟩)
 (.leaf ⟨(30, 3153313431552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 3157073657856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 3157610463232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record007_result⟩)
 (.leaf ⟨(30, 3164726165504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 3166806540288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 3200042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record010_result⟩)
 (.leaf ⟨(30, 3208479047936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 3208743224064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 3209015918592), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record013_result⟩)
 (.leaf ⟨(30, 3209024241664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 3217068949760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 3217737940992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record016_result⟩)
 (.leaf ⟨(30, 3225658916864), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 3225931481088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 3226195722240), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record019_result⟩)
 (.leaf ⟨(30, 3232254459904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 3237075746816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record021_result⟩)
 (.leaf ⟨(30, 3240955478784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 3241236496384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record023_result⟩)
 (.leaf ⟨(30, 3243308548096), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(30, 3243316871168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(30, 3249281204480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record026_result⟩)
 (.leaf ⟨(30, 3249818075136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(30, 3249950195712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(30, 3338676502784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record029_result⟩)
 (.leaf ⟨(30, 3377129881856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(30, 3423764250880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 3423772639232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record032_result⟩)
 (.leaf ⟨(30, 3492490018816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(30, 3524702273536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(30, 3527447478272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record035_result⟩)
 (.leaf ⟨(30, 3629920583808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(30, 3647842877440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(30, 3784067809536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record038_result⟩)
 (.leaf ⟨(30, 3786689019904), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(30, 3853839794432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(30, 3853967753472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record041_result⟩)
 (.leaf ⟨(30, 3853971915008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(30, 3853971980288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(30, 3854074646784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record044_result⟩)
 (.leaf ⟨(30, 3861859274768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(30, 3866953257216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record046_result⟩)
 (.leaf ⟨(30, 3921595138304), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(30, 3921599299840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record048_result⟩)
 (.leaf ⟨(30, 3921599365120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00004.record049_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23730 + i))) 0 50 :=
  interval_of_check _ 0 50 (by decide +kernel)

public theorem complete : Block 23730 23780 :=
  block_of_table results 23730 50 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0732
