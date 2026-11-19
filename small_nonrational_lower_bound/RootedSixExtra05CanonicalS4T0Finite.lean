module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import IntegerTables
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
open ConcreteGrowth
abbrev blockCount : Nat := 87
noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩
cert_root_6 05
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨0, 4, 12816, 12816, 361617201270, 215026792020⟩, 87))
 (.leaf (⟨1, 4, 12816, 12816, 361617786720, 288326448720⟩, 23)))
 (.branch 3
 (.leaf (⟨1, 4, 12816, 12816, 361616738145, 288326448645⟩, 39))
 (.branch 4
 (.leaf (⟨1, 4, 12816, 12816, 361599960930, 288326447205⟩, 49))
 (.leaf (⟨1, 4, 12816, 12816, 361331525475, 288326420325⟩, 69)))))
 (.branch 7
 (.branch 6
 (.leaf (⟨1, 4, 12816, 12816, 357036558180, 288325928805⟩, 79))
 (.leaf (⟨1, 4, 12816, 12816, 288317081445, 288317081445⟩, 83)))
 (.branch 8
 (.leaf (⟨1, 4, 12801, 12801, 361617786720, 288326448720⟩, 23))
 (.branch 9
 (.leaf (⟨1, 4, 12801, 12801, 361616738145, 288326448645⟩, 39))
 (.leaf (⟨1, 4, 12801, 12801, 361599960930, 288326447205⟩, 49))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (⟨1, 4, 12801, 12801, 361331525475, 288326420325⟩, 69))
 (.leaf (⟨1, 4, 12801, 12801, 357036558180, 288325928805⟩, 79)))
 (.branch 13
 (.leaf (⟨1, 4, 12801, 12801, 288317081445, 288317081445⟩, 83))
 (.branch 14
 (.leaf (⟨2, 4, 12816, 12816, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 12816, 12816, 361609328160, 361626104160⟩, 720907)))))
 (.branch 18
 (.branch 16
 (.leaf (⟨2, 4, 12816, 12816, 361592550945, 361626104070⟩, 1769499))
 (.branch 17
 (.leaf (⟨2, 4, 12816, 12816, 361340892720, 361626081120⟩, 1114129))
 (.leaf (⟨2, 4, 12816, 12816, 357029148225, 361625650950⟩, 2162721))))
 (.branch 19
 (.leaf (⟨2, 4, 12816, 12816, 352465745475, 361625618550⟩, 3735609))
 (.branch 20
 (.leaf (⟨2, 4, 12816, 12816, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 12816, 12816, 283746268755, 361617754230⟩, 4128831)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 12816, 12816, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨1, 4, 12546, 12321, 361617786720, 288326448720⟩, 23)))
 (.branch 24
 (.leaf (⟨1, 4, 12546, 12321, 361616738145, 288326448645⟩, 39))
 (.branch 25
 (.leaf (⟨1, 4, 12546, 12321, 361599960930, 288326447205⟩, 49))
 (.leaf (⟨1, 4, 12546, 12321, 361331525475, 288326420325⟩, 69)))))
 (.branch 29
 (.branch 27
 (.leaf (⟨1, 4, 12546, 12321, 357036558180, 288325928805⟩, 79))
 (.branch 28
 (.leaf (⟨1, 4, 12546, 12321, 288317081445, 288317081445⟩, 83))
 (.leaf (⟨2, 4, 12576, 12576, 361626105360, 361626105360⟩, 327685))))
 (.branch 30
 (.leaf (⟨2, 4, 12576, 12576, 361609328160, 361626104160⟩, 720907))
 (.branch 31
 (.leaf (⟨2, 4, 12576, 12576, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 12576, 12576, 361340892720, 361626081120⟩, 1114129))))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 12576, 12576, 357029148225, 361625650950⟩, 2162721))
 (.leaf (⟨2, 4, 12576, 12576, 352465745475, 361625618550⟩, 3735609)))
 (.branch 35
 (.leaf (⟨2, 4, 12576, 12576, 288041236050, 361617784950⟩, 2818091))
 (.branch 36
 (.leaf (⟨2, 4, 12576, 12576, 283746268755, 361617754230⟩, 4128831))
 (.leaf (⟨2, 4, 12576, 12576, 215026792020, 361617201270⟩, 4784201)))))
 (.branch 40
 (.branch 38
 (.leaf (⟨2, 4, 12321, 12546, 361626105360, 361626105360⟩, 327685))
 (.branch 39
 (.leaf (⟨2, 4, 12321, 12546, 361609328160, 361626104160⟩, 720907))
 (.leaf (⟨2, 4, 12321, 12546, 361592550945, 361626104070⟩, 1769499))))
 (.branch 41
 (.leaf (⟨2, 4, 12321, 12546, 361340892720, 361626081120⟩, 1114129))
 (.branch 42
 (.leaf (⟨2, 4, 12321, 12546, 357029148225, 361625650950⟩, 2162721))
 (.leaf (⟨2, 4, 12321, 12546, 352465745475, 361625618550⟩, 3735609))))))))
 (.branch 65
 (.branch 54
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf (⟨2, 4, 12321, 12546, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 12321, 12546, 283746268755, 361617754230⟩, 4128831)))
 (.branch 46
 (.leaf (⟨2, 4, 12321, 12546, 215026792020, 361617201270⟩, 4784201))
 (.branch 47
 (.leaf (⟨3, 4, 12816, 12816, 361742426640, 434925761040⟩, 1208944266640182156001281))
 (.leaf (⟨3, 4, 12816, 12816, 141893788995, 434917935495⟩, 64074046131929654268067893)))))
 (.branch 51
 (.branch 49
 (.leaf (⟨1, 4, 8451, 801, 361617786720, 288326448720⟩, 23))
 (.branch 50
 (.leaf (⟨1, 4, 8451, 801, 361616738145, 288326448645⟩, 39))
 (.leaf (⟨1, 4, 8451, 801, 361599960930, 288326447205⟩, 49))))
 (.branch 52
 (.leaf (⟨1, 4, 8451, 801, 361331525475, 288326420325⟩, 69))
 (.branch 53
 (.leaf (⟨1, 4, 8451, 801, 357036558180, 288325928805⟩, 79))
 (.leaf (⟨1, 4, 8451, 801, 288317081445, 288317081445⟩, 83))))))
 (.branch 59
 (.branch 56
 (.branch 55
 (.leaf (⟨2, 4, 8496, 4896, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 8496, 4896, 361609328160, 361626104160⟩, 720907)))
 (.branch 57
 (.leaf (⟨2, 4, 8496, 4896, 361592550945, 361626104070⟩, 1769499))
 (.branch 58
 (.leaf (⟨2, 4, 8496, 4896, 361340892720, 361626081120⟩, 1114129))
 (.leaf (⟨2, 4, 8496, 4896, 357029148225, 361625650950⟩, 2162721)))))
 (.branch 62
 (.branch 60
 (.leaf (⟨2, 4, 8496, 4896, 352465745475, 361625618550⟩, 3735609))
 (.branch 61
 (.leaf (⟨2, 4, 8496, 4896, 288041236050, 361617784950⟩, 2818091))
 (.leaf (⟨2, 4, 8496, 4896, 283746268755, 361617754230⟩, 4128831))))
 (.branch 63
 (.leaf (⟨2, 4, 8496, 4896, 215026792020, 361617201270⟩, 4784201))
 (.branch 64
 (.leaf (⟨2, 4, 8241, 4866, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 8241, 4866, 361609328160, 361626104160⟩, 720907)))))))
 (.branch 76
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 4, 8241, 4866, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 8241, 4866, 361340892720, 361626081120⟩, 1114129)))
 (.branch 68
 (.leaf (⟨2, 4, 8241, 4866, 357029148225, 361625650950⟩, 2162721))
 (.branch 69
 (.leaf (⟨2, 4, 8241, 4866, 352465745475, 361625618550⟩, 3735609))
 (.leaf (⟨2, 4, 8241, 4866, 288041236050, 361617784950⟩, 2818091)))))
 (.branch 73
 (.branch 71
 (.leaf (⟨2, 4, 8241, 4866, 283746268755, 361617754230⟩, 4128831))
 (.branch 72
 (.leaf (⟨2, 4, 8241, 4866, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨3, 4, 8976, 8976, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 74
 (.leaf (⟨3, 4, 8976, 8976, 141893788995, 434917935495⟩, 64074046131929654268067893))
 (.branch 75
 (.leaf (⟨2, 4, 4146, 4146, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 4146, 4146, 361609328160, 361626104160⟩, 720907))))))
 (.branch 81
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 4146, 4146, 361592550945, 361626104070⟩, 1769499))
 (.leaf (⟨2, 4, 4146, 4146, 361340892720, 361626081120⟩, 1114129)))
 (.branch 79
 (.leaf (⟨2, 4, 4146, 4146, 357029148225, 361625650950⟩, 2162721))
 (.branch 80
 (.leaf (⟨2, 4, 4146, 4146, 352465745475, 361625618550⟩, 3735609))
 (.leaf (⟨2, 4, 4146, 4146, 288041236050, 361617784950⟩, 2818091)))))
 (.branch 84
 (.branch 82
 (.leaf (⟨2, 4, 4146, 4146, 283746268755, 361617754230⟩, 4128831))
 (.branch 83
 (.leaf (⟨2, 4, 4146, 4146, 215026792020, 361617201270⟩, 4784201))
 (.leaf (⟨3, 4, 4896, 8496, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 85
 (.leaf (⟨3, 4, 4896, 8496, 141893788995, 434917935495⟩, 64074046131929654268067893))
 (.branch 86
 (.leaf (⟨3, 4, 801, 8451, 361742426640, 434925761040⟩, 1208944266640182156001281))
 (.leaf (⟨3, 4, 801, 8451, 141893788995, 434917935495⟩, 64074046131929654268067893)))))))))
cert_raw_4
cert_witness_4 2170
cert_faceTable_4 173
cert_faceWitness_4
cert_validity_4 4
cert_placement_4 4 05
cert_test_10
cert_symmetry_4 05
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
cert_check_4 0000 0000 0 0 1 1
cert_block_8 0000 0 1
cert_check_4 0001 0000 1 0 1 1
cert_block_8 0001 1 1
cert_check_4 0002 0000 2 0 1 1
cert_block_8 0002 2 1
cert_check_4 0003 0000 3 0 1 1
cert_block_8 0003 3 1
cert_check_4 0004 0000 4 0 1 1
cert_block_8 0004 4 1
cert_check_4 0005 0000 5 0 1 1
cert_block_8 0005 5 1
cert_check_4 0006 0000 6 0 1 1
cert_block_8 0006 6 1
cert_check_4 0007 0000 7 0 1 1
cert_block_8 0007 7 1
cert_check_4 0008 0000 8 0 1 1
cert_block_8 0008 8 1
cert_check_4 0009 0000 9 0 1 1
cert_block_8 0009 9 1
cert_check_4 0010 0000 10 0 1 1
cert_block_8 0010 10 1
cert_check_4 0011 0000 11 0 1 1
cert_block_8 0011 11 1
cert_check_4 0012 0000 12 0 1 1
cert_block_8 0012 12 1
cert_check_4 0013 0000 13 0 2 2
cert_block_8 0013 13 2
cert_check_4 0014 0000 14 0 2 2
cert_block_8 0014 14 2
cert_check_4 0015 0000 15 0 2 2
cert_block_8 0015 15 2
cert_check_4 0016 0000 16 0 2 2
cert_block_8 0016 16 2
cert_check_4 0017 0000 17 0 2 2
cert_block_8 0017 17 2
cert_check_4 0018 0000 18 0 2 2
cert_block_8 0018 18 2
cert_check_4 0019 0000 19 0 2 2
cert_block_8 0019 19 2
cert_check_4 0020 0000 20 0 2 2
cert_block_8 0020 20 2
cert_check_4 0021 0000 21 0 2 2
cert_block_8 0021 21 2
cert_check_4 0022 0000 22 0 1 1
cert_block_8 0022 22 1
cert_check_4 0023 0000 23 0 1 1
cert_block_8 0023 23 1
cert_check_4 0024 0000 24 0 1 1
cert_block_8 0024 24 1
cert_check_4 0025 0000 25 0 1 1
cert_block_8 0025 25 1
cert_check_4 0026 0000 26 0 1 1
cert_block_8 0026 26 1
cert_check_4 0027 0000 27 0 1 1
cert_block_8 0027 27 1
cert_check_4 0028 0000 28 0 2 2
cert_block_8 0028 28 2
cert_check_4 0029 0000 29 0 2 2
cert_block_8 0029 29 2
cert_check_4 0030 0000 30 0 2 2
cert_block_8 0030 30 2
cert_check_4 0031 0000 31 0 2 2
cert_block_8 0031 31 2
cert_check_4 0032 0000 32 0 2 2
cert_block_8 0032 32 2
cert_check_4 0033 0000 33 0 2 2
cert_block_8 0033 33 2
cert_check_4 0034 0000 34 0 2 2
cert_block_8 0034 34 2
cert_check_4 0035 0000 35 0 2 2
cert_block_8 0035 35 2
cert_check_4 0036 0000 36 0 2 2
cert_block_8 0036 36 2
cert_check_4 0037 0000 37 0 2 2
cert_block_8 0037 37 2
cert_check_4 0038 0000 38 0 2 2
cert_block_8 0038 38 2
cert_check_4 0039 0000 39 0 2 2
cert_block_8 0039 39 2
cert_check_4 0040 0000 40 0 2 2
cert_block_8 0040 40 2
cert_check_4 0041 0000 41 0 2 2
cert_block_8 0041 41 2
cert_check_4 0042 0000 42 0 2 2
cert_block_8 0042 42 2
cert_check_4 0043 0000 43 0 2 2
cert_block_8 0043 43 2
cert_check_4 0044 0000 44 0 2 2
cert_block_8 0044 44 2
cert_check_4 0045 0000 45 0 2 2
cert_block_8 0045 45 2
cert_check_4 0046 0000 46 0 6 6
cert_block_8 0046 46 6
cert_check_4 0047 0000 47 0 6 6
cert_block_8 0047 47 6
cert_check_4 0048 0000 48 0 1 1
cert_block_8 0048 48 1
cert_check_4 0049 0000 49 0 1 1
cert_block_8 0049 49 1
cert_check_4 0050 0000 50 0 1 1
cert_block_8 0050 50 1
cert_check_4 0051 0000 51 0 1 1
cert_block_8 0051 51 1
cert_check_4 0052 0000 52 0 1 1
cert_block_8 0052 52 1
cert_check_4 0053 0000 53 0 1 1
cert_block_8 0053 53 1
cert_check_4 0054 0000 54 0 2 2
cert_block_8 0054 54 2
cert_check_4 0055 0000 55 0 2 2
cert_block_8 0055 55 2
cert_check_4 0056 0000 56 0 2 2
cert_block_8 0056 56 2
cert_check_4 0057 0000 57 0 2 2
cert_block_8 0057 57 2
cert_check_4 0058 0000 58 0 2 2
cert_block_8 0058 58 2
cert_check_4 0059 0000 59 0 2 2
cert_block_8 0059 59 2
cert_check_4 0060 0000 60 0 2 2
cert_block_8 0060 60 2
cert_check_4 0061 0000 61 0 2 2
cert_block_8 0061 61 2
cert_check_4 0062 0000 62 0 2 2
cert_block_8 0062 62 2
cert_check_4 0063 0000 63 0 2 2
cert_block_8 0063 63 2
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
cert_check_4 0064 0000 64 0 2 2
cert_block_8 0064 64 2
cert_check_4 0065 0000 65 0 2 2
cert_block_8 0065 65 2
cert_check_4 0066 0000 66 0 2 2
cert_block_8 0066 66 2
cert_check_4 0067 0000 67 0 2 2
cert_block_8 0067 67 2
cert_check_4 0068 0000 68 0 2 2
cert_block_8 0068 68 2
cert_check_4 0069 0000 69 0 2 2
cert_block_8 0069 69 2
cert_check_4 0070 0000 70 0 2 2
cert_block_8 0070 70 2
cert_check_4 0071 0000 71 0 2 2
cert_block_8 0071 71 2
cert_check_4 0072 0000 72 0 6 6
cert_block_8 0072 72 6
cert_check_4 0073 0000 73 0 6 6
cert_block_8 0073 73 6
cert_check_4 0074 0000 74 0 2 2
cert_block_8 0074 74 2
cert_check_4 0075 0000 75 0 2 2
cert_block_8 0075 75 2
cert_check_4 0076 0000 76 0 2 2
cert_block_8 0076 76 2
cert_check_4 0077 0000 77 0 2 2
cert_block_8 0077 77 2
cert_check_4 0078 0000 78 0 2 2
cert_block_8 0078 78 2
cert_check_4 0079 0000 79 0 2 2
cert_block_8 0079 79 2
cert_check_4 0080 0000 80 0 2 2
cert_block_8 0080 80 2
cert_check_4 0081 0000 81 0 2 2
cert_block_8 0081 81 2
cert_check_4 0082 0000 82 0 2 2
cert_block_8 0082 82 2
cert_check_4 0083 0000 83 0 6 6
cert_block_8 0083 83 6
cert_check_4 0084 0000 84 0 6 6
cert_block_8 0084 84 6
cert_check_4 0085 0000 85 0 6 6
cert_block_8 0085 85 6
cert_check_4 0086 0000 86 0 6 6
cert_block_8 0086 86 6
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
cert_metadata_validity_12 0000 0 16 16
cert_metadata_validity_12 0016 16 32 16
cert_metadata_validity_12 0032 32 48 16
cert_metadata_validity_12 0048 48 64 16
cert_metadata_validity_12 0064 64 80 16
cert_metadata_validity_12 0080 80 87 7
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 87
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 64 87
  metadata_validity_0048
  (FiniteChecks.interval_append (validity) 64 80 87
  metadata_validity_0064
  metadata_validity_0080)))
cert_metadata_symmetry_13 0000 0 16 16
cert_metadata_symmetry_13 0016 16 32 16
cert_metadata_symmetry_13 0032 32 48 16
cert_metadata_symmetry_13 0048 48 64 16
cert_metadata_symmetry_13 0064 64 80 16
cert_metadata_symmetry_13 0080 80 87 7
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 87
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 64 87
  metadata_symmetry_0048
  (FiniteChecks.interval_append (symmetry) 64 80 87
  metadata_symmetry_0064
  metadata_symmetry_0080)))
cert_metadata_normalizers_4 4
cert_metadata_root_4
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.S4T0
