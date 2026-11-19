module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import IntegerTables
public import RootedSixExtra06
public import RawKindedFacePlacement
public import RootedSixExtra06OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
open ConcreteGrowth
abbrev blockCount : Nat := 105
noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩
cert_root_6 06
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 52
 (.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, 4, 12816, 12816, 361617201270, 215026792020⟩, 105))
 (.branch 2
 (.leaf (⟨1, 4, 12816, 12816, 361617786720, 288326448720⟩, 27))
 (.leaf (⟨1, 4, 12816, 12816, 361616738145, 288326448645⟩, 47))))
 (.branch 4
 (.leaf (⟨1, 4, 12816, 12816, 361599960930, 288326447205⟩, 77))
 (.branch 5
 (.leaf (⟨1, 4, 12816, 12816, 361331525475, 288326420325⟩, 87))
 (.leaf (⟨1, 4, 12816, 12816, 357036558180, 288325928805⟩, 97)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨1, 4, 12816, 12816, 288317081445, 288317081445⟩, 101))
 (.branch 8
 (.leaf (⟨1, 4, 12801, 12801, 361617786720, 288326448720⟩, 27))
 (.leaf (⟨1, 4, 12801, 12801, 361616738145, 288326448645⟩, 47))))
 (.branch 11
 (.branch 10
 (.leaf (⟨1, 4, 12801, 12801, 361599960930, 288326447205⟩, 77))
 (.leaf (⟨1, 4, 12801, 12801, 361331525475, 288326420325⟩, 87)))
 (.branch 12
 (.leaf (⟨1, 4, 12801, 12801, 357036558180, 288325928805⟩, 97))
 (.leaf (⟨1, 4, 12801, 12801, 288317081445, 288317081445⟩, 101))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨2, 4, 12816, 12816, 361626105360, 361626105360⟩, 327685))
 (.branch 15
 (.leaf (⟨2, 4, 12816, 12816, 361609328160, 361626104160⟩, 983055))
 (.leaf (⟨2, 4, 12816, 12816, 361592550945, 361626104070⟩, 2293795))))
 (.branch 17
 (.leaf (⟨2, 4, 12816, 12816, 361324115505, 361626081030⟩, 2687017))
 (.branch 18
 (.leaf (⟨2, 4, 12816, 12816, 361055680050, 361626079350⟩, 3604535))
 (.leaf (⟨2, 4, 12816, 12816, 356760712770, 361625649270⟩, 4259905)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨2, 4, 12816, 12816, 352465745475, 361625618550⟩, 5308497))
 (.branch 21
 (.leaf (⟨2, 4, 12816, 12816, 288326448720, 361617786720⟩, 1376277))
 (.leaf (⟨2, 4, 12816, 12816, 288041236050, 361617784950⟩, 4653127))))
 (.branch 24
 (.branch 23
 (.leaf (⟨2, 4, 12816, 12816, 215026792020, 361617201270⟩, 5963867))
 (.leaf (⟨1, 4, 12546, 12321, 361617786720, 288326448720⟩, 27)))
 (.branch 25
 (.leaf (⟨1, 4, 12546, 12321, 361616738145, 288326448645⟩, 47))
 (.leaf (⟨1, 4, 12546, 12321, 361599960930, 288326447205⟩, 77)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (⟨1, 4, 12546, 12321, 361331525475, 288326420325⟩, 87))
 (.branch 28
 (.leaf (⟨1, 4, 12546, 12321, 357036558180, 288325928805⟩, 97))
 (.leaf (⟨1, 4, 12546, 12321, 288317081445, 288317081445⟩, 101))))
 (.branch 30
 (.leaf (⟨2, 4, 12576, 12576, 361626105360, 361626105360⟩, 327685))
 (.branch 31
 (.leaf (⟨2, 4, 12576, 12576, 361609328160, 361626104160⟩, 983055))
 (.leaf (⟨2, 4, 12576, 12576, 361592550945, 361626104070⟩, 2293795)))))
 (.branch 35
 (.branch 33
 (.leaf (⟨2, 4, 12576, 12576, 361324115505, 361626081030⟩, 2687017))
 (.branch 34
 (.leaf (⟨2, 4, 12576, 12576, 361055680050, 361626079350⟩, 3604535))
 (.leaf (⟨2, 4, 12576, 12576, 356760712770, 361625649270⟩, 4259905))))
 (.branch 37
 (.branch 36
 (.leaf (⟨2, 4, 12576, 12576, 352465745475, 361625618550⟩, 5308497))
 (.leaf (⟨2, 4, 12576, 12576, 288326448720, 361617786720⟩, 1376277)))
 (.branch 38
 (.leaf (⟨2, 4, 12576, 12576, 288041236050, 361617784950⟩, 4653127))
 (.leaf (⟨2, 4, 12576, 12576, 215026792020, 361617201270⟩, 5963867))))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf (⟨2, 4, 12321, 12546, 361626105360, 361626105360⟩, 327685))
 (.branch 41
 (.leaf (⟨2, 4, 12321, 12546, 361609328160, 361626104160⟩, 983055))
 (.leaf (⟨2, 4, 12321, 12546, 361592550945, 361626104070⟩, 2293795))))
 (.branch 43
 (.leaf (⟨2, 4, 12321, 12546, 361324115505, 361626081030⟩, 2687017))
 (.branch 44
 (.leaf (⟨2, 4, 12321, 12546, 361055680050, 361626079350⟩, 3604535))
 (.leaf (⟨2, 4, 12321, 12546, 356760712770, 361625649270⟩, 4259905)))))
 (.branch 48
 (.branch 46
 (.leaf (⟨2, 4, 12321, 12546, 352465745475, 361625618550⟩, 5308497))
 (.branch 47
 (.leaf (⟨2, 4, 12321, 12546, 288326448720, 361617786720⟩, 1376277))
 (.leaf (⟨2, 4, 12321, 12546, 288041236050, 361617784950⟩, 4653127))))
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 4, 12321, 12546, 215026792020, 361617201270⟩, 5963867))
 (.leaf (⟨3, 4, 12816, 12816, 361742426640, 434925761040⟩, 1208944266640182156001281)))
 (.branch 51
 (.leaf (⟨3, 4, 12816, 12816, 360937120545, 434925740295⟩, 37477272265845646836039711))
 (.leaf (⟨3, 4, 12816, 12816, 348052218930, 434925342855⟩, 61656157598649289956065331))))))))
 (.branch 78
 (.branch 65
 (.branch 58
 (.branch 55
 (.branch 53
 (.leaf (⟨3, 4, 12816, 12816, 288191112480, 434918490480⟩, 13298386933042003716014091))
 (.branch 54
 (.leaf (⟨3, 4, 12816, 12816, 210613265730, 434917970055⟩, 73745600265051111516078141))
 (.leaf (⟨1, 4, 8451, 801, 361617786720, 288326448720⟩, 27))))
 (.branch 56
 (.leaf (⟨1, 4, 8451, 801, 361616738145, 288326448645⟩, 47))
 (.branch 57
 (.leaf (⟨1, 4, 8451, 801, 361599960930, 288326447205⟩, 77))
 (.leaf (⟨1, 4, 8451, 801, 361331525475, 288326420325⟩, 87)))))
 (.branch 61
 (.branch 59
 (.leaf (⟨1, 4, 8451, 801, 357036558180, 288325928805⟩, 97))
 (.branch 60
 (.leaf (⟨1, 4, 8451, 801, 288317081445, 288317081445⟩, 101))
 (.leaf (⟨2, 4, 8496, 4896, 361626105360, 361626105360⟩, 327685))))
 (.branch 63
 (.branch 62
 (.leaf (⟨2, 4, 8496, 4896, 361609328160, 361626104160⟩, 983055))
 (.leaf (⟨2, 4, 8496, 4896, 361592550945, 361626104070⟩, 2293795)))
 (.branch 64
 (.leaf (⟨2, 4, 8496, 4896, 361324115505, 361626081030⟩, 2687017))
 (.leaf (⟨2, 4, 8496, 4896, 361055680050, 361626079350⟩, 3604535))))))
 (.branch 71
 (.branch 68
 (.branch 66
 (.leaf (⟨2, 4, 8496, 4896, 356760712770, 361625649270⟩, 4259905))
 (.branch 67
 (.leaf (⟨2, 4, 8496, 4896, 352465745475, 361625618550⟩, 5308497))
 (.leaf (⟨2, 4, 8496, 4896, 288326448720, 361617786720⟩, 1376277))))
 (.branch 69
 (.leaf (⟨2, 4, 8496, 4896, 288041236050, 361617784950⟩, 4653127))
 (.branch 70
 (.leaf (⟨2, 4, 8496, 4896, 215026792020, 361617201270⟩, 5963867))
 (.leaf (⟨2, 4, 8241, 4866, 361626105360, 361626105360⟩, 327685)))))
 (.branch 74
 (.branch 72
 (.leaf (⟨2, 4, 8241, 4866, 361609328160, 361626104160⟩, 983055))
 (.branch 73
 (.leaf (⟨2, 4, 8241, 4866, 361592550945, 361626104070⟩, 2293795))
 (.leaf (⟨2, 4, 8241, 4866, 361324115505, 361626081030⟩, 2687017))))
 (.branch 76
 (.branch 75
 (.leaf (⟨2, 4, 8241, 4866, 361055680050, 361626079350⟩, 3604535))
 (.leaf (⟨2, 4, 8241, 4866, 356760712770, 361625649270⟩, 4259905)))
 (.branch 77
 (.leaf (⟨2, 4, 8241, 4866, 352465745475, 361625618550⟩, 5308497))
 (.leaf (⟨2, 4, 8241, 4866, 288326448720, 361617786720⟩, 1376277)))))))
 (.branch 91
 (.branch 84
 (.branch 81
 (.branch 79
 (.leaf (⟨2, 4, 8241, 4866, 288041236050, 361617784950⟩, 4653127))
 (.branch 80
 (.leaf (⟨2, 4, 8241, 4866, 215026792020, 361617201270⟩, 5963867))
 (.leaf (⟨3, 4, 8976, 8976, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 82
 (.leaf (⟨3, 4, 8976, 8976, 360937120545, 434925740295⟩, 37477272265845646836039711))
 (.branch 83
 (.leaf (⟨3, 4, 8976, 8976, 348052218930, 434925342855⟩, 61656157598649289956065331))
 (.leaf (⟨3, 4, 8976, 8976, 288191112480, 434918490480⟩, 13298386933042003716014091)))))
 (.branch 87
 (.branch 85
 (.leaf (⟨3, 4, 8976, 8976, 210613265730, 434917970055⟩, 73745600265051111516078141))
 (.branch 86
 (.leaf (⟨2, 4, 4146, 4146, 361626105360, 361626105360⟩, 327685))
 (.leaf (⟨2, 4, 4146, 4146, 361609328160, 361626104160⟩, 983055))))
 (.branch 89
 (.branch 88
 (.leaf (⟨2, 4, 4146, 4146, 361592550945, 361626104070⟩, 2293795))
 (.leaf (⟨2, 4, 4146, 4146, 361324115505, 361626081030⟩, 2687017)))
 (.branch 90
 (.leaf (⟨2, 4, 4146, 4146, 361055680050, 361626079350⟩, 3604535))
 (.leaf (⟨2, 4, 4146, 4146, 356760712770, 361625649270⟩, 4259905))))))
 (.branch 98
 (.branch 94
 (.branch 92
 (.leaf (⟨2, 4, 4146, 4146, 352465745475, 361625618550⟩, 5308497))
 (.branch 93
 (.leaf (⟨2, 4, 4146, 4146, 288326448720, 361617786720⟩, 1376277))
 (.leaf (⟨2, 4, 4146, 4146, 288041236050, 361617784950⟩, 4653127))))
 (.branch 96
 (.branch 95
 (.leaf (⟨2, 4, 4146, 4146, 215026792020, 361617201270⟩, 5963867))
 (.leaf (⟨3, 4, 4896, 8496, 361742426640, 434925761040⟩, 1208944266640182156001281)))
 (.branch 97
 (.leaf (⟨3, 4, 4896, 8496, 360937120545, 434925740295⟩, 37477272265845646836039711))
 (.leaf (⟨3, 4, 4896, 8496, 348052218930, 434925342855⟩, 61656157598649289956065331)))))
 (.branch 101
 (.branch 99
 (.leaf (⟨3, 4, 4896, 8496, 288191112480, 434918490480⟩, 13298386933042003716014091))
 (.branch 100
 (.leaf (⟨3, 4, 4896, 8496, 210613265730, 434917970055⟩, 73745600265051111516078141))
 (.leaf (⟨3, 4, 801, 8451, 361742426640, 434925761040⟩, 1208944266640182156001281))))
 (.branch 103
 (.branch 102
 (.leaf (⟨3, 4, 801, 8451, 360937120545, 434925740295⟩, 37477272265845646836039711))
 (.leaf (⟨3, 4, 801, 8451, 348052218930, 434925342855⟩, 61656157598649289956065331)))
 (.branch 104
 (.leaf (⟨3, 4, 801, 8451, 288191112480, 434918490480⟩, 13298386933042003716014091))
 (.leaf (⟨3, 4, 801, 8451, 210613265730, 434917970055⟩, 73745600265051111516078141)))))))))
cert_raw_4
cert_witness_4 2300
cert_faceTable_4 209
cert_faceWitness_4
cert_validity_4 4
cert_placement_4 4 06
cert_test_10
cert_symmetry_4 06
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
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
cert_check_4 0022 0000 22 0 2 2
cert_block_8 0022 22 2
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
cert_check_4 0028 0000 28 0 1 1
cert_block_8 0028 28 1
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
cert_check_4 0046 0000 46 0 2 2
cert_block_8 0046 46 2
cert_check_4 0047 0000 47 0 2 2
cert_block_8 0047 47 2
cert_check_4 0048 0000 48 0 2 2
cert_block_8 0048 48 2
cert_check_4 0049 0000 49 0 6 6
cert_block_8 0049 49 6
cert_check_4 0050 0000 50 0 6 6
cert_block_8 0050 50 6
cert_check_4 0051 0000 51 0 6 6
cert_block_8 0051 51 6
cert_check_4 0052 0000 52 0 6 6
cert_block_8 0052 52 6
cert_check_4 0053 0000 53 0 6 6
cert_block_8 0053 53 6
cert_check_4 0054 0000 54 0 1 1
cert_block_8 0054 54 1
cert_check_4 0055 0000 55 0 1 1
cert_block_8 0055 55 1
cert_check_4 0056 0000 56 0 1 1
cert_block_8 0056 56 1
cert_check_4 0057 0000 57 0 1 1
cert_block_8 0057 57 1
cert_check_4 0058 0000 58 0 1 1
cert_block_8 0058 58 1
cert_check_4 0059 0000 59 0 1 1
cert_block_8 0059 59 1
cert_check_4 0060 0000 60 0 2 2
cert_block_8 0060 60 2
cert_check_4 0061 0000 61 0 2 2
cert_block_8 0061 61 2
cert_check_4 0062 0000 62 0 2 2
cert_block_8 0062 62 2
cert_check_4 0063 0000 63 0 2 2
cert_block_8 0063 63 2
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
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
cert_check_4 0072 0000 72 0 2 2
cert_block_8 0072 72 2
cert_check_4 0073 0000 73 0 2 2
cert_block_8 0073 73 2
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
cert_check_4 0080 0000 80 0 6 6
cert_block_8 0080 80 6
cert_check_4 0081 0000 81 0 6 6
cert_block_8 0081 81 6
cert_check_4 0082 0000 82 0 6 6
cert_block_8 0082 82 6
cert_check_4 0083 0000 83 0 6 6
cert_block_8 0083 83 6
cert_check_4 0084 0000 84 0 6 6
cert_block_8 0084 84 6
cert_check_4 0085 0000 85 0 2 2
cert_block_8 0085 85 2
cert_check_4 0086 0000 86 0 2 2
cert_block_8 0086 86 2
cert_check_4 0087 0000 87 0 2 2
cert_block_8 0087 87 2
cert_check_4 0088 0000 88 0 2 2
cert_block_8 0088 88 2
cert_check_4 0089 0000 89 0 2 2
cert_block_8 0089 89 2
cert_check_4 0090 0000 90 0 2 2
cert_block_8 0090 90 2
cert_check_4 0091 0000 91 0 2 2
cert_block_8 0091 91 2
cert_check_4 0092 0000 92 0 2 2
cert_block_8 0092 92 2
cert_check_4 0093 0000 93 0 2 2
cert_block_8 0093 93 2
cert_check_4 0094 0000 94 0 2 2
cert_block_8 0094 94 2
cert_check_4 0095 0000 95 0 6 6
cert_block_8 0095 95 6
cert_check_4 0096 0000 96 0 6 6
cert_block_8 0096 96 6
cert_check_4 0097 0000 97 0 6 6
cert_block_8 0097 97 6
cert_check_4 0098 0000 98 0 6 6
cert_block_8 0098 98 6
cert_check_4 0099 0000 99 0 6 6
cert_block_8 0099 99 6
cert_check_4 0100 0000 100 0 6 6
cert_block_8 0100 100 6
cert_check_4 0101 0000 101 0 6 6
cert_block_8 0101 101 6
cert_check_4 0102 0000 102 0 6 6
cert_block_8 0102 102 6
cert_check_4 0103 0000 103 0 6 6
cert_block_8 0103 103 6
cert_check_4 0104 0000 104 0 6 6
cert_block_8 0104 104 6
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
cert_metadata_validity_12 0000 0 16 16
cert_metadata_validity_12 0016 16 32 16
cert_metadata_validity_12 0032 32 48 16
cert_metadata_validity_12 0048 48 64 16
cert_metadata_validity_12 0064 64 80 16
cert_metadata_validity_12 0080 80 96 16
cert_metadata_validity_12 0096 96 105 9
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 105
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 80 105
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)
  (FiniteChecks.interval_append (validity) 80 96 105
  metadata_validity_0080
  metadata_validity_0096)))
cert_metadata_symmetry_13 0000 0 16 16
cert_metadata_symmetry_13 0016 16 32 16
cert_metadata_symmetry_13 0032 32 48 16
cert_metadata_symmetry_13 0048 48 64 16
cert_metadata_symmetry_13 0064 64 80 16
cert_metadata_symmetry_13 0080 80 96 16
cert_metadata_symmetry_13 0096 96 105 9
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 105
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 80 105
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)
  (FiniteChecks.interval_append (symmetry) 80 96 105
  metadata_symmetry_0080
  metadata_symmetry_0096)))
cert_metadata_normalizers_4 4
cert_metadata_root_4
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S4T0
