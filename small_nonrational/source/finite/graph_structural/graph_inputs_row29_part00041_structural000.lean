module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00041Data
public import GraphInputsRow29Part00041Frames
public import GraphInputsRow29Part00041Leaves
public import GraphInputsRow29Part00041Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002
def vertexColumn : Fields := ⟨10, hexnat% "d62b8d52b4ab29c9723c2f07cd4b4aaab1a9695a8e87ae1b46a9b16959568d9361da8e938ce8b8ae1ba1e1783ec6699564b91e785c56954d4b51d68d334ad1b61d2745d0f783c4d534cc73c2e8b52ccb1ae1b46c5b0ef07a1d8731d2719e1745c570de0f23c4f0bc1fc5154a28aac1a86518a6544a916439514a5454550d54328c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db6db6d36db49269b69b69b6db4934d24da6da4da6da4936924924d24d24c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf2bffff7fffeddfffc000000", hexnat% "2000000000001000000000000", hexnat% "d0000000000000000000000", 37383395344384, hexnat% "800004000080000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf0bffff7fffebffffc000000", hexnat% "a0000000000000000000000", hexnat% "2000000000001400000000000", hexnat% "800014000080000000000000000", hexnat% "40000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdfdfffffefffffffffc000000", hexnat% "10000000000000000", hexnat% "800000000000000000000000000", hexnat% "2020000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdfffff6fffeff7ffc000000", hexnat% "10000000000000000", hexnat% "80001008000000000", hexnat% "2020000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf5fffff6fffeff2ffc000000", hexnat% "10000001000000000", hexnat% "800000000080000000000000000", hexnat% "2000000000001000000000000", hexnat% "a000000000000c000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdffffb7fffe1f7ffc000000", 246290604621824, hexnat% "80001008000000000", hexnat% "400000000000000000", hexnat% "2020000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff4bfffbeffffffad7c000000", hexnat% "410000000000000000", hexnat% "a0000000000004000000000", hexnat% "800014000000000000200000000", 70866960384]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf4bfffb6fffffe2d7c000000", hexnat% "410000000000000000", hexnat% "2020000000000000000000000", hexnat% "800014000080000000200000000", hexnat% "8000000000001c000000000", 70866960384]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c13 c0
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c18
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff2ffff75ffefbbfffc000000", 74766790688768, hexnat% "8000000000a0000000000000000", hexnat% "800010000000000000", hexnat% "d0000000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdfbff3fef6fb9fffc000000", hexnat% "800010040000000000", hexnat% "2000000000000400000000000", hexnat% "401080020000000000", hexnat% "20400000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf0bbff3fef6eb9fffc000000", hexnat% "800010040000000000", hexnat% "2000000000001400000000000", hexnat% "401080020000000000", hexnat% "a0400000000000000000000", hexnat% "54000000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c24 c21
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c16 c15
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c26
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c16 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdffffff5d7ffefffffc000000", hexnat% "2000000000001000000000000", hexnat% "28000000000000000", hexnat% "a00000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff2ffff557fefdbfffc000000", hexnat% "d0000000000000000000000", hexnat% "800010040000000000", hexnat% "8000000000a0000000000000000", hexnat% "208000200000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdffbbbf147f6ed9fffc000000", hexnat% "2000440000001000000000000", hexnat% "38080000000000000", hexnat% "800010040000000000", hexnat% "600000220000000000", hexnat% "800004000080000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c15
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c16 c36
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c37
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c16 c38
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ffffffff97ffff9ffffc000000", 105553116266496, hexnat% "800000000080000000000000000", hexnat% "600000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ffffbfff177fff19fffc000000", hexnat% "600000220000000000", hexnat% "800004000080000000000000000", 215504279044096, hexnat% "808000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdfebfff176f6e19fffc000000", hexnat% "800014000080000000000000000", hexnat% "401080020000000000", hexnat% "2000000000001400000000000", hexnat% "800010840000000000", hexnat% "208000200000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fffbffff747ffefefffc000000", hexnat% "80001010000000000", hexnat% "38000000000000000", hexnat% "800000000000000000", hexnat% "800040000000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf3fbbf7fffff7fbfcc000000", hexnat% "800000800000000000", hexnat% "c0000000000004000000000", hexnat% "2000440000000000020000000", 268435456]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf3fbbffc7ffefe3fcc000000", hexnat% "38000000000000000", hexnat% "800040000000000000000000000", hexnat% "2000440000001000020000000", 275146342400, hexnat% "80000000000018000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c48 c47
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c49 c46
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf1ffff7ffffffffffc000000", hexnat% "800000000000000000", hexnat% "c0000000000000000000000", hexnat% "2020000000000000000000000"]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdfbbf1fffff1fffdc000000", hexnat% "600000200000000000", hexnat% "800000800000000000", hexnat% "2000000000000400020000000", hexnat% "20440000000000000000000"]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdfbbf1eef6f1bfec4000000", hexnat% "411080000008000000", hexnat% "800010840100000000", hexnat% "200000200000000000", hexnat% "2020440000000000020000000", 70369012613120]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdfebbbffcef7ffffffc000000", hexnat% "2000440000000000000000000", hexnat% "30080000000000000", hexnat% "800014000000000000000000000", 1152921504606846976]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfebbbf1e6f6e3bfffc000000", 215504279044096, hexnat% "2000440000001000000000000", hexnat% "411080000000000000", hexnat% "14000000010000000000000", hexnat% "a08000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37ffffffff1c7fffffff7c000000", hexnat% "800000000020000000000000000", hexnat% "600000000000000000", hexnat% "808000000000000000", hexnat% "10000000080000000"]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff0bfff1c7fffff7d7c000000", hexnat% "600000000000000000", hexnat% "808000000000000000", hexnat% "a0000000000008000000000", hexnat% "30000000080000000", hexnat% "800054000000000000200000000"]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff0bfff5d7fef7a7cfc000000", hexnat% "a08000000000000000", hexnat% "a0000000000008000000000", 4648739457204224, hexnat% "800000000020000000200000000", hexnat% "54000000000010000000000"]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fffbffff9c6f7fdffffc000000", hexnat% "800040000000000000000000000", hexnat% "208000200000000000", hexnat% "411080000000000000", hexnat% "20000000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff1ffffdd7ffffe7ffc000000", hexnat% "800000000020000000000000000", hexnat% "208000000000000000", hexnat% "a0000000000008000000000", hexnat% "40000000000010000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff5fbbf9c7f7e9e7fdc000000", 387028629848064, hexnat% "80000000000018000000000", hexnat% "38080000000000000", hexnat% "600000000000000000", hexnat% "20440000000000000000000"]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c65 c64
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c66 c63
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fff2bfff1c7ffffefc7c000000", hexnat% "410000000000000000", hexnat% "d0000000000010000000000", hexnat% "a08000000000000000", hexnat% "800000000020000000200000000", hexnat% "4000000000000180000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf5fbff1ffffe1e7fdc000000", hexnat% "600000200000000000", hexnat% "800000800000000000", hexnat% "80000000000018000000000", hexnat% "2000000000001400020000000", hexnat% "20400000000000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdfdfbff9c6f7e9f7fdc000000", hexnat% "38080000000000000", hexnat% "20400000000008020000000", hexnat% "2000000000001400000000000", hexnat% "401000000000000000", hexnat% "200000200000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf1bbfffcef7ffe7dfc000000", hexnat% "2020400000000000000000000", hexnat% "11080000000000000", hexnat% "80000000000018000000000", hexnat% "800000000020000000200000000", hexnat% "44000000000000000000000"]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffdf5fbff9eef7ebe7fdc000000", hexnat% "600080000000000000", hexnat% "2000000000001400020000000", hexnat% "11000000000000000", hexnat% "80000000000018000000000", hexnat% "20400000000000000000000"]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fdf1bbff9c6f7ebe7ddc000000", hexnat% "411080000000000000", hexnat% "800000000020000000200000000", hexnat% "2000000000001400020000000", hexnat% "208000000000000000", hexnat% "44000000000010000000000", hexnat% "a0400000000008000000000"]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c78 c67
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c79 c62
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c80 c61
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c81 c58
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c82 c55
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c83 c50
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c84 c45
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c85 c35
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c86 c25
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c87 c14
  c88
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004
def vertexColumn : Fields := ⟨10, hexnat% "d52b4d32ac9723c1f352acb4aaaa5a8e87ae1b46a9b16a5a5655a364d8b61db0ea3a4e538ce8b8ae1ba1e1783e1e785c56954d4b51d70da354d3346d8745d0f783c4e934ccb31cf0ba2d4b32c6b86c5b0ef07a1d8751cc749ca719e1745c9715c3783d0f23c4f0bc1fc5154a30acc4952a28aa544a9514a5454550d48d1342d50ca344c530cc8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1369b69b4db6da6d36db4db69b6db4d24d249a4d34934926936d369b4d26d24c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120840b9d867624b38000000", hexnat% "2040000000000000000000000000", hexnat% "408000000000000000000000000", hexnat% "20208000000000000", 36028797018963968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040120840b95825424b38000000", 54078379900534784, hexnat% "400000000028000000000000000", hexnat% "800000000000a000000000000", 144115188075855872]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040120840b95861224b38000000", 1759218604441600, 180143985094819840, hexnat% "400000000028000000000000000", hexnat% "8000000000008000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b958e1224b08000000", 1759218872877056, hexnat% "2040120000000000000000000000", hexnat% "400000000028000000020000000", 146366987889541120, hexnat% "8000840000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1208403bd8e5624b38000000", hexnat% "408000000000000000000000000", hexnat% "2040000000000000000000000000", 2814749767106560, hexnat% "800200000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4081208401bd825424b38000000", 54078379900534784, 2814749767106560, hexnat% "2000000000a00000000000000000", hexnat% "40000000000200000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040120840bbdaa1024b38000000", hexnat% "408000000000000000000000000", 1759218604441600, 2251799813685248, 18049582881570816]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1200001bd827420238000000", hexnat% "408000840000000000000000000", 18049862054445056, hexnat% "2040000000000000000800000000", hexnat% "800208000000000000", hexnat% "200080000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c11 c9
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c8
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c13 c7
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12084019dae7624b38000000", hexnat% "2040000000000000000000000000", hexnat% "408000000000000000000000000", hexnat% "820008000000000000", hexnat% "200000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20401208400952e5624b38000000", hexnat% "300800000000000000", hexnat% "800000000000a000000000000", hexnat% "400000000028000000000000000", hexnat% "800000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040120840184ae5624b38000000", hexnat% "19000000000000000", hexnat% "800000000000a000000000000", hexnat% "a00000000000000000", hexnat% "400000000020000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "384ae5624b08000000", hexnat% "19000000010000000", hexnat% "2040120000000000000000000000", hexnat% "800000000000a000020000000", hexnat% "820000000000000000", hexnat% "400000840000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4401208403bdae6624b38000000", 2533274790395904, hexnat% "8000000000000000000000000", hexnat% "2000000000800000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4081208400bd8ae424b38000000", 18331057858281472, hexnat% "300000000000000000", hexnat% "40000000000200000000000000", hexnat% "2000000000800000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4001208403bd8e6424b38000000", hexnat% "8000000000008000000000000", 316659348799488, hexnat% "2040000000000000000000000000", hexnat% "800200000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000000bd827420238000000", hexnat% "8000840000008000000000000", hexnat% "100040004100000000", 36063981391052800, hexnat% "2000000000a00000000800000000", hexnat% "40120000000200000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000038cae0604b08000000", hexnat% "2000120000800000000000000000", hexnat% "11000020010000000", 1970324836974592, hexnat% "400000840020000000020000000", hexnat% "8000000000008000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9c0a4020210000000", hexnat% "2040120000000000000800000000", hexnat% "408000840000000000020000000", hexnat% "100040004108000000", hexnat% "820208000000000000", hexnat% "201800000000000000", 949978046398464]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c21
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c33 c14
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c34 c6
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004
