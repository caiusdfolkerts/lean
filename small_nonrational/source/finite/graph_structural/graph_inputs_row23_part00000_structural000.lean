module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00000Data
public import GraphInputsRow23Part00000Frames
public import GraphInputsRow23Part00000Leaves
public import GraphInputsRow23Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021
def vertexColumn : Fields := ⟨10, hexnat% "3c2e2b4a2d8762b85ef0789d24b51d4ad176c370ea368e5354cb31ce8b62e4b52e2b4acab86d1b16e8761e4751cc719c9783d0f23c4f0f382d0b0a0e8a6158360b81ee0741c2439294550d42d07703a0d8390d4328c530ce0b42c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11bffdff000000000", 7205794588164882432, hexnat% "40808000000000000000", hexnat% "1a0000000000000000", hexnat% "22440000000000000000", hexnat% "11200000000000000000", hexnat% "c000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [11240914232453103616, 7205829772536971264, hexnat% "40810000000000000000", hexnat% "1a0000000000000000", hexnat% "22440000000000000000", hexnat% "11200000000000000000", hexnat% "c000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "62c5f1df74e000000000", hexnat% "8100400030000000000", hexnat% "4080200000000000000", hexnat% "11220020801000000000", 576469548396445696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4081810004c000000000", hexnat% "1c0000020000000000", hexnat% "e000000000000000000", hexnat% "20400084002000000000", hexnat% "11220060801000000000", 7599824371187712, 432346663739195392, 1729408645189337088, 6917634580757348352]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022
def vertexColumn : Fields := ⟨10, hexnat% "f0b8aaa8bad19561d8ae17bc1e26a92e745554752b45db0dc3a8da394d532cc73c2d8b92e2b86c9b16f0761e4749ca719d1783d0f23c4f0f382d0a8a2a83a518560d82e07b81d06892a439514550d42d07703a0d8390d4328c530ce0b22c2b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e452fdffffc000000000", hexnat% "200200000000000000", hexnat% "1800000000000000000", hexnat% "200000000000000000000", hexnat% "d0000000000000000", hexnat% "1a000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe5da4ffefc000000000", hexnat% "1800000000000000000", 648518346341351424, hexnat% "220000000000000000", hexnat% "200004000000000000000", 1297054284868747264]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe5da1ffefc000000000", hexnat% "1800000000000000000", 5476377146882523136, hexnat% "220000000000000000", hexnat% "200000000000000000000", 1297054284868747264]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fdd0a0ffefc000000000", hexnat% "2010000000000000000", hexnat% "220000000000000000", hexnat% "200004000000000000000", 936748722493063168, 1297054284868747264, hexnat% "c0000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba18ffffffc000000000", hexnat% "50000000000000000", hexnat% "201000000000000000000", hexnat% "44000000000000000000", hexnat% "100800000000000000000", hexnat% "620000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba14ffffffc000000000", hexnat% "90000000000000000", hexnat% "201000000000000000000", hexnat% "44000000000000000000", hexnat% "100800000000000000000", hexnat% "620000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba11f2ffffc000000000", 936748722493063168, hexnat% "201000000000000000000", hexnat% "44000000000000000000", hexnat% "100800000000000000000", hexnat% "620000000000000000", hexnat% "c0000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba1d94ff6fc000000000", 648518346341351424, hexnat% "201004000000000000000", hexnat% "40200200000000000000", hexnat% "100802000000000000000", hexnat% "420000000000000000", hexnat% "4000000900000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b412fdffffc000000000", hexnat% "d0000000000000000", hexnat% "600000000000000000", hexnat% "201000000000000000000", hexnat% "a000000000000000000", hexnat% "40000200000000000000", hexnat% "100800000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f432b3ffffc000000000", 5476377146882523136, hexnat% "c00000000000000000", hexnat% "a000000000000000000", hexnat% "300000000000000000000", hexnat% "d0000000000000000", hexnat% "1000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bef6b3ffffc000000000", hexnat% "90000000000000000", hexnat% "40000000000000000000", hexnat% "300000000000000000000", 5476377146882523136, hexnat% "1000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "baf3b2ffefc000000000", hexnat% "44000000000000000000", hexnat% "300000000000000000000", 72075186223972352, hexnat% "1004000000000000000", 864691128455135232, hexnat% "c0000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b1d0feffefc000000000", hexnat% "d0000000000000000", hexnat% "40200000000000000000", hexnat% "a000000000000000000", 72075186223972352, hexnat% "4020000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b050dfffefc000000000", hexnat% "40200000000000000000", hexnat% "201000000000000000000", hexnat% "2010000000000000000", hexnat% "100802000000000000000", hexnat% "4020000100000000000", hexnat% "c0000000000000000", hexnat% "8000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13a89feffffc000000000", hexnat% "40100000000000000", hexnat% "1100000000000000000", hexnat% "200000000000000000000", hexnat% "620000000000000000", hexnat% "c4000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1feea64fdffc000000000", hexnat% "1100000000000000000", 1297036692682702848, hexnat% "50000000000000000", hexnat% "200008000000000000000", 649081296294772736]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1feea46fdffc000000000", hexnat% "1100000000000000000", 12682136550675316736, hexnat% "50000000000000000", hexnat% "200000000000000000000", 649081296294772736]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fb9844fdffc000000000", hexnat% "4020000000000000000", hexnat% "50000000000000000", hexnat% "200008000000000000000", 649081296294772736, 3602879701896396800, hexnat% "600000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c27
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d4c0ffffffc000000000", hexnat% "220000000000000000", hexnat% "201000000000000000000", hexnat% "a000000000000000000", hexnat% "20100000000000000000", hexnat% "d0000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d4a0ffffffc000000000", hexnat% "420000000000000000", hexnat% "201000000000000000000", hexnat% "a000000000000000000", hexnat% "20100000000000000000", hexnat% "d0000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d482cdffffc000000000", 3602879701896396800, hexnat% "201000000000000000000", hexnat% "a000000000000000000", hexnat% "20100000000000000000", hexnat% "d0000000000000000", hexnat% "600000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d4e268ddffc000000000", 1297036692682702848, hexnat% "201008000000000000000", hexnat% "8040100000000000000", hexnat% "20100400000000000000", hexnat% "90000000000000000", hexnat% "2000022000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19281feffffc000000000", hexnat% "c0000000000000000", hexnat% "620000000000000000", hexnat% "201000000000000000000", hexnat% "44000000000000000000", hexnat% "8000100000000000000", hexnat% "20100000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19a854fffffc000000000", 12682136550675316736, hexnat% "180000000000000000", hexnat% "44000000000000000000", hexnat% "220000000000000000000", hexnat% "620000000000000000", hexnat% "1000000000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d6bd4fffffc000000000", hexnat% "420000000000000000", hexnat% "8000000000000000000", hexnat% "220000000000000000000", 12682136550675316736, hexnat% "1000000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d49f4dfdffc000000000", hexnat% "a000000000000000000", hexnat% "220000000000000000000", 144678138029277184, hexnat% "1008000000000000000", 3458764513820540928, hexnat% "600000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b198fdfdffc000000000", hexnat% "8040000000000000000", hexnat% "620000000000000000", hexnat% "44000000000000000000", 144678138029277184, hexnat% "2010000000000000000"]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19088fbfdffc000000000", hexnat% "8040000000000000000", hexnat% "201000000000000000000", hexnat% "4020000000000000000", hexnat% "20100400000000000000", hexnat% "2010002000000000000", hexnat% "600000000000000000", hexnat% "40000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c48 c41
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c49 c40
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c50 c39
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c51 c38
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c52 c33
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c462ffffffc000000000", hexnat% "1800000000000000000", hexnat% "220000000000000000000", hexnat% "d0000000000000000", hexnat% "100000000000000000", hexnat% "1a000000000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c5c0edfecbc000000000", hexnat% "220000000000000000", hexnat% "220000001000000000000", 1297089469240836096, hexnat% "d0000040000000000", hexnat% "100000000000000000", hexnat% "1a000000000000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4e2ffffffc000000000", hexnat% "300000000000000000000", hexnat% "1100000000000000000", hexnat% "d0000000000000000", hexnat% "1a000000000000000000", hexnat% "20000000000000000000"]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "380e2edfecbc000000000", hexnat% "44000000000000000000", hexnat% "1100001000000000000", 1297089469240836096, hexnat% "d0000040000000000", hexnat% "1a000000000000000000", hexnat% "20000000000000000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804dcdaa4f4000000000", hexnat% "1100001000000000000", hexnat% "100802040000000000000", hexnat% "1a000000000000000000", hexnat% "220000000000000000000", hexnat% "40200214000000000000", hexnat% "4020000908000000000", 1152956688978935808]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c61 c56
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a0dffffffc000000000", hexnat% "1100000000000000000", hexnat% "300000000000000000000", hexnat% "620000000000000000", hexnat% "800000000000000000", hexnat% "c4000000000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b18fe4dffc000000000", hexnat% "40100000000000000", hexnat% "10022000000000000", hexnat% "300000080000000000000", hexnat% "620010000000000000", hexnat% "800000000000000000", hexnat% "c4000000000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a1dffe7ffc000000000", 6755399441055744, hexnat% "201000000000000000000", hexnat% "100800000000000000000", hexnat% "620000000000000000", hexnat% "c4000000000000000000"]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a0dfb67ffc000000000", 42784196460019712, hexnat% "20100400000000000000", hexnat% "620000000000000000", hexnat% "1800000000000000000", hexnat% "c4000000000000000000", hexnat% "300000000000000000000"]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c67 c66
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a01fbffb7c000000000", hexnat% "620000000000000000", hexnat% "1800000000000000000", hexnat% "c4000000000000000000", hexnat% "300000000000000000000", hexnat% "c0000080000000000", hexnat% "20100400400000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1063fa5db38000000000", hexnat% "1800080000000000000", hexnat% "c4000000000000000000", hexnat% "220000000000000000000", hexnat% "100000000000000000000", hexnat% "80401000c0000000000", hexnat% "180400400000000000", hexnat% "2000022004000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c71 c68
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c72 c65
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe4dffffffc000000000", hexnat% "220000000000000000", hexnat% "1100000000000000000", hexnat% "800000000000000000", hexnat% "200000000000000000000"]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fe4dbdfe6fc000000000", hexnat% "1800000000000000000", hexnat% "200200000000000000", hexnat% "20000900000000000", hexnat% "104001000000000000", hexnat% "200000000000000000000"]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba0ddfffffc000000000", hexnat% "1100000000000000000", hexnat% "44000000000000000000", hexnat% "300000000000000000000", hexnat% "c02000000000000000", hexnat% "220000000000000000"]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ba0d9dfe6fc000000000", hexnat% "1104001000000000000", hexnat% "40200200000000000000", hexnat% "100802000000000000000", hexnat% "420000000000000000", hexnat% "4000000900000000000", hexnat% "200000000000000000000"]
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c78 c77
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c79 c76
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5422ffffbfc000000000", hexnat% "a000000000000000000", hexnat% "20100000400000000000", hexnat% "d0000000000000000", hexnat% "c00000000000000000", hexnat% "201000000000000000000", hexnat% "180000000000000000000"]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a1d9dfecfc000000000", hexnat% "220004001000000000000", 144167964633989120, hexnat% "620000000000000000", hexnat% "1800000000000000000", hexnat% "c4000000000000000000", hexnat% "100002000000000000000"]
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120999fe87c000000000", hexnat% "620000000000000000", hexnat% "8040000080000000000", hexnat% "100802000000000000000", hexnat% "c4000000000000000000", hexnat% "201004001000000000000", 144167964633989120, hexnat% "20100400400000000000"]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c83 c82
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c84 c81
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c85 c80
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c4627a5dffc000000000", hexnat% "1808080000000000000", hexnat% "8040100000000000000", hexnat% "20100400000000000000", hexnat% "200000000000000000000", hexnat% "2010022000000000000", hexnat% "10080000000000000000"]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c4e27a5dffc000000000", hexnat% "300008080000000000000", hexnat% "8040100000000000000", hexnat% "1100000000000000000", hexnat% "30000400000000000000", hexnat% "2010022000000000000", hexnat% "80000000000000000"]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182c1feffffc000000000", hexnat% "8040100000000000000", hexnat% "220000000000000000", hexnat% "44000000000000000000", hexnat% "180000000000000000", hexnat% "201000000000000000000", hexnat% "30000000000000000000"]
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84425a39ffc000000000", hexnat% "d0000000000000000", hexnat% "20100400000000000000", hexnat% "40200004000000000000", hexnat% "1a000000000000000000", 72620543991349248, hexnat% "201008080000000000000", hexnat% "100802040000000000000"]
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c90 c89
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c91 c88
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c92 c87
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80419082f0000000000", hexnat% "40200214000000000000", hexnat% "2010022004000000000", hexnat% "4020000908000000000", hexnat% "1104001000000000000", hexnat% "10080a0c0000000000000", hexnat% "220000000000000000000", hexnat% "10080400400000000000", hexnat% "80400000000000000000"]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c94 c93
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c95 c86
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c96 c73
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c97 c62
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c98 c53
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c99 c26
  c100
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046
def vertexColumn : Fields := ⟨10, hexnat% "3929ab869991e2785e0fb919a7859951d2745d0f743b0f23a8f13a4e4b8ad1b26c5b0ef07a1e4751cc789d2729c570dd0f23d941b382989921a986199162584e0b81ee06616446961465454951342d07703a0d8390e2318d1324c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492492492492492492492492491249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80800600000000000000", hexnat% "101001800000000000000", hexnat% "1e0000000000000000", hexnat% "6060001c800000000000", hexnat% "1e000000000000000000", 135107988821114880, hexnat% "1e000000000000000", 982963395231744]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00000.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00000.record046
