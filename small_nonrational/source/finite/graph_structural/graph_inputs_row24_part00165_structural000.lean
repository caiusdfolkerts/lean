module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00165Data
public import GraphInputsRow24Part00165Frames
public import GraphInputsRow24Part00165Leaves
public import GraphInputsRow24Part00165Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004
def vertexColumn : Fields := ⟨10, hexnat% "9e2749b16ca725c570dc8f07c5aa9a56a3a1e966a59568d876c3a8e6394e8b92e2b86e8791e2785e0f969564d98e47959555356351d58d534cd8b52d2b46d8751d2745d0f56354e331cd8b52e2b4acab1ae1b46c5b0ed8751e2749ca719e1745c570de0f43c8f13c2f07e2a8689a89a16259491a49916545194951549342c8b0ac1b41c8709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6da69b4d36db4db4d36926924d34db69b49b6da49249249249249349a449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10808a00084c1b2ecad800000", 74839805132800, hexnat% "3a0000000040000000", hexnat% "7400000010000000000", hexnat% "420000000000000000000000", 8804682956800]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8a77a84c080200d800000", hexnat% "a0000000000000120000000", hexnat% "1400000000000048000000000", 405874409472, 415615395299328, 1100585369600]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1420007428441ff802d800000", hexnat% "800a0000000000100000000", hexnat% "800000000001000000000", hexnat% "80080000040000000", 474593886208, hexnat% "300000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10808a00084c132ccad800000", 74839805132800, hexnat% "1080000000000000000", hexnat% "420000420000000000000000", hexnat% "300000002240000000", hexnat% "6000000890000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10808a00084c17adead800000", 4402341478400, hexnat% "420000420000000000000000", 141975512678400, hexnat% "380000000000000000", hexnat% "7000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8a77a84c008820d800000", hexnat% "420000000000000020000000", hexnat% "1080000000000000000000000", 141975512678400, 411217348788224, 401579442176]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a08a00884c044dded800000", hexnat% "1400000000000000000000000", 487083651104768, hexnat% "320000002200000000", hexnat% "7400000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200074a84c089816d800000", hexnat% "800000000401000000000", hexnat% "10800a0000000000000000000", 340848604610560, hexnat% "300000002200000000", 328564998144]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800077a84c089efed800000", hexnat% "20800000000001000000000", hexnat% "10000a0000000040000000000", 406819302277120, hexnat% "400000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2080072840089ffed000000", hexnat% "10800c0000000800000", hexnat% "6000000000000000000", hexnat% "10800a0000000000000000000", 411217348788224, hexnat% "400000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77a84c007a34d800000", hexnat% "10800a0000000000000000000", 483785116221440, hexnat% "400800000000400000000000", 397821345792, hexnat% "20000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000007708401ffa9cd800000", hexnat% "800a0000000000000000000", 369904058368, hexnat% "800c0000000000000", hexnat% "420000020000000000000000", hexnat% "800000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7408441ffe14d800000", hexnat% "10800a0000000000000000000", 131533373440, hexnat% "80080000000000000", hexnat% "420800000000000000000000", hexnat% "320000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14a08a14084c142b14d800000", 58274116272128, 337691803648, hexnat% "3a0000000000000000", hexnat% "6000000880000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "807708441ffa94d800000", hexnat% "a0000080000000000000", hexnat% "1400000000000000000000000", 372051542016, hexnat% "a0000000000000000", hexnat% "a0000000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8014084017aa14d000000", hexnat% "6000000810000000000", hexnat% "a00000c0000000800000", hexnat% "a0000000000000020000000", 405874409472, hexnat% "3a0000000000000000", hexnat% "1400000000000040000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c20 c9
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c21 c8
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c22 c7
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c23 c6
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c25 c4
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c26 c3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c27 c2
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c28 c1
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c29 c0
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005
def vertexColumn : Fields := ⟨10, hexnat% "9d16c5723c1f2725a95a8e87a99966a5a56558d68d8766394e8b92e2b86e8791e2785e0fa715a5598e47999565a5655554d58d4756354d8b52d2b46d8751d1743d98d63a4e5354cd38cc7362d4b8ad2b2ac6b86d1b16c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07c9c268995162519615254554348d0b41d50e2318e1324c5342c8b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6db6db4db6db4924924924924924924924924926db4d369349b49a449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdffc23ff0844d800000", hexnat% "8000000000002280000000", 3765009288481734656, 684547143360315392, hexnat% "2000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff67c220408440000000", hexnat% "800000000000228d800000", 1158867663489859584, hexnat% "980000000000000000", 990950247695908864, 2308657758980800512]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8008220feef0a6cd800000", 1157706579210928128, hexnat% "90002000000000000000", hexnat% "2700c000000000000000", hexnat% "dd0000000000000000", hexnat% "40000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "803fbbc00880a6cd800000", hexnat% "40440000000000000000", hexnat% "80002400000000000000", 702614318427930624, 15551492463263744, 1297036692682702848]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "803cffc200c0a6cd800000", 15533900277219328, hexnat% "83000000000000000000", hexnat% "40001000000000000000", 990791918021509120, 2308094809027379200]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48133fddb08440000000", hexnat% "ccc000000000000000", hexnat% "800000000000228d800000", 9640517952339968, hexnat% "83200000000000000000", hexnat% "34000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f03ffd9b086c0800000", 10766418077286400, hexnat% "40540000000000000000", hexnat% "8000000000002000000000", hexnat% "80280000000000000000", hexnat% "800000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "dbfff440802401000000", 38579663995404288, hexnat% "240000000002c0800000", hexnat% "800000000000800c000000", 792739087533473792, 15199648742375424]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808803104080a6cd800000", 1080969463685185536, hexnat% "3700c000000000000000", 2344422673209098240, hexnat% "bc0000000000000000", hexnat% "40400000000000000000", 15199648742375424]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c15 c2
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record005
