module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00078Data
public import GraphInputsRow29Part00078Frames
public import GraphInputsRow29Part00078Leaves
public import GraphInputsRow29Part00078Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018
def vertexColumn : Fields := ⟨10, hexnat% "3e1b46b0bc1f3926c8f2e29aa3aa9a968da2e87a69966c59964d8b61db0e6392e2b86e8789e1783ee47316c4f1e27296a4e9a6659366392e47969565c55954d4b5c358d4b4ad8749d1743de0da358ce3c4e9364e5334d332cc73c2e8b62e4b32d2b2ac6b86c9b16c3bc1d8751d2729c6785d1725c3783d0f23c2f07c741b056139a12c4712a46949465154351342dc0d8384c9314e0b22c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6d36db6db6db6db4db69b4db49b49b6d249b49b49b4926d24934924934924d249a492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8408c2cccd00d6c0d5f8000000", hexnat% "40100000000000000000000", hexnat% "2000000800000000000380000000000", hexnat% "20028030000000000", 4467570873301204992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008003000e36363bdff8000000", hexnat% "ccc00000000000000000", hexnat% "840000000100c0c00000000000", hexnat% "cc000000000000000000000", 578712552117108736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840c82cccd16c0c0df58000000", hexnat% "4100000000000000000000", hexnat% "2000000800000000000380000000000", hexnat% "22800030000000000", 17451451240415232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80008033ebe930ff8000000", hexnat% "4c200000000000000000000", hexnat% "4000000000d000000000", hexnat% "84c40000000000000000", hexnat% "84000000080040400000000000", hexnat% "2000000800100000000280000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000833ebe930ff8000000", hexnat% "c4200000000000000000000", hexnat% "4000000000d000000000", hexnat% "8c440000000000000000", hexnat% "84000000080040400000000000", hexnat% "2000000800100000000280000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000848003000d1edef8dbb8000000", hexnat% "ccc00000000000000000", hexnat% "cc000000000000000000000", hexnat% "22020030000000000", 18253611008]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84088284433efefbdff8000000", hexnat% "48840000000000000000", hexnat% "2000000800100080000000000000000", hexnat% "44000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840000ccc73efefbdff8000000", hexnat% "2000000800300080000000000000000", hexnat% "cc000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008443cccd3ec879df78000000", hexnat% "84000000000000800000000000", hexnat% "20020020000000000", hexnat% "88000000000000000000000", 6192451635118080]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "184433ee83bcf78000000", 6403557867651072, hexnat% "48840000001000000000", hexnat% "cc200000000000000000000", hexnat% "2000084800000080000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008003000f3ebebb0bb8000000", hexnat% "84000000000040405000000000", 568009424896, hexnat% "cc000000000000000000000", hexnat% "ccc00000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840cc204011ecad85b18000000", hexnat% "20000008001000c0000200000000000", hexnat% "c8c00000000000000000", 2320479710150131712, hexnat% "20000038440000000", 536870912]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008c434c4e3efc7b9ff8000000", 703687441776640, hexnat% "8080800000000000000000", hexnat% "84000000010000004000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80108023ebe3b0ff8000000", hexnat% "800000080000009000000000", hexnat% "4c200000000000000000000", hexnat% "2000000000040040000000000000000", hexnat% "84000000010040c04000000000", hexnat% "84c00000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008003000e3ebe3bcff8000000", hexnat% "cc000000000000000000000", hexnat% "84000000010040c01000000000", hexnat% "ccc00000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000848883800f28c8fb5318000000", 1585267120374022144, 15199652500471808, hexnat% "4000c000000000000000000", hexnat% "4000c00000000000000000", hexnat% "40000000008000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000848043004d28def853b8000000", 1585267120374022144, hexnat% "20000038040000000", hexnat% "cc800000000000000000", hexnat% "c8000000000000000000000", 9007199254740992]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000008cc3844f3ee8fbcfd8000000", 6192450024505344, hexnat% "84000000000000001000000000", hexnat% "48800000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000848cc3844d28c8f85b18000000", 1585267086014283776, hexnat% "48800000000000000000", 15199652500471808, hexnat% "20000038000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000848443444d28c8f85318000000", 1585267120374022144, hexnat% "80088000000000000000000", hexnat% "8000800020000040000000", 6192452171988992, hexnat% "20000038000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300012cac780318000000", hexnat% "2000084800000080000001000000000", 1315051125551923200, hexnat% "2000003c440000000", 5207289753501696, hexnat% "cc000000000000000000000", hexnat% "ccc40000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c29 c18
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c30 c17
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c34 c5
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c35 c4
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c37 c2
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c38 c1
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c39 c0
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00078.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00078.record018
