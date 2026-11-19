module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00004Data
public import GraphInputsRow25Part00004Frames
public import GraphInputsRow25Part00004Leaves
public import GraphInputsRow25Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031
def vertexColumn : Fields := ⟨10, hexnat% "338573c274b2a5693aa9956358b61da8e53a2e4789e1783ef079174731ac729c6699566394e6a5554b51d68d5362d4749d17783d0ec370f23a8d9354cd34ccb31ce8b52d2b46c9b16c3ba1d4789ca719d1725c570de0f43c8f13c1f3503cc2a2a3182e544d1c26294643931495154350b41dc0e8350cc388e0b42c2b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b6d36da6da6d369349349369249249349b6924da4924d2492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ee3f6059fbfc0000000", hexnat% "40040000000000000000", hexnat% "4010000000000000000000000", hexnat% "2010000000c0000000000000", hexnat% "200000800000000000000", 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000242037ec70fbfc0000000", hexnat% "e08000000000000000", hexnat% "24000000000000000000", hexnat% "11000040000100000000000", hexnat% "200000000000800000000000", hexnat% "8000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4316050fbfc0000000", hexnat% "4010000000000000000000000", hexnat% "200a08000000000000000", 7494552729897926656, hexnat% "46040000100000000000", hexnat% "2010000000c0800000000000", hexnat% "28000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "228e3eec3853fc0000000", 11544872091648, 1154047404513689600, hexnat% "201000000000100000000000", hexnat% "46040000000000000000", hexnat% "4010000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401102ae7ec879fbfc0000000", hexnat% "44000000000000000000", hexnat% "200000040000000000000", hexnat% "200000000000000000000000", 1297036692682702848]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1022ae3ecc7843fc0000000", hexnat% "4000040000000000000000000", 12644383719424, hexnat% "4040000100000000000", hexnat% "201000000000000000000000", 1297036692682702848]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "228e1ec83841780000000", hexnat% "4000040000004000000000000", 1297046588287352832, hexnat% "6020000100000000000", hexnat% "10000040000020000000000", hexnat% "201000000040002840000000", 549755813888]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208e1dac60fbfc0000000", hexnat% "201000000000900000000000", 2594354860342116352, hexnat% "4010000000000000000000000", hexnat% "26020000000000000000", hexnat% "40040000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200407a020fbfc0000000", hexnat% "a38000000000000000", hexnat% "4010000000001000000000000", hexnat% "2010000000c0900000000000", hexnat% "40000404000000000000", hexnat% "6040000000000000000", hexnat% "28000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "668620079587c0000000", hexnat% "208000080000000000000", hexnat% "4010000000000000000000000", 5044042577771233280, hexnat% "201000000040003800000000", 1729382256910270464, hexnat% "618000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "66000003010300000000", hexnat% "4010000000000000400000000", 8503921996382339072, hexnat% "208808000000000000000", hexnat% "2010000000c0903840000000", 576465702253232128, hexnat% "630000000000000000", hexnat% "400000a0000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031
