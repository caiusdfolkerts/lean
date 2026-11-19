module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00136Data
public import GraphInputsRow29Part00136Frames
public import GraphInputsRow29Part00136Leaves
public import GraphInputsRow29Part00136Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019
def vertexColumn : Fields := ⟨10, hexnat% "b30dc4f2caa68da4eac6359362da8e9394e3386e4789e17ac9a64d94e6c5355352d68d9354d3346d4749d1769334d332cf0ba2d4b32e2b1ae1b46c9b16e8761e4751ca719d1715e0f23d2c0f2c29292a0e8c6498960d90e1382e07ac1925290e4c5494950d50d1342d0768390cc348c930ce0b42c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b49b4924d249249b4924d2492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd6b7d6b1fff5d80000000000", hexnat% "60008000000000000", hexnat% "4000400000000000000000", hexnat% "80008000000200000000000", hexnat% "10001000002000000000000", hexnat% "200820080000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdef7d7f928d5d80000000000", hexnat% "60008000000000000", hexnat% "8008000200000000000", hexnat% "10000001002000000000000", 5125096375947624448, hexnat% "200820000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "377fff669f287d380000000000", hexnat% "1001002000000000000", 5152117973711847424, hexnat% "8008000400000000000", hexnat% "10400000800000000000", hexnat% "8800080200000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fdebfdeb7a8dff80000000000", hexnat% "14000000000000000000000", hexnat% "1480000000000000000", hexnat% "200020000020000000000000", 6269010681299730432]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37569f4697285d580000000000", hexnat% "10001001002000000000000", 5161125172966588416, hexnat% "80008008000200000000000", hexnat% "4000400000800000000000", hexnat% "200020080000000000000000", hexnat% "8802090200000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3734df34dfab7ff80000000000", hexnat% "80008000000000000000000", hexnat% "420042000000000000000000", 6088866696204910592, hexnat% "10001000000000000000000", hexnat% "8802080200000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37249f249e2879a80000000000", 6305057070504738816, hexnat% "80008008000400000000000", hexnat% "420042000004000000000000", hexnat% "10001000002000000000000", hexnat% "8004000400000000000000000", hexnat% "902090210000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3757ff56d57ffff80000000000", hexnat% "1280000000000000000", hexnat% "80008008000000000000000", hexnat% "200020020000000000000000", hexnat% "8800080000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3716d714d57ffff80000000000", hexnat% "400042000000000000000000", hexnat% "10001000000000000000000", hexnat% "80008008000000000000000", hexnat% "8802080200000000000000000", hexnat% "2008200a0000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3747ff46947ff4980000000000", hexnat% "1000002000000000000", hexnat% "680000000000000000", hexnat% "200020020009200000000000", hexnat% "80008008000400000000000", hexnat% "8900090010000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f97ff9ffd29c0d80000000000", 6205960286516543488, hexnat% "400040020014000000000000", hexnat% "80000008001200000000000", 2814749767106560, hexnat% "200020000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f9fff94b57fe0d80000000000", hexnat% "3480000000000000000", hexnat% "8008001200000000000", hexnat% "400040020014000000000000", 2814749767106560, hexnat% "200020000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3766bf6ffe2974b80000000000", hexnat% "14000000000000000000000", 6232981884280766464, hexnat% "80000008001400000000000", 2814749767106560, hexnat% "8900090010000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fbfffbcbfafe1f80000000000", 5764607523034234880, hexnat% "3400000000000000000", 8444249301319680, hexnat% "400040000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fd6bfd7fdfff5d80000000000", hexnat% "14000000000000000000000", 2849934139195392, hexnat% "80008000000000000000000", hexnat% "200020020000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f96bf96bdffe1d80000000000", hexnat% "4000400000000000000000", hexnat% "80008000000200000000000", hexnat% "10001000002000000000000", hexnat% "400040020014000000000000", hexnat% "200020000008000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fb6f7b4bf7ffff80000000000", hexnat% "3400000000000000000", hexnat% "80008008000000000000000", hexnat% "400040000000000000000000", hexnat% "10800000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fe6f7f7ff2b5ff80000000000", hexnat% "80008008000000000000000", hexnat% "10800000000000000000000", hexnat% "100000000080000000000000", 6061845098440687616]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37e6b766ff295ff80000000000", hexnat% "10001001000000000000000", hexnat% "80008008000000000000000", hexnat% "4800000000000000000000", 5089067578928660480, hexnat% "8100090000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3706b704bd7fe8980000000000", hexnat% "10001000002000000000000", hexnat% "80008008001600000000000", hexnat% "400042000014000000000000", hexnat% "8004000400000000000000000", hexnat% "900090000000000000000000", hexnat% "200820020000000000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c31 c18
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c32 c17
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c33 c16
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c35 c14
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37669f669e2879280000000000", 6305057070504738816, hexnat% "10001000002000000000000", hexnat% "80008008000400000000000", 1266637395197952, hexnat% "8004000400000000000000000", hexnat% "902090210000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c37 c39
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3767ff67fe285d180000000000", 1153484454560268288, 5161125172966588416, hexnat% "80008008000600000000000", hexnat% "8900090010000000000000000", 140737488355328]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c37 c41
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffffffffffffff80000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c44 c40
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c45 c38
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c46 c11
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c47 c8
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020
def vertexColumn : Fields := ⟨10, hexnat% "3713c3693aa58d64d8b69394e3386e4789e178d94e695355352d64d534cd1b51d2745da4cd34ccb392d4b32c6b46c9b16f0761d4789ca719e1745c5783c8fb112c0f2c24a83aa1a4631926258364384e0b81eb05290e685914c5494950d50d1342d0768390cc348c930cd0b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69a492492493492492492492492492492492489249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ac27613c2695400000000000", hexnat% "4002004040800000000000", 83879543059775488, hexnat% "8004008000000000000000", hexnat% "10008010000000000000000", hexnat% "1000801000000000000000", hexnat% "520890420800000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c2 c0
  c3
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record020
