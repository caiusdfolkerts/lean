module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00084Data
public import GraphInputsRow26Part00084Frames
public import GraphInputsRow26Part00084Leaves
public import GraphInputsRow26Part00084Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002
def vertexColumn : Fields := ⟨10, hexnat% "ccaaa96a3a1e9a6559362d8ce4b8ae8785e0fb31aa6598e479695554d4b53352d2b61d1743dc8ea368f1394d532cc73a2e4b32d2b1ae1b16c3b61d4731d2729e1725c3783d0f0bc1f8c9328a8aa458562384e8c5318a4a9454552344d88d2328e1344c530ce0b22c4b0ad0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1269b49a69a6934da4d34d3492492492492492492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b7e96fd2020b9f00000000", hexnat% "800100040046000000000", hexnat% "10002000409900000000000", hexnat% "20004000930000000000000", 37260250042073088, hexnat% "4010802000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3b9e77086720f00000000", hexnat% "800100040047000000000", hexnat% "10002000409800000000000", hexnat% "20004000930000000000000", 144125633436319744, hexnat% "440088000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fefdedf930f1b300000000", hexnat% "100040044000000000", hexnat% "2000409000000000000", 37154696925806592, 144123984168878080, hexnat% "100020002020c00000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2fff9fdf06075fb00000000", hexnat% "20002020400000000", hexnat% "4000910000000000000", 144123984168878080, 37154696925806592, hexnat% "10002000409800000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3fffebfbfffffff00000000", hexnat% "1404000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3f7fbedf419f19700000000", hexnat% "20002020800000000", hexnat% "4000920000000000000", 37154696925806592, 144123984168878080, hexnat% "800100040046000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffffdaffffffff00000000", hexnat% "250000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fff9eff00373df00000000", hexnat% "100040042000000000", hexnat% "2000408800000000000", 144123984168878080, 37154696925806592, hexnat% "20004000930000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3ffd7daffffffff00000000", hexnat% "8250000000000000000", hexnat% "20000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c14 c6
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006
def vertexColumn : Fields := ⟨10, hexnat% "332aaa5a699568d93633a2e2ba1e4789ecc6a9965a5556354d4cd8b4ad8751d27723a8da3c4e5354e334ce8b92ccb8acab46c9b61d4731e2719e1725c3783d0f0bc5c8685a498a6458562384e07a1916525295151548d1341d88d2328e1344c5382c8b12c1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da49a4d249b49349a492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7f7bfbcbffc5f800000000", 1441154079781814272, hexnat% "42000000000000000", hexnat% "84000000000000000000", 61572651155456]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f7b7bdc7b076800000000", hexnat% "80040004081000000000", hexnat% "1000800100c00000000000", 53326313947136, 180143985094819840, hexnat% "4002000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c3 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c3 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7bf7dfb3ffc5f800000000", 864693327478390784, hexnat% "204000000000000000", hexnat% "408000000000000000000", 61572651155456]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6bf75fbf63076800000000", hexnat% "400200080108000000000", hexnat% "1000800008c00000000000", 44049184587776, 5629499534213120, hexnat% "8004000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c3 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ff3b9afffff800000000", hexnat% "800100000000000000", hexnat% "800400400000000000000", hexnat% "46000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ff9f9b7ffff800000000", hexnat% "200080000000000000", hexnat% "800400400000000000000", 6917529027641081856]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ff9ffb7fdd7800000000", hexnat% "200080008000000000", hexnat% "800400400220000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ff9b9a7fdd7800000000", 108086940812705792, hexnat% "800400400220000000000", hexnat% "46000000000000000", hexnat% "200000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6b735b1e73264800000000", hexnat% "80040004083000000000", hexnat% "400200080118000000000", hexnat% "1000800108c00000000000", hexnat% "c000000000000000000", 16140901064495857664]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c3 c21
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7ffefdfffffff800000000", hexnat% "1020000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "5ffdeffffffff800000000", hexnat% "2100000000000000000", hexnat% "2000000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c6
  c29
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record006
