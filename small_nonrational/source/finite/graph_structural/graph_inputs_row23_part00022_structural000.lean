module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00022Data
public import GraphInputsRow23Part00022Frames
public import GraphInputsRow23Part00022Leaves
public import GraphInputsRow23Part00022Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002
def vertexColumn : Fields := ⟨10, hexnat% "749ca8e9c6658d68d8b6538ce8b86e0f9d17263971595356352d54d3362d1b43dc4e9354cd34ccb3c2d8b92ccb4ac6b86d1b0ed8751e2729c6785d1715e0f43c8f07dc264a3252a2a318960d84e0b9c16463152629314950d44d0b58350cc388e1344c930ce0b42c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "882441fd2e4e2000000000", hexnat% "400200000200000000000", 202663907377020928, hexnat% "80040000000000000000", hexnat% "21010800001000000000000", hexnat% "10108080000800000000000", hexnat% "40020000100000000000", hexnat% "6203100000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ca0e51c03ffe000000000", hexnat% "40020010000000000000", hexnat% "800400000c000000000000", 16140901064495857664, hexnat% "20010000100000000000000", hexnat% "6203100000000000000000", hexnat% "10108080040000000000000", 189151184349560832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a4052bfe61e000000000", hexnat% "40020000100000000000", 15276225329203511296, hexnat% "800400000000000000000", hexnat% "10108080000800000000000", hexnat% "400200000000000000000", hexnat% "21010800001000000000000", hexnat% "6203100000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9e04f0873ffe000000000", hexnat% "400200400000000000000", hexnat% "800400000c000000000000", 252201579132747776, hexnat% "10008002000000000000000", hexnat% "6203100000000000000000", 14987979559889010688, hexnat% "21010800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3731b987d65b6e000000000", 9370301974697738240, hexnat% "400200000080000000000", 40533496157962240, hexnat% "40020000000000000000", hexnat% "8024010000400000000000", hexnat% "880440000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3731b103961b48000000000", hexnat% "880000024000000000", hexnat% "40020010012000000000", hexnat% "400200400080000000000", 184084634768769024, 13835058055282163712, hexnat% "8024010000400000000000", hexnat% "880440000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4240120bffb1e000000000", hexnat% "10108080000000000000000", hexnat% "8024010000400000000000", 17582068338417205248, hexnat% "880440000000000000000", hexnat% "13800000000000000000", hexnat% "23000000000000000000000", hexnat% "400200000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "250108038a1320000000000", hexnat% "4002001001e000000000", hexnat% "4002004000c0000000000", hexnat% "802401000a400000000000", hexnat% "10108080140800000000000", hexnat% "880440000000000000000", 9368613124837474304, hexnat% "2203100000000000000000", 4611686018427387904]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00022.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00022.record002
