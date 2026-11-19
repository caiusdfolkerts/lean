module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00287Data
public import GraphInputsRow29Part00287Frames
public import GraphInputsRow29Part00287Leaves
public import GraphInputsRow29Part00287Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00287.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000
def vertexColumn : Fields := ⟨10, hexnat% "ad2743d1ac5b0ec372b29c8f26a96a3a8dac9aa669a66598e6a5a5635a362d8766394e3392e2b86e8791e2785eac6713c5a95a4e936725a95a59956539695954d58d4b51d58d534cd4b4ad1b61d47723a8da398d6338e9394cd38ccb31cd8b52ccb4acab1ae1b46f07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f2705c2685a264598952529465854951550d2344d0762348ca318e1324c5342c8b12c1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6d36db69b6db6db6db6db6d26db6d24924924924924924924924924924936db69249a4da49a249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨118, by decide⟩, ⟨125, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "303ffffe07e3c07d9d0000000", hexnat% "20400000000000008040000000000000", 108649341010313216, hexnat% "1f0000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400003020f45dffffe07d9d0000000", hexnat% "1a200000000000000000", hexnat% "1f0a0000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000303ff5fe0f47c07d9d0000000", hexnat% "a0000a00000000000000", 108649341010313216, hexnat% "1f0000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000003020747e0f41407d9d0000000", hexnat% "400000000000000042000000000000", hexnat% "18000000000000000000", 119345390125318144, hexnat% "1f0a00000000000000", hexnat% "1f8a0000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400003020f25dffffe07d9d0000000", hexnat% "1a200000000000000000", hexnat% "1f0c0000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000303ff3fe0f27c07d9d0000000", hexnat% "c0000c00000000000000", 108649341010313216, hexnat% "1f0000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000003020727e0f20c07d9d0000000", hexnat% "400000000000000042000000000000", hexnat% "18000000000000000000", 121597189939003392, hexnat% "1f0c00000000000000", hexnat% "1f8c0000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c11 c0
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "303ffffe00ffa07d9d0000000", hexnat% "20400000000000009000000000000000", 6918654927547924480, hexnat% "1f0000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000302097d3ffffe07d9d0000000", hexnat% "680400000000000000000", hexnat% "1f002800000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000303fffd609fd207d9d0000000", hexnat% "2800028000000000000", 6918654927547924480, hexnat% "1f0000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000030201fd6085d207d9d0000000", hexnat% "400000000000001004000000000000", hexnat% "600000000000000000000", hexnat% "1f0028000000000000", 7638104968020361216, hexnat% "1f802800000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000302097cbffffe07d9d0000000", hexnat% "680400000000000000000", hexnat% "1f003000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000303fffce09fca07d9d0000000", hexnat% "3000030000000000000", 6918654927547924480, hexnat% "1f0000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000030201fce083ca07d9d0000000", hexnat% "400000000000001004000000000000", hexnat% "600000000000000000000", hexnat% "1f0030000000000000", 7782220156096217088, hexnat% "1f803000000000000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c24 c13
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e01ffffe0118c0000000", hexnat% "700400000004010000000", hexnat% "20400003020000000000000000000000", hexnat% "1e200000000100000000", hexnat% "1f800000000068000000000", hexnat% "1800000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000003f9e79ffffe07d8c0000000", hexnat% "3000000000000000110000000", hexnat% "18600000000000000000", hexnat% "600000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000303f9e780944807d9d0000000", hexnat% "18600000000000000000", hexnat% "600000000000000000000", hexnat% "1f0030000000000000", 109775240917155840, 7638104968020361216]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e01ffffe0098c0000000", hexnat% "700400000004010000000", hexnat% "20400003020000000000000000000000", hexnat% "1e200000000100000000", hexnat% "1f000000000070000000000", hexnat% "1800000000000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8039ffffe0158c0000000", hexnat% "1c200000000110000000", hexnat% "20400003020000000000000000000000", hexnat% "7e0400000000000000000", hexnat% "1f000000000068000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301f8209f87fa07d9d0000000", 8648037184458194944, hexnat% "1f200000000000000000", hexnat% "7c0400000000000000000", hexnat% "20400000020000000000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "301f8021f87fa07d9d0000000", 8648037184458194944, hexnat% "7e0400000000000000000", hexnat% "1da00000000000000000", hexnat% "20400000020000000000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8039ffffe02d8c0000000", hexnat% "1c200000000110000000", hexnat% "20400003020000000000000000000000", hexnat% "1f000000000050000000000", hexnat% "7e0400000000000000000"]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040000302091e2097fa07d9d0000000", 7495115679851347968, hexnat% "1f0000000000000000", hexnat% "6e0400000000000000000", hexnat% "1f001800000000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204000030208000006180299d0000000", 127789639426637824, 8646911559429259264, hexnat% "1f8020000000000000", hexnat% "1fa00000000000000000", hexnat% "7e0400000000000000000", hexnat% "1f000000000050000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c38 c33
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c39 c32
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c41 c30
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c42 c29
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c43 c26
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c44 c25
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c45 c19
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c46 c12
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c47 c6
  c48
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00287.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00287.record000
