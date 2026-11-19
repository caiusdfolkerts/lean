module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00084Data
public import GraphInputsRow29Part00084Frames
public import GraphInputsRow29Part00084Leaves
public import GraphInputsRow29Part00084Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00084.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010
def vertexColumn : Fields := ⟨10, hexnat% "370bc368d6354d316c3b31c9715c9c8f29a8ea968e63392e2b86e4785eb86d1cc6b16c6713c6693a719965a539715656553570d934cd4b4ad1b61d4745d98ce394cd38cd332cc7392ccb8ad2b2ac6b86d1b16cc749ca719d1715d0f23c4f0bc1fca268350e23486a318961584ec8711c26294a5152550d28c930ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6db6da49a4da69b4db69a6da4d26d36d369a6d36d249b69a692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d10851322523c53f000000", 9223372037928517632, hexnat% "840000000000000000000", hexnat% "10000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d94050322523c52f000000", 1342177280, hexnat% "10008000000000000000000", hexnat% "18000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d14040320523c52f000000", hexnat% "10800000000000000000000", 9007200596918272, hexnat% "18000000000000000", hexnat% "8100000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1114811922520c55b000000", hexnat% "400000030000000000", 2305843009817673728, hexnat% "4800000000000000000000", hexnat% "4008000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1590000022520c50b000000", hexnat% "4008000400000020000000000", 1152922604386910208, 11529215047679082496, hexnat% "8110000000000000000", hexnat% "40000000000004000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401d94040220503c526000000", 35184506306560, 9232379237200035840, hexnat% "8111000000000000000", 268435456]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1594000020520c50a000000", hexnat% "4008000400000020000000000", hexnat% "8111000000000000000", 2305843009817673728, 1100853805056, 9232379236126294016]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d14851322503c527000000", 9223372037928517632, 402653184, hexnat% "10000000000200000000000", hexnat% "800000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d10050200503c526000000", hexnat% "10008000000200000000000", 1306043892205879296, hexnat% "840000000000000000000", hexnat% "18000000040000000", 150994944]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1584811922020c57f000000", hexnat% "8100000000000000000000", hexnat% "400000030000000000", 2307250384097247232, hexnat% "4000000000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "580000a02020c57f000000", hexnat% "140000000000000000000", hexnat% "10000000005000000000000", hexnat% "4008000400000020000000000", 1297037792194330624, hexnat% "8110000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1584850a02520457f000000", hexnat% "11000000000000000", 3848290697216, hexnat% "100000200000000000000", hexnat% "4008000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1104811902000457f000000", hexnat% "402005000000000000", hexnat% "4900000000000000000000", hexnat% "4008000000000020000000000", 35734127902720, 144116287587483648]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1594040200520c52d000000", hexnat% "4008000000000020000000000", hexnat% "18020000040000000", hexnat% "8101000000000000000", 144116287889473536]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d94811922420415f000000", hexnat% "4000000400000020000000000", 1649267441664, 2306124501907144704]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400d94040022402410f000000", 1152922604386910208, 35734127902720, hexnat% "8110000000000000000", 11529215047679082496, hexnat% "10000000001000400000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "110811122403c11b000000", 11529215047679082496, hexnat% "4008000400000000000000000", hexnat% "10000000001200400000000", hexnat% "840000000000004000000", hexnat% "4000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400910040b00502456d000000", hexnat% "10008000000200000000000", hexnat% "110020000000000000", hexnat% "840000000000000000000", 144116287889473536, hexnat% "4000000000008000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "594010322423c53f000000", hexnat% "10000000001000000000000", hexnat% "18000000040000000", hexnat% "8000000000000000000", hexnat% "4008000400000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "194011b02400c56d000000", hexnat% "c000000000000000000000", hexnat% "10000000001200000000000", hexnat% "8000000000000000000", hexnat% "4000000400000020000000000", 144116287889473536]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4009140403004024109000000", hexnat% "18020000040000000", hexnat% "8100000000000000000", hexnat% "4800000000008000000000", hexnat% "10000000001200400000000", 144116287889473536, 603979776]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c31 c26
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c25
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c24
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c34 c21
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c35 c20
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c36 c17
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c37 c14
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c38 c11
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c39 c8
  c40
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00084.record010
