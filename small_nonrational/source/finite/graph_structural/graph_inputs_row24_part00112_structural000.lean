module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00112Data
public import GraphInputsRow24Part00112Frames
public import GraphInputsRow24Part00112Leaves
public import GraphInputsRow24Part00112Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002
def vertexColumn : Fields := ⟨10, hexnat% "2749723c3c8da2e9c669a663987663a4e33a2e2b91e1783eb86713c6c9aa659366392e5c569665396558d475c358d934cd8b4ad8751d1743d70da398ce334cb31ce4b32e2b2ad1b26c5b0ed8791d4731e2749ca719d1783c8f13c2f628560d90e0798991625154358350d0758330ca314c3342c8b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6da4db6926db6db6da6924934d24926924d3492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000044037abfbdc000000", hexnat% "400000100040020000000", hexnat% "10300000000000000000000", hexnat% "130000000400000000", 11709359031163289600, 594475150812905472]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000024037abdfdc000000", hexnat% "400000100040020000000", hexnat% "10300000000000000000000", hexnat% "150000002000000000", 9961962375743537152, 2341871806232657920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840001ebc004497c000000", hexnat% "10300000000000000000000", hexnat% "160000000080000000", 231928233984, 989010709184512, 14680679254065152]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "820016eb80256d38000000", hexnat% "10040000040000000", hexnat% "10500000000000000000000", 79524003840, 15492118835363840, 141287244169216]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "107001723c4802dc0000000", hexnat% "8000004000044010000000", 9799832789762179072, 77443629056, 848273220829184, 13554779347222528]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000016100044910000000", hexnat% "10700000000000040000000", 15527303207452672, 9421530420995948544, hexnat% "160800000000000000", 142386755796992, 234277044224]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003
def vertexColumn : Fields := ⟨10, hexnat% "2e29c8f2b2aaa968da8e8ba719a6998e61d98e938ce8b8ae4785e0fae19c4f1b26a9964d98e4b9715a5994e51d58d934cd8b4ad4745d0f6c370ea368e6338e5334e332cc73c2e8b92ccb8acab86d1b26c5b0ed8791d4731e2749ca719d1783c8f13c2f628560d90e07989154354341d60e4330e2328c530ce0b42c8b06d0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db49b6d24db6db6db6d26db492492492492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000030fbe4d17bdc000000", hexnat% "83800000000000000000000", 295021526900539392, 859818629791744]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000205fffff7ffc000000", hexnat% "40000100000000000000000", hexnat% "800002000008000000000", hexnat% "2000008000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41000105573ef6db8000000", 78450262016, hexnat% "20a000000000000000", hexnat% "82800000000000000000000", 3378249476341760, 756622329584287744]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810002055fccfadc8000000", hexnat% "40000100002004010000000", hexnat% "800002000300004000000", 77846282240, 720857415355990016, hexnat% "2000008000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000101f87ffc93c000000", 27021806070136832, hexnat% "20e000000040000000", hexnat% "83800000000000000000000", 6755425210859520]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800007efffffffc000000", hexnat% "40000100000000000000000", hexnat% "80000200100000000000000", hexnat% "2000008000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4380010f47ffffffc000000", 756604737398243328, hexnat% "80000200100000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81000205fffdffffc000000", hexnat% "800002000200000000000", hexnat% "40000100000000000000000", hexnat% "2000008000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100020f0ffdfa8fc000000", hexnat% "40000100000004100000000", hexnat% "82800000000000000000000", 576460821022900224, 432345589997371392, 72092778410016768]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c10 c8
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c7
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c6
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41000105eefdf6938000000", 97777614848, hexnat% "80000200100000000000000", hexnat% "2000008000000000000000", 4539333755273216, hexnat% "800002000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000101ffdf1ffdc000000", 578343653081088, hexnat% "20e000000000000000", hexnat% "83800000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000100aafffc93c000000", hexnat% "20e000000040000000", hexnat% "83800000000000000000000", 94575594322264064, 1441151880758558720, 231928233984]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2305266588296675328, hexnat% "20e000000040000000", hexnat% "83800000000000000000000", 576144898260992, hexnat% "40000100000004000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2305266040151474176, hexnat% "20e000000000000000", hexnat% "83800000000000000000000", 576694117203968, hexnat% "40000100000004000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800003efffffffc000000", hexnat% "40000100000000000000000", hexnat% "80000200100000000000000", hexnat% "1000004000000000000000", hexnat% "2000008000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2233174086643613696, hexnat% "1000004000000000000000", hexnat% "40000100002040000000000", 72101574503038976, hexnat% "20a000000000000000", hexnat% "82800000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200010850ffffffc000000", 58546795155816448, hexnat% "206000000000000000", hexnat% "81800000000000000000000", 1882504644240867328]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2305257792673415168, hexnat% "20e000000040000000", hexnat% "83800000000000000000000", hexnat% "40000100002044010000000", 17592253153280]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c380020e44dc7397c000000", hexnat% "100002004000000000", 4503627544657920, 62122406969344, 1918533441259831296, 72057594037927936]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200010055ffff93c000000", hexnat% "81800000000000040000000", 144115213845659648, 1774418253183975424, hexnat% "20e000000000000000", 2147483648]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300000444dcb3968000000", hexnat% "40000100002044010000000", 1918551033445875712, hexnat% "80000200100000080000000", hexnat% "800002000208004000000", 4503625397174272, 9223372036854775808]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c30 c21
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c31 c17
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c32 c18
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c33 c17
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c34 c16
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c35 c15
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c36 c14
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c37 c13
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c38 c5
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c39 c4
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c40 c3
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c41 c0
  c42
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record003
