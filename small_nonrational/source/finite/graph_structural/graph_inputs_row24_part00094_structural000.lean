module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00094Data
public import GraphInputsRow24Part00094Frames
public import GraphInputsRow24Part00094Leaves
public import GraphInputsRow24Part00094Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00094.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006
def vertexColumn : Fields := ⟨10, hexnat% "ae0f4a715c2f07cac8f2aa96aa6a3a2e87a39a96358b61da8e538ae1ba1e2785e0fab13c6a95a699566392e47939695554d52d475a354d2b46d8751d2745d0f6a358ce3a4e5334e332cc73c2e8b52e2b4acab1ae1b26c5b0ee8761cc729c6785c9715c3783c8f13c2f07d4643a912c47186439514951550d0768350ca318e0b42c2b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db4db6da4da69269249a6d24924936d24924926d2492693492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1834801e3073762800000", hexnat% "8000010000200800000000", hexnat% "14002a00000000000000", hexnat% "340400000000000000", 237494729703424, 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1977d3ea3452d6f800000", hexnat% "8000000000220000000000", 90072069856821248, 167125767421952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8003350ca3232d66800000", hexnat% "4003200000000000000", hexnat% "180480000000000000000", 90076467903332352, 237494662594560, hexnat% "10000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4353e23992d6f800000", hexnat% "8001000000220000000000", 54047593574957056, 72128040091516928, hexnat% "112480000000000000000", hexnat% "80000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "97302be3df3f6f800000", hexnat% "8000010400200000000000", 1152921504606846976, hexnat% "c0000000000000000", hexnat% "100400000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "870022e3bf256b800000", hexnat% "8000010000000800000000", 72128040158625792, hexnat% "110480800000000000000", hexnat% "301400000000000000", hexnat% "40000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1937d1f22dc3f6f800000", hexnat% "4002000010000000000", 54326869528412160, hexnat% "8000000000200000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "933c1fc3de3f6f800000", 9008298766368768, hexnat% "402000000000000000", hexnat% "8000010000200000000000", hexnat% "104000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "122d1d02dc3f6f800000", 9289773743079424, 54045394551701504, hexnat% "8001000000200000000000", hexnat% "180500000000000000000", hexnat% "4002200000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80012d06c3262f27800000", 238594157445120, hexnat% "180500000000000000000", 81064863085887488, hexnat% "4003800000000000000", hexnat% "12000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1970c3fe3573f67800000", hexnat% "300000000000000000", hexnat% "400000000008000000", hexnat% "8000010000200000000000", 149533581377536]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "197343f02112324800000", hexnat% "8000010000200802000000", hexnat% "480020000040000000", 224300523061248, 54326869528412160, 85899345920]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "175c3fe3ff3f6f800000", hexnat% "210000000000000000", hexnat% "180000000000000000000", hexnat% "8000000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "975c3fe3473f6f800000", hexnat% "210000000000000000", hexnat% "100000000100000000000", hexnat% "8000000000200000000000", 149533581377536]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8017513fe3ff332f800000", 52613349376, hexnat% "240000000000000000", hexnat% "180080000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8097713fc2233f6f800000", hexnat% "40001000000000000", hexnat% "100080020000000000000", 241892558110720]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17713e0203372e800000", hexnat% "8000000000200800000000", hexnat% "800c0000000000000000", hexnat% "100000120000040000000", 54329068551667712, 237494528376832]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8004012002202926800000", 54331267574923264, hexnat% "301c00000000000000", 238594174222336, hexnat% "110480020000000000000", hexnat% "83040200000000000000", 72057689600950272]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c27 c16
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c28 c13
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c29 c12
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c31 c4
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c33 c0
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00094.record006
