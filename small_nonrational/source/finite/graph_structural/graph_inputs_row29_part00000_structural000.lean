module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00000Data
public import GraphInputsRow29Part00000Frames
public import GraphInputsRow29Part00000Leaves
public import GraphInputsRow29Part00000Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00000.record040
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040
def vertexColumn : Fields := ⟨10, hexnat% "f0b32b29caaaa6a6695ab19c6a9a6665956338ae1b89e17bc1cc6c9726a99a599566c5716a599595554cd2b46d2745db0dc3c8ea398f1364d538cd33a2d8b92d4b32e2b2ac6b46c9b16e8761e4751cc789ca719d1725c570f382d083a0d88e1382e07b81d04390d48d1342d07703a0d8390d4388d130cc8b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4db6db6db6d24926db6db6db692492492492492492492492492489249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002100043e8ef794800000000", 5102421147648, hexnat% "3c0000000000000000", hexnat% "1e000000000000000000000", 1369235092928462848, 292736174802337792]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800210007f00f81ffc00000000", hexnat% "1e000000000000000000000", 11313042263954685952, 7062770115623780352, 1090715534753792]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1200025dffffffc00000000", hexnat% "22000000000000000", hexnat% "4000080000000000000000", hexnat% "80021000400000000000000000", hexnat% "8000100000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80023000479dfaaf1400000000", hexnat% "380000000000000000", hexnat% "1c000000000000000000000", 87995289960448, 4756927931043807232, 2306124621629358080]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80021000433cfbe72400000000", 9174050144256, hexnat% "3c0000000000000000", hexnat% "1e000000000000000000000", 13835076197224022016, 217298682020626432]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "120002446fff9c400000000", hexnat% "580000000000000000", hexnat% "2c000000000000000000000", 648518449420566528, hexnat% "80001000039000000000000000", 2305849743722414080]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800230004704ffff0400000000", hexnat% "380000000000000000", hexnat% "1c000000000000000000000", 11024811887802974208, 515396075520, 7061644765472751616]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "33cfbef7c00000000", hexnat% "80021000400000000000000000", 13835076197224022016, hexnat% "3c0000000000000000", hexnat% "1e000000000000000000000", 217298682020626432]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8003f0007f0ddadffc00000000", 10449758510383104, 17437937757178560512]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e000080ddadffc00000000", hexnat% "40000200000000000", hexnat% "700000000000000000", hexnat% "80001000039000000000000000", 2451365572173103104, 4620693217682128896]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800050000bfffffffc00000000", hexnat% "20000400000000000000000", hexnat% "340000000000000000", hexnat% "1a000000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000100003fffe5fc800000000", 176007759790080, hexnat% "7c0000000000000000", hexnat% "3e000000000000000000000", 281612415664128]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002100043ffda8b1800000000", 22969485099008, hexnat% "3c0000000000000000", hexnat% "1e000000000000000000000", 10520127254560768]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002100043949a030800000000", hexnat% "3c0000000000000000", hexnat% "1e000000000000000000000", 648729521293361152, 4629727080093843456, 9046798853210112, 2451366259367870464]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c21 c6
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c22 c5
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c23 c4
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00000.record040_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00000.record040
