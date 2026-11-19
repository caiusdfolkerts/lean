module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00035Data
public import GraphInputsRow23Part00035Frames
public import GraphInputsRow23Part00035Leaves
public import GraphInputsRow23Part00035Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002
def vertexColumn : Fields := ⟨10, hexnat% "f2c68d6c3a2e4b8ae1ba1e478f1c64d5c362d4b4ad1b61d47713a4d9394d532cc73c2e2b4acab1ac9b16c3bc1e8761e4751e2749e1745c9715c8f13c1f390e234a1a468c6298668390e0b8e134619464c5294658350d0b4c328c6384d1324c5382d0b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4010003010000000000000", hexnat% "3e00000000000000000", hexnat% "f80000000000000000000", hexnat% "10641800001e4000000000", hexnat% "2008040808000000000000", 2218264709038080, 540431955284459520, hexnat% "3c060000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022
def vertexColumn : Fields := ⟨10, hexnat% "9723c5693a358b68b92e2b86e8791e2783eca719965598e539a9695954d58d4b59352d2b46d4749d0f5a364d5334d332cd4b8acab1ae1b26c3b31e2749c6785d170de0f43c8f8b21c1712a4685a298961584e0b81e8a529865191662529615254558344d0b41d48ca344c9314d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "312383ec0e5de0000000000", hexnat% "1c0010018000000000000", hexnat% "cc00000000010000000000", hexnat% "7c00000200000000000", hexnat% "c02000000000000000000000", hexnat% "300000000100000000000000", 4467570830351532032, hexnat% "c0000000002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28a08fdc0edcd0000000000", hexnat% "7020000300000000000", hexnat% "15400000000020000000000", hexnat% "1f0000010000000000000", hexnat% "c02000000000000000000000", hexnat% "c0000000002000000000000", 4467570830351532032, hexnat% "300000000100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "322381cc1f5ee0000000000", hexnat% "1c0030008000000000000", hexnat% "cc00000000010000000000", 4467588422537576448, hexnat% "301000000000000000000000", hexnat% "c00000200000000000000000", hexnat% "7c00000000000000000", hexnat% "c0000000002000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18a00197ffdfb0000000000", hexnat% "8048000000000000000", hexnat% "26400000000040000000000", hexnat% "1f0020000000000000000", hexnat% "301000000000000000000000", hexnat% "c0000000002000000000000", hexnat% "7c00000000000000000", hexnat% "c00000200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "df743fff8fffff0000000000", hexnat% "300000000000000000000", 6917529027641081856, hexnat% "c0000000000000000000", hexnat% "8800000000000000000000", hexnat% "200000001000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777f3fffffeff0000000000", hexnat% "c000000000000000000", hexnat% "80800000000000000000000", hexnat% "200000000000000000000000", hexnat% "8000000001000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777f3ffa7fedf0000000000", 4611967493404098560, hexnat% "c000000000000000000", hexnat% "8800000000000000000000", hexnat% "200000001000000000000000", hexnat% "80000000800200000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d777b1fefffeff0000000000", hexnat% "80800000000000000000000", hexnat% "8000001000000000000", hexnat% "6010000000000000000", hexnat% "200040000000000000000000", hexnat% "8000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d774b1fee7ffdf0000000000", hexnat% "300000000000000000000", hexnat% "c000000000000000000", hexnat% "80000000800200000000000", hexnat% "2010000000000000000", hexnat% "8800000000000000000000", hexnat% "200040001000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d7b638fec6e7df0000000000", hexnat% "4800000000000000000000", hexnat% "7010000200000000000", hexnat% "80000000800000000000000", hexnat% "200040001118000000000000", 2305843009213693952, hexnat% "180000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d76638fcc7fdcf0000000000", hexnat% "8800010000000000000000", 4035278042682097664, hexnat% "1c0020000000000000000", hexnat% "201000000000000000000000", hexnat% "80001000002000000000000", hexnat% "6000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffff0fb86fcbf0000000000", 1224979098644774912, hexnat% "7000000000000000000", 6917529027641081856, hexnat% "8040001400000000000", 577023702256844800]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefd3dfdfeffff0000000000", hexnat% "200000000000000000000", hexnat% "40000100000000000000", hexnat% "10000020000000000000000", hexnat% "82000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefd79f9bffebf0000000000", hexnat% "200040000000000000000", hexnat% "10000020000000000000000", 4612037862148276224, hexnat% "6000000000000000000", hexnat% "80000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefffeff8efdff0000000000", hexnat% "10000000000000000000000", hexnat% "1000002000000000000", 1224979098644774912, 6917529027641081856]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffdfafb8efcbf0000000000", 1224979098644774912, hexnat% "5000000000000000000", hexnat% "200040000000000000000", 6917529027641081856, 914793674309632]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "feffb0fd8eecbf0000000000", hexnat% "10000020000000000000000", hexnat% "1000002000000000000", hexnat% "40001110000000000000", 6917529027641081856, hexnat% "6000000000000000000", hexnat% "8000001400000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffe38ff86fddf0000000000", 6917529027641081856, hexnat% "40001100000000000000", hexnat% "180000000000000000000", hexnat% "1000802200000000000", hexnat% "6000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff7f30fe86fc9e0000000000", hexnat% "40001100000000000000", 6917529027641081856, hexnat% "c000000000000000000", hexnat% "82010000000000000000", hexnat% "8000000001410000000000", hexnat% "1000802200000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d63f30f886e48e0000000000", 6917529027641081856, hexnat% "c000000000000000000", hexnat% "1c000000000000000000000", hexnat% "80001000802300000000000", hexnat% "200040001118000000000000", hexnat% "82030000000000000000", hexnat% "40001410000000000"]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c30 c25
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c31 c14
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42a00fdfc0d3fd0000000000", hexnat% "200000024000000000000", hexnat% "15400000000020000000000", 4469822630165217280, hexnat% "800080200000000000000000", hexnat% "c0800000000000000000000", hexnat% "170000000000000000000", hexnat% "300000000100000000000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f77df2ffffff7f0000000000", hexnat% "200000000000000000000", hexnat% "8000000000800000000000", hexnat% "80001000000000000000000", hexnat% "c000000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f77730ffffff7f0000000000", hexnat% "8000000800000000000", hexnat% "c0000000000000000000", hexnat% "8800000000000000000000", hexnat% "80001000000000000000000", hexnat% "6000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "777430ffe7f7ef0000000000", hexnat% "300000000000000000000", hexnat% "c000000000000000000", hexnat% "8800000008000000000000", hexnat% "800082000000000000000000", hexnat% "40001000000000000000", hexnat% "80001000800100000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "775638ffc7e5cf0000000000", hexnat% "8800000008000000000000", hexnat% "7000000300000000000", hexnat% "1c0000010000000000000", hexnat% "802000000000000000000000", hexnat% "80000000802000000000000", 3458764513820540928]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffff0df87dd3f0000000000", hexnat% "2200000000000000000", 4035225266123964416, 4620904323914661888, hexnat% "c000000000000000000", hexnat% "1000002000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfd3fdfefefff0000000000", hexnat% "200000000000000000000", hexnat% "80200000000000000000", hexnat% "20000000010000000000000", hexnat% "40001000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfdb7ffcfcf3f0000000000", hexnat% "200000020000000000000", hexnat% "20000000010000000000000", 3458764513820540928, hexnat% "8000000c00000000000", hexnat% "40000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfff1dff7fdff0000000000", hexnat% "20000000000000000000000", 577023702256844800, hexnat% "2200000000000000000", hexnat% "c000000000000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffdf1dfd7dd3f0000000000", 2882303761517117440, hexnat% "2200000000000000000", hexnat% "200000020000000000000", hexnat% "c000000000000000000", 774056185954304]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c47 c46
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdff71dd87ed3f0000000000", hexnat% "20000000010000000000000", 577023702256844800, 3458764513820540928, hexnat% "82220000000000000000", hexnat% "c000000000000000000", 4611897124659920896]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c50 c45
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c51 c42
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffe30dfc7fdef0000000000", hexnat% "c000000000000000000", hexnat% "82200000000000000000", hexnat% "140000000000000000000", hexnat% "1000802100000000000", 3458764513820540928]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ff7f30df87f52e0000000000", 6917529027641081856, hexnat% "82200000000000000000", hexnat% "c000000000000000000", hexnat% "40001008000000000000", hexnat% "8000000000c10000000000", hexnat% "1000802100000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "753f30dc87c50e0000000000", hexnat% "c000000000000000000", 6917529027641081856, hexnat% "2c000000000000000000000", hexnat% "80001000802300000000000", hexnat% "800082230000000000000000", hexnat% "40001018000000000000", 9219404998901760]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c57 c52
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c58 c41
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c59 c40
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5190081a7efffb0000000000", hexnat% "200048000000000000000", hexnat% "26400000000040000000000", hexnat% "200040000100000000000000", hexnat% "7c10000000000000000", hexnat% "c0800000000000000000000", hexnat% "800080200000000000000000", hexnat% "130000000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefe38ffe6f7ef0000000000", hexnat% "10000000000100000000000", hexnat% "40001108000000000000", hexnat% "7000000000000000000", hexnat% "180000000000000000000", 576460752303423488]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefc37dffedfbd0000000000", hexnat% "8000000400000000000", hexnat% "300000000000000000000", hexnat% "10000000020020000000000", hexnat% "40000100000000000000", hexnat% "80200000000000000000"]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fefc30dfe6f7ed0000000000", hexnat% "c000000000000000000", hexnat% "300000000000000000000", hexnat% "82200000000000000000", hexnat% "10000000000120000000000", hexnat% "1000800000000000000", hexnat% "40001108000000000000"]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c65 c62
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfe3cdec7ffdf0000000000", hexnat% "20000000000200000000000", 4035225266123964416, hexnat% "82210000000000000000", hexnat% "140000000000000000000", hexnat% "1000000000000000000"]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfc3fdbbeffbb0000000000", 4611756387171565568, hexnat% "300000000000000000000", hexnat% "20000040000040000000000", hexnat% "40000100000000000000", hexnat% "80200000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdfc34dae6ff9b0000000000", hexnat% "8040000400000000000", hexnat% "300000000000000000000", hexnat% "40001100000000000000", hexnat% "20000000000240000000000", hexnat% "1000800000000000000", hexnat% "82210000000000000000"]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c69 c68
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c70 c67
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5cbc30d8e6c7890000000000", hexnat% "c000000000000000000", hexnat% "300000000000000000000", hexnat% "200040001118000000000000", hexnat% "800082230000000000000000", hexnat% "34000000000000000000000", hexnat% "1000800300000000000", hexnat% "40020460000000000"]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c72 c71
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c73 c66
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5400001866c5880000000000", hexnat% "cc08000000000000000", hexnat% "330000000000000000000", hexnat% "3c400000000000000000000", hexnat% "80001000802300000000000", hexnat% "200040001118000000000000", hexnat% "800082230000000000000000", hexnat% "40020470000000000", hexnat% "3800000000000000000000"]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c76 c61
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c77 c60
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c78 c35
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c79 c34
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c80 c3
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c81 c2
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c82 c1
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c83 c0
  c84
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024
def vertexColumn : Fields := ⟨10, hexnat% "c9aa669b16959568d93633a2e4b86e8791e2783ec96a569715955558d5353362d4b46d8751d2743dc8ea368f1394d538cd3332e2b4ac6b86d1b26c3bc1e8761e4751cc719c970de0f43cac170aa16a26498a6859161588e1382e078a916625494a5855151548d1342d0762348ca384d1314c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020002001180000000000", hexnat% "703c0000000000000", hexnat% "381c00800000000000", hexnat% "703c00000000000000000", hexnat% "381c000000000000000000", hexnat% "703c000000000000000000000", hexnat% "381c0000000000000000000000", 17557001672327168, hexnat% "c000c000c000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c8ea39b169595635876c3a2e4b8ae1ba1e478f13a4e5c5655554d51d70d8b52d2b46d8751dc4e9364e5354cb31cf0ba2d8b32e2b4ac6b86d1b26f0791d4731e2749ca725c3723c4f07ce2348aa19a16458568390e0b8e1344a919615454558350d0b4c328c6384d1324c5382d0b22c2b81d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 93), (facetIndex 94), (facetIndex 95)])))
 (.branch 3
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 92)]))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 41), (facetIndex 49), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))))
 (.branch 9
 (.leaf ([(facetIndex 37), (facetIndex 48), (facetIndex 50), (facetIndex 51), (facetIndex 66), (facetIndex 67), (facetIndex 81), (facetIndex 82)]))
 (.branch 10
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 59)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "111555554444488000333332222288777777a6666666887899999979668z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6, 7]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9, 10]
def grouped2_0018 : List Nat := [9]
def grouped2_0019 : List Nat := [9, 10]
def grouped2_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001" 61

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001" "{\"ridges\":[[12,19],[12,273],[12,274],[13,529],[13,530],[21,21],[21,273],[21,276],[22,21],[22,532],[31,274],[31,276],[32,532],[49,19],[50,273],[50,274],[51,19],[51,530],[59,19],[60,19],[61,273],[61,274],[62,530],[63,273],[63,274],[64,529],[64,530],[65,273],[65,274],[65,529],[65,530],[66,21],[66,273],[66,276],[67,532],[73,21],[74,21],[75,84],[75,273],[75,276],[76,84],[76,532],[77,273],[77,532],[81,274],[81,276],[82,532],[88,84],[89,84],[90,84],[90,274],[90,276],[91,84],[92,274],[92,276],[93,70],[95,82]],\"owners\":[[93,70,[3,30,38,46,47,90,91],[33,45,83,89]],[95,82,[10,30,61,62,90,91],[35,59,88]],[12,273,[21,66,75,77],[50,61,63,65]],[21,273,[12,50,61,63,65],[66,75,77]],[50,273,[21,75,77],[12,61,63,65,66]],[61,273,[21,66,77],[12,50,63,65,75]],[63,273,[21,66,75,77],[12,50,61,65]],[65,273,[21,66,75],[12,50,61,63,77]],[66,273,[12,61,63,65],[21,50,75,77]],[75,273,[12,50,63,65],[21,61,66,77]],[77,273,[12,50,61,63],[21,65,66,75]],[12,274,[31,81,90,92],[50,61,63,65]],[31,274,[12,50,61,63,65],[81,90,92]],[50,274,[31,90,92],[12,61,63,65,81]],[61,274,[31,81,92],[12,50,63,65,90]],[63,274,[31,81,90,92],[12,50,61,65]],[65,274,[31,81,90],[12,50,61,63,92]],[81,274,[12,61,63,65],[31,50,90,92]],[90,274,[12,50,63,65],[31,61,81,92]],[92,274,[12,50,61,63],[31,65,81,90]],[13,529,[22,67,76,77],[51,62,64,65]],[64,529,[22,67,76,77],[13,51,62,65]],[65,529,[22,67,76],[13,51,62,64,77]],[13,530,[32,82,91,92],[51,62,64,65]],[51,530,[32,91,92],[13,62,64,65,82]],[62,530,[32,82,92],[13,51,64,65,91]],[64,530,[32,82,91,92],[13,51,62,65]],[65,530,[32,82,91],[13,51,62,64,92]],[75,84,[30,88,89,91],[20,73,74,76,90]],[76,84,[30,88,89,90],[20,73,74,75,91]],[88,84,[20,74,75,76],[30,73,89,90,91]],[89,84,[20,73,75,76],[30,74,88,90,91]],[90,84,[20,73,74,76],[30,75,88,89,91]],[91,84,[20,73,74,75],[30,76,88,89,90]],[21,276,[31,81,90,92],[66,75,77]],[31,276,[21,66,75,77],[81,90,92]],[66,276,[31,90,92],[21,75,77,81]],[75,276,[31,81,92],[21,66,77,90]],[81,276,[21,75,77],[31,66,90,92]],[90,276,[21,66,77],[31,75,81,92]],[92,276,[21,66,75],[31,77,81,90]],[22,532,[32,82,91,92],[67,76,77]],[32,532,[22,67,76,77],[82,91,92]],[67,532,[32,91,92],[22,76,77,82]],[76,532,[32,82,92],[22,67,77,91]],[77,532,[32,82,91],[22,67,76,92]],[82,532,[22,76,77],[32,67,91,92]]],\"edges\":[[33,[12,21,31,50,61,63,65,66,75,77,81,90,92]],[34,[13,22,32,51,62,64,65,67,76,77,82,91,92]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-15],[-17,-12],[-17,-15],[-17,-16],[-18,-12],[-19,-18],[-20,-17],[-20,-18],[-21,-3],[-21,-16],[-21,-18],[-21,-20],[-22,-17],[-22,-18],[-22,-21],[-23,-17],[-23,-18],[-24,-17],[-24,-18],[-24,-21],[-25,-15],[-25,-17],[-27,-1],[-27,-11],[-27,-13],[-27,-14],[-28,-2],[-28,-20],[-28,-21],[-29,-7],[-29,-26],[-29,-27],[-29,-28],[-30,-6],[-30,-7],[-30,-25],[-30,-29],[-31,-5],[-31,-7],[-31,-27],[-31,-28],[-31,-29],[-31,-30],[-32,-18],[-32,-27],[-32,-28],[-34,-18],[-34,-27],[-34,-28],[-35,-15],[-35,-17],[-37,-27],[-38,-28],[-39,-10],[-39,-36],[-40,-9],[-40,-30],[-40,-35],[-40,-39],[-41,-8],[-41,-31],[-41,-37],[-41,-38],[-41,-39],[-41,-40],[-42,-18],[-42,-28],[-42,-38],[-43,-33],[-44,-18],[-44,-27],[-44,-37],[-3,-15,-18],[-3,-17,-19],[-6,-7,-27],[-6,-7,-28],[-7,-25,-27],[-7,-25,-28],[-42,1,8,11,13,14,39,40],[-44,2,8,20,21,39,40],[-3,6,25,29,31],[-6,3,16,20,22,24],[-16,6,29,31],[-20,6,25,31],[-22,6,25,29,31],[-24,6,25,29],[-25,3,20,22,24],[-29,3,16,22,24],[-31,3,16,20,22],[-3,9,35,39,41],[-9,3,16,20,22,24],[-16,9,39,41],[-20,9,35,41],[-22,9,35,39,41],[-24,9,35,39],[-35,3,20,22,24],[-39,3,16,22,24],[-41,3,16,20,22],[-4,7,26,30,31],[-23,7,26,30,31],[-24,7,26,30],[-4,10,36,40,41],[-17,10,40,41],[-21,10,36,41],[-23,10,36,40,41],[-24,10,36,40],[-29,8,37,38,40],[-30,8,37,38,39],[-37,5,28,29,30],[-38,5,27,29,30],[-39,5,27,28,30],[-40,5,27,28,29],[-6,9,35,39,41],[-9,6,25,29,31],[-25,9,39,41],[-29,9,35,41],[-35,6,29,31],[-39,6,25,31],[-41,6,25,29],[-7,10,36,40,41],[-10,7,26,30,31],[-26,10,40,41],[-30,10,36,41],[-31,10,36,40],[-36,7,30,31],[-45,32,33,34],[-46,42,43,44],[-47,27,28,29,30,31],[-48,37,38,39,40,41],[-49,12,15,19,20,21,22,23,24],[-50,18],[-51,45],[-51,46],[-52,47],[-53,52],[-54,51],[-54,53],[-55,49],[-56,48],[-56,55],[-57,50],[-58,57],[-59,56,58],[-60,56],[-60,58],[-61,54,60],[-61,59],[61],[3,6,9,16,20,22,24,25,29,31,35,39,41],[4,7,10,17,21,23,24,26,30,31,36,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":12},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":51},{\"tag\":\"incompatible\",\"a\":63,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":51},{\"tag\":\"incompatible\",\"a\":73,\"b\":3},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":10},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":74,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":22},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":21},{\"tag\":\"incompatible\",\"a\":76,\"b\":22},{\"tag\":\"incompatible\",\"a\":76,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":20},{\"tag\":\"incompatible\",\"a\":77,\"b\":22},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":59},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"incompatible\",\"a\":78,\"b\":74},{\"tag\":\"incompatible\",\"a\":80,\"b\":59},{\"tag\":\"incompatible\",\"a\":80,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":49},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":74},{\"tag\":\"incompatible\",\"a\":90,\"b\":32},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":91,\"b\":31},{\"tag\":\"incompatible\",\"a\":91,\"b\":76},{\"tag\":\"incompatible\",\"a\":91,\"b\":81},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":30},{\"tag\":\"incompatible\",\"a\":92,\"b\":77},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":93,\"b\":59},{\"tag\":\"incompatible\",\"a\":93,\"b\":74},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"incompatible\",\"a\":94,\"b\":79},{\"tag\":\"incompatible\",\"a\":95,\"b\":59},{\"tag\":\"incompatible\",\"a\":95,\"b\":73},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[12,49,59]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[12,51,60]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[21,22,73]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[21,22,74]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[22,66,73]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[22,66,74]},{\"tag\":\"mate\",\"ridge\":70,\"a\":93,\"owners\":[3,30,38,46,47,90,91]},{\"tag\":\"mate\",\"ridge\":82,\"a\":95,\"owners\":[10,30,61,62,90,91]},{\"tag\":\"mate\",\"ridge\":273,\"a\":12,\"owners\":[21,66,75,77]},{\"tag\":\"mate\",\"ridge\":273,\"a\":21,\"owners\":[12,50,61,63,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":50,\"owners\":[21,75,77]},{\"tag\":\"mate\",\"ridge\":273,\"a\":61,\"owners\":[21,66,77]},{\"tag\":\"mate\",\"ridge\":273,\"a\":63,\"owners\":[21,66,75,77]},{\"tag\":\"mate\",\"ridge\":273,\"a\":65,\"owners\":[21,66,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":66,\"owners\":[12,61,63,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":75,\"owners\":[12,50,63,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":77,\"owners\":[12,50,61,63]},{\"tag\":\"mate\",\"ridge\":274,\"a\":12,\"owners\":[31,81,90,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":31,\"owners\":[12,50,61,63,65]},{\"tag\":\"mate\",\"ridge\":274,\"a\":50,\"owners\":[31,90,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":61,\"owners\":[31,81,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":63,\"owners\":[31,81,90,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":65,\"owners\":[31,81,90]},{\"tag\":\"mate\",\"ridge\":274,\"a\":81,\"owners\":[12,61,63,65]},{\"tag\":\"mate\",\"ridge\":274,\"a\":90,\"owners\":[12,50,63,65]},{\"tag\":\"mate\",\"ridge\":274,\"a\":92,\"owners\":[12,50,61,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":13,\"owners\":[22,67,76,77]},{\"tag\":\"mate\",\"ridge\":529,\"a\":64,\"owners\":[22,67,76,77]},{\"tag\":\"mate\",\"ridge\":529,\"a\":65,\"owners\":[22,67,76]},{\"tag\":\"mate\",\"ridge\":530,\"a\":13,\"owners\":[32,82,91,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":51,\"owners\":[32,91,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":62,\"owners\":[32,82,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":64,\"owners\":[32,82,91,92]},{\"tag\":\"mate\",\"ridge\":530,\"a\":65,\"owners\":[32,82,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":75,\"owners\":[30,88,89,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":76,\"owners\":[30,88,89,90]},{\"tag\":\"mate\",\"ridge\":84,\"a\":88,\"owners\":[20,74,75,76]},{\"tag\":\"mate\",\"ridge\":84,\"a\":89,\"owners\":[20,73,75,76]},{\"tag\":\"mate\",\"ridge\":84,\"a\":90,\"owners\":[20,73,74,76]},{\"tag\":\"mate\",\"ridge\":84,\"a\":91,\"owners\":[20,73,74,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":21,\"owners\":[31,81,90,92]},{\"tag\":\"mate\",\"ridge\":276,\"a\":31,\"owners\":[21,66,75,77]},{\"tag\":\"mate\",\"ridge\":276,\"a\":66,\"owners\":[31,90,92]},{\"tag\":\"mate\",\"ridge\":276,\"a\":75,\"owners\":[31,81,92]},{\"tag\":\"mate\",\"ridge\":276,\"a\":81,\"owners\":[21,75,77]},{\"tag\":\"mate\",\"ridge\":276,\"a\":90,\"owners\":[21,66,77]},{\"tag\":\"mate\",\"ridge\":276,\"a\":92,\"owners\":[21,66,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":22,\"owners\":[32,82,91,92]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[22,67,76,77]},{\"tag\":\"mate\",\"ridge\":532,\"a\":67,\"owners\":[32,91,92]},{\"tag\":\"mate\",\"ridge\":532,\"a\":76,\"owners\":[32,82,92]},{\"tag\":\"mate\",\"ridge\":532,\"a\":77,\"owners\":[32,82,91]},{\"tag\":\"mate\",\"ridge\":532,\"a\":82,\"owners\":[22,76,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[78,79,80],\"full_literals\":[-45,32,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[93,94,95],\"full_literals\":[-46,42,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[73,74,75,76,77],\"full_literals\":[-47,27,28,29,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[88,89,90,91,92],\"full_literals\":[-48,37,38,39,40,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[41,49,60,61,62,63,64,65],\"full_literals\":[-49,12,15,19,20,21,22,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[59],\"full_literals\":[-50,18]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,56,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-60,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-61,54,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-61,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[12,21,31,50,61,63,65,66,75,77,81,90,92]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[13,22,32,51,62,64,65,67,76,77,82,91,92]}]}"
  "p cnf 61 150\n-16 -15 0\n-17 -12 0\n-17 -15 0\n-17 -16 0\n-18 -12 0\n-19 -18 0\n-20 -17 0\n-20 -18 0\n-21 -3 0\n-21 -16 0\n-21 -18 0\n-21 -20 0\n-22 -17 0\n-22 -18 0\n-22 -21 0\n-23 -17 0\n-23 -18 0\n-24 -17 0\n-24 -18 0\n-24 -21 0\n-25 -15 0\n-25 -17 0\n-27 -1 0\n-27 -11 0\n-27 -13 0\n-27 -14 0\n-28 -2 0\n-28 -20 0\n-28 -21 0\n-29 -7 0\n-29 -26 0\n-29 -27 0\n-29 -28 0\n-30 -6 0\n-30 -7 0\n-30 -25 0\n-30 -29 0\n-31 -5 0\n-31 -7 0\n-31 -27 0\n-31 -28 0\n-31 -29 0\n-31 -30 0\n-32 -18 0\n-32 -27 0\n-32 -28 0\n-34 -18 0\n-34 -27 0\n-34 -28 0\n-35 -15 0\n-35 -17 0\n-37 -27 0\n-38 -28 0\n-39 -10 0\n-39 -36 0\n-40 -9 0\n-40 -30 0\n-40 -35 0\n-40 -39 0\n-41 -8 0\n-41 -31 0\n-41 -37 0\n-41 -38 0\n-41 -39 0\n-41 -40 0\n-42 -18 0\n-42 -28 0\n-42 -38 0\n-43 -33 0\n-44 -18 0\n-44 -27 0\n-44 -37 0\n-3 -15 -18 0\n-3 -17 -19 0\n-6 -7 -27 0\n-6 -7 -28 0\n-7 -25 -27 0\n-7 -25 -28 0\n-42 1 8 11 13 14 39 40 0\n-44 2 8 20 21 39 40 0\n-3 6 25 29 31 0\n-6 3 16 20 22 24 0\n-16 6 29 31 0\n-20 6 25 31 0\n-22 6 25 29 31 0\n-24 6 25 29 0\n-25 3 20 22 24 0\n-29 3 16 22 24 0\n-31 3 16 20 22 0\n-3 9 35 39 41 0\n-9 3 16 20 22 24 0\n-16 9 39 41 0\n-20 9 35 41 0\n-22 9 35 39 41 0\n-24 9 35 39 0\n-35 3 20 22 24 0\n-39 3 16 22 24 0\n-41 3 16 20 22 0\n-4 7 26 30 31 0\n-23 7 26 30 31 0\n-24 7 26 30 0\n-4 10 36 40 41 0\n-17 10 40 41 0\n-21 10 36 41 0\n-23 10 36 40 41 0\n-24 10 36 40 0\n-29 8 37 38 40 0\n-30 8 37 38 39 0\n-37 5 28 29 30 0\n-38 5 27 29 30 0\n-39 5 27 28 30 0\n-40 5 27 28 29 0\n-6 9 35 39 41 0\n-9 6 25 29 31 0\n-25 9 39 41 0\n-29 9 35 41 0\n-35 6 29 31 0\n-39 6 25 31 0\n-41 6 25 29 0\n-7 10 36 40 41 0\n-10 7 26 30 31 0\n-26 10 40 41 0\n-30 10 36 41 0\n-31 10 36 40 0\n-36 7 30 31 0\n-45 32 33 34 0\n-46 42 43 44 0\n-47 27 28 29 30 31 0\n-48 37 38 39 40 41 0\n-49 12 15 19 20 21 22 23 24 0\n-50 18 0\n-51 45 0\n-51 46 0\n-52 47 0\n-53 52 0\n-54 51 0\n-54 53 0\n-55 49 0\n-56 48 0\n-56 55 0\n-57 50 0\n-58 57 0\n-59 56 58 0\n-60 56 0\n-60 58 0\n-61 54 60 0\n-61 59 0\n61 0\n3 6 9 16 20 22 24 25 29 31 35 39 41 0\n4 7 10 17 21 23 24 26 30 31 36 40 41 0\n"
  "151 59 0 148 147 0\n152 -60 0 144 145 140 142 138 141 131 5 6 8 11 14 17 19 130 1 21 50 73 82 88 89 91 97 98 149 0\n153 54 0 152 148 146 0\n154 51 0 153 136 0\n155 53 0 153 137 0\n156 45 0 154 132 0\n157 46 0 154 133 0\n158 52 0 155 135 0\n159 47 0 158 134 0\n160 -18 0 156 157 44 47 66 70 126 127 69 0\n161 -50 0 160 131 0\n162 -57 0 161 141 0\n163 -58 0 162 142 0\n164 56 0 163 151 143 0\n165 48 0 164 139 0\n166 55 0 164 140 0\n167 49 0 166 138 0\n168 40 41 37 38 7 4 0 165 129 54 55 103 122 104 105 106 123 124 150 0\n169 -6 -7 0 159 39 35 30 75 76 128 0\n170 -28 -7 3 0 30 39 169 83 117 28 78 114 85 86 119 118 149 0\n171 -7 3 0 159 30 35 39 169 117 83 170 128 77 114 85 86 84 119 118 149 0\n172 29 31 6 28 20 16 41 39 27 3 0 159 128 117 36 114 85 86 149 0\n173 -31 0 165 38 40 41 42 43 61 111 112 109 110 129 0\n174 -17 3 16 20 39 41 0 173 13 18 22 51 91 88 82 149 0\n175 -21 3 16 20 39 41 0 173 15 20 87 91 96 88 82 149 0\n176 -40 41 28 27 0 173 159 56 57 58 128 116 0\n177 -29 7 17 21 40 41 0 173 31 37 100 101 121 99 125 150 0\n178 3 17 21 16 20 39 41 28 27 0 159 173 176 171 177 128 172 34 0\n179 29 -3 28 27 0 159 173 128 34 36 81 0\n180 -29 17 21 40 41 0 30 177 0\n181 17 21 41 28 27 0 159 173 176 180 128 179 34 36 83 84 118 178 0\n182 21 41 28 27 0 167 176 181 2 3 4 7 13 16 18 103 130 54 74 174 0\n183 41 28 27 0 182 9 10 12 15 20 175 97 0\n184 28 27 0 159 173 183 60 62 63 64 65 107 108 128 0\n185 -41 -28 0 156 157 67 46 49 126 69 127 29 28 27 60 64 65 80 0\n186 39 -28 0 156 157 165 173 185 67 46 49 126 69 127 72 53 33 28 129 56 58 90 92 115 95 94 113 149 0\n187 -28 0 156 157 46 49 53 67 126 69 127 72 185 186 54 55 59 102 120 168 0\n188 27 0 187 184 0\n189 -1 0 188 23 0\n190 -11 0 188 24 0\n191 -13 0 188 25 0\n192 -14 0 188 26 0\n193 -29 0 188 32 0\n194 -32 0 188 45 0\n195 -34 0 188 48 0\n196 -37 0 188 52 0\n197 -44 0 188 71 0\n198 33 0 195 194 156 126 0\n199 -43 0 198 69 0\n200 42 0 199 197 157 127 0\n201 -38 0 200 68 0\n202 10 36 41 40 0 196 201 102 120 168 0\n203 -39 41 0 54 55 59 202 0\n204 9 41 35 39 0 193 173 90 92 115 95 94 113 93 149 0\n205 39 41 0 196 165 201 129 56 58 204 0\n206 41 0 203 205 0\n207 -8 0 206 60 0\n208 -39 0 206 64 0\n209 -40 0 206 65 0\n210 0 207 208 189 190 191 192 200 209 79 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2aa96a3a699564d8ce8b92e1ba1e4789e0faa996639695554d4cd8b52d1b61d4749d0f723a8da3c4e5354e334ce8b92ccb4ac6b46c9b0ed8751cc789c6785c970de0f43cac1722a2aa1a16926299161588e1382e07a292a61916525295151548d1342d0762348ca384d1314e0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 53), (facetIndex 61), (facetIndex 62), (facetIndex 65), (facetIndex 68)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 51), (facetIndex 63), (facetIndex 78), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 52), (facetIndex 66), (facetIndex 79), (facetIndex 93)]))
 (.branch 4
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 59), (facetIndex 64), (facetIndex 81), (facetIndex 95)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 60), (facetIndex 67), (facetIndex 82), (facetIndex 96)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 50), (facetIndex 58), (facetIndex 76), (facetIndex 90)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 87), (facetIndex 88)])))
 (.branch 8
 (.leaf ([(facetIndex 69), (facetIndex 77), (facetIndex 80), (facetIndex 91), (facetIndex 94)]))
 (.branch 9
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 72), (facetIndex 75), (facetIndex 86), (facetIndex 89)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "437217596696664372175988988704203100435443302152211055z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8, 9]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9]
def grouped2_0016 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023" "{\"ridges\":[[3,70],[4,133],[8,73],[9,137],[9,138],[19,13],[19,76],[20,13],[21,84],[25,73],[27,41],[27,137],[27,168],[28,41],[31,76],[32,140],[33,84],[35,164],[37,88],[39,168],[41,28],[42,44],[42,140],[46,133],[48,70],[50,70],[50,133],[50,134],[51,70],[52,133],[54,137],[54,138],[56,73],[58,73],[58,137],[58,138],[59,73],[60,137],[60,138],[67,545],[70,28],[70,137],[70,140],[71,13],[71,28],[72,13],[72,28],[73,41],[73,44],[73,73],[74,13],[74,44],[75,13],[75,44],[80,25],[80,41],[82,137],[84,28],[85,28],[87,44],[88,44],[89,44]],\"owners\":[[3,70,[31,33,87,90,92],[48,50,51]],[48,70,[31,33,90,92],[3,50,51,87]],[50,70,[31,33,87,92],[3,48,51,90]],[51,70,[31,33,87,90],[3,48,50,92]],[4,133,[20,23,70,76,79],[46,50,52]],[46,133,[20,23,76,79],[4,50,52,70]],[50,133,[20,23,70,79],[4,46,52,76]],[52,133,[20,23,70,76],[4,46,50,79]],[50,134,[32,35,84,93],[4,46,52,90]],[80,25,[6,17,25,54,55,70,71],[26,53,69]],[28,41,[7,18,27,53,56,57,69,73,74],[80]],[80,41,[7,18,27,56,57,73,74],[28,53,69]],[8,73,[19,25,73,76,81],[56,58,59]],[56,73,[19,25,76,81],[8,58,59,73]],[58,73,[19,25,73,81],[8,56,59,76]],[59,73,[19,25,73,76],[8,56,58,81]],[9,137,[20,27,70,76,82],[54,58,60]],[54,137,[20,27,76,82],[9,58,60,70]],[58,137,[20,27,70,82],[9,54,60,76]],[60,137,[20,27,70,76],[9,54,58,82]],[9,138,[32,39,84,90,96],[54,58,60]],[54,138,[32,39,90,96],[9,58,60,84]],[58,138,[32,39,84,96],[9,54,60,90]],[60,138,[32,39,84,90],[9,54,58,96]],[67,545,[28,75,80],[16,49,62,68,82]],[88,44,[18,42,69,73,75],[30,74,83,87,89]],[19,76,[31,41,87,90],[73,76]],[31,76,[19,41,73,76],[87,90]],[32,140,[20,42,70,76],[84,90]],[21,84,[33,41,92],[78]],[33,84,[21,41,78],[92]],[35,164,[23,42,79],[93]],[37,88,[25,41,81],[95]],[27,168,[39,42,96],[82]],[39,168,[27,42,82],[96]]],\"edges\":[[20,[3,19,21,31,33,41,48,50,51,73,76,78,87,90,92]],[21,[4,20,23,32,35,42,46,50,52,70,76,79,84,90,93]],[26,[8,19,25,31,37,41,56,58,59,73,76,81,87,90,95]],[27,[9,20,27,32,39,42,54,58,60,70,76,82,84,90,96]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-36,-3],[-36,-4],[-36,-31],[-36,-32],[-36,-34],[-38,-36],[-41,-8],[-41,-9],[-41,-25],[-41,-40],[-42,-11],[-42,-41],[-43,-13],[-43,-41],[-43,-42],[-44,-7],[-44,-10],[-44,-25],[-44,-41],[-44,-43],[-45,-12],[-46,-14],[-46,-41],[-46,-44],[-46,-45],[-47,-41],[-47,-42],[-47,-43],[-47,-44],[-47,-46],[-49,-41],[-49,-42],[-50,-45],[-52,-43],[-53,-44],[-53,-46],[-54,-40],[-54,-48],[-54,-51],[-55,-16],[-55,-17],[-55,-41],[-56,-18],[-56,-42],[-56,-45],[-57,-55],[-57,-56],[-58,-17],[-58,-44],[-58,-55],[-58,-57],[-59,-19],[-59,-24],[-59,-33],[-59,-35],[-59,-42],[-59,-45],[-59,-55],[-60,-21],[-60,-55],[-60,-58],[-61,-55],[-61,-56],[-61,-58],[-61,-59],[-61,-60],[-62,-54],[-63,-55],[-63,-56],[-64,-58],[-64,-59],[-65,-54],[-66,-55],[-67,-58],[-67,-59],[-67,-60],[-9,-43,-45],[-10,-42,-46],[-10,-43,-45],[-1,16,18,58,61,63],[-27,16,18,61,63],[-28,16,18,58,63],[-29,16,18,58,61],[-2,10,12,41,47,50],[-26,10,12,47,50],[-28,10,12,41,50],[-30,10,12,41,47],[-28,17,19,55,64],[-51,3,7,13,32,33,41,42],[-15,4,8,14,31,34,35,40,44,45],[-51,4,8,14,34,35,44,45],[-14,-15,-44],[-5,9,13,44,47,52],[-34,9,13,47,52],[-36,9,13,44,52],[-37,9,13,44,47],[-13,-36,-44],[-6,10,14,41,47,53],[-32,10,14,47,53],[-36,10,14,41,53],[-38,10,14,41,47],[-14,-36,-41],[-36,-41,-53],[-6,17,21,55,61,67],[-32,17,21,61,67],[-36,17,21,55,67],[-38,17,21,55,61],[-39,15,46,51],[-22,-41,-56],[-22,-42,-55],[-22,-43,-55],[-59,8,23,40,44,46],[-23,-44,-59],[-23,-44,-60],[-23,-45,-58],[-23,-46,-58],[-9,16,22,58,61],[-16,9,22,44,47],[-17,10,23,41,47],[-17,-23,-41],[-11,18,22,63],[-18,11,22,49],[-19,12,23,50],[-20,13,22,52],[-14,21,23,67],[-21,14,23,53],[-68,34,35,38,39,53,67],[-69,24,25,28,36,47,61],[-70,54,55,56,58,59],[-71,40,48,51,62,65],[-72,41,42,44,45],[-73,43,46,57,60],[-74,68],[-75,74],[-76,75],[-77,69],[-77,70],[-78,72],[-78,73],[-79,71],[-79,78],[-80,77],[-80,79],[-81,76],[-81,80],[81],[1,9,11,16,18,22,27,28,29,44,47,49,58,61,63],[2,10,12,17,19,23,26,28,30,41,47,50,55,61,64],[5,9,13,16,20,22,34,36,37,44,47,52,58,61,66],[6,10,14,17,21,23,32,36,38,41,47,53,55,61,67]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":58,\"b\":6},{\"tag\":\"incompatible\",\"a\":58,\"b\":7},{\"tag\":\"incompatible\",\"a\":58,\"b\":53},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":18},{\"tag\":\"incompatible\",\"a\":70,\"b\":19},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":21},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":25},{\"tag\":\"incompatible\",\"a\":72,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":17},{\"tag\":\"incompatible\",\"a\":73,\"b\":20},{\"tag\":\"incompatible\",\"a\":73,\"b\":44},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":23},{\"tag\":\"incompatible\",\"a\":75,\"b\":27},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":72},{\"tag\":\"incompatible\",\"a\":82,\"b\":73},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":83,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":84,\"b\":31},{\"tag\":\"incompatible\",\"a\":84,\"b\":32},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"incompatible\",\"a\":85,\"b\":33},{\"tag\":\"incompatible\",\"a\":85,\"b\":71},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":35},{\"tag\":\"incompatible\",\"a\":88,\"b\":43},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":57},{\"tag\":\"incompatible\",\"a\":88,\"b\":71},{\"tag\":\"incompatible\",\"a\":88,\"b\":74},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":84},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":83},{\"tag\":\"incompatible\",\"a\":92,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":93,\"b\":87},{\"tag\":\"incompatible\",\"a\":93,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":84},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":89},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[19,72,74]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[20,71,75]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[20,72,74]},{\"tag\":\"mate\",\"ridge\":70,\"a\":3,\"owners\":[31,33,87,90,92]},{\"tag\":\"mate\",\"ridge\":70,\"a\":48,\"owners\":[31,33,90,92]},{\"tag\":\"mate\",\"ridge\":70,\"a\":50,\"owners\":[31,33,87,92]},{\"tag\":\"mate\",\"ridge\":70,\"a\":51,\"owners\":[31,33,87,90]},{\"tag\":\"mate\",\"ridge\":133,\"a\":4,\"owners\":[20,23,70,76,79]},{\"tag\":\"mate\",\"ridge\":133,\"a\":46,\"owners\":[20,23,76,79]},{\"tag\":\"mate\",\"ridge\":133,\"a\":50,\"owners\":[20,23,70,79]},{\"tag\":\"mate\",\"ridge\":133,\"a\":52,\"owners\":[20,23,70,76]},{\"tag\":\"mate\",\"ridge\":134,\"a\":50,\"owners\":[32,35,84,93]},{\"tag\":\"mate\",\"ridge\":25,\"a\":80,\"owners\":[6,17,25,54,55,70,71]},{\"tag\":\"mate\",\"ridge\":41,\"a\":28,\"owners\":[7,18,27,53,56,57,69,73,74]},{\"tag\":\"mate\",\"ridge\":41,\"a\":80,\"owners\":[7,18,27,56,57,73,74]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[27,28,73]},{\"tag\":\"mate\",\"ridge\":73,\"a\":8,\"owners\":[19,25,73,76,81]},{\"tag\":\"mate\",\"ridge\":73,\"a\":56,\"owners\":[19,25,76,81]},{\"tag\":\"mate\",\"ridge\":73,\"a\":58,\"owners\":[19,25,73,81]},{\"tag\":\"mate\",\"ridge\":73,\"a\":59,\"owners\":[19,25,73,76]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[25,58,73]},{\"tag\":\"mate\",\"ridge\":137,\"a\":9,\"owners\":[20,27,70,76,82]},{\"tag\":\"mate\",\"ridge\":137,\"a\":54,\"owners\":[20,27,76,82]},{\"tag\":\"mate\",\"ridge\":137,\"a\":58,\"owners\":[20,27,70,82]},{\"tag\":\"mate\",\"ridge\":137,\"a\":60,\"owners\":[20,27,70,76]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[27,58,70]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[58,70,82]},{\"tag\":\"mate\",\"ridge\":138,\"a\":9,\"owners\":[32,39,84,90,96]},{\"tag\":\"mate\",\"ridge\":138,\"a\":54,\"owners\":[32,39,90,96]},{\"tag\":\"mate\",\"ridge\":138,\"a\":58,\"owners\":[32,39,84,96]},{\"tag\":\"mate\",\"ridge\":138,\"a\":60,\"owners\":[32,39,84,90]},{\"tag\":\"mate\",\"ridge\":545,\"a\":67,\"owners\":[28,75,80]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[41,70,85]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[41,71,84]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[41,72,84]},{\"tag\":\"mate\",\"ridge\":44,\"a\":88,\"owners\":[18,42,69,73,75]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[42,73,88]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[42,73,89]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[42,74,87]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[42,75,87]},{\"tag\":\"mate\",\"ridge\":76,\"a\":19,\"owners\":[31,41,87,90]},{\"tag\":\"mate\",\"ridge\":76,\"a\":31,\"owners\":[19,41,73,76]},{\"tag\":\"mate\",\"ridge\":140,\"a\":32,\"owners\":[20,42,70,76]},{\"tag\":\"three\",\"ridge\":140,\"vertices\":[32,42,70]},{\"tag\":\"mate\",\"ridge\":84,\"a\":21,\"owners\":[33,41,92]},{\"tag\":\"mate\",\"ridge\":84,\"a\":33,\"owners\":[21,41,78]},{\"tag\":\"mate\",\"ridge\":164,\"a\":35,\"owners\":[23,42,79]},{\"tag\":\"mate\",\"ridge\":88,\"a\":37,\"owners\":[25,41,81]},{\"tag\":\"mate\",\"ridge\":168,\"a\":27,\"owners\":[39,42,96]},{\"tag\":\"mate\",\"ridge\":168,\"a\":39,\"owners\":[27,42,82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[56,57,60,67,82,96],\"full_literals\":[-68,34,35,38,39,53,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[43,44,50,58,76,90],\"full_literals\":[-69,24,25,28,36,47,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[83,84,85,87,88],\"full_literals\":[-70,54,55,56,58,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[69,77,80,91,94],\"full_literals\":[-71,40,48,51,62,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[70,71,73,74],\"full_literals\":[-72,41,42,44,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[72,75,86,89],\"full_literals\":[-73,43,46,57,60]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-79,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-80,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-80,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-81,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-81,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,19,21,31,33,41,48,50,51,73,76,78,87,90,92]},{\"tag\":\"edge\",\"edge\":21,\"owners\":[4,20,23,32,35,42,46,50,52,70,76,79,84,90,93]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[8,19,25,31,37,41,56,58,59,73,76,81,87,90,95]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[9,20,27,32,39,42,54,58,60,70,76,82,84,90,96]}]}"
  "p cnf 81 150\n-36 -3 0\n-36 -4 0\n-36 -31 0\n-36 -32 0\n-36 -34 0\n-38 -36 0\n-41 -8 0\n-41 -9 0\n-41 -25 0\n-41 -40 0\n-42 -11 0\n-42 -41 0\n-43 -13 0\n-43 -41 0\n-43 -42 0\n-44 -7 0\n-44 -10 0\n-44 -25 0\n-44 -41 0\n-44 -43 0\n-45 -12 0\n-46 -14 0\n-46 -41 0\n-46 -44 0\n-46 -45 0\n-47 -41 0\n-47 -42 0\n-47 -43 0\n-47 -44 0\n-47 -46 0\n-49 -41 0\n-49 -42 0\n-50 -45 0\n-52 -43 0\n-53 -44 0\n-53 -46 0\n-54 -40 0\n-54 -48 0\n-54 -51 0\n-55 -16 0\n-55 -17 0\n-55 -41 0\n-56 -18 0\n-56 -42 0\n-56 -45 0\n-57 -55 0\n-57 -56 0\n-58 -17 0\n-58 -44 0\n-58 -55 0\n-58 -57 0\n-59 -19 0\n-59 -24 0\n-59 -33 0\n-59 -35 0\n-59 -42 0\n-59 -45 0\n-59 -55 0\n-60 -21 0\n-60 -55 0\n-60 -58 0\n-61 -55 0\n-61 -56 0\n-61 -58 0\n-61 -59 0\n-61 -60 0\n-62 -54 0\n-63 -55 0\n-63 -56 0\n-64 -58 0\n-64 -59 0\n-65 -54 0\n-66 -55 0\n-67 -58 0\n-67 -59 0\n-67 -60 0\n-9 -43 -45 0\n-10 -42 -46 0\n-10 -43 -45 0\n-1 16 18 58 61 63 0\n-27 16 18 61 63 0\n-28 16 18 58 63 0\n-29 16 18 58 61 0\n-2 10 12 41 47 50 0\n-26 10 12 47 50 0\n-28 10 12 41 50 0\n-30 10 12 41 47 0\n-28 17 19 55 64 0\n-51 3 7 13 32 33 41 42 0\n-15 4 8 14 31 34 35 40 44 45 0\n-51 4 8 14 34 35 44 45 0\n-14 -15 -44 0\n-5 9 13 44 47 52 0\n-34 9 13 47 52 0\n-36 9 13 44 52 0\n-37 9 13 44 47 0\n-13 -36 -44 0\n-6 10 14 41 47 53 0\n-32 10 14 47 53 0\n-36 10 14 41 53 0\n-38 10 14 41 47 0\n-14 -36 -41 0\n-36 -41 -53 0\n-6 17 21 55 61 67 0\n-32 17 21 61 67 0\n-36 17 21 55 67 0\n-38 17 21 55 61 0\n-39 15 46 51 0\n-22 -41 -56 0\n-22 -42 -55 0\n-22 -43 -55 0\n-59 8 23 40 44 46 0\n-23 -44 -59 0\n-23 -44 -60 0\n-23 -45 -58 0\n-23 -46 -58 0\n-9 16 22 58 61 0\n-16 9 22 44 47 0\n-17 10 23 41 47 0\n-17 -23 -41 0\n-11 18 22 63 0\n-18 11 22 49 0\n-19 12 23 50 0\n-20 13 22 52 0\n-14 21 23 67 0\n-21 14 23 53 0\n-68 34 35 38 39 53 67 0\n-69 24 25 28 36 47 61 0\n-70 54 55 56 58 59 0\n-71 40 48 51 62 65 0\n-72 41 42 44 45 0\n-73 43 46 57 60 0\n-74 68 0\n-75 74 0\n-76 75 0\n-77 69 0\n-77 70 0\n-78 72 0\n-78 73 0\n-79 71 0\n-79 78 0\n-80 77 0\n-80 79 0\n-81 76 0\n-81 80 0\n81 0\n1 9 11 16 18 22 27 28 29 44 47 49 58 61 63 0\n2 10 12 17 19 23 26 28 30 41 47 50 55 61 64 0\n5 9 13 16 20 22 34 36 37 44 47 52 58 61 66 0\n6 10 14 17 21 23 32 36 38 41 47 53 55 61 67 0\n"
  "151 76 0 146 144 0\n152 80 0 146 145 0\n153 75 0 151 135 0\n154 77 0 152 142 0\n155 79 0 152 143 0\n156 74 0 153 134 0\n157 69 0 154 136 0\n158 70 0 154 137 0\n159 71 0 155 140 0\n160 78 0 155 141 0\n161 68 0 156 133 0\n162 72 0 160 138 0\n163 73 0 160 139 0\n164 -47 57 60 0 163 28 30 132 0\n165 -54 0 159 37 38 39 67 72 130 0\n166 -47 -59 0 162 57 56 26 29 131 0\n167 44 -36 -59 0 162 161 6 5 3 2 75 57 56 55 131 7 10 23 103 102 91 127 90 108 0\n168 -36 -59 0 161 75 56 55 54 1 4 5 6 167 16 17 19 24 35 97 100 89 127 92 108 0\n169 -25 -59 0 162 57 56 9 18 131 0\n170 44 -59 0 157 162 58 71 52 166 65 53 168 169 128 88 57 56 131 7 10 23 120 112 0\n171 -59 0 157 52 53 58 65 71 166 168 169 128 88 170 17 19 113 119 0\n172 -17 -44 0 171 165 158 163 49 29 24 20 19 17 41 119 129 114 47 132 0\n173 -57 58 0 171 165 158 46 47 129 0\n174 -44 0 163 17 19 20 24 29 35 49 172 173 132 59 60 66 76 114 125 105 106 107 104 150 0\n175 -56 58 42 0 162 174 43 45 63 69 131 8 26 31 109 118 121 80 83 81 82 147 0\n176 58 46 42 0 171 165 158 162 163 174 173 175 129 40 42 60 62 73 131 132 164 13 34 77 111 96 95 93 94 124 149 0\n177 46 42 0 162 174 163 176 48 50 51 61 64 70 132 164 14 131 21 33 115 79 87 86 123 84 85 148 0\n178 42 0 174 162 177 23 25 131 0\n179 -11 0 178 11 0\n180 -41 0 178 12 0\n181 -43 0 178 15 0\n182 -47 0 178 27 0\n183 -49 0 178 32 0\n184 -56 0 178 44 0\n185 -58 0 181 163 178 182 180 48 50 51 61 64 74 132 22 36 78 116 101 100 98 99 126 150 0\n186 55 0 185 158 184 165 171 129 0\n187 -16 0 186 40 0\n188 -61 0 186 62 0\n189 -63 0 186 68 0\n190 -22 0 186 178 110 0\n191 -18 0 190 179 183 122 0\n192 -9 0 190 187 185 188 117 0\n193 -1 0 191 187 185 188 189 80 0\n194 -29 0 191 188 187 185 83 0\n195 -27 0 191 189 187 188 81 0\n196 -28 0 191 187 189 185 82 0\n197 0 193 195 183 192 179 187 191 190 194 196 182 174 185 188 189 147 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035.record023_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record023
