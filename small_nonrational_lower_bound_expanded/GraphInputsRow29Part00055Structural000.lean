module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00055Data
public import GraphInputsRow29Part00055Frames
public import GraphInputsRow29Part00055Leaves
public import GraphInputsRow29Part00055Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨95, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 72057628397666304, (certNat% 4), 144115256795332608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), 69256347648, (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 35218731827200]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 2287293423419392, (certNat% 17)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 144255994283687936, (certNat% 19), (certNat% 20), 74344612583440384, (certNat% 21)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 9), 33554432]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 23), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 85899345920, 252342316621103104, (certNat% 30), (certNat% 13)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 27), (certNat% 32), (certNat% 33), (certNat% 34)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 27), 252412685365280768, (certNat% 36), 9511602415153971200, (certNat% 37)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 13), (certNat% 40), (certNat% 41)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 10), 216313519602139136, (certNat% 43), 35184372088832]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 17985175552, (certNat% 45), (certNat% 46), (certNat% 47)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 4), (certNat% 24), 144185625539510272, (certNat% 46)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 33), (certNat% 51), (certNat% 47)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 24), 216260743044005888, (certNat% 53), (certNat% 10), (certNat% 33)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c27 c23
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c28 c22
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c29 c21
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c30 c20
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 72057628397666304, (certNat% 41), (certNat% 39), (certNat% 55)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 88046829568, 216190374299828224, 2251834173423616, (certNat% 47)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), 85899345920, 17626545782784]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), 17179869184, (certNat% 68)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 66), (certNat% 70), 72075186223972352, (certNat% 71)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), 19327352832, 34359738368]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 70), 19327352832, 34359738368, (certNat% 10)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), 88046829568, 162727720910848, (certNat% 5)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), (certNat% 68), (certNat% 47), 72075220583710720]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 10), 51539607552, 72057594037927936, (certNat% 68)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), 19327352832, (certNat% 68), 72075220583710720, (certNat% 47)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c39
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c51 c38
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c52 c35
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 82), (certNat% 83), (certNat% 84), (certNat% 85), (certNat% 23)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 23), (certNat% 24), (certNat% 87)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 23), 144273517750255616, 2181038080, 9259400833873739776]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 23), (certNat% 26), (certNat% 27), (certNat% 90)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), 158329674399744, (certNat% 30), 85899345920]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 3), 85899345920, (certNat% 30)]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 23), 9223376434901286912, (certNat% 94), 144115256795332608]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c60 c59
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c61 c58
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 27), 144277915796766720, (certNat% 96), (certNat% 20), 70900514816]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c63 c62
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c64 c57
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c65 c56
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c66 c55
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), (certNat% 98), 88617254912, (certNat% 30), (certNat% 83), (certNat% 99)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 82), (certNat% 60), (certNat% 83), 72110404955799552, 17179869184]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), 72110404955799552, (certNat% 60), (certNat% 102), (certNat% 103), (certNat% 104)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 60), (certNat% 106), 9223372037391646720, 35235911696384, 72215923712327680]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), (certNat% 109), 51573161984, 189291921837916160, 72110370596061184]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 58), 72233515898372096, (certNat% 80), 9268412431174991872, 144115188075855872]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 112), 35235911696384, 216331111788183552, (certNat% 83)]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), (certNat% 60), (certNat% 80), (certNat% 114), 19864223744, 72110404955799552, 189296319884427264]
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c75 c74
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c76 c73
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c77 c72
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c78 c71
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c79 c70
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c80 c69
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c81 c68
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c82 c67
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c83 c54
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c84 c53
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c85 c34
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c86 c31
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c87 c19
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c88 c10
  c89
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001
def vertexColumn : Fields := ⟨10, (certNat% 115)⟩
def kindColumn : Fields := ⟨3, (certNat% 116)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨40, by decide⟩, ⟨46, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 118), (certNat% 119), (certNat% 120)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), (certNat% 122), (certNat% 123), (certNat% 124)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 126), (certNat% 127), (certNat% 128), (certNat% 129)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 131), (certNat% 132), (certNat% 133), (certNat% 134)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), (certNat% 136), (certNat% 137), (certNat% 138), (certNat% 139)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 141), (certNat% 142), (certNat% 143), (certNat% 144)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 146), (certNat% 132), (certNat% 147)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 148), (certNat% 123), (certNat% 120), (certNat% 142), (certNat% 119)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 149), (certNat% 128), (certNat% 150), (certNat% 151), (certNat% 147), (certNat% 136)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 152), (certNat% 153), (certNat% 154), (certNat% 155), (certNat% 156), (certNat% 157)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 159), (certNat% 119), (certNat% 160), (certNat% 161)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 159), (certNat% 119), (certNat% 123), (certNat% 162)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), (certNat% 147), (certNat% 123), (certNat% 164), (certNat% 162)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 165), (certNat% 160), 36029896564146176, (certNat% 159), (certNat% 161)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 166), (certNat% 160), (certNat% 132), (certNat% 164), (certNat% 167), (certNat% 146)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c25 c18
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 168), (certNat% 119), (certNat% 169), (certNat% 170), (certNat% 159)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 171), (certNat% 150), (certNat% 119), (certNat% 172), (certNat% 159)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 173), (certNat% 132), (certNat% 174), (certNat% 175), (certNat% 176), (certNat% 177)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 178), (certNat% 141), (certNat% 179), (certNat% 180)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 181), (certNat% 150), (certNat% 160), (certNat% 128), (certNat% 129)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 182), (certNat% 179), (certNat% 183), (certNat% 184), (certNat% 185), (certNat% 159)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 186), (certNat% 187), (certNat% 188), (certNat% 184), (certNat% 129), (certNat% 189)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 190), (certNat% 131), (certNat% 191), (certNat% 138), (certNat% 192), (certNat% 187)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 193), (certNat% 194), (certNat% 195), (certNat% 196), (certNat% 197)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 198), (certNat% 199), (certNat% 200), (certNat% 184), (certNat% 188), (certNat% 201)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 202), (certNat% 122), (certNat% 119), (certNat% 203), (certNat% 162)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 204), (certNat% 205), (certNat% 206), (certNat% 207)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 208), (certNat% 209), (certNat% 210), (certNat% 129), (certNat% 211), (certNat% 134)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c46 c42
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 212), (certNat% 131), (certNat% 164), (certNat% 138), (certNat% 199), (certNat% 213)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 214), (certNat% 215), (certNat% 216), (certNat% 217), (certNat% 154)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 218), (certNat% 128), (certNat% 219), (certNat% 220), (certNat% 132), (certNat% 221)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 222), (certNat% 223), (certNat% 224), (certNat% 225)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 226), (certNat% 179), (certNat% 227), (certNat% 228), (certNat% 220), (certNat% 221)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c52 c51
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 229), (certNat% 230), (certNat% 224), (certNat% 184), (certNat% 231), (certNat% 199), (certNat% 189)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c55 c50
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c56 c49
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c57 c48
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c58 c47
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨108, by decide⟩ c59 c41
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c60 c38
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c61 c37
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c62 c36
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c63 c31
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c64 c26
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c65 c17
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c66 c16
  c67
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9b19c2f07ce8b523cb8aaaa6ac699a968ba1eb46c99a699996558b61db0e63a4e8b8ae1b91e2785e0fba1d44f1e26a99a719666592e479d172569665655552d475c358d9362d2b46d4749d1743de0f43c8ea368e6338f1364e5354cd32cc73c2e8b62e4b8acab1ae1b46c9b16c3bc1d8791d4789d2729c6745c9715c3783d0f23c4f0bc1f989928a8aa26866458560b81e985918a4a926465454550b41d"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d269a6db4934db4924936da4d34db69269b6924926db69b4db6db6d26da6db6db6934db6d2249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 70), (facetIndex 78), (facetIndex 99), (facetIndex 107)]))
 (.leaf ([(facetIndex 40), (facetIndex 55), (facetIndex 85), (facetIndex 114)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 87), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 96), (facetIndex 105), (facetIndex 106)]))
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 116), (facetIndex 117)])))
 (.branch 7
 (.leaf ([(facetIndex 64), (facetIndex 74), (facetIndex 83), (facetIndex 93), (facetIndex 103), (facetIndex 112)]))
 (.leaf ([(facetIndex 20), (facetIndex 21), (facetIndex 27), (facetIndex 29), (facetIndex 30), (facetIndex 44), (facetIndex 45), (facetIndex 58)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2d046000120c0016c930003608c0001218001b4960001c020000003f0010000001f8e0003f000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 52), (facetIndex 90)]))
 (.leaf ([(facetIndex 34), (facetIndex 81), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 48), (facetIndex 89), (facetIndex 92)]))
 (.leaf ([(facetIndex 38), (facetIndex 57), (facetIndex 119)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 53), (facetIndex 110), (facetIndex 120)]))
 (.leaf ([(facetIndex 60), (facetIndex 118), (facetIndex 121)])))
 (.branch 7
 (.leaf ([(facetIndex 22), (facetIndex 71), (facetIndex 82), (facetIndex 84)]))
 (.branch 8
 (.leaf ([(facetIndex 24), (facetIndex 72), (facetIndex 73), (facetIndex 86)]))
 (.leaf ([(facetIndex 39), (facetIndex 100), (facetIndex 111), (facetIndex 113)]))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 41), (facetIndex 101), (facetIndex 102), (facetIndex 115)]))
 (.leaf ([(facetIndex 23), (facetIndex 75), (facetIndex 79), (facetIndex 124)])))
 (.branch 12
 (.leaf ([(facetIndex 25), (facetIndex 80), (facetIndex 125)]))
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 33), (facetIndex 42), (facetIndex 43), (facetIndex 47), (facetIndex 50), (facetIndex 62), (facetIndex 63)]))))
 (.branch 15
 (.branch 14
 (.leaf ([(facetIndex 35), (facetIndex 59), (facetIndex 109)]))
 (.leaf ([(facetIndex 31), (facetIndex 37), (facetIndex 46), (facetIndex 49), (facetIndex 51), (facetIndex 54), (facetIndex 61)])))
 (.branch 16
 (.leaf ([(facetIndex 104), (facetIndex 122)]))
 (.branch 17
 (.leaf ([(facetIndex 36), (facetIndex 108), (facetIndex 123)]))
 (.leaf ([(facetIndex 56)])))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "16a83ca41940048100411b00000f0252800000000020804001c060182b50000500e73000000000631c56807103880731c2638006312040dd06858c7000c00167518z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 18
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0014 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2]
def grouped3_0018 : List Nat := [2, 3]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [4, 5]
def grouped3_0022 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [6, 7, 8]
def grouped3_0026 : List Nat := [7]
def grouped3_0027 : List Nat := [7, 8]
def grouped3_0028 : List Nat := [8]
def grouped3_0029 : List Nat := [9]
def grouped3_0030 : List Nat := [9, 10]
def grouped3_0031 : List Nat := [9, 10, 11, 12]
def grouped3_0032 : List Nat := [9, 10, 11, 12, 13, 14, 15, 16, 17]
def grouped3_0033 : List Nat := [10]
def grouped3_0034 : List Nat := [11, 12]
def grouped3_0035 : List Nat := [13]
def grouped3_0036 : List Nat := [13, 14]
def grouped3_0037 : List Nat := [13, 14, 15, 16, 17]
def grouped3_0038 : List Nat := [14]
def grouped3_0039 : List Nat := [15]
def grouped3_0040 : List Nat := [15, 16, 17]
def grouped3_0041 : List Nat := [16]
def grouped3_0042 : List Nat := [16, 17]
def grouped3_0043 : List Nat := [17]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":14},{\"tag\":\"group\",\"kind\":3,\"index\":17},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0031\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0036\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0042\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0040\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0037\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005" "{\"ridges\":[[29,261],[37,769],[37,770],[49,769],[49,770],[55,385],[56,769],[56,770],[61,769],[61,770],[62,323],[62,770],[63,643],[63,770],[73,780],[81,836],[86,792],[89,904],[91,769],[91,848],[92,769],[92,928],[102,780],[109,804],[115,792],[118,770],[118,904],[120,848],[121,928]],\"owners\":[[29,261,[72,73,79,80,81],[3,24,32,34,36,37,67,76,77]],[55,385,[72,79,89,92],[8,36,47,59,63,77,85]],[62,323,[34,53],[]],[37,769,[86,89,91,92],[49,56,61,62,63,73,80,81]],[49,769,[80,81,91,92],[37,56,61,62,63,73,86,89]],[56,769,[73,80,81,89,92],[37,49,61,62,63,86,91]],[61,769,[73,81,86,89,91],[37,49,56,62,63,80,92]],[91,769,[37,49,61,63,73,80,89,92],[56,62,81,86]],[92,769,[37,49,56,62,73,81,86,91],[61,63,80,89]],[37,770,[115,118,120,121],[49,56,61,62,63,102,109,110]],[49,770,[109,110,120,121],[37,56,61,62,63,102,115,118]],[56,770,[102,109,110,118,121],[37,49,61,62,63,115,120]],[61,770,[102,110,115,118,120],[37,49,56,62,63,109,121]],[62,770,[102,109,115,118,121],[37,49,56,61,63,110,120]],[63,770,[102,109,110,115,120],[37,49,56,61,62,118,121]],[118,770,[37,56,61,62,109,110,120],[49,63,102,115,121]],[63,643,[48,60],[]],[73,780,[102],[]],[102,780,[73],[]],[109,804,[80],[]],[81,836,[110],[]],[86,792,[115],[]],[115,792,[86],[]],[89,904,[118],[]],[118,904,[89],[]],[91,848,[120],[]],[120,848,[91],[]],[92,928,[121],[]],[121,928,[92],[]]],\"edges\":[[44,[37,49,56,61,62,63,73,80,81,86,89,91,92,102,109,110,115,118,120,121]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-1],[-8,-2],[-8,-3],[-8,-5],[-9,-8],[-10,-8],[-16,-8],[-26,-21],[-26,-24],[-33,-26],[-34,-21],[-34,-24],[-34,-33],[-35,-26],[-35,-34],[-37,-21],[-37,-24],[-37,-33],[-37,-35],[-39,-22],[-39,-28],[-39,-38],[-4,22,23,25,26,27],[-14,22,25,30,32],[-19,6,13],[-7,29,30,31,32],[-12,26,27,31,32],[-15,23,26,27,30,32],[-18,23,27,29,30,31],[-31,7,12,18,20,23,26,30,32],[-32,7,12,15,19,23,27,29,31],[-7,39,40,41,42],[-12,36,37,41,42],[-15,34,36,37,40,42],[-18,34,37,39,40,41],[-19,34,36,39,40,42],[-20,34,36,37,39,41],[-40,7,15,18,19,36,37,41],[-20,11,17],[-23,34],[-34,23],[-36,26],[-27,37],[-29,39],[-39,29],[-30,40],[-40,30],[-31,41],[-41,31],[-32,42],[-42,32],[-43,21,24,33,35],[-44,8,14,28,38],[-45,1,2,3,4,5,9,10,16],[-46,43],[-46,44],[-47,46],[-48,45],[-49,48],[-50,47],[-50,49],[50],[-6,51],[-27,51],[-31,51],[-11,52],[-30,52],[-32,52],[-13,53],[-37,53],[-41,53],[-17,54],[-40,54],[-42,54],[-23,55],[-29,55],[-39,56],[-25,57],[-7,58],[-12,58],[-18,58],[-15,59],[-51,60],[-52,61],[-61,62],[-60,62],[-60,-61,63],[-54,64],[-53,64],[-53,-54,65],[-55,66],[-66,67],[-67,68],[-64,68],[-64,-67,69],[-65,69],[-68,70],[-62,70],[-62,-68,71],[-62,-69,72],[-63,-68,72],[-56,-57,73],[-73,74],[-58,75],[-59,76],[-76,77],[-77,78],[-75,78],[-78,79],[-74,80],[-70,-80,81],[-71,-79,81],[-72,81],[-81],[7,12,15,18,19,20,23,26,27,29,30,31,32,34,36,37,39,40,41,42]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":14,\"kind\":3},{\"tag\":\"group\",\"index\":17,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":20},{\"tag\":\"incompatible\",\"a\":40,\"b\":21},{\"tag\":\"incompatible\",\"a\":40,\"b\":27},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":58,\"b\":40},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":99,\"b\":80},{\"tag\":\"incompatible\",\"a\":102,\"b\":70},{\"tag\":\"incompatible\",\"a\":102,\"b\":78},{\"tag\":\"incompatible\",\"a\":102,\"b\":99},{\"tag\":\"incompatible\",\"a\":107,\"b\":80},{\"tag\":\"incompatible\",\"a\":107,\"b\":102},{\"tag\":\"incompatible\",\"a\":110,\"b\":70},{\"tag\":\"incompatible\",\"a\":110,\"b\":78},{\"tag\":\"incompatible\",\"a\":110,\"b\":99},{\"tag\":\"incompatible\",\"a\":110,\"b\":107},{\"tag\":\"incompatible\",\"a\":115,\"b\":72},{\"tag\":\"incompatible\",\"a\":115,\"b\":85},{\"tag\":\"incompatible\",\"a\":115,\"b\":114},{\"tag\":\"mate\",\"ridge\":261,\"a\":29,\"owners\":[72,73,79,80,81]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[72,79,89,92]},{\"tag\":\"mate\",\"ridge\":323,\"a\":62,\"owners\":[34,53]},{\"tag\":\"mate\",\"ridge\":769,\"a\":37,\"owners\":[86,89,91,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":49,\"owners\":[80,81,91,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":56,\"owners\":[73,80,81,89,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":61,\"owners\":[73,81,86,89,91]},{\"tag\":\"mate\",\"ridge\":769,\"a\":91,\"owners\":[37,49,61,63,73,80,89,92]},{\"tag\":\"mate\",\"ridge\":769,\"a\":92,\"owners\":[37,49,56,62,73,81,86,91]},{\"tag\":\"mate\",\"ridge\":770,\"a\":37,\"owners\":[115,118,120,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[109,110,120,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[102,109,110,118,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":61,\"owners\":[102,110,115,118,120]},{\"tag\":\"mate\",\"ridge\":770,\"a\":62,\"owners\":[102,109,115,118,121]},{\"tag\":\"mate\",\"ridge\":770,\"a\":63,\"owners\":[102,109,110,115,120]},{\"tag\":\"mate\",\"ridge\":770,\"a\":118,\"owners\":[37,56,61,62,109,110,120]},{\"tag\":\"mate\",\"ridge\":643,\"a\":63,\"owners\":[48,60]},{\"tag\":\"mate\",\"ridge\":780,\"a\":73,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":780,\"a\":102,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":804,\"a\":109,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":836,\"a\":81,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":792,\"a\":86,\"owners\":[115]},{\"tag\":\"mate\",\"ridge\":792,\"a\":115,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":904,\"a\":89,\"owners\":[118]},{\"tag\":\"mate\",\"ridge\":904,\"a\":118,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":848,\"a\":91,\"owners\":[120]},{\"tag\":\"mate\",\"ridge\":848,\"a\":120,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":928,\"a\":92,\"owners\":[121]},{\"tag\":\"mate\",\"ridge\":928,\"a\":121,\"owners\":[92]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[70,78,99,107],\"full_literals\":[-43,21,24,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,55,85,114],\"full_literals\":[-44,8,14,28,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[20,21,27,29,30,44,45,58],\"full_literals\":[-45,1,2,3,4,5,9,10,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-50,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":34,\"full_literals\":[-6,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-27,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-31,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-11,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-32,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-13,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":110,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":120,\"full_literals\":[-41,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-17,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":118,\"full_literals\":[-40,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":121,\"full_literals\":[-42,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-29,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":115,\"full_literals\":[-39,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":79,\"full_literals\":[-25,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":14,\"member\":37,\"full_literals\":[-7,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":14,\"member\":49,\"full_literals\":[-12,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":14,\"member\":61,\"full_literals\":[-18,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":17,\"member\":56,\"full_literals\":[-15,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-68,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0033\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10],\"right\":[11,12],\"left_name\":\"grouped3_0030\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0031\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped3_0035\",\"right_name\":\"grouped3_0038\",\"joined_name\":\"grouped3_0036\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped3_0041\",\"right_name\":\"grouped3_0043\",\"joined_name\":\"grouped3_0042\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[15],\"right\":[16,17],\"left_name\":\"grouped3_0039\",\"right_name\":\"grouped3_0042\",\"joined_name\":\"grouped3_0040\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[13,14],\"right\":[15,16,17],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[13,14],\"right\":[15,16,17],\"left_name\":\"grouped3_0036\",\"right_name\":\"grouped3_0040\",\"joined_name\":\"grouped3_0037\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10,11,12],\"right\":[13,14,15,16,17],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0037\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9,10,11,12],\"right\":[13,14,15,16,17],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0037\",\"joined_name\":\"grouped3_0032\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8],\"right\":[9,10,11,12,13,14,15,16,17],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8],\"right\":[9,10,11,12,13,14,15,16,17],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8],\"right\":[9,10,11,12,13,14,15,16,17],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[37,49,56,61,62,63,73,80,81,86,89,91,92,102,109,110,115,118,120,121]}]}"
  "116 47 0 62 60 0\n117 49 0 62 61 0\n118 46 0 116 57 0\n119 48 0 117 59 0\n120 43 0 118 55 0\n121 44 0 118 56 0\n122 45 0 119 58 0\n123 -72 0 114 113 0\n124 26 70 0 97 93 92 91 76 45 75 41 98 86 83 65 85 84 67 64 29 68 26 94 88 72 66 39 63 89 69 25 71 70 74 73 42 27 28 115 0\n125 -26 0 120 8 9 10 14 52 0\n126 -36 0 125 42 0\n127 70 0 125 124 0\n128 -80 0 127 114 111 0\n129 -74 0 128 110 0\n130 -73 0 129 103 0\n131 34 37 39 40 41 42 0 126 125 33 43 32 44 46 48 50 40 36 37 35 34 115 0\n132 -34 0 120 11 12 13 15 52 0\n133 -23 0 132 40 0\n134 -37 0 120 16 17 18 19 52 0\n135 -27 0 134 43 0\n136 40 41 42 0 134 132 130 135 125 133 121 122 50 46 131 20 21 22 77 102 78 24 23 53 1 2 3 4 5 6 7 54 0\n137 41 42 0 126 134 114 123 136 47 73 67 88 84 94 85 101 99 100 87 112 96 83 109 90 63 107 108 69 106 104 25 105 79 81 82 38 0\n138 42 0 123 114 133 125 50 137 49 71 65 89 83 94 86 101 99 100 87 112 96 84 109 90 66 67 108 72 39 104 79 80 81 30 0\n139 32 0 138 51 0\n140 54 0 138 74 0\n141 52 0 139 68 0\n142 64 0 140 88 0\n143 61 0 141 84 0\n144 68 0 142 94 0\n145 62 0 143 85 0\n146 -63 0 144 123 101 0\n147 71 0 145 144 99 0\n148 -69 0 145 123 100 0\n149 -60 0 146 143 87 0\n150 -79 0 147 114 112 0\n151 -65 0 148 96 0\n152 -67 0 148 142 95 0\n153 -51 0 149 83 0\n154 -78 0 150 109 0\n155 -53 0 151 140 90 0\n156 -66 0 152 92 0\n157 -6 0 153 63 0\n158 -31 0 153 65 0\n159 -77 0 154 107 0\n160 -75 0 154 108 0\n161 -13 0 155 69 0\n162 -55 0 156 91 0\n163 -76 0 159 106 0\n164 -58 0 160 104 0\n165 -19 0 161 157 25 0\n166 -29 0 162 76 0\n167 -59 0 163 105 0\n168 -7 0 164 79 0\n169 -12 0 164 80 0\n170 -15 0 167 82 0\n171 0 168 170 158 166 165 169 133 135 139 31 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record005
