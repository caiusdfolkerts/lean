import cubical_indecomposability.face_data_checks.anchors
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
# Sparse, exact finite certificates

The proposed finite data are checked by ordinary Lean kernel reduction.
The generic proof then recovers the full universally quantified statement.
Exhaustive case splits have at most 32 leaves per declaration.

Regenerate with `python3 scripts/sparse_supports_lower.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace CubicalIndecomposability

/-- The common equality labels of the selected supporting facets. -/
private def supportIntersection (i : Fin 1069) : Finset (Fin 144) :=
  if h : (supportRows i).Nonempty then
    (supportRows i).inf' h facetLabels
  else Finset.univ

private theorem mem_supportIntersection (i : Fin 1069) (v : Fin 144) :
    v ∈ supportIntersection i ↔ ∀ f ∈ supportRows i, incident f v := by
  unfold supportIntersection
  split_ifs with h
  · simpa only [Finset.mem_inf', incident]
  · have he : supportRows i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

private theorem support0000 : supportIntersection (⟨0, by decide⟩ : Fin 1069) = faceMask (⟨0, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0001 : supportIntersection (⟨1, by decide⟩ : Fin 1069) = faceMask (⟨1, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0002 : supportIntersection (⟨2, by decide⟩ : Fin 1069) = faceMask (⟨2, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0003 : supportIntersection (⟨3, by decide⟩ : Fin 1069) = faceMask (⟨3, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0004 : supportIntersection (⟨4, by decide⟩ : Fin 1069) = faceMask (⟨4, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0005 : supportIntersection (⟨5, by decide⟩ : Fin 1069) = faceMask (⟨5, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0006 : supportIntersection (⟨6, by decide⟩ : Fin 1069) = faceMask (⟨6, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0007 : supportIntersection (⟨7, by decide⟩ : Fin 1069) = faceMask (⟨7, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0008 : supportIntersection (⟨8, by decide⟩ : Fin 1069) = faceMask (⟨8, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0009 : supportIntersection (⟨9, by decide⟩ : Fin 1069) = faceMask (⟨9, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0010 : supportIntersection (⟨10, by decide⟩ : Fin 1069) = faceMask (⟨10, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0011 : supportIntersection (⟨11, by decide⟩ : Fin 1069) = faceMask (⟨11, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0012 : supportIntersection (⟨12, by decide⟩ : Fin 1069) = faceMask (⟨12, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0013 : supportIntersection (⟨13, by decide⟩ : Fin 1069) = faceMask (⟨13, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0014 : supportIntersection (⟨14, by decide⟩ : Fin 1069) = faceMask (⟨14, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0015 : supportIntersection (⟨15, by decide⟩ : Fin 1069) = faceMask (⟨15, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0016 : supportIntersection (⟨16, by decide⟩ : Fin 1069) = faceMask (⟨16, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0017 : supportIntersection (⟨17, by decide⟩ : Fin 1069) = faceMask (⟨17, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0018 : supportIntersection (⟨18, by decide⟩ : Fin 1069) = faceMask (⟨18, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0019 : supportIntersection (⟨19, by decide⟩ : Fin 1069) = faceMask (⟨19, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0020 : supportIntersection (⟨20, by decide⟩ : Fin 1069) = faceMask (⟨20, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0021 : supportIntersection (⟨21, by decide⟩ : Fin 1069) = faceMask (⟨21, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0022 : supportIntersection (⟨22, by decide⟩ : Fin 1069) = faceMask (⟨22, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0023 : supportIntersection (⟨23, by decide⟩ : Fin 1069) = faceMask (⟨23, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0024 : supportIntersection (⟨24, by decide⟩ : Fin 1069) = faceMask (⟨24, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0025 : supportIntersection (⟨25, by decide⟩ : Fin 1069) = faceMask (⟨25, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0026 : supportIntersection (⟨26, by decide⟩ : Fin 1069) = faceMask (⟨26, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0027 : supportIntersection (⟨27, by decide⟩ : Fin 1069) = faceMask (⟨27, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0028 : supportIntersection (⟨28, by decide⟩ : Fin 1069) = faceMask (⟨28, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0029 : supportIntersection (⟨29, by decide⟩ : Fin 1069) = faceMask (⟨29, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0030 : supportIntersection (⟨30, by decide⟩ : Fin 1069) = faceMask (⟨30, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0031 : supportIntersection (⟨31, by decide⟩ : Fin 1069) = faceMask (⟨31, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0032 : supportIntersection (⟨32, by decide⟩ : Fin 1069) = faceMask (⟨32, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0033 : supportIntersection (⟨33, by decide⟩ : Fin 1069) = faceMask (⟨33, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0034 : supportIntersection (⟨34, by decide⟩ : Fin 1069) = faceMask (⟨34, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0035 : supportIntersection (⟨35, by decide⟩ : Fin 1069) = faceMask (⟨35, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0036 : supportIntersection (⟨36, by decide⟩ : Fin 1069) = faceMask (⟨36, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0037 : supportIntersection (⟨37, by decide⟩ : Fin 1069) = faceMask (⟨37, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0038 : supportIntersection (⟨38, by decide⟩ : Fin 1069) = faceMask (⟨38, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0039 : supportIntersection (⟨39, by decide⟩ : Fin 1069) = faceMask (⟨39, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0040 : supportIntersection (⟨40, by decide⟩ : Fin 1069) = faceMask (⟨40, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0041 : supportIntersection (⟨41, by decide⟩ : Fin 1069) = faceMask (⟨41, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0042 : supportIntersection (⟨42, by decide⟩ : Fin 1069) = faceMask (⟨42, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0043 : supportIntersection (⟨43, by decide⟩ : Fin 1069) = faceMask (⟨43, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0044 : supportIntersection (⟨44, by decide⟩ : Fin 1069) = faceMask (⟨44, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0045 : supportIntersection (⟨45, by decide⟩ : Fin 1069) = faceMask (⟨45, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0046 : supportIntersection (⟨46, by decide⟩ : Fin 1069) = faceMask (⟨46, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0047 : supportIntersection (⟨47, by decide⟩ : Fin 1069) = faceMask (⟨47, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0048 : supportIntersection (⟨48, by decide⟩ : Fin 1069) = faceMask (⟨48, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0049 : supportIntersection (⟨49, by decide⟩ : Fin 1069) = faceMask (⟨49, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0050 : supportIntersection (⟨50, by decide⟩ : Fin 1069) = faceMask (⟨50, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0051 : supportIntersection (⟨51, by decide⟩ : Fin 1069) = faceMask (⟨51, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0052 : supportIntersection (⟨52, by decide⟩ : Fin 1069) = faceMask (⟨52, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0053 : supportIntersection (⟨53, by decide⟩ : Fin 1069) = faceMask (⟨53, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0054 : supportIntersection (⟨54, by decide⟩ : Fin 1069) = faceMask (⟨54, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0055 : supportIntersection (⟨55, by decide⟩ : Fin 1069) = faceMask (⟨55, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0056 : supportIntersection (⟨56, by decide⟩ : Fin 1069) = faceMask (⟨56, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0057 : supportIntersection (⟨57, by decide⟩ : Fin 1069) = faceMask (⟨57, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0058 : supportIntersection (⟨58, by decide⟩ : Fin 1069) = faceMask (⟨58, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0059 : supportIntersection (⟨59, by decide⟩ : Fin 1069) = faceMask (⟨59, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0060 : supportIntersection (⟨60, by decide⟩ : Fin 1069) = faceMask (⟨60, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0061 : supportIntersection (⟨61, by decide⟩ : Fin 1069) = faceMask (⟨61, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0062 : supportIntersection (⟨62, by decide⟩ : Fin 1069) = faceMask (⟨62, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0063 : supportIntersection (⟨63, by decide⟩ : Fin 1069) = faceMask (⟨63, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0064 : supportIntersection (⟨64, by decide⟩ : Fin 1069) = faceMask (⟨64, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0065 : supportIntersection (⟨65, by decide⟩ : Fin 1069) = faceMask (⟨65, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0066 : supportIntersection (⟨66, by decide⟩ : Fin 1069) = faceMask (⟨66, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0067 : supportIntersection (⟨67, by decide⟩ : Fin 1069) = faceMask (⟨67, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0068 : supportIntersection (⟨68, by decide⟩ : Fin 1069) = faceMask (⟨68, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0069 : supportIntersection (⟨69, by decide⟩ : Fin 1069) = faceMask (⟨69, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0070 : supportIntersection (⟨70, by decide⟩ : Fin 1069) = faceMask (⟨70, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0071 : supportIntersection (⟨71, by decide⟩ : Fin 1069) = faceMask (⟨71, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0072 : supportIntersection (⟨72, by decide⟩ : Fin 1069) = faceMask (⟨72, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0073 : supportIntersection (⟨73, by decide⟩ : Fin 1069) = faceMask (⟨73, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0074 : supportIntersection (⟨74, by decide⟩ : Fin 1069) = faceMask (⟨74, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0075 : supportIntersection (⟨75, by decide⟩ : Fin 1069) = faceMask (⟨75, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0076 : supportIntersection (⟨76, by decide⟩ : Fin 1069) = faceMask (⟨76, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0077 : supportIntersection (⟨77, by decide⟩ : Fin 1069) = faceMask (⟨77, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0078 : supportIntersection (⟨78, by decide⟩ : Fin 1069) = faceMask (⟨78, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0079 : supportIntersection (⟨79, by decide⟩ : Fin 1069) = faceMask (⟨79, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0080 : supportIntersection (⟨80, by decide⟩ : Fin 1069) = faceMask (⟨80, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0081 : supportIntersection (⟨81, by decide⟩ : Fin 1069) = faceMask (⟨81, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0082 : supportIntersection (⟨82, by decide⟩ : Fin 1069) = faceMask (⟨82, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0083 : supportIntersection (⟨83, by decide⟩ : Fin 1069) = faceMask (⟨83, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0084 : supportIntersection (⟨84, by decide⟩ : Fin 1069) = faceMask (⟨84, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0085 : supportIntersection (⟨85, by decide⟩ : Fin 1069) = faceMask (⟨85, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0086 : supportIntersection (⟨86, by decide⟩ : Fin 1069) = faceMask (⟨86, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0087 : supportIntersection (⟨87, by decide⟩ : Fin 1069) = faceMask (⟨87, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0088 : supportIntersection (⟨88, by decide⟩ : Fin 1069) = faceMask (⟨88, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0089 : supportIntersection (⟨89, by decide⟩ : Fin 1069) = faceMask (⟨89, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0090 : supportIntersection (⟨90, by decide⟩ : Fin 1069) = faceMask (⟨90, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0091 : supportIntersection (⟨91, by decide⟩ : Fin 1069) = faceMask (⟨91, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0092 : supportIntersection (⟨92, by decide⟩ : Fin 1069) = faceMask (⟨92, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0093 : supportIntersection (⟨93, by decide⟩ : Fin 1069) = faceMask (⟨93, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0094 : supportIntersection (⟨94, by decide⟩ : Fin 1069) = faceMask (⟨94, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0095 : supportIntersection (⟨95, by decide⟩ : Fin 1069) = faceMask (⟨95, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0096 : supportIntersection (⟨96, by decide⟩ : Fin 1069) = faceMask (⟨96, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0097 : supportIntersection (⟨97, by decide⟩ : Fin 1069) = faceMask (⟨97, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0098 : supportIntersection (⟨98, by decide⟩ : Fin 1069) = faceMask (⟨98, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0099 : supportIntersection (⟨99, by decide⟩ : Fin 1069) = faceMask (⟨99, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0100 : supportIntersection (⟨100, by decide⟩ : Fin 1069) = faceMask (⟨100, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0101 : supportIntersection (⟨101, by decide⟩ : Fin 1069) = faceMask (⟨101, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0102 : supportIntersection (⟨102, by decide⟩ : Fin 1069) = faceMask (⟨102, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0103 : supportIntersection (⟨103, by decide⟩ : Fin 1069) = faceMask (⟨103, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0104 : supportIntersection (⟨104, by decide⟩ : Fin 1069) = faceMask (⟨104, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0105 : supportIntersection (⟨105, by decide⟩ : Fin 1069) = faceMask (⟨105, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0106 : supportIntersection (⟨106, by decide⟩ : Fin 1069) = faceMask (⟨106, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0107 : supportIntersection (⟨107, by decide⟩ : Fin 1069) = faceMask (⟨107, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0108 : supportIntersection (⟨108, by decide⟩ : Fin 1069) = faceMask (⟨108, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0109 : supportIntersection (⟨109, by decide⟩ : Fin 1069) = faceMask (⟨109, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0110 : supportIntersection (⟨110, by decide⟩ : Fin 1069) = faceMask (⟨110, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0111 : supportIntersection (⟨111, by decide⟩ : Fin 1069) = faceMask (⟨111, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0112 : supportIntersection (⟨112, by decide⟩ : Fin 1069) = faceMask (⟨112, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0113 : supportIntersection (⟨113, by decide⟩ : Fin 1069) = faceMask (⟨113, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0114 : supportIntersection (⟨114, by decide⟩ : Fin 1069) = faceMask (⟨114, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0115 : supportIntersection (⟨115, by decide⟩ : Fin 1069) = faceMask (⟨115, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0116 : supportIntersection (⟨116, by decide⟩ : Fin 1069) = faceMask (⟨116, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0117 : supportIntersection (⟨117, by decide⟩ : Fin 1069) = faceMask (⟨117, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0118 : supportIntersection (⟨118, by decide⟩ : Fin 1069) = faceMask (⟨118, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0119 : supportIntersection (⟨119, by decide⟩ : Fin 1069) = faceMask (⟨119, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0120 : supportIntersection (⟨120, by decide⟩ : Fin 1069) = faceMask (⟨120, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0121 : supportIntersection (⟨121, by decide⟩ : Fin 1069) = faceMask (⟨121, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0122 : supportIntersection (⟨122, by decide⟩ : Fin 1069) = faceMask (⟨122, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0123 : supportIntersection (⟨123, by decide⟩ : Fin 1069) = faceMask (⟨123, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0124 : supportIntersection (⟨124, by decide⟩ : Fin 1069) = faceMask (⟨124, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0125 : supportIntersection (⟨125, by decide⟩ : Fin 1069) = faceMask (⟨125, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0126 : supportIntersection (⟨126, by decide⟩ : Fin 1069) = faceMask (⟨126, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0127 : supportIntersection (⟨127, by decide⟩ : Fin 1069) = faceMask (⟨127, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0128 : supportIntersection (⟨128, by decide⟩ : Fin 1069) = faceMask (⟨128, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0129 : supportIntersection (⟨129, by decide⟩ : Fin 1069) = faceMask (⟨129, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0130 : supportIntersection (⟨130, by decide⟩ : Fin 1069) = faceMask (⟨130, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0131 : supportIntersection (⟨131, by decide⟩ : Fin 1069) = faceMask (⟨131, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0132 : supportIntersection (⟨132, by decide⟩ : Fin 1069) = faceMask (⟨132, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0133 : supportIntersection (⟨133, by decide⟩ : Fin 1069) = faceMask (⟨133, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0134 : supportIntersection (⟨134, by decide⟩ : Fin 1069) = faceMask (⟨134, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0135 : supportIntersection (⟨135, by decide⟩ : Fin 1069) = faceMask (⟨135, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0136 : supportIntersection (⟨136, by decide⟩ : Fin 1069) = faceMask (⟨136, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0137 : supportIntersection (⟨137, by decide⟩ : Fin 1069) = faceMask (⟨137, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0138 : supportIntersection (⟨138, by decide⟩ : Fin 1069) = faceMask (⟨138, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0139 : supportIntersection (⟨139, by decide⟩ : Fin 1069) = faceMask (⟨139, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0140 : supportIntersection (⟨140, by decide⟩ : Fin 1069) = faceMask (⟨140, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0141 : supportIntersection (⟨141, by decide⟩ : Fin 1069) = faceMask (⟨141, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0142 : supportIntersection (⟨142, by decide⟩ : Fin 1069) = faceMask (⟨142, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0143 : supportIntersection (⟨143, by decide⟩ : Fin 1069) = faceMask (⟨143, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0144 : supportIntersection (⟨144, by decide⟩ : Fin 1069) = faceMask (⟨144, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0145 : supportIntersection (⟨145, by decide⟩ : Fin 1069) = faceMask (⟨145, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0146 : supportIntersection (⟨146, by decide⟩ : Fin 1069) = faceMask (⟨146, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0147 : supportIntersection (⟨147, by decide⟩ : Fin 1069) = faceMask (⟨147, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0148 : supportIntersection (⟨148, by decide⟩ : Fin 1069) = faceMask (⟨148, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0149 : supportIntersection (⟨149, by decide⟩ : Fin 1069) = faceMask (⟨149, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0150 : supportIntersection (⟨150, by decide⟩ : Fin 1069) = faceMask (⟨150, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0151 : supportIntersection (⟨151, by decide⟩ : Fin 1069) = faceMask (⟨151, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0152 : supportIntersection (⟨152, by decide⟩ : Fin 1069) = faceMask (⟨152, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0153 : supportIntersection (⟨153, by decide⟩ : Fin 1069) = faceMask (⟨153, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0154 : supportIntersection (⟨154, by decide⟩ : Fin 1069) = faceMask (⟨154, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0155 : supportIntersection (⟨155, by decide⟩ : Fin 1069) = faceMask (⟨155, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0156 : supportIntersection (⟨156, by decide⟩ : Fin 1069) = faceMask (⟨156, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0157 : supportIntersection (⟨157, by decide⟩ : Fin 1069) = faceMask (⟨157, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0158 : supportIntersection (⟨158, by decide⟩ : Fin 1069) = faceMask (⟨158, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0159 : supportIntersection (⟨159, by decide⟩ : Fin 1069) = faceMask (⟨159, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0160 : supportIntersection (⟨160, by decide⟩ : Fin 1069) = faceMask (⟨160, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0161 : supportIntersection (⟨161, by decide⟩ : Fin 1069) = faceMask (⟨161, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0162 : supportIntersection (⟨162, by decide⟩ : Fin 1069) = faceMask (⟨162, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0163 : supportIntersection (⟨163, by decide⟩ : Fin 1069) = faceMask (⟨163, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0164 : supportIntersection (⟨164, by decide⟩ : Fin 1069) = faceMask (⟨164, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0165 : supportIntersection (⟨165, by decide⟩ : Fin 1069) = faceMask (⟨165, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0166 : supportIntersection (⟨166, by decide⟩ : Fin 1069) = faceMask (⟨166, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0167 : supportIntersection (⟨167, by decide⟩ : Fin 1069) = faceMask (⟨167, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0168 : supportIntersection (⟨168, by decide⟩ : Fin 1069) = faceMask (⟨168, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0169 : supportIntersection (⟨169, by decide⟩ : Fin 1069) = faceMask (⟨169, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0170 : supportIntersection (⟨170, by decide⟩ : Fin 1069) = faceMask (⟨170, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0171 : supportIntersection (⟨171, by decide⟩ : Fin 1069) = faceMask (⟨171, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0172 : supportIntersection (⟨172, by decide⟩ : Fin 1069) = faceMask (⟨172, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0173 : supportIntersection (⟨173, by decide⟩ : Fin 1069) = faceMask (⟨173, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0174 : supportIntersection (⟨174, by decide⟩ : Fin 1069) = faceMask (⟨174, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0175 : supportIntersection (⟨175, by decide⟩ : Fin 1069) = faceMask (⟨175, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0176 : supportIntersection (⟨176, by decide⟩ : Fin 1069) = faceMask (⟨176, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0177 : supportIntersection (⟨177, by decide⟩ : Fin 1069) = faceMask (⟨177, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0178 : supportIntersection (⟨178, by decide⟩ : Fin 1069) = faceMask (⟨178, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0179 : supportIntersection (⟨179, by decide⟩ : Fin 1069) = faceMask (⟨179, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0180 : supportIntersection (⟨180, by decide⟩ : Fin 1069) = faceMask (⟨180, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0181 : supportIntersection (⟨181, by decide⟩ : Fin 1069) = faceMask (⟨181, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0182 : supportIntersection (⟨182, by decide⟩ : Fin 1069) = faceMask (⟨182, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0183 : supportIntersection (⟨183, by decide⟩ : Fin 1069) = faceMask (⟨183, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0184 : supportIntersection (⟨184, by decide⟩ : Fin 1069) = faceMask (⟨184, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0185 : supportIntersection (⟨185, by decide⟩ : Fin 1069) = faceMask (⟨185, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0186 : supportIntersection (⟨186, by decide⟩ : Fin 1069) = faceMask (⟨186, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0187 : supportIntersection (⟨187, by decide⟩ : Fin 1069) = faceMask (⟨187, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0188 : supportIntersection (⟨188, by decide⟩ : Fin 1069) = faceMask (⟨188, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0189 : supportIntersection (⟨189, by decide⟩ : Fin 1069) = faceMask (⟨189, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0190 : supportIntersection (⟨190, by decide⟩ : Fin 1069) = faceMask (⟨190, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0191 : supportIntersection (⟨191, by decide⟩ : Fin 1069) = faceMask (⟨191, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0192 : supportIntersection (⟨192, by decide⟩ : Fin 1069) = faceMask (⟨192, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0193 : supportIntersection (⟨193, by decide⟩ : Fin 1069) = faceMask (⟨193, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0194 : supportIntersection (⟨194, by decide⟩ : Fin 1069) = faceMask (⟨194, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0195 : supportIntersection (⟨195, by decide⟩ : Fin 1069) = faceMask (⟨195, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0196 : supportIntersection (⟨196, by decide⟩ : Fin 1069) = faceMask (⟨196, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0197 : supportIntersection (⟨197, by decide⟩ : Fin 1069) = faceMask (⟨197, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0198 : supportIntersection (⟨198, by decide⟩ : Fin 1069) = faceMask (⟨198, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0199 : supportIntersection (⟨199, by decide⟩ : Fin 1069) = faceMask (⟨199, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0200 : supportIntersection (⟨200, by decide⟩ : Fin 1069) = faceMask (⟨200, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0201 : supportIntersection (⟨201, by decide⟩ : Fin 1069) = faceMask (⟨201, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0202 : supportIntersection (⟨202, by decide⟩ : Fin 1069) = faceMask (⟨202, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0203 : supportIntersection (⟨203, by decide⟩ : Fin 1069) = faceMask (⟨203, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0204 : supportIntersection (⟨204, by decide⟩ : Fin 1069) = faceMask (⟨204, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0205 : supportIntersection (⟨205, by decide⟩ : Fin 1069) = faceMask (⟨205, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0206 : supportIntersection (⟨206, by decide⟩ : Fin 1069) = faceMask (⟨206, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0207 : supportIntersection (⟨207, by decide⟩ : Fin 1069) = faceMask (⟨207, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0208 : supportIntersection (⟨208, by decide⟩ : Fin 1069) = faceMask (⟨208, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0209 : supportIntersection (⟨209, by decide⟩ : Fin 1069) = faceMask (⟨209, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0210 : supportIntersection (⟨210, by decide⟩ : Fin 1069) = faceMask (⟨210, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0211 : supportIntersection (⟨211, by decide⟩ : Fin 1069) = faceMask (⟨211, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0212 : supportIntersection (⟨212, by decide⟩ : Fin 1069) = faceMask (⟨212, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0213 : supportIntersection (⟨213, by decide⟩ : Fin 1069) = faceMask (⟨213, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0214 : supportIntersection (⟨214, by decide⟩ : Fin 1069) = faceMask (⟨214, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0215 : supportIntersection (⟨215, by decide⟩ : Fin 1069) = faceMask (⟨215, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0216 : supportIntersection (⟨216, by decide⟩ : Fin 1069) = faceMask (⟨216, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0217 : supportIntersection (⟨217, by decide⟩ : Fin 1069) = faceMask (⟨217, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0218 : supportIntersection (⟨218, by decide⟩ : Fin 1069) = faceMask (⟨218, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0219 : supportIntersection (⟨219, by decide⟩ : Fin 1069) = faceMask (⟨219, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0220 : supportIntersection (⟨220, by decide⟩ : Fin 1069) = faceMask (⟨220, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0221 : supportIntersection (⟨221, by decide⟩ : Fin 1069) = faceMask (⟨221, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0222 : supportIntersection (⟨222, by decide⟩ : Fin 1069) = faceMask (⟨222, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0223 : supportIntersection (⟨223, by decide⟩ : Fin 1069) = faceMask (⟨223, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0224 : supportIntersection (⟨224, by decide⟩ : Fin 1069) = faceMask (⟨224, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0225 : supportIntersection (⟨225, by decide⟩ : Fin 1069) = faceMask (⟨225, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0226 : supportIntersection (⟨226, by decide⟩ : Fin 1069) = faceMask (⟨226, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0227 : supportIntersection (⟨227, by decide⟩ : Fin 1069) = faceMask (⟨227, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0228 : supportIntersection (⟨228, by decide⟩ : Fin 1069) = faceMask (⟨228, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0229 : supportIntersection (⟨229, by decide⟩ : Fin 1069) = faceMask (⟨229, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0230 : supportIntersection (⟨230, by decide⟩ : Fin 1069) = faceMask (⟨230, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0231 : supportIntersection (⟨231, by decide⟩ : Fin 1069) = faceMask (⟨231, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0232 : supportIntersection (⟨232, by decide⟩ : Fin 1069) = faceMask (⟨232, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0233 : supportIntersection (⟨233, by decide⟩ : Fin 1069) = faceMask (⟨233, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0234 : supportIntersection (⟨234, by decide⟩ : Fin 1069) = faceMask (⟨234, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0235 : supportIntersection (⟨235, by decide⟩ : Fin 1069) = faceMask (⟨235, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0236 : supportIntersection (⟨236, by decide⟩ : Fin 1069) = faceMask (⟨236, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0237 : supportIntersection (⟨237, by decide⟩ : Fin 1069) = faceMask (⟨237, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0238 : supportIntersection (⟨238, by decide⟩ : Fin 1069) = faceMask (⟨238, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0239 : supportIntersection (⟨239, by decide⟩ : Fin 1069) = faceMask (⟨239, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0240 : supportIntersection (⟨240, by decide⟩ : Fin 1069) = faceMask (⟨240, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0241 : supportIntersection (⟨241, by decide⟩ : Fin 1069) = faceMask (⟨241, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0242 : supportIntersection (⟨242, by decide⟩ : Fin 1069) = faceMask (⟨242, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0243 : supportIntersection (⟨243, by decide⟩ : Fin 1069) = faceMask (⟨243, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0244 : supportIntersection (⟨244, by decide⟩ : Fin 1069) = faceMask (⟨244, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0245 : supportIntersection (⟨245, by decide⟩ : Fin 1069) = faceMask (⟨245, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0246 : supportIntersection (⟨246, by decide⟩ : Fin 1069) = faceMask (⟨246, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0247 : supportIntersection (⟨247, by decide⟩ : Fin 1069) = faceMask (⟨247, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0248 : supportIntersection (⟨248, by decide⟩ : Fin 1069) = faceMask (⟨248, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0249 : supportIntersection (⟨249, by decide⟩ : Fin 1069) = faceMask (⟨249, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0250 : supportIntersection (⟨250, by decide⟩ : Fin 1069) = faceMask (⟨250, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0251 : supportIntersection (⟨251, by decide⟩ : Fin 1069) = faceMask (⟨251, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0252 : supportIntersection (⟨252, by decide⟩ : Fin 1069) = faceMask (⟨252, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0253 : supportIntersection (⟨253, by decide⟩ : Fin 1069) = faceMask (⟨253, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0254 : supportIntersection (⟨254, by decide⟩ : Fin 1069) = faceMask (⟨254, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0255 : supportIntersection (⟨255, by decide⟩ : Fin 1069) = faceMask (⟨255, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0256 : supportIntersection (⟨256, by decide⟩ : Fin 1069) = faceMask (⟨256, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0257 : supportIntersection (⟨257, by decide⟩ : Fin 1069) = faceMask (⟨257, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0258 : supportIntersection (⟨258, by decide⟩ : Fin 1069) = faceMask (⟨258, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0259 : supportIntersection (⟨259, by decide⟩ : Fin 1069) = faceMask (⟨259, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0260 : supportIntersection (⟨260, by decide⟩ : Fin 1069) = faceMask (⟨260, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0261 : supportIntersection (⟨261, by decide⟩ : Fin 1069) = faceMask (⟨261, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0262 : supportIntersection (⟨262, by decide⟩ : Fin 1069) = faceMask (⟨262, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0263 : supportIntersection (⟨263, by decide⟩ : Fin 1069) = faceMask (⟨263, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0264 : supportIntersection (⟨264, by decide⟩ : Fin 1069) = faceMask (⟨264, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0265 : supportIntersection (⟨265, by decide⟩ : Fin 1069) = faceMask (⟨265, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0266 : supportIntersection (⟨266, by decide⟩ : Fin 1069) = faceMask (⟨266, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0267 : supportIntersection (⟨267, by decide⟩ : Fin 1069) = faceMask (⟨267, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0268 : supportIntersection (⟨268, by decide⟩ : Fin 1069) = faceMask (⟨268, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0269 : supportIntersection (⟨269, by decide⟩ : Fin 1069) = faceMask (⟨269, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0270 : supportIntersection (⟨270, by decide⟩ : Fin 1069) = faceMask (⟨270, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0271 : supportIntersection (⟨271, by decide⟩ : Fin 1069) = faceMask (⟨271, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0272 : supportIntersection (⟨272, by decide⟩ : Fin 1069) = faceMask (⟨272, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0273 : supportIntersection (⟨273, by decide⟩ : Fin 1069) = faceMask (⟨273, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0274 : supportIntersection (⟨274, by decide⟩ : Fin 1069) = faceMask (⟨274, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0275 : supportIntersection (⟨275, by decide⟩ : Fin 1069) = faceMask (⟨275, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0276 : supportIntersection (⟨276, by decide⟩ : Fin 1069) = faceMask (⟨276, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0277 : supportIntersection (⟨277, by decide⟩ : Fin 1069) = faceMask (⟨277, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0278 : supportIntersection (⟨278, by decide⟩ : Fin 1069) = faceMask (⟨278, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0279 : supportIntersection (⟨279, by decide⟩ : Fin 1069) = faceMask (⟨279, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0280 : supportIntersection (⟨280, by decide⟩ : Fin 1069) = faceMask (⟨280, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0281 : supportIntersection (⟨281, by decide⟩ : Fin 1069) = faceMask (⟨281, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0282 : supportIntersection (⟨282, by decide⟩ : Fin 1069) = faceMask (⟨282, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0283 : supportIntersection (⟨283, by decide⟩ : Fin 1069) = faceMask (⟨283, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0284 : supportIntersection (⟨284, by decide⟩ : Fin 1069) = faceMask (⟨284, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0285 : supportIntersection (⟨285, by decide⟩ : Fin 1069) = faceMask (⟨285, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0286 : supportIntersection (⟨286, by decide⟩ : Fin 1069) = faceMask (⟨286, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0287 : supportIntersection (⟨287, by decide⟩ : Fin 1069) = faceMask (⟨287, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0288 : supportIntersection (⟨288, by decide⟩ : Fin 1069) = faceMask (⟨288, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0289 : supportIntersection (⟨289, by decide⟩ : Fin 1069) = faceMask (⟨289, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0290 : supportIntersection (⟨290, by decide⟩ : Fin 1069) = faceMask (⟨290, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0291 : supportIntersection (⟨291, by decide⟩ : Fin 1069) = faceMask (⟨291, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0292 : supportIntersection (⟨292, by decide⟩ : Fin 1069) = faceMask (⟨292, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0293 : supportIntersection (⟨293, by decide⟩ : Fin 1069) = faceMask (⟨293, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0294 : supportIntersection (⟨294, by decide⟩ : Fin 1069) = faceMask (⟨294, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0295 : supportIntersection (⟨295, by decide⟩ : Fin 1069) = faceMask (⟨295, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0296 : supportIntersection (⟨296, by decide⟩ : Fin 1069) = faceMask (⟨296, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0297 : supportIntersection (⟨297, by decide⟩ : Fin 1069) = faceMask (⟨297, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0298 : supportIntersection (⟨298, by decide⟩ : Fin 1069) = faceMask (⟨298, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0299 : supportIntersection (⟨299, by decide⟩ : Fin 1069) = faceMask (⟨299, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0300 : supportIntersection (⟨300, by decide⟩ : Fin 1069) = faceMask (⟨300, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0301 : supportIntersection (⟨301, by decide⟩ : Fin 1069) = faceMask (⟨301, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0302 : supportIntersection (⟨302, by decide⟩ : Fin 1069) = faceMask (⟨302, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0303 : supportIntersection (⟨303, by decide⟩ : Fin 1069) = faceMask (⟨303, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0304 : supportIntersection (⟨304, by decide⟩ : Fin 1069) = faceMask (⟨304, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0305 : supportIntersection (⟨305, by decide⟩ : Fin 1069) = faceMask (⟨305, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0306 : supportIntersection (⟨306, by decide⟩ : Fin 1069) = faceMask (⟨306, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0307 : supportIntersection (⟨307, by decide⟩ : Fin 1069) = faceMask (⟨307, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0308 : supportIntersection (⟨308, by decide⟩ : Fin 1069) = faceMask (⟨308, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0309 : supportIntersection (⟨309, by decide⟩ : Fin 1069) = faceMask (⟨309, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0310 : supportIntersection (⟨310, by decide⟩ : Fin 1069) = faceMask (⟨310, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0311 : supportIntersection (⟨311, by decide⟩ : Fin 1069) = faceMask (⟨311, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0312 : supportIntersection (⟨312, by decide⟩ : Fin 1069) = faceMask (⟨312, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0313 : supportIntersection (⟨313, by decide⟩ : Fin 1069) = faceMask (⟨313, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0314 : supportIntersection (⟨314, by decide⟩ : Fin 1069) = faceMask (⟨314, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0315 : supportIntersection (⟨315, by decide⟩ : Fin 1069) = faceMask (⟨315, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0316 : supportIntersection (⟨316, by decide⟩ : Fin 1069) = faceMask (⟨316, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0317 : supportIntersection (⟨317, by decide⟩ : Fin 1069) = faceMask (⟨317, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0318 : supportIntersection (⟨318, by decide⟩ : Fin 1069) = faceMask (⟨318, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0319 : supportIntersection (⟨319, by decide⟩ : Fin 1069) = faceMask (⟨319, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0320 : supportIntersection (⟨320, by decide⟩ : Fin 1069) = faceMask (⟨320, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0321 : supportIntersection (⟨321, by decide⟩ : Fin 1069) = faceMask (⟨321, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0322 : supportIntersection (⟨322, by decide⟩ : Fin 1069) = faceMask (⟨322, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0323 : supportIntersection (⟨323, by decide⟩ : Fin 1069) = faceMask (⟨323, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0324 : supportIntersection (⟨324, by decide⟩ : Fin 1069) = faceMask (⟨324, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0325 : supportIntersection (⟨325, by decide⟩ : Fin 1069) = faceMask (⟨325, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0326 : supportIntersection (⟨326, by decide⟩ : Fin 1069) = faceMask (⟨326, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0327 : supportIntersection (⟨327, by decide⟩ : Fin 1069) = faceMask (⟨327, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0328 : supportIntersection (⟨328, by decide⟩ : Fin 1069) = faceMask (⟨328, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0329 : supportIntersection (⟨329, by decide⟩ : Fin 1069) = faceMask (⟨329, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0330 : supportIntersection (⟨330, by decide⟩ : Fin 1069) = faceMask (⟨330, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0331 : supportIntersection (⟨331, by decide⟩ : Fin 1069) = faceMask (⟨331, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0332 : supportIntersection (⟨332, by decide⟩ : Fin 1069) = faceMask (⟨332, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0333 : supportIntersection (⟨333, by decide⟩ : Fin 1069) = faceMask (⟨333, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0334 : supportIntersection (⟨334, by decide⟩ : Fin 1069) = faceMask (⟨334, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0335 : supportIntersection (⟨335, by decide⟩ : Fin 1069) = faceMask (⟨335, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0336 : supportIntersection (⟨336, by decide⟩ : Fin 1069) = faceMask (⟨336, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0337 : supportIntersection (⟨337, by decide⟩ : Fin 1069) = faceMask (⟨337, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0338 : supportIntersection (⟨338, by decide⟩ : Fin 1069) = faceMask (⟨338, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0339 : supportIntersection (⟨339, by decide⟩ : Fin 1069) = faceMask (⟨339, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0340 : supportIntersection (⟨340, by decide⟩ : Fin 1069) = faceMask (⟨340, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0341 : supportIntersection (⟨341, by decide⟩ : Fin 1069) = faceMask (⟨341, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0342 : supportIntersection (⟨342, by decide⟩ : Fin 1069) = faceMask (⟨342, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0343 : supportIntersection (⟨343, by decide⟩ : Fin 1069) = faceMask (⟨343, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0344 : supportIntersection (⟨344, by decide⟩ : Fin 1069) = faceMask (⟨344, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0345 : supportIntersection (⟨345, by decide⟩ : Fin 1069) = faceMask (⟨345, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0346 : supportIntersection (⟨346, by decide⟩ : Fin 1069) = faceMask (⟨346, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0347 : supportIntersection (⟨347, by decide⟩ : Fin 1069) = faceMask (⟨347, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0348 : supportIntersection (⟨348, by decide⟩ : Fin 1069) = faceMask (⟨348, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0349 : supportIntersection (⟨349, by decide⟩ : Fin 1069) = faceMask (⟨349, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0350 : supportIntersection (⟨350, by decide⟩ : Fin 1069) = faceMask (⟨350, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0351 : supportIntersection (⟨351, by decide⟩ : Fin 1069) = faceMask (⟨351, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0352 : supportIntersection (⟨352, by decide⟩ : Fin 1069) = faceMask (⟨352, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0353 : supportIntersection (⟨353, by decide⟩ : Fin 1069) = faceMask (⟨353, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0354 : supportIntersection (⟨354, by decide⟩ : Fin 1069) = faceMask (⟨354, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0355 : supportIntersection (⟨355, by decide⟩ : Fin 1069) = faceMask (⟨355, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0356 : supportIntersection (⟨356, by decide⟩ : Fin 1069) = faceMask (⟨356, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0357 : supportIntersection (⟨357, by decide⟩ : Fin 1069) = faceMask (⟨357, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0358 : supportIntersection (⟨358, by decide⟩ : Fin 1069) = faceMask (⟨358, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0359 : supportIntersection (⟨359, by decide⟩ : Fin 1069) = faceMask (⟨359, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0360 : supportIntersection (⟨360, by decide⟩ : Fin 1069) = faceMask (⟨360, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0361 : supportIntersection (⟨361, by decide⟩ : Fin 1069) = faceMask (⟨361, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0362 : supportIntersection (⟨362, by decide⟩ : Fin 1069) = faceMask (⟨362, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0363 : supportIntersection (⟨363, by decide⟩ : Fin 1069) = faceMask (⟨363, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0364 : supportIntersection (⟨364, by decide⟩ : Fin 1069) = faceMask (⟨364, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0365 : supportIntersection (⟨365, by decide⟩ : Fin 1069) = faceMask (⟨365, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0366 : supportIntersection (⟨366, by decide⟩ : Fin 1069) = faceMask (⟨366, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0367 : supportIntersection (⟨367, by decide⟩ : Fin 1069) = faceMask (⟨367, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0368 : supportIntersection (⟨368, by decide⟩ : Fin 1069) = faceMask (⟨368, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0369 : supportIntersection (⟨369, by decide⟩ : Fin 1069) = faceMask (⟨369, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0370 : supportIntersection (⟨370, by decide⟩ : Fin 1069) = faceMask (⟨370, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0371 : supportIntersection (⟨371, by decide⟩ : Fin 1069) = faceMask (⟨371, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0372 : supportIntersection (⟨372, by decide⟩ : Fin 1069) = faceMask (⟨372, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0373 : supportIntersection (⟨373, by decide⟩ : Fin 1069) = faceMask (⟨373, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0374 : supportIntersection (⟨374, by decide⟩ : Fin 1069) = faceMask (⟨374, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0375 : supportIntersection (⟨375, by decide⟩ : Fin 1069) = faceMask (⟨375, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0376 : supportIntersection (⟨376, by decide⟩ : Fin 1069) = faceMask (⟨376, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0377 : supportIntersection (⟨377, by decide⟩ : Fin 1069) = faceMask (⟨377, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0378 : supportIntersection (⟨378, by decide⟩ : Fin 1069) = faceMask (⟨378, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0379 : supportIntersection (⟨379, by decide⟩ : Fin 1069) = faceMask (⟨379, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0380 : supportIntersection (⟨380, by decide⟩ : Fin 1069) = faceMask (⟨380, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0381 : supportIntersection (⟨381, by decide⟩ : Fin 1069) = faceMask (⟨381, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0382 : supportIntersection (⟨382, by decide⟩ : Fin 1069) = faceMask (⟨382, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0383 : supportIntersection (⟨383, by decide⟩ : Fin 1069) = faceMask (⟨383, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0384 : supportIntersection (⟨384, by decide⟩ : Fin 1069) = faceMask (⟨384, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0385 : supportIntersection (⟨385, by decide⟩ : Fin 1069) = faceMask (⟨385, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0386 : supportIntersection (⟨386, by decide⟩ : Fin 1069) = faceMask (⟨386, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0387 : supportIntersection (⟨387, by decide⟩ : Fin 1069) = faceMask (⟨387, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0388 : supportIntersection (⟨388, by decide⟩ : Fin 1069) = faceMask (⟨388, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0389 : supportIntersection (⟨389, by decide⟩ : Fin 1069) = faceMask (⟨389, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0390 : supportIntersection (⟨390, by decide⟩ : Fin 1069) = faceMask (⟨390, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0391 : supportIntersection (⟨391, by decide⟩ : Fin 1069) = faceMask (⟨391, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0392 : supportIntersection (⟨392, by decide⟩ : Fin 1069) = faceMask (⟨392, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0393 : supportIntersection (⟨393, by decide⟩ : Fin 1069) = faceMask (⟨393, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0394 : supportIntersection (⟨394, by decide⟩ : Fin 1069) = faceMask (⟨394, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0395 : supportIntersection (⟨395, by decide⟩ : Fin 1069) = faceMask (⟨395, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0396 : supportIntersection (⟨396, by decide⟩ : Fin 1069) = faceMask (⟨396, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0397 : supportIntersection (⟨397, by decide⟩ : Fin 1069) = faceMask (⟨397, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0398 : supportIntersection (⟨398, by decide⟩ : Fin 1069) = faceMask (⟨398, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0399 : supportIntersection (⟨399, by decide⟩ : Fin 1069) = faceMask (⟨399, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0400 : supportIntersection (⟨400, by decide⟩ : Fin 1069) = faceMask (⟨400, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0401 : supportIntersection (⟨401, by decide⟩ : Fin 1069) = faceMask (⟨401, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0402 : supportIntersection (⟨402, by decide⟩ : Fin 1069) = faceMask (⟨402, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0403 : supportIntersection (⟨403, by decide⟩ : Fin 1069) = faceMask (⟨403, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0404 : supportIntersection (⟨404, by decide⟩ : Fin 1069) = faceMask (⟨404, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0405 : supportIntersection (⟨405, by decide⟩ : Fin 1069) = faceMask (⟨405, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0406 : supportIntersection (⟨406, by decide⟩ : Fin 1069) = faceMask (⟨406, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0407 : supportIntersection (⟨407, by decide⟩ : Fin 1069) = faceMask (⟨407, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0408 : supportIntersection (⟨408, by decide⟩ : Fin 1069) = faceMask (⟨408, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0409 : supportIntersection (⟨409, by decide⟩ : Fin 1069) = faceMask (⟨409, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0410 : supportIntersection (⟨410, by decide⟩ : Fin 1069) = faceMask (⟨410, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0411 : supportIntersection (⟨411, by decide⟩ : Fin 1069) = faceMask (⟨411, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0412 : supportIntersection (⟨412, by decide⟩ : Fin 1069) = faceMask (⟨412, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0413 : supportIntersection (⟨413, by decide⟩ : Fin 1069) = faceMask (⟨413, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0414 : supportIntersection (⟨414, by decide⟩ : Fin 1069) = faceMask (⟨414, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0415 : supportIntersection (⟨415, by decide⟩ : Fin 1069) = faceMask (⟨415, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0416 : supportIntersection (⟨416, by decide⟩ : Fin 1069) = faceMask (⟨416, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0417 : supportIntersection (⟨417, by decide⟩ : Fin 1069) = faceMask (⟨417, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0418 : supportIntersection (⟨418, by decide⟩ : Fin 1069) = faceMask (⟨418, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0419 : supportIntersection (⟨419, by decide⟩ : Fin 1069) = faceMask (⟨419, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0420 : supportIntersection (⟨420, by decide⟩ : Fin 1069) = faceMask (⟨420, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0421 : supportIntersection (⟨421, by decide⟩ : Fin 1069) = faceMask (⟨421, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0422 : supportIntersection (⟨422, by decide⟩ : Fin 1069) = faceMask (⟨422, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0423 : supportIntersection (⟨423, by decide⟩ : Fin 1069) = faceMask (⟨423, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0424 : supportIntersection (⟨424, by decide⟩ : Fin 1069) = faceMask (⟨424, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0425 : supportIntersection (⟨425, by decide⟩ : Fin 1069) = faceMask (⟨425, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0426 : supportIntersection (⟨426, by decide⟩ : Fin 1069) = faceMask (⟨426, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0427 : supportIntersection (⟨427, by decide⟩ : Fin 1069) = faceMask (⟨427, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0428 : supportIntersection (⟨428, by decide⟩ : Fin 1069) = faceMask (⟨428, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0429 : supportIntersection (⟨429, by decide⟩ : Fin 1069) = faceMask (⟨429, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0430 : supportIntersection (⟨430, by decide⟩ : Fin 1069) = faceMask (⟨430, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0431 : supportIntersection (⟨431, by decide⟩ : Fin 1069) = faceMask (⟨431, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0432 : supportIntersection (⟨432, by decide⟩ : Fin 1069) = faceMask (⟨432, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0433 : supportIntersection (⟨433, by decide⟩ : Fin 1069) = faceMask (⟨433, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0434 : supportIntersection (⟨434, by decide⟩ : Fin 1069) = faceMask (⟨434, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0435 : supportIntersection (⟨435, by decide⟩ : Fin 1069) = faceMask (⟨435, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0436 : supportIntersection (⟨436, by decide⟩ : Fin 1069) = faceMask (⟨436, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0437 : supportIntersection (⟨437, by decide⟩ : Fin 1069) = faceMask (⟨437, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0438 : supportIntersection (⟨438, by decide⟩ : Fin 1069) = faceMask (⟨438, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0439 : supportIntersection (⟨439, by decide⟩ : Fin 1069) = faceMask (⟨439, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0440 : supportIntersection (⟨440, by decide⟩ : Fin 1069) = faceMask (⟨440, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0441 : supportIntersection (⟨441, by decide⟩ : Fin 1069) = faceMask (⟨441, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0442 : supportIntersection (⟨442, by decide⟩ : Fin 1069) = faceMask (⟨442, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0443 : supportIntersection (⟨443, by decide⟩ : Fin 1069) = faceMask (⟨443, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0444 : supportIntersection (⟨444, by decide⟩ : Fin 1069) = faceMask (⟨444, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0445 : supportIntersection (⟨445, by decide⟩ : Fin 1069) = faceMask (⟨445, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0446 : supportIntersection (⟨446, by decide⟩ : Fin 1069) = faceMask (⟨446, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0447 : supportIntersection (⟨447, by decide⟩ : Fin 1069) = faceMask (⟨447, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0448 : supportIntersection (⟨448, by decide⟩ : Fin 1069) = faceMask (⟨448, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0449 : supportIntersection (⟨449, by decide⟩ : Fin 1069) = faceMask (⟨449, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0450 : supportIntersection (⟨450, by decide⟩ : Fin 1069) = faceMask (⟨450, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0451 : supportIntersection (⟨451, by decide⟩ : Fin 1069) = faceMask (⟨451, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0452 : supportIntersection (⟨452, by decide⟩ : Fin 1069) = faceMask (⟨452, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0453 : supportIntersection (⟨453, by decide⟩ : Fin 1069) = faceMask (⟨453, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0454 : supportIntersection (⟨454, by decide⟩ : Fin 1069) = faceMask (⟨454, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0455 : supportIntersection (⟨455, by decide⟩ : Fin 1069) = faceMask (⟨455, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0456 : supportIntersection (⟨456, by decide⟩ : Fin 1069) = faceMask (⟨456, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0457 : supportIntersection (⟨457, by decide⟩ : Fin 1069) = faceMask (⟨457, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0458 : supportIntersection (⟨458, by decide⟩ : Fin 1069) = faceMask (⟨458, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0459 : supportIntersection (⟨459, by decide⟩ : Fin 1069) = faceMask (⟨459, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0460 : supportIntersection (⟨460, by decide⟩ : Fin 1069) = faceMask (⟨460, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0461 : supportIntersection (⟨461, by decide⟩ : Fin 1069) = faceMask (⟨461, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0462 : supportIntersection (⟨462, by decide⟩ : Fin 1069) = faceMask (⟨462, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0463 : supportIntersection (⟨463, by decide⟩ : Fin 1069) = faceMask (⟨463, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0464 : supportIntersection (⟨464, by decide⟩ : Fin 1069) = faceMask (⟨464, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0465 : supportIntersection (⟨465, by decide⟩ : Fin 1069) = faceMask (⟨465, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0466 : supportIntersection (⟨466, by decide⟩ : Fin 1069) = faceMask (⟨466, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0467 : supportIntersection (⟨467, by decide⟩ : Fin 1069) = faceMask (⟨467, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0468 : supportIntersection (⟨468, by decide⟩ : Fin 1069) = faceMask (⟨468, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0469 : supportIntersection (⟨469, by decide⟩ : Fin 1069) = faceMask (⟨469, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0470 : supportIntersection (⟨470, by decide⟩ : Fin 1069) = faceMask (⟨470, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0471 : supportIntersection (⟨471, by decide⟩ : Fin 1069) = faceMask (⟨471, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0472 : supportIntersection (⟨472, by decide⟩ : Fin 1069) = faceMask (⟨472, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0473 : supportIntersection (⟨473, by decide⟩ : Fin 1069) = faceMask (⟨473, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0474 : supportIntersection (⟨474, by decide⟩ : Fin 1069) = faceMask (⟨474, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0475 : supportIntersection (⟨475, by decide⟩ : Fin 1069) = faceMask (⟨475, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0476 : supportIntersection (⟨476, by decide⟩ : Fin 1069) = faceMask (⟨476, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0477 : supportIntersection (⟨477, by decide⟩ : Fin 1069) = faceMask (⟨477, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0478 : supportIntersection (⟨478, by decide⟩ : Fin 1069) = faceMask (⟨478, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0479 : supportIntersection (⟨479, by decide⟩ : Fin 1069) = faceMask (⟨479, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0480 : supportIntersection (⟨480, by decide⟩ : Fin 1069) = faceMask (⟨480, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0481 : supportIntersection (⟨481, by decide⟩ : Fin 1069) = faceMask (⟨481, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0482 : supportIntersection (⟨482, by decide⟩ : Fin 1069) = faceMask (⟨482, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0483 : supportIntersection (⟨483, by decide⟩ : Fin 1069) = faceMask (⟨483, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0484 : supportIntersection (⟨484, by decide⟩ : Fin 1069) = faceMask (⟨484, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0485 : supportIntersection (⟨485, by decide⟩ : Fin 1069) = faceMask (⟨485, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0486 : supportIntersection (⟨486, by decide⟩ : Fin 1069) = faceMask (⟨486, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0487 : supportIntersection (⟨487, by decide⟩ : Fin 1069) = faceMask (⟨487, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0488 : supportIntersection (⟨488, by decide⟩ : Fin 1069) = faceMask (⟨488, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0489 : supportIntersection (⟨489, by decide⟩ : Fin 1069) = faceMask (⟨489, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0490 : supportIntersection (⟨490, by decide⟩ : Fin 1069) = faceMask (⟨490, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0491 : supportIntersection (⟨491, by decide⟩ : Fin 1069) = faceMask (⟨491, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0492 : supportIntersection (⟨492, by decide⟩ : Fin 1069) = faceMask (⟨492, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0493 : supportIntersection (⟨493, by decide⟩ : Fin 1069) = faceMask (⟨493, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0494 : supportIntersection (⟨494, by decide⟩ : Fin 1069) = faceMask (⟨494, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0495 : supportIntersection (⟨495, by decide⟩ : Fin 1069) = faceMask (⟨495, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0496 : supportIntersection (⟨496, by decide⟩ : Fin 1069) = faceMask (⟨496, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0497 : supportIntersection (⟨497, by decide⟩ : Fin 1069) = faceMask (⟨497, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0498 : supportIntersection (⟨498, by decide⟩ : Fin 1069) = faceMask (⟨498, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0499 : supportIntersection (⟨499, by decide⟩ : Fin 1069) = faceMask (⟨499, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0500 : supportIntersection (⟨500, by decide⟩ : Fin 1069) = faceMask (⟨500, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0501 : supportIntersection (⟨501, by decide⟩ : Fin 1069) = faceMask (⟨501, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0502 : supportIntersection (⟨502, by decide⟩ : Fin 1069) = faceMask (⟨502, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0503 : supportIntersection (⟨503, by decide⟩ : Fin 1069) = faceMask (⟨503, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0504 : supportIntersection (⟨504, by decide⟩ : Fin 1069) = faceMask (⟨504, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0505 : supportIntersection (⟨505, by decide⟩ : Fin 1069) = faceMask (⟨505, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0506 : supportIntersection (⟨506, by decide⟩ : Fin 1069) = faceMask (⟨506, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0507 : supportIntersection (⟨507, by decide⟩ : Fin 1069) = faceMask (⟨507, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0508 : supportIntersection (⟨508, by decide⟩ : Fin 1069) = faceMask (⟨508, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0509 : supportIntersection (⟨509, by decide⟩ : Fin 1069) = faceMask (⟨509, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0510 : supportIntersection (⟨510, by decide⟩ : Fin 1069) = faceMask (⟨510, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0511 : supportIntersection (⟨511, by decide⟩ : Fin 1069) = faceMask (⟨511, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0512 : supportIntersection (⟨512, by decide⟩ : Fin 1069) = faceMask (⟨512, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0513 : supportIntersection (⟨513, by decide⟩ : Fin 1069) = faceMask (⟨513, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0514 : supportIntersection (⟨514, by decide⟩ : Fin 1069) = faceMask (⟨514, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0515 : supportIntersection (⟨515, by decide⟩ : Fin 1069) = faceMask (⟨515, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0516 : supportIntersection (⟨516, by decide⟩ : Fin 1069) = faceMask (⟨516, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0517 : supportIntersection (⟨517, by decide⟩ : Fin 1069) = faceMask (⟨517, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0518 : supportIntersection (⟨518, by decide⟩ : Fin 1069) = faceMask (⟨518, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0519 : supportIntersection (⟨519, by decide⟩ : Fin 1069) = faceMask (⟨519, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0520 : supportIntersection (⟨520, by decide⟩ : Fin 1069) = faceMask (⟨520, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0521 : supportIntersection (⟨521, by decide⟩ : Fin 1069) = faceMask (⟨521, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0522 : supportIntersection (⟨522, by decide⟩ : Fin 1069) = faceMask (⟨522, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0523 : supportIntersection (⟨523, by decide⟩ : Fin 1069) = faceMask (⟨523, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0524 : supportIntersection (⟨524, by decide⟩ : Fin 1069) = faceMask (⟨524, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0525 : supportIntersection (⟨525, by decide⟩ : Fin 1069) = faceMask (⟨525, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0526 : supportIntersection (⟨526, by decide⟩ : Fin 1069) = faceMask (⟨526, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0527 : supportIntersection (⟨527, by decide⟩ : Fin 1069) = faceMask (⟨527, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0528 : supportIntersection (⟨528, by decide⟩ : Fin 1069) = faceMask (⟨528, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0529 : supportIntersection (⟨529, by decide⟩ : Fin 1069) = faceMask (⟨529, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0530 : supportIntersection (⟨530, by decide⟩ : Fin 1069) = faceMask (⟨530, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0531 : supportIntersection (⟨531, by decide⟩ : Fin 1069) = faceMask (⟨531, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0532 : supportIntersection (⟨532, by decide⟩ : Fin 1069) = faceMask (⟨532, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0533 : supportIntersection (⟨533, by decide⟩ : Fin 1069) = faceMask (⟨533, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0534 : supportIntersection (⟨534, by decide⟩ : Fin 1069) = faceMask (⟨534, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0535 : supportIntersection (⟨535, by decide⟩ : Fin 1069) = faceMask (⟨535, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0536 : supportIntersection (⟨536, by decide⟩ : Fin 1069) = faceMask (⟨536, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0537 : supportIntersection (⟨537, by decide⟩ : Fin 1069) = faceMask (⟨537, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0538 : supportIntersection (⟨538, by decide⟩ : Fin 1069) = faceMask (⟨538, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0539 : supportIntersection (⟨539, by decide⟩ : Fin 1069) = faceMask (⟨539, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0540 : supportIntersection (⟨540, by decide⟩ : Fin 1069) = faceMask (⟨540, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0541 : supportIntersection (⟨541, by decide⟩ : Fin 1069) = faceMask (⟨541, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0542 : supportIntersection (⟨542, by decide⟩ : Fin 1069) = faceMask (⟨542, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0543 : supportIntersection (⟨543, by decide⟩ : Fin 1069) = faceMask (⟨543, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0544 : supportIntersection (⟨544, by decide⟩ : Fin 1069) = faceMask (⟨544, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0545 : supportIntersection (⟨545, by decide⟩ : Fin 1069) = faceMask (⟨545, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0546 : supportIntersection (⟨546, by decide⟩ : Fin 1069) = faceMask (⟨546, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0547 : supportIntersection (⟨547, by decide⟩ : Fin 1069) = faceMask (⟨547, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0548 : supportIntersection (⟨548, by decide⟩ : Fin 1069) = faceMask (⟨548, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0549 : supportIntersection (⟨549, by decide⟩ : Fin 1069) = faceMask (⟨549, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0550 : supportIntersection (⟨550, by decide⟩ : Fin 1069) = faceMask (⟨550, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0551 : supportIntersection (⟨551, by decide⟩ : Fin 1069) = faceMask (⟨551, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0552 : supportIntersection (⟨552, by decide⟩ : Fin 1069) = faceMask (⟨552, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0553 : supportIntersection (⟨553, by decide⟩ : Fin 1069) = faceMask (⟨553, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0554 : supportIntersection (⟨554, by decide⟩ : Fin 1069) = faceMask (⟨554, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0555 : supportIntersection (⟨555, by decide⟩ : Fin 1069) = faceMask (⟨555, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0556 : supportIntersection (⟨556, by decide⟩ : Fin 1069) = faceMask (⟨556, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0557 : supportIntersection (⟨557, by decide⟩ : Fin 1069) = faceMask (⟨557, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0558 : supportIntersection (⟨558, by decide⟩ : Fin 1069) = faceMask (⟨558, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0559 : supportIntersection (⟨559, by decide⟩ : Fin 1069) = faceMask (⟨559, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0560 : supportIntersection (⟨560, by decide⟩ : Fin 1069) = faceMask (⟨560, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0561 : supportIntersection (⟨561, by decide⟩ : Fin 1069) = faceMask (⟨561, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0562 : supportIntersection (⟨562, by decide⟩ : Fin 1069) = faceMask (⟨562, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0563 : supportIntersection (⟨563, by decide⟩ : Fin 1069) = faceMask (⟨563, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0564 : supportIntersection (⟨564, by decide⟩ : Fin 1069) = faceMask (⟨564, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0565 : supportIntersection (⟨565, by decide⟩ : Fin 1069) = faceMask (⟨565, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0566 : supportIntersection (⟨566, by decide⟩ : Fin 1069) = faceMask (⟨566, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0567 : supportIntersection (⟨567, by decide⟩ : Fin 1069) = faceMask (⟨567, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0568 : supportIntersection (⟨568, by decide⟩ : Fin 1069) = faceMask (⟨568, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0569 : supportIntersection (⟨569, by decide⟩ : Fin 1069) = faceMask (⟨569, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0570 : supportIntersection (⟨570, by decide⟩ : Fin 1069) = faceMask (⟨570, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0571 : supportIntersection (⟨571, by decide⟩ : Fin 1069) = faceMask (⟨571, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0572 : supportIntersection (⟨572, by decide⟩ : Fin 1069) = faceMask (⟨572, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0573 : supportIntersection (⟨573, by decide⟩ : Fin 1069) = faceMask (⟨573, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0574 : supportIntersection (⟨574, by decide⟩ : Fin 1069) = faceMask (⟨574, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0575 : supportIntersection (⟨575, by decide⟩ : Fin 1069) = faceMask (⟨575, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0576 : supportIntersection (⟨576, by decide⟩ : Fin 1069) = faceMask (⟨576, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0577 : supportIntersection (⟨577, by decide⟩ : Fin 1069) = faceMask (⟨577, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0578 : supportIntersection (⟨578, by decide⟩ : Fin 1069) = faceMask (⟨578, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0579 : supportIntersection (⟨579, by decide⟩ : Fin 1069) = faceMask (⟨579, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0580 : supportIntersection (⟨580, by decide⟩ : Fin 1069) = faceMask (⟨580, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0581 : supportIntersection (⟨581, by decide⟩ : Fin 1069) = faceMask (⟨581, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0582 : supportIntersection (⟨582, by decide⟩ : Fin 1069) = faceMask (⟨582, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0583 : supportIntersection (⟨583, by decide⟩ : Fin 1069) = faceMask (⟨583, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0584 : supportIntersection (⟨584, by decide⟩ : Fin 1069) = faceMask (⟨584, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0585 : supportIntersection (⟨585, by decide⟩ : Fin 1069) = faceMask (⟨585, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0586 : supportIntersection (⟨586, by decide⟩ : Fin 1069) = faceMask (⟨586, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0587 : supportIntersection (⟨587, by decide⟩ : Fin 1069) = faceMask (⟨587, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0588 : supportIntersection (⟨588, by decide⟩ : Fin 1069) = faceMask (⟨588, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0589 : supportIntersection (⟨589, by decide⟩ : Fin 1069) = faceMask (⟨589, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0590 : supportIntersection (⟨590, by decide⟩ : Fin 1069) = faceMask (⟨590, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0591 : supportIntersection (⟨591, by decide⟩ : Fin 1069) = faceMask (⟨591, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0592 : supportIntersection (⟨592, by decide⟩ : Fin 1069) = faceMask (⟨592, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0593 : supportIntersection (⟨593, by decide⟩ : Fin 1069) = faceMask (⟨593, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0594 : supportIntersection (⟨594, by decide⟩ : Fin 1069) = faceMask (⟨594, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0595 : supportIntersection (⟨595, by decide⟩ : Fin 1069) = faceMask (⟨595, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0596 : supportIntersection (⟨596, by decide⟩ : Fin 1069) = faceMask (⟨596, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0597 : supportIntersection (⟨597, by decide⟩ : Fin 1069) = faceMask (⟨597, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0598 : supportIntersection (⟨598, by decide⟩ : Fin 1069) = faceMask (⟨598, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0599 : supportIntersection (⟨599, by decide⟩ : Fin 1069) = faceMask (⟨599, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0600 : supportIntersection (⟨600, by decide⟩ : Fin 1069) = faceMask (⟨600, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0601 : supportIntersection (⟨601, by decide⟩ : Fin 1069) = faceMask (⟨601, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0602 : supportIntersection (⟨602, by decide⟩ : Fin 1069) = faceMask (⟨602, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0603 : supportIntersection (⟨603, by decide⟩ : Fin 1069) = faceMask (⟨603, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0604 : supportIntersection (⟨604, by decide⟩ : Fin 1069) = faceMask (⟨604, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0605 : supportIntersection (⟨605, by decide⟩ : Fin 1069) = faceMask (⟨605, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0606 : supportIntersection (⟨606, by decide⟩ : Fin 1069) = faceMask (⟨606, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0607 : supportIntersection (⟨607, by decide⟩ : Fin 1069) = faceMask (⟨607, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0608 : supportIntersection (⟨608, by decide⟩ : Fin 1069) = faceMask (⟨608, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0609 : supportIntersection (⟨609, by decide⟩ : Fin 1069) = faceMask (⟨609, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0610 : supportIntersection (⟨610, by decide⟩ : Fin 1069) = faceMask (⟨610, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0611 : supportIntersection (⟨611, by decide⟩ : Fin 1069) = faceMask (⟨611, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0612 : supportIntersection (⟨612, by decide⟩ : Fin 1069) = faceMask (⟨612, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0613 : supportIntersection (⟨613, by decide⟩ : Fin 1069) = faceMask (⟨613, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0614 : supportIntersection (⟨614, by decide⟩ : Fin 1069) = faceMask (⟨614, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0615 : supportIntersection (⟨615, by decide⟩ : Fin 1069) = faceMask (⟨615, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0616 : supportIntersection (⟨616, by decide⟩ : Fin 1069) = faceMask (⟨616, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0617 : supportIntersection (⟨617, by decide⟩ : Fin 1069) = faceMask (⟨617, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0618 : supportIntersection (⟨618, by decide⟩ : Fin 1069) = faceMask (⟨618, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0619 : supportIntersection (⟨619, by decide⟩ : Fin 1069) = faceMask (⟨619, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0620 : supportIntersection (⟨620, by decide⟩ : Fin 1069) = faceMask (⟨620, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0621 : supportIntersection (⟨621, by decide⟩ : Fin 1069) = faceMask (⟨621, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0622 : supportIntersection (⟨622, by decide⟩ : Fin 1069) = faceMask (⟨622, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0623 : supportIntersection (⟨623, by decide⟩ : Fin 1069) = faceMask (⟨623, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0624 : supportIntersection (⟨624, by decide⟩ : Fin 1069) = faceMask (⟨624, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0625 : supportIntersection (⟨625, by decide⟩ : Fin 1069) = faceMask (⟨625, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0626 : supportIntersection (⟨626, by decide⟩ : Fin 1069) = faceMask (⟨626, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0627 : supportIntersection (⟨627, by decide⟩ : Fin 1069) = faceMask (⟨627, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0628 : supportIntersection (⟨628, by decide⟩ : Fin 1069) = faceMask (⟨628, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0629 : supportIntersection (⟨629, by decide⟩ : Fin 1069) = faceMask (⟨629, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0630 : supportIntersection (⟨630, by decide⟩ : Fin 1069) = faceMask (⟨630, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0631 : supportIntersection (⟨631, by decide⟩ : Fin 1069) = faceMask (⟨631, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0632 : supportIntersection (⟨632, by decide⟩ : Fin 1069) = faceMask (⟨632, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0633 : supportIntersection (⟨633, by decide⟩ : Fin 1069) = faceMask (⟨633, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0634 : supportIntersection (⟨634, by decide⟩ : Fin 1069) = faceMask (⟨634, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0635 : supportIntersection (⟨635, by decide⟩ : Fin 1069) = faceMask (⟨635, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0636 : supportIntersection (⟨636, by decide⟩ : Fin 1069) = faceMask (⟨636, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0637 : supportIntersection (⟨637, by decide⟩ : Fin 1069) = faceMask (⟨637, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0638 : supportIntersection (⟨638, by decide⟩ : Fin 1069) = faceMask (⟨638, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0639 : supportIntersection (⟨639, by decide⟩ : Fin 1069) = faceMask (⟨639, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0640 : supportIntersection (⟨640, by decide⟩ : Fin 1069) = faceMask (⟨640, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0641 : supportIntersection (⟨641, by decide⟩ : Fin 1069) = faceMask (⟨641, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0642 : supportIntersection (⟨642, by decide⟩ : Fin 1069) = faceMask (⟨642, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0643 : supportIntersection (⟨643, by decide⟩ : Fin 1069) = faceMask (⟨643, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0644 : supportIntersection (⟨644, by decide⟩ : Fin 1069) = faceMask (⟨644, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0645 : supportIntersection (⟨645, by decide⟩ : Fin 1069) = faceMask (⟨645, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0646 : supportIntersection (⟨646, by decide⟩ : Fin 1069) = faceMask (⟨646, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0647 : supportIntersection (⟨647, by decide⟩ : Fin 1069) = faceMask (⟨647, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0648 : supportIntersection (⟨648, by decide⟩ : Fin 1069) = faceMask (⟨648, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0649 : supportIntersection (⟨649, by decide⟩ : Fin 1069) = faceMask (⟨649, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0650 : supportIntersection (⟨650, by decide⟩ : Fin 1069) = faceMask (⟨650, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0651 : supportIntersection (⟨651, by decide⟩ : Fin 1069) = faceMask (⟨651, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0652 : supportIntersection (⟨652, by decide⟩ : Fin 1069) = faceMask (⟨652, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0653 : supportIntersection (⟨653, by decide⟩ : Fin 1069) = faceMask (⟨653, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0654 : supportIntersection (⟨654, by decide⟩ : Fin 1069) = faceMask (⟨654, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0655 : supportIntersection (⟨655, by decide⟩ : Fin 1069) = faceMask (⟨655, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0656 : supportIntersection (⟨656, by decide⟩ : Fin 1069) = faceMask (⟨656, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0657 : supportIntersection (⟨657, by decide⟩ : Fin 1069) = faceMask (⟨657, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0658 : supportIntersection (⟨658, by decide⟩ : Fin 1069) = faceMask (⟨658, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0659 : supportIntersection (⟨659, by decide⟩ : Fin 1069) = faceMask (⟨659, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0660 : supportIntersection (⟨660, by decide⟩ : Fin 1069) = faceMask (⟨660, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0661 : supportIntersection (⟨661, by decide⟩ : Fin 1069) = faceMask (⟨661, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0662 : supportIntersection (⟨662, by decide⟩ : Fin 1069) = faceMask (⟨662, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0663 : supportIntersection (⟨663, by decide⟩ : Fin 1069) = faceMask (⟨663, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0664 : supportIntersection (⟨664, by decide⟩ : Fin 1069) = faceMask (⟨664, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0665 : supportIntersection (⟨665, by decide⟩ : Fin 1069) = faceMask (⟨665, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0666 : supportIntersection (⟨666, by decide⟩ : Fin 1069) = faceMask (⟨666, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0667 : supportIntersection (⟨667, by decide⟩ : Fin 1069) = faceMask (⟨667, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0668 : supportIntersection (⟨668, by decide⟩ : Fin 1069) = faceMask (⟨668, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0669 : supportIntersection (⟨669, by decide⟩ : Fin 1069) = faceMask (⟨669, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0670 : supportIntersection (⟨670, by decide⟩ : Fin 1069) = faceMask (⟨670, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0671 : supportIntersection (⟨671, by decide⟩ : Fin 1069) = faceMask (⟨671, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0672 : supportIntersection (⟨672, by decide⟩ : Fin 1069) = faceMask (⟨672, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0673 : supportIntersection (⟨673, by decide⟩ : Fin 1069) = faceMask (⟨673, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0674 : supportIntersection (⟨674, by decide⟩ : Fin 1069) = faceMask (⟨674, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0675 : supportIntersection (⟨675, by decide⟩ : Fin 1069) = faceMask (⟨675, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0676 : supportIntersection (⟨676, by decide⟩ : Fin 1069) = faceMask (⟨676, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0677 : supportIntersection (⟨677, by decide⟩ : Fin 1069) = faceMask (⟨677, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0678 : supportIntersection (⟨678, by decide⟩ : Fin 1069) = faceMask (⟨678, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0679 : supportIntersection (⟨679, by decide⟩ : Fin 1069) = faceMask (⟨679, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0680 : supportIntersection (⟨680, by decide⟩ : Fin 1069) = faceMask (⟨680, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0681 : supportIntersection (⟨681, by decide⟩ : Fin 1069) = faceMask (⟨681, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0682 : supportIntersection (⟨682, by decide⟩ : Fin 1069) = faceMask (⟨682, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0683 : supportIntersection (⟨683, by decide⟩ : Fin 1069) = faceMask (⟨683, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0684 : supportIntersection (⟨684, by decide⟩ : Fin 1069) = faceMask (⟨684, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0685 : supportIntersection (⟨685, by decide⟩ : Fin 1069) = faceMask (⟨685, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0686 : supportIntersection (⟨686, by decide⟩ : Fin 1069) = faceMask (⟨686, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0687 : supportIntersection (⟨687, by decide⟩ : Fin 1069) = faceMask (⟨687, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0688 : supportIntersection (⟨688, by decide⟩ : Fin 1069) = faceMask (⟨688, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0689 : supportIntersection (⟨689, by decide⟩ : Fin 1069) = faceMask (⟨689, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0690 : supportIntersection (⟨690, by decide⟩ : Fin 1069) = faceMask (⟨690, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0691 : supportIntersection (⟨691, by decide⟩ : Fin 1069) = faceMask (⟨691, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0692 : supportIntersection (⟨692, by decide⟩ : Fin 1069) = faceMask (⟨692, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0693 : supportIntersection (⟨693, by decide⟩ : Fin 1069) = faceMask (⟨693, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0694 : supportIntersection (⟨694, by decide⟩ : Fin 1069) = faceMask (⟨694, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0695 : supportIntersection (⟨695, by decide⟩ : Fin 1069) = faceMask (⟨695, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0696 : supportIntersection (⟨696, by decide⟩ : Fin 1069) = faceMask (⟨696, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0697 : supportIntersection (⟨697, by decide⟩ : Fin 1069) = faceMask (⟨697, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0698 : supportIntersection (⟨698, by decide⟩ : Fin 1069) = faceMask (⟨698, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0699 : supportIntersection (⟨699, by decide⟩ : Fin 1069) = faceMask (⟨699, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0700 : supportIntersection (⟨700, by decide⟩ : Fin 1069) = faceMask (⟨700, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0701 : supportIntersection (⟨701, by decide⟩ : Fin 1069) = faceMask (⟨701, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0702 : supportIntersection (⟨702, by decide⟩ : Fin 1069) = faceMask (⟨702, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0703 : supportIntersection (⟨703, by decide⟩ : Fin 1069) = faceMask (⟨703, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0704 : supportIntersection (⟨704, by decide⟩ : Fin 1069) = faceMask (⟨704, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0705 : supportIntersection (⟨705, by decide⟩ : Fin 1069) = faceMask (⟨705, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0706 : supportIntersection (⟨706, by decide⟩ : Fin 1069) = faceMask (⟨706, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0707 : supportIntersection (⟨707, by decide⟩ : Fin 1069) = faceMask (⟨707, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0708 : supportIntersection (⟨708, by decide⟩ : Fin 1069) = faceMask (⟨708, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0709 : supportIntersection (⟨709, by decide⟩ : Fin 1069) = faceMask (⟨709, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0710 : supportIntersection (⟨710, by decide⟩ : Fin 1069) = faceMask (⟨710, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0711 : supportIntersection (⟨711, by decide⟩ : Fin 1069) = faceMask (⟨711, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0712 : supportIntersection (⟨712, by decide⟩ : Fin 1069) = faceMask (⟨712, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0713 : supportIntersection (⟨713, by decide⟩ : Fin 1069) = faceMask (⟨713, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0714 : supportIntersection (⟨714, by decide⟩ : Fin 1069) = faceMask (⟨714, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0715 : supportIntersection (⟨715, by decide⟩ : Fin 1069) = faceMask (⟨715, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0716 : supportIntersection (⟨716, by decide⟩ : Fin 1069) = faceMask (⟨716, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0717 : supportIntersection (⟨717, by decide⟩ : Fin 1069) = faceMask (⟨717, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0718 : supportIntersection (⟨718, by decide⟩ : Fin 1069) = faceMask (⟨718, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0719 : supportIntersection (⟨719, by decide⟩ : Fin 1069) = faceMask (⟨719, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0720 : supportIntersection (⟨720, by decide⟩ : Fin 1069) = faceMask (⟨720, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0721 : supportIntersection (⟨721, by decide⟩ : Fin 1069) = faceMask (⟨721, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0722 : supportIntersection (⟨722, by decide⟩ : Fin 1069) = faceMask (⟨722, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0723 : supportIntersection (⟨723, by decide⟩ : Fin 1069) = faceMask (⟨723, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0724 : supportIntersection (⟨724, by decide⟩ : Fin 1069) = faceMask (⟨724, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0725 : supportIntersection (⟨725, by decide⟩ : Fin 1069) = faceMask (⟨725, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0726 : supportIntersection (⟨726, by decide⟩ : Fin 1069) = faceMask (⟨726, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0727 : supportIntersection (⟨727, by decide⟩ : Fin 1069) = faceMask (⟨727, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0728 : supportIntersection (⟨728, by decide⟩ : Fin 1069) = faceMask (⟨728, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0729 : supportIntersection (⟨729, by decide⟩ : Fin 1069) = faceMask (⟨729, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0730 : supportIntersection (⟨730, by decide⟩ : Fin 1069) = faceMask (⟨730, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0731 : supportIntersection (⟨731, by decide⟩ : Fin 1069) = faceMask (⟨731, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0732 : supportIntersection (⟨732, by decide⟩ : Fin 1069) = faceMask (⟨732, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0733 : supportIntersection (⟨733, by decide⟩ : Fin 1069) = faceMask (⟨733, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0734 : supportIntersection (⟨734, by decide⟩ : Fin 1069) = faceMask (⟨734, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0735 : supportIntersection (⟨735, by decide⟩ : Fin 1069) = faceMask (⟨735, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0736 : supportIntersection (⟨736, by decide⟩ : Fin 1069) = faceMask (⟨736, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0737 : supportIntersection (⟨737, by decide⟩ : Fin 1069) = faceMask (⟨737, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0738 : supportIntersection (⟨738, by decide⟩ : Fin 1069) = faceMask (⟨738, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0739 : supportIntersection (⟨739, by decide⟩ : Fin 1069) = faceMask (⟨739, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0740 : supportIntersection (⟨740, by decide⟩ : Fin 1069) = faceMask (⟨740, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0741 : supportIntersection (⟨741, by decide⟩ : Fin 1069) = faceMask (⟨741, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0742 : supportIntersection (⟨742, by decide⟩ : Fin 1069) = faceMask (⟨742, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0743 : supportIntersection (⟨743, by decide⟩ : Fin 1069) = faceMask (⟨743, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0744 : supportIntersection (⟨744, by decide⟩ : Fin 1069) = faceMask (⟨744, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0745 : supportIntersection (⟨745, by decide⟩ : Fin 1069) = faceMask (⟨745, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0746 : supportIntersection (⟨746, by decide⟩ : Fin 1069) = faceMask (⟨746, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0747 : supportIntersection (⟨747, by decide⟩ : Fin 1069) = faceMask (⟨747, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0748 : supportIntersection (⟨748, by decide⟩ : Fin 1069) = faceMask (⟨748, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0749 : supportIntersection (⟨749, by decide⟩ : Fin 1069) = faceMask (⟨749, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0750 : supportIntersection (⟨750, by decide⟩ : Fin 1069) = faceMask (⟨750, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0751 : supportIntersection (⟨751, by decide⟩ : Fin 1069) = faceMask (⟨751, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0752 : supportIntersection (⟨752, by decide⟩ : Fin 1069) = faceMask (⟨752, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0753 : supportIntersection (⟨753, by decide⟩ : Fin 1069) = faceMask (⟨753, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0754 : supportIntersection (⟨754, by decide⟩ : Fin 1069) = faceMask (⟨754, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0755 : supportIntersection (⟨755, by decide⟩ : Fin 1069) = faceMask (⟨755, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0756 : supportIntersection (⟨756, by decide⟩ : Fin 1069) = faceMask (⟨756, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0757 : supportIntersection (⟨757, by decide⟩ : Fin 1069) = faceMask (⟨757, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0758 : supportIntersection (⟨758, by decide⟩ : Fin 1069) = faceMask (⟨758, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0759 : supportIntersection (⟨759, by decide⟩ : Fin 1069) = faceMask (⟨759, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0760 : supportIntersection (⟨760, by decide⟩ : Fin 1069) = faceMask (⟨760, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0761 : supportIntersection (⟨761, by decide⟩ : Fin 1069) = faceMask (⟨761, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0762 : supportIntersection (⟨762, by decide⟩ : Fin 1069) = faceMask (⟨762, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0763 : supportIntersection (⟨763, by decide⟩ : Fin 1069) = faceMask (⟨763, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0764 : supportIntersection (⟨764, by decide⟩ : Fin 1069) = faceMask (⟨764, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0765 : supportIntersection (⟨765, by decide⟩ : Fin 1069) = faceMask (⟨765, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0766 : supportIntersection (⟨766, by decide⟩ : Fin 1069) = faceMask (⟨766, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0767 : supportIntersection (⟨767, by decide⟩ : Fin 1069) = faceMask (⟨767, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0768 : supportIntersection (⟨768, by decide⟩ : Fin 1069) = faceMask (⟨768, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0769 : supportIntersection (⟨769, by decide⟩ : Fin 1069) = faceMask (⟨769, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0770 : supportIntersection (⟨770, by decide⟩ : Fin 1069) = faceMask (⟨770, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0771 : supportIntersection (⟨771, by decide⟩ : Fin 1069) = faceMask (⟨771, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0772 : supportIntersection (⟨772, by decide⟩ : Fin 1069) = faceMask (⟨772, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0773 : supportIntersection (⟨773, by decide⟩ : Fin 1069) = faceMask (⟨773, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0774 : supportIntersection (⟨774, by decide⟩ : Fin 1069) = faceMask (⟨774, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0775 : supportIntersection (⟨775, by decide⟩ : Fin 1069) = faceMask (⟨775, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0776 : supportIntersection (⟨776, by decide⟩ : Fin 1069) = faceMask (⟨776, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0777 : supportIntersection (⟨777, by decide⟩ : Fin 1069) = faceMask (⟨777, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0778 : supportIntersection (⟨778, by decide⟩ : Fin 1069) = faceMask (⟨778, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0779 : supportIntersection (⟨779, by decide⟩ : Fin 1069) = faceMask (⟨779, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0780 : supportIntersection (⟨780, by decide⟩ : Fin 1069) = faceMask (⟨780, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0781 : supportIntersection (⟨781, by decide⟩ : Fin 1069) = faceMask (⟨781, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0782 : supportIntersection (⟨782, by decide⟩ : Fin 1069) = faceMask (⟨782, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0783 : supportIntersection (⟨783, by decide⟩ : Fin 1069) = faceMask (⟨783, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0784 : supportIntersection (⟨784, by decide⟩ : Fin 1069) = faceMask (⟨784, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0785 : supportIntersection (⟨785, by decide⟩ : Fin 1069) = faceMask (⟨785, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0786 : supportIntersection (⟨786, by decide⟩ : Fin 1069) = faceMask (⟨786, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0787 : supportIntersection (⟨787, by decide⟩ : Fin 1069) = faceMask (⟨787, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0788 : supportIntersection (⟨788, by decide⟩ : Fin 1069) = faceMask (⟨788, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0789 : supportIntersection (⟨789, by decide⟩ : Fin 1069) = faceMask (⟨789, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0790 : supportIntersection (⟨790, by decide⟩ : Fin 1069) = faceMask (⟨790, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0791 : supportIntersection (⟨791, by decide⟩ : Fin 1069) = faceMask (⟨791, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0792 : supportIntersection (⟨792, by decide⟩ : Fin 1069) = faceMask (⟨792, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0793 : supportIntersection (⟨793, by decide⟩ : Fin 1069) = faceMask (⟨793, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0794 : supportIntersection (⟨794, by decide⟩ : Fin 1069) = faceMask (⟨794, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0795 : supportIntersection (⟨795, by decide⟩ : Fin 1069) = faceMask (⟨795, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0796 : supportIntersection (⟨796, by decide⟩ : Fin 1069) = faceMask (⟨796, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0797 : supportIntersection (⟨797, by decide⟩ : Fin 1069) = faceMask (⟨797, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0798 : supportIntersection (⟨798, by decide⟩ : Fin 1069) = faceMask (⟨798, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0799 : supportIntersection (⟨799, by decide⟩ : Fin 1069) = faceMask (⟨799, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0800 : supportIntersection (⟨800, by decide⟩ : Fin 1069) = faceMask (⟨800, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0801 : supportIntersection (⟨801, by decide⟩ : Fin 1069) = faceMask (⟨801, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0802 : supportIntersection (⟨802, by decide⟩ : Fin 1069) = faceMask (⟨802, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0803 : supportIntersection (⟨803, by decide⟩ : Fin 1069) = faceMask (⟨803, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0804 : supportIntersection (⟨804, by decide⟩ : Fin 1069) = faceMask (⟨804, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0805 : supportIntersection (⟨805, by decide⟩ : Fin 1069) = faceMask (⟨805, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0806 : supportIntersection (⟨806, by decide⟩ : Fin 1069) = faceMask (⟨806, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0807 : supportIntersection (⟨807, by decide⟩ : Fin 1069) = faceMask (⟨807, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0808 : supportIntersection (⟨808, by decide⟩ : Fin 1069) = faceMask (⟨808, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0809 : supportIntersection (⟨809, by decide⟩ : Fin 1069) = faceMask (⟨809, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0810 : supportIntersection (⟨810, by decide⟩ : Fin 1069) = faceMask (⟨810, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0811 : supportIntersection (⟨811, by decide⟩ : Fin 1069) = faceMask (⟨811, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0812 : supportIntersection (⟨812, by decide⟩ : Fin 1069) = faceMask (⟨812, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0813 : supportIntersection (⟨813, by decide⟩ : Fin 1069) = faceMask (⟨813, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0814 : supportIntersection (⟨814, by decide⟩ : Fin 1069) = faceMask (⟨814, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0815 : supportIntersection (⟨815, by decide⟩ : Fin 1069) = faceMask (⟨815, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0816 : supportIntersection (⟨816, by decide⟩ : Fin 1069) = faceMask (⟨816, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0817 : supportIntersection (⟨817, by decide⟩ : Fin 1069) = faceMask (⟨817, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0818 : supportIntersection (⟨818, by decide⟩ : Fin 1069) = faceMask (⟨818, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0819 : supportIntersection (⟨819, by decide⟩ : Fin 1069) = faceMask (⟨819, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0820 : supportIntersection (⟨820, by decide⟩ : Fin 1069) = faceMask (⟨820, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0821 : supportIntersection (⟨821, by decide⟩ : Fin 1069) = faceMask (⟨821, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0822 : supportIntersection (⟨822, by decide⟩ : Fin 1069) = faceMask (⟨822, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0823 : supportIntersection (⟨823, by decide⟩ : Fin 1069) = faceMask (⟨823, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0824 : supportIntersection (⟨824, by decide⟩ : Fin 1069) = faceMask (⟨824, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0825 : supportIntersection (⟨825, by decide⟩ : Fin 1069) = faceMask (⟨825, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0826 : supportIntersection (⟨826, by decide⟩ : Fin 1069) = faceMask (⟨826, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0827 : supportIntersection (⟨827, by decide⟩ : Fin 1069) = faceMask (⟨827, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0828 : supportIntersection (⟨828, by decide⟩ : Fin 1069) = faceMask (⟨828, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0829 : supportIntersection (⟨829, by decide⟩ : Fin 1069) = faceMask (⟨829, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0830 : supportIntersection (⟨830, by decide⟩ : Fin 1069) = faceMask (⟨830, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0831 : supportIntersection (⟨831, by decide⟩ : Fin 1069) = faceMask (⟨831, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0832 : supportIntersection (⟨832, by decide⟩ : Fin 1069) = faceMask (⟨832, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0833 : supportIntersection (⟨833, by decide⟩ : Fin 1069) = faceMask (⟨833, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0834 : supportIntersection (⟨834, by decide⟩ : Fin 1069) = faceMask (⟨834, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0835 : supportIntersection (⟨835, by decide⟩ : Fin 1069) = faceMask (⟨835, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0836 : supportIntersection (⟨836, by decide⟩ : Fin 1069) = faceMask (⟨836, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0837 : supportIntersection (⟨837, by decide⟩ : Fin 1069) = faceMask (⟨837, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0838 : supportIntersection (⟨838, by decide⟩ : Fin 1069) = faceMask (⟨838, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0839 : supportIntersection (⟨839, by decide⟩ : Fin 1069) = faceMask (⟨839, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0840 : supportIntersection (⟨840, by decide⟩ : Fin 1069) = faceMask (⟨840, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0841 : supportIntersection (⟨841, by decide⟩ : Fin 1069) = faceMask (⟨841, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0842 : supportIntersection (⟨842, by decide⟩ : Fin 1069) = faceMask (⟨842, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0843 : supportIntersection (⟨843, by decide⟩ : Fin 1069) = faceMask (⟨843, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0844 : supportIntersection (⟨844, by decide⟩ : Fin 1069) = faceMask (⟨844, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0845 : supportIntersection (⟨845, by decide⟩ : Fin 1069) = faceMask (⟨845, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0846 : supportIntersection (⟨846, by decide⟩ : Fin 1069) = faceMask (⟨846, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0847 : supportIntersection (⟨847, by decide⟩ : Fin 1069) = faceMask (⟨847, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0848 : supportIntersection (⟨848, by decide⟩ : Fin 1069) = faceMask (⟨848, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0849 : supportIntersection (⟨849, by decide⟩ : Fin 1069) = faceMask (⟨849, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0850 : supportIntersection (⟨850, by decide⟩ : Fin 1069) = faceMask (⟨850, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0851 : supportIntersection (⟨851, by decide⟩ : Fin 1069) = faceMask (⟨851, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0852 : supportIntersection (⟨852, by decide⟩ : Fin 1069) = faceMask (⟨852, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0853 : supportIntersection (⟨853, by decide⟩ : Fin 1069) = faceMask (⟨853, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0854 : supportIntersection (⟨854, by decide⟩ : Fin 1069) = faceMask (⟨854, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0855 : supportIntersection (⟨855, by decide⟩ : Fin 1069) = faceMask (⟨855, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0856 : supportIntersection (⟨856, by decide⟩ : Fin 1069) = faceMask (⟨856, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0857 : supportIntersection (⟨857, by decide⟩ : Fin 1069) = faceMask (⟨857, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0858 : supportIntersection (⟨858, by decide⟩ : Fin 1069) = faceMask (⟨858, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0859 : supportIntersection (⟨859, by decide⟩ : Fin 1069) = faceMask (⟨859, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0860 : supportIntersection (⟨860, by decide⟩ : Fin 1069) = faceMask (⟨860, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0861 : supportIntersection (⟨861, by decide⟩ : Fin 1069) = faceMask (⟨861, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0862 : supportIntersection (⟨862, by decide⟩ : Fin 1069) = faceMask (⟨862, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0863 : supportIntersection (⟨863, by decide⟩ : Fin 1069) = faceMask (⟨863, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0864 : supportIntersection (⟨864, by decide⟩ : Fin 1069) = faceMask (⟨864, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0865 : supportIntersection (⟨865, by decide⟩ : Fin 1069) = faceMask (⟨865, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0866 : supportIntersection (⟨866, by decide⟩ : Fin 1069) = faceMask (⟨866, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0867 : supportIntersection (⟨867, by decide⟩ : Fin 1069) = faceMask (⟨867, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0868 : supportIntersection (⟨868, by decide⟩ : Fin 1069) = faceMask (⟨868, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0869 : supportIntersection (⟨869, by decide⟩ : Fin 1069) = faceMask (⟨869, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0870 : supportIntersection (⟨870, by decide⟩ : Fin 1069) = faceMask (⟨870, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0871 : supportIntersection (⟨871, by decide⟩ : Fin 1069) = faceMask (⟨871, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0872 : supportIntersection (⟨872, by decide⟩ : Fin 1069) = faceMask (⟨872, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0873 : supportIntersection (⟨873, by decide⟩ : Fin 1069) = faceMask (⟨873, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0874 : supportIntersection (⟨874, by decide⟩ : Fin 1069) = faceMask (⟨874, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0875 : supportIntersection (⟨875, by decide⟩ : Fin 1069) = faceMask (⟨875, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0876 : supportIntersection (⟨876, by decide⟩ : Fin 1069) = faceMask (⟨876, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0877 : supportIntersection (⟨877, by decide⟩ : Fin 1069) = faceMask (⟨877, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0878 : supportIntersection (⟨878, by decide⟩ : Fin 1069) = faceMask (⟨878, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0879 : supportIntersection (⟨879, by decide⟩ : Fin 1069) = faceMask (⟨879, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0880 : supportIntersection (⟨880, by decide⟩ : Fin 1069) = faceMask (⟨880, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0881 : supportIntersection (⟨881, by decide⟩ : Fin 1069) = faceMask (⟨881, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0882 : supportIntersection (⟨882, by decide⟩ : Fin 1069) = faceMask (⟨882, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0883 : supportIntersection (⟨883, by decide⟩ : Fin 1069) = faceMask (⟨883, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0884 : supportIntersection (⟨884, by decide⟩ : Fin 1069) = faceMask (⟨884, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0885 : supportIntersection (⟨885, by decide⟩ : Fin 1069) = faceMask (⟨885, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0886 : supportIntersection (⟨886, by decide⟩ : Fin 1069) = faceMask (⟨886, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0887 : supportIntersection (⟨887, by decide⟩ : Fin 1069) = faceMask (⟨887, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0888 : supportIntersection (⟨888, by decide⟩ : Fin 1069) = faceMask (⟨888, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0889 : supportIntersection (⟨889, by decide⟩ : Fin 1069) = faceMask (⟨889, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0890 : supportIntersection (⟨890, by decide⟩ : Fin 1069) = faceMask (⟨890, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0891 : supportIntersection (⟨891, by decide⟩ : Fin 1069) = faceMask (⟨891, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0892 : supportIntersection (⟨892, by decide⟩ : Fin 1069) = faceMask (⟨892, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0893 : supportIntersection (⟨893, by decide⟩ : Fin 1069) = faceMask (⟨893, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0894 : supportIntersection (⟨894, by decide⟩ : Fin 1069) = faceMask (⟨894, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0895 : supportIntersection (⟨895, by decide⟩ : Fin 1069) = faceMask (⟨895, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0896 : supportIntersection (⟨896, by decide⟩ : Fin 1069) = faceMask (⟨896, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0897 : supportIntersection (⟨897, by decide⟩ : Fin 1069) = faceMask (⟨897, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0898 : supportIntersection (⟨898, by decide⟩ : Fin 1069) = faceMask (⟨898, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0899 : supportIntersection (⟨899, by decide⟩ : Fin 1069) = faceMask (⟨899, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0900 : supportIntersection (⟨900, by decide⟩ : Fin 1069) = faceMask (⟨900, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0901 : supportIntersection (⟨901, by decide⟩ : Fin 1069) = faceMask (⟨901, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0902 : supportIntersection (⟨902, by decide⟩ : Fin 1069) = faceMask (⟨902, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0903 : supportIntersection (⟨903, by decide⟩ : Fin 1069) = faceMask (⟨903, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0904 : supportIntersection (⟨904, by decide⟩ : Fin 1069) = faceMask (⟨904, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0905 : supportIntersection (⟨905, by decide⟩ : Fin 1069) = faceMask (⟨905, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0906 : supportIntersection (⟨906, by decide⟩ : Fin 1069) = faceMask (⟨906, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0907 : supportIntersection (⟨907, by decide⟩ : Fin 1069) = faceMask (⟨907, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0908 : supportIntersection (⟨908, by decide⟩ : Fin 1069) = faceMask (⟨908, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0909 : supportIntersection (⟨909, by decide⟩ : Fin 1069) = faceMask (⟨909, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0910 : supportIntersection (⟨910, by decide⟩ : Fin 1069) = faceMask (⟨910, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0911 : supportIntersection (⟨911, by decide⟩ : Fin 1069) = faceMask (⟨911, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0912 : supportIntersection (⟨912, by decide⟩ : Fin 1069) = faceMask (⟨912, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0913 : supportIntersection (⟨913, by decide⟩ : Fin 1069) = faceMask (⟨913, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0914 : supportIntersection (⟨914, by decide⟩ : Fin 1069) = faceMask (⟨914, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0915 : supportIntersection (⟨915, by decide⟩ : Fin 1069) = faceMask (⟨915, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0916 : supportIntersection (⟨916, by decide⟩ : Fin 1069) = faceMask (⟨916, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0917 : supportIntersection (⟨917, by decide⟩ : Fin 1069) = faceMask (⟨917, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0918 : supportIntersection (⟨918, by decide⟩ : Fin 1069) = faceMask (⟨918, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0919 : supportIntersection (⟨919, by decide⟩ : Fin 1069) = faceMask (⟨919, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0920 : supportIntersection (⟨920, by decide⟩ : Fin 1069) = faceMask (⟨920, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0921 : supportIntersection (⟨921, by decide⟩ : Fin 1069) = faceMask (⟨921, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0922 : supportIntersection (⟨922, by decide⟩ : Fin 1069) = faceMask (⟨922, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0923 : supportIntersection (⟨923, by decide⟩ : Fin 1069) = faceMask (⟨923, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0924 : supportIntersection (⟨924, by decide⟩ : Fin 1069) = faceMask (⟨924, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0925 : supportIntersection (⟨925, by decide⟩ : Fin 1069) = faceMask (⟨925, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0926 : supportIntersection (⟨926, by decide⟩ : Fin 1069) = faceMask (⟨926, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0927 : supportIntersection (⟨927, by decide⟩ : Fin 1069) = faceMask (⟨927, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0928 : supportIntersection (⟨928, by decide⟩ : Fin 1069) = faceMask (⟨928, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0929 : supportIntersection (⟨929, by decide⟩ : Fin 1069) = faceMask (⟨929, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0930 : supportIntersection (⟨930, by decide⟩ : Fin 1069) = faceMask (⟨930, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0931 : supportIntersection (⟨931, by decide⟩ : Fin 1069) = faceMask (⟨931, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0932 : supportIntersection (⟨932, by decide⟩ : Fin 1069) = faceMask (⟨932, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0933 : supportIntersection (⟨933, by decide⟩ : Fin 1069) = faceMask (⟨933, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0934 : supportIntersection (⟨934, by decide⟩ : Fin 1069) = faceMask (⟨934, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0935 : supportIntersection (⟨935, by decide⟩ : Fin 1069) = faceMask (⟨935, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0936 : supportIntersection (⟨936, by decide⟩ : Fin 1069) = faceMask (⟨936, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0937 : supportIntersection (⟨937, by decide⟩ : Fin 1069) = faceMask (⟨937, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0938 : supportIntersection (⟨938, by decide⟩ : Fin 1069) = faceMask (⟨938, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0939 : supportIntersection (⟨939, by decide⟩ : Fin 1069) = faceMask (⟨939, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0940 : supportIntersection (⟨940, by decide⟩ : Fin 1069) = faceMask (⟨940, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0941 : supportIntersection (⟨941, by decide⟩ : Fin 1069) = faceMask (⟨941, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0942 : supportIntersection (⟨942, by decide⟩ : Fin 1069) = faceMask (⟨942, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0943 : supportIntersection (⟨943, by decide⟩ : Fin 1069) = faceMask (⟨943, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0944 : supportIntersection (⟨944, by decide⟩ : Fin 1069) = faceMask (⟨944, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0945 : supportIntersection (⟨945, by decide⟩ : Fin 1069) = faceMask (⟨945, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0946 : supportIntersection (⟨946, by decide⟩ : Fin 1069) = faceMask (⟨946, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0947 : supportIntersection (⟨947, by decide⟩ : Fin 1069) = faceMask (⟨947, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0948 : supportIntersection (⟨948, by decide⟩ : Fin 1069) = faceMask (⟨948, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0949 : supportIntersection (⟨949, by decide⟩ : Fin 1069) = faceMask (⟨949, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0950 : supportIntersection (⟨950, by decide⟩ : Fin 1069) = faceMask (⟨950, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0951 : supportIntersection (⟨951, by decide⟩ : Fin 1069) = faceMask (⟨951, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0952 : supportIntersection (⟨952, by decide⟩ : Fin 1069) = faceMask (⟨952, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0953 : supportIntersection (⟨953, by decide⟩ : Fin 1069) = faceMask (⟨953, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0954 : supportIntersection (⟨954, by decide⟩ : Fin 1069) = faceMask (⟨954, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0955 : supportIntersection (⟨955, by decide⟩ : Fin 1069) = faceMask (⟨955, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0956 : supportIntersection (⟨956, by decide⟩ : Fin 1069) = faceMask (⟨956, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0957 : supportIntersection (⟨957, by decide⟩ : Fin 1069) = faceMask (⟨957, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0958 : supportIntersection (⟨958, by decide⟩ : Fin 1069) = faceMask (⟨958, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0959 : supportIntersection (⟨959, by decide⟩ : Fin 1069) = faceMask (⟨959, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0960 : supportIntersection (⟨960, by decide⟩ : Fin 1069) = faceMask (⟨960, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0961 : supportIntersection (⟨961, by decide⟩ : Fin 1069) = faceMask (⟨961, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0962 : supportIntersection (⟨962, by decide⟩ : Fin 1069) = faceMask (⟨962, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0963 : supportIntersection (⟨963, by decide⟩ : Fin 1069) = faceMask (⟨963, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0964 : supportIntersection (⟨964, by decide⟩ : Fin 1069) = faceMask (⟨964, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0965 : supportIntersection (⟨965, by decide⟩ : Fin 1069) = faceMask (⟨965, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0966 : supportIntersection (⟨966, by decide⟩ : Fin 1069) = faceMask (⟨966, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0967 : supportIntersection (⟨967, by decide⟩ : Fin 1069) = faceMask (⟨967, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0968 : supportIntersection (⟨968, by decide⟩ : Fin 1069) = faceMask (⟨968, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0969 : supportIntersection (⟨969, by decide⟩ : Fin 1069) = faceMask (⟨969, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0970 : supportIntersection (⟨970, by decide⟩ : Fin 1069) = faceMask (⟨970, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0971 : supportIntersection (⟨971, by decide⟩ : Fin 1069) = faceMask (⟨971, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0972 : supportIntersection (⟨972, by decide⟩ : Fin 1069) = faceMask (⟨972, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0973 : supportIntersection (⟨973, by decide⟩ : Fin 1069) = faceMask (⟨973, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0974 : supportIntersection (⟨974, by decide⟩ : Fin 1069) = faceMask (⟨974, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0975 : supportIntersection (⟨975, by decide⟩ : Fin 1069) = faceMask (⟨975, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0976 : supportIntersection (⟨976, by decide⟩ : Fin 1069) = faceMask (⟨976, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0977 : supportIntersection (⟨977, by decide⟩ : Fin 1069) = faceMask (⟨977, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0978 : supportIntersection (⟨978, by decide⟩ : Fin 1069) = faceMask (⟨978, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0979 : supportIntersection (⟨979, by decide⟩ : Fin 1069) = faceMask (⟨979, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0980 : supportIntersection (⟨980, by decide⟩ : Fin 1069) = faceMask (⟨980, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0981 : supportIntersection (⟨981, by decide⟩ : Fin 1069) = faceMask (⟨981, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0982 : supportIntersection (⟨982, by decide⟩ : Fin 1069) = faceMask (⟨982, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0983 : supportIntersection (⟨983, by decide⟩ : Fin 1069) = faceMask (⟨983, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0984 : supportIntersection (⟨984, by decide⟩ : Fin 1069) = faceMask (⟨984, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0985 : supportIntersection (⟨985, by decide⟩ : Fin 1069) = faceMask (⟨985, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0986 : supportIntersection (⟨986, by decide⟩ : Fin 1069) = faceMask (⟨986, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0987 : supportIntersection (⟨987, by decide⟩ : Fin 1069) = faceMask (⟨987, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0988 : supportIntersection (⟨988, by decide⟩ : Fin 1069) = faceMask (⟨988, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0989 : supportIntersection (⟨989, by decide⟩ : Fin 1069) = faceMask (⟨989, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0990 : supportIntersection (⟨990, by decide⟩ : Fin 1069) = faceMask (⟨990, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0991 : supportIntersection (⟨991, by decide⟩ : Fin 1069) = faceMask (⟨991, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0992 : supportIntersection (⟨992, by decide⟩ : Fin 1069) = faceMask (⟨992, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0993 : supportIntersection (⟨993, by decide⟩ : Fin 1069) = faceMask (⟨993, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0994 : supportIntersection (⟨994, by decide⟩ : Fin 1069) = faceMask (⟨994, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0995 : supportIntersection (⟨995, by decide⟩ : Fin 1069) = faceMask (⟨995, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0996 : supportIntersection (⟨996, by decide⟩ : Fin 1069) = faceMask (⟨996, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0997 : supportIntersection (⟨997, by decide⟩ : Fin 1069) = faceMask (⟨997, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0998 : supportIntersection (⟨998, by decide⟩ : Fin 1069) = faceMask (⟨998, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support0999 : supportIntersection (⟨999, by decide⟩ : Fin 1069) = faceMask (⟨999, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1000 : supportIntersection (⟨1000, by decide⟩ : Fin 1069) = faceMask (⟨1000, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1001 : supportIntersection (⟨1001, by decide⟩ : Fin 1069) = faceMask (⟨1001, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1002 : supportIntersection (⟨1002, by decide⟩ : Fin 1069) = faceMask (⟨1002, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1003 : supportIntersection (⟨1003, by decide⟩ : Fin 1069) = faceMask (⟨1003, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1004 : supportIntersection (⟨1004, by decide⟩ : Fin 1069) = faceMask (⟨1004, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1005 : supportIntersection (⟨1005, by decide⟩ : Fin 1069) = faceMask (⟨1005, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1006 : supportIntersection (⟨1006, by decide⟩ : Fin 1069) = faceMask (⟨1006, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1007 : supportIntersection (⟨1007, by decide⟩ : Fin 1069) = faceMask (⟨1007, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1008 : supportIntersection (⟨1008, by decide⟩ : Fin 1069) = faceMask (⟨1008, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1009 : supportIntersection (⟨1009, by decide⟩ : Fin 1069) = faceMask (⟨1009, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1010 : supportIntersection (⟨1010, by decide⟩ : Fin 1069) = faceMask (⟨1010, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1011 : supportIntersection (⟨1011, by decide⟩ : Fin 1069) = faceMask (⟨1011, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1012 : supportIntersection (⟨1012, by decide⟩ : Fin 1069) = faceMask (⟨1012, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1013 : supportIntersection (⟨1013, by decide⟩ : Fin 1069) = faceMask (⟨1013, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1014 : supportIntersection (⟨1014, by decide⟩ : Fin 1069) = faceMask (⟨1014, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1015 : supportIntersection (⟨1015, by decide⟩ : Fin 1069) = faceMask (⟨1015, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1016 : supportIntersection (⟨1016, by decide⟩ : Fin 1069) = faceMask (⟨1016, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1017 : supportIntersection (⟨1017, by decide⟩ : Fin 1069) = faceMask (⟨1017, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1018 : supportIntersection (⟨1018, by decide⟩ : Fin 1069) = faceMask (⟨1018, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1019 : supportIntersection (⟨1019, by decide⟩ : Fin 1069) = faceMask (⟨1019, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1020 : supportIntersection (⟨1020, by decide⟩ : Fin 1069) = faceMask (⟨1020, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1021 : supportIntersection (⟨1021, by decide⟩ : Fin 1069) = faceMask (⟨1021, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1022 : supportIntersection (⟨1022, by decide⟩ : Fin 1069) = faceMask (⟨1022, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1023 : supportIntersection (⟨1023, by decide⟩ : Fin 1069) = faceMask (⟨1023, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1024 : supportIntersection (⟨1024, by decide⟩ : Fin 1069) = faceMask (⟨1024, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1025 : supportIntersection (⟨1025, by decide⟩ : Fin 1069) = faceMask (⟨1025, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1026 : supportIntersection (⟨1026, by decide⟩ : Fin 1069) = faceMask (⟨1026, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1027 : supportIntersection (⟨1027, by decide⟩ : Fin 1069) = faceMask (⟨1027, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1028 : supportIntersection (⟨1028, by decide⟩ : Fin 1069) = faceMask (⟨1028, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1029 : supportIntersection (⟨1029, by decide⟩ : Fin 1069) = faceMask (⟨1029, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1030 : supportIntersection (⟨1030, by decide⟩ : Fin 1069) = faceMask (⟨1030, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1031 : supportIntersection (⟨1031, by decide⟩ : Fin 1069) = faceMask (⟨1031, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1032 : supportIntersection (⟨1032, by decide⟩ : Fin 1069) = faceMask (⟨1032, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1033 : supportIntersection (⟨1033, by decide⟩ : Fin 1069) = faceMask (⟨1033, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1034 : supportIntersection (⟨1034, by decide⟩ : Fin 1069) = faceMask (⟨1034, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1035 : supportIntersection (⟨1035, by decide⟩ : Fin 1069) = faceMask (⟨1035, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1036 : supportIntersection (⟨1036, by decide⟩ : Fin 1069) = faceMask (⟨1036, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1037 : supportIntersection (⟨1037, by decide⟩ : Fin 1069) = faceMask (⟨1037, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1038 : supportIntersection (⟨1038, by decide⟩ : Fin 1069) = faceMask (⟨1038, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1039 : supportIntersection (⟨1039, by decide⟩ : Fin 1069) = faceMask (⟨1039, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1040 : supportIntersection (⟨1040, by decide⟩ : Fin 1069) = faceMask (⟨1040, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1041 : supportIntersection (⟨1041, by decide⟩ : Fin 1069) = faceMask (⟨1041, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1042 : supportIntersection (⟨1042, by decide⟩ : Fin 1069) = faceMask (⟨1042, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1043 : supportIntersection (⟨1043, by decide⟩ : Fin 1069) = faceMask (⟨1043, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1044 : supportIntersection (⟨1044, by decide⟩ : Fin 1069) = faceMask (⟨1044, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1045 : supportIntersection (⟨1045, by decide⟩ : Fin 1069) = faceMask (⟨1045, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1046 : supportIntersection (⟨1046, by decide⟩ : Fin 1069) = faceMask (⟨1046, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1047 : supportIntersection (⟨1047, by decide⟩ : Fin 1069) = faceMask (⟨1047, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1048 : supportIntersection (⟨1048, by decide⟩ : Fin 1069) = faceMask (⟨1048, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1049 : supportIntersection (⟨1049, by decide⟩ : Fin 1069) = faceMask (⟨1049, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1050 : supportIntersection (⟨1050, by decide⟩ : Fin 1069) = faceMask (⟨1050, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1051 : supportIntersection (⟨1051, by decide⟩ : Fin 1069) = faceMask (⟨1051, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1052 : supportIntersection (⟨1052, by decide⟩ : Fin 1069) = faceMask (⟨1052, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1053 : supportIntersection (⟨1053, by decide⟩ : Fin 1069) = faceMask (⟨1053, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1054 : supportIntersection (⟨1054, by decide⟩ : Fin 1069) = faceMask (⟨1054, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1055 : supportIntersection (⟨1055, by decide⟩ : Fin 1069) = faceMask (⟨1055, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1056 : supportIntersection (⟨1056, by decide⟩ : Fin 1069) = faceMask (⟨1056, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1057 : supportIntersection (⟨1057, by decide⟩ : Fin 1069) = faceMask (⟨1057, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1058 : supportIntersection (⟨1058, by decide⟩ : Fin 1069) = faceMask (⟨1058, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1059 : supportIntersection (⟨1059, by decide⟩ : Fin 1069) = faceMask (⟨1059, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1060 : supportIntersection (⟨1060, by decide⟩ : Fin 1069) = faceMask (⟨1060, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1061 : supportIntersection (⟨1061, by decide⟩ : Fin 1069) = faceMask (⟨1061, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1062 : supportIntersection (⟨1062, by decide⟩ : Fin 1069) = faceMask (⟨1062, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1063 : supportIntersection (⟨1063, by decide⟩ : Fin 1069) = faceMask (⟨1063, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1064 : supportIntersection (⟨1064, by decide⟩ : Fin 1069) = faceMask (⟨1064, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1065 : supportIntersection (⟨1065, by decide⟩ : Fin 1069) = faceMask (⟨1065, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1066 : supportIntersection (⟨1066, by decide⟩ : Fin 1069) = faceMask (⟨1066, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1067 : supportIntersection (⟨1067, by decide⟩ : Fin 1069) = faceMask (⟨1067, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem support1068 : supportIntersection (⟨1068, by decide⟩ : Fin 1069) = faceMask (⟨1068, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem supportGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h16 : i.val < 16
  ·
    by_cases h8 : i.val < 8
    ·
      by_cases h4 : i.val < 4
      ·
        by_cases h2 : i.val < 2
        ·
          by_cases h1 : i.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 0 = i.val
              omega
            simpa only [he] using support0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using support0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using support0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using support0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using support0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using support0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using support0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using support0007
    ·
      by_cases h12 : i.val < 12
      ·
        by_cases h10 : i.val < 10
        ·
          by_cases h9 : i.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using support0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using support0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using support0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using support0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using support0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using support0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using support0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using support0015
  ·
    by_cases h24 : i.val < 24
    ·
      by_cases h20 : i.val < 20
      ·
        by_cases h18 : i.val < 18
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using support0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using support0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using support0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using support0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using support0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using support0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using support0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using support0023
    ·
      by_cases h28 : i.val < 28
      ·
        by_cases h26 : i.val < 26
        ·
          by_cases h25 : i.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 24 = i.val
              omega
            simpa only [he] using support0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using support0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using support0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using support0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using support0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using support0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using support0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using support0031

private theorem supportGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h48 : i.val < 48
  ·
    by_cases h40 : i.val < 40
    ·
      by_cases h36 : i.val < 36
      ·
        by_cases h34 : i.val < 34
        ·
          by_cases h33 : i.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 32 = i.val
              omega
            simpa only [he] using support0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using support0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using support0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using support0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using support0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using support0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using support0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using support0039
    ·
      by_cases h44 : i.val < 44
      ·
        by_cases h42 : i.val < 42
        ·
          by_cases h41 : i.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 40 = i.val
              omega
            simpa only [he] using support0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using support0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using support0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using support0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using support0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using support0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using support0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using support0047
  ·
    by_cases h56 : i.val < 56
    ·
      by_cases h52 : i.val < 52
      ·
        by_cases h50 : i.val < 50
        ·
          by_cases h49 : i.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 48 = i.val
              omega
            simpa only [he] using support0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using support0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using support0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using support0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using support0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using support0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using support0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using support0055
    ·
      by_cases h60 : i.val < 60
      ·
        by_cases h58 : i.val < 58
        ·
          by_cases h57 : i.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 56 = i.val
              omega
            simpa only [he] using support0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using support0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using support0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using support0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using support0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using support0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using support0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using support0063

private theorem supportGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h80 : i.val < 80
  ·
    by_cases h72 : i.val < 72
    ·
      by_cases h68 : i.val < 68
      ·
        by_cases h66 : i.val < 66
        ·
          by_cases h65 : i.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 64 = i.val
              omega
            simpa only [he] using support0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using support0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using support0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using support0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using support0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using support0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using support0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using support0071
    ·
      by_cases h76 : i.val < 76
      ·
        by_cases h74 : i.val < 74
        ·
          by_cases h73 : i.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 72 = i.val
              omega
            simpa only [he] using support0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using support0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using support0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using support0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using support0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using support0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using support0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using support0079
  ·
    by_cases h88 : i.val < 88
    ·
      by_cases h84 : i.val < 84
      ·
        by_cases h82 : i.val < 82
        ·
          by_cases h81 : i.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 80 = i.val
              omega
            simpa only [he] using support0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using support0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using support0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using support0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using support0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using support0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using support0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using support0087
    ·
      by_cases h92 : i.val < 92
      ·
        by_cases h90 : i.val < 90
        ·
          by_cases h89 : i.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 88 = i.val
              omega
            simpa only [he] using support0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using support0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using support0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using support0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using support0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using support0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using support0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using support0095

private theorem supportGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h112 : i.val < 112
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h100 : i.val < 100
      ·
        by_cases h98 : i.val < 98
        ·
          by_cases h97 : i.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 96 = i.val
              omega
            simpa only [he] using support0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using support0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using support0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using support0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using support0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using support0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using support0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using support0103
    ·
      by_cases h108 : i.val < 108
      ·
        by_cases h106 : i.val < 106
        ·
          by_cases h105 : i.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 104 = i.val
              omega
            simpa only [he] using support0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using support0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using support0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using support0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using support0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using support0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using support0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using support0111
  ·
    by_cases h120 : i.val < 120
    ·
      by_cases h116 : i.val < 116
      ·
        by_cases h114 : i.val < 114
        ·
          by_cases h113 : i.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 112 = i.val
              omega
            simpa only [he] using support0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using support0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using support0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using support0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using support0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using support0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using support0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using support0119
    ·
      by_cases h124 : i.val < 124
      ·
        by_cases h122 : i.val < 122
        ·
          by_cases h121 : i.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 120 = i.val
              omega
            simpa only [he] using support0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using support0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using support0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using support0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using support0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using support0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using support0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using support0127

private theorem supportGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h144 : i.val < 144
  ·
    by_cases h136 : i.val < 136
    ·
      by_cases h132 : i.val < 132
      ·
        by_cases h130 : i.val < 130
        ·
          by_cases h129 : i.val < 129
          ·
            have he : (⟨128, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 128 = i.val
              omega
            simpa only [he] using support0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using support0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using support0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using support0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using support0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using support0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using support0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using support0135
    ·
      by_cases h140 : i.val < 140
      ·
        by_cases h138 : i.val < 138
        ·
          by_cases h137 : i.val < 137
          ·
            have he : (⟨136, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 136 = i.val
              omega
            simpa only [he] using support0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using support0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using support0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using support0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using support0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using support0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using support0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using support0143
  ·
    by_cases h152 : i.val < 152
    ·
      by_cases h148 : i.val < 148
      ·
        by_cases h146 : i.val < 146
        ·
          by_cases h145 : i.val < 145
          ·
            have he : (⟨144, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 144 = i.val
              omega
            simpa only [he] using support0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using support0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using support0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using support0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using support0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using support0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using support0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using support0151
    ·
      by_cases h156 : i.val < 156
      ·
        by_cases h154 : i.val < 154
        ·
          by_cases h153 : i.val < 153
          ·
            have he : (⟨152, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 152 = i.val
              omega
            simpa only [he] using support0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using support0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using support0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using support0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using support0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using support0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using support0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using support0159

private theorem supportGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h176 : i.val < 176
  ·
    by_cases h168 : i.val < 168
    ·
      by_cases h164 : i.val < 164
      ·
        by_cases h162 : i.val < 162
        ·
          by_cases h161 : i.val < 161
          ·
            have he : (⟨160, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 160 = i.val
              omega
            simpa only [he] using support0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using support0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using support0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using support0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using support0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using support0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using support0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using support0167
    ·
      by_cases h172 : i.val < 172
      ·
        by_cases h170 : i.val < 170
        ·
          by_cases h169 : i.val < 169
          ·
            have he : (⟨168, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 168 = i.val
              omega
            simpa only [he] using support0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using support0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using support0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using support0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using support0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using support0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using support0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using support0175
  ·
    by_cases h184 : i.val < 184
    ·
      by_cases h180 : i.val < 180
      ·
        by_cases h178 : i.val < 178
        ·
          by_cases h177 : i.val < 177
          ·
            have he : (⟨176, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 176 = i.val
              omega
            simpa only [he] using support0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using support0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using support0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using support0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using support0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using support0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using support0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using support0183
    ·
      by_cases h188 : i.val < 188
      ·
        by_cases h186 : i.val < 186
        ·
          by_cases h185 : i.val < 185
          ·
            have he : (⟨184, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 184 = i.val
              omega
            simpa only [he] using support0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using support0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using support0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using support0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using support0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using support0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using support0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using support0191

private theorem supportGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h208 : i.val < 208
  ·
    by_cases h200 : i.val < 200
    ·
      by_cases h196 : i.val < 196
      ·
        by_cases h194 : i.val < 194
        ·
          by_cases h193 : i.val < 193
          ·
            have he : (⟨192, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 192 = i.val
              omega
            simpa only [he] using support0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using support0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using support0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using support0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using support0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using support0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using support0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using support0199
    ·
      by_cases h204 : i.val < 204
      ·
        by_cases h202 : i.val < 202
        ·
          by_cases h201 : i.val < 201
          ·
            have he : (⟨200, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 200 = i.val
              omega
            simpa only [he] using support0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using support0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using support0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using support0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using support0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using support0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using support0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using support0207
  ·
    by_cases h216 : i.val < 216
    ·
      by_cases h212 : i.val < 212
      ·
        by_cases h210 : i.val < 210
        ·
          by_cases h209 : i.val < 209
          ·
            have he : (⟨208, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 208 = i.val
              omega
            simpa only [he] using support0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using support0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using support0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using support0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using support0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using support0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using support0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using support0215
    ·
      by_cases h220 : i.val < 220
      ·
        by_cases h218 : i.val < 218
        ·
          by_cases h217 : i.val < 217
          ·
            have he : (⟨216, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 216 = i.val
              omega
            simpa only [he] using support0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using support0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using support0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using support0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using support0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using support0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using support0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using support0223

private theorem supportGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h240 : i.val < 240
  ·
    by_cases h232 : i.val < 232
    ·
      by_cases h228 : i.val < 228
      ·
        by_cases h226 : i.val < 226
        ·
          by_cases h225 : i.val < 225
          ·
            have he : (⟨224, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 224 = i.val
              omega
            simpa only [he] using support0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using support0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using support0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using support0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using support0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using support0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using support0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using support0231
    ·
      by_cases h236 : i.val < 236
      ·
        by_cases h234 : i.val < 234
        ·
          by_cases h233 : i.val < 233
          ·
            have he : (⟨232, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 232 = i.val
              omega
            simpa only [he] using support0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using support0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using support0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using support0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using support0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using support0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using support0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using support0239
  ·
    by_cases h248 : i.val < 248
    ·
      by_cases h244 : i.val < 244
      ·
        by_cases h242 : i.val < 242
        ·
          by_cases h241 : i.val < 241
          ·
            have he : (⟨240, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 240 = i.val
              omega
            simpa only [he] using support0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using support0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using support0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using support0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using support0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using support0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using support0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using support0247
    ·
      by_cases h252 : i.val < 252
      ·
        by_cases h250 : i.val < 250
        ·
          by_cases h249 : i.val < 249
          ·
            have he : (⟨248, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 248 = i.val
              omega
            simpa only [he] using support0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using support0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using support0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using support0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using support0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using support0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using support0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using support0255

private theorem supportGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h272 : i.val < 272
  ·
    by_cases h264 : i.val < 264
    ·
      by_cases h260 : i.val < 260
      ·
        by_cases h258 : i.val < 258
        ·
          by_cases h257 : i.val < 257
          ·
            have he : (⟨256, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 256 = i.val
              omega
            simpa only [he] using support0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using support0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using support0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using support0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using support0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using support0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using support0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using support0263
    ·
      by_cases h268 : i.val < 268
      ·
        by_cases h266 : i.val < 266
        ·
          by_cases h265 : i.val < 265
          ·
            have he : (⟨264, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 264 = i.val
              omega
            simpa only [he] using support0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using support0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using support0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using support0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using support0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using support0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using support0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using support0271
  ·
    by_cases h280 : i.val < 280
    ·
      by_cases h276 : i.val < 276
      ·
        by_cases h274 : i.val < 274
        ·
          by_cases h273 : i.val < 273
          ·
            have he : (⟨272, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 272 = i.val
              omega
            simpa only [he] using support0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using support0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using support0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using support0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using support0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using support0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using support0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using support0279
    ·
      by_cases h284 : i.val < 284
      ·
        by_cases h282 : i.val < 282
        ·
          by_cases h281 : i.val < 281
          ·
            have he : (⟨280, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 280 = i.val
              omega
            simpa only [he] using support0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using support0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using support0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using support0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using support0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using support0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using support0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using support0287

private theorem supportGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h304 : i.val < 304
  ·
    by_cases h296 : i.val < 296
    ·
      by_cases h292 : i.val < 292
      ·
        by_cases h290 : i.val < 290
        ·
          by_cases h289 : i.val < 289
          ·
            have he : (⟨288, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 288 = i.val
              omega
            simpa only [he] using support0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using support0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using support0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using support0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using support0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using support0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using support0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using support0295
    ·
      by_cases h300 : i.val < 300
      ·
        by_cases h298 : i.val < 298
        ·
          by_cases h297 : i.val < 297
          ·
            have he : (⟨296, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 296 = i.val
              omega
            simpa only [he] using support0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using support0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using support0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using support0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using support0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using support0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using support0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using support0303
  ·
    by_cases h312 : i.val < 312
    ·
      by_cases h308 : i.val < 308
      ·
        by_cases h306 : i.val < 306
        ·
          by_cases h305 : i.val < 305
          ·
            have he : (⟨304, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 304 = i.val
              omega
            simpa only [he] using support0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using support0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using support0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using support0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using support0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using support0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using support0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using support0311
    ·
      by_cases h316 : i.val < 316
      ·
        by_cases h314 : i.val < 314
        ·
          by_cases h313 : i.val < 313
          ·
            have he : (⟨312, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 312 = i.val
              omega
            simpa only [he] using support0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using support0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using support0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using support0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using support0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using support0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using support0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using support0319

private theorem supportGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h336 : i.val < 336
  ·
    by_cases h328 : i.val < 328
    ·
      by_cases h324 : i.val < 324
      ·
        by_cases h322 : i.val < 322
        ·
          by_cases h321 : i.val < 321
          ·
            have he : (⟨320, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 320 = i.val
              omega
            simpa only [he] using support0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using support0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using support0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using support0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using support0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using support0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using support0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using support0327
    ·
      by_cases h332 : i.val < 332
      ·
        by_cases h330 : i.val < 330
        ·
          by_cases h329 : i.val < 329
          ·
            have he : (⟨328, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 328 = i.val
              omega
            simpa only [he] using support0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using support0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using support0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using support0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using support0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using support0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using support0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using support0335
  ·
    by_cases h344 : i.val < 344
    ·
      by_cases h340 : i.val < 340
      ·
        by_cases h338 : i.val < 338
        ·
          by_cases h337 : i.val < 337
          ·
            have he : (⟨336, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 336 = i.val
              omega
            simpa only [he] using support0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using support0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using support0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using support0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using support0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using support0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using support0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using support0343
    ·
      by_cases h348 : i.val < 348
      ·
        by_cases h346 : i.val < 346
        ·
          by_cases h345 : i.val < 345
          ·
            have he : (⟨344, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 344 = i.val
              omega
            simpa only [he] using support0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using support0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using support0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using support0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using support0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using support0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using support0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using support0351

private theorem supportGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h368 : i.val < 368
  ·
    by_cases h360 : i.val < 360
    ·
      by_cases h356 : i.val < 356
      ·
        by_cases h354 : i.val < 354
        ·
          by_cases h353 : i.val < 353
          ·
            have he : (⟨352, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 352 = i.val
              omega
            simpa only [he] using support0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using support0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using support0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using support0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using support0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using support0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using support0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using support0359
    ·
      by_cases h364 : i.val < 364
      ·
        by_cases h362 : i.val < 362
        ·
          by_cases h361 : i.val < 361
          ·
            have he : (⟨360, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 360 = i.val
              omega
            simpa only [he] using support0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using support0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using support0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using support0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using support0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using support0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using support0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using support0367
  ·
    by_cases h376 : i.val < 376
    ·
      by_cases h372 : i.val < 372
      ·
        by_cases h370 : i.val < 370
        ·
          by_cases h369 : i.val < 369
          ·
            have he : (⟨368, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 368 = i.val
              omega
            simpa only [he] using support0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using support0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using support0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using support0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using support0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using support0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using support0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using support0375
    ·
      by_cases h380 : i.val < 380
      ·
        by_cases h378 : i.val < 378
        ·
          by_cases h377 : i.val < 377
          ·
            have he : (⟨376, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 376 = i.val
              omega
            simpa only [he] using support0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using support0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using support0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using support0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using support0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using support0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using support0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using support0383

private theorem supportGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h400 : i.val < 400
  ·
    by_cases h392 : i.val < 392
    ·
      by_cases h388 : i.val < 388
      ·
        by_cases h386 : i.val < 386
        ·
          by_cases h385 : i.val < 385
          ·
            have he : (⟨384, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 384 = i.val
              omega
            simpa only [he] using support0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using support0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using support0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using support0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using support0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using support0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using support0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using support0391
    ·
      by_cases h396 : i.val < 396
      ·
        by_cases h394 : i.val < 394
        ·
          by_cases h393 : i.val < 393
          ·
            have he : (⟨392, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 392 = i.val
              omega
            simpa only [he] using support0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using support0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using support0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using support0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using support0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using support0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using support0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using support0399
  ·
    by_cases h408 : i.val < 408
    ·
      by_cases h404 : i.val < 404
      ·
        by_cases h402 : i.val < 402
        ·
          by_cases h401 : i.val < 401
          ·
            have he : (⟨400, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 400 = i.val
              omega
            simpa only [he] using support0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using support0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using support0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using support0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using support0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using support0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using support0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using support0407
    ·
      by_cases h412 : i.val < 412
      ·
        by_cases h410 : i.val < 410
        ·
          by_cases h409 : i.val < 409
          ·
            have he : (⟨408, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 408 = i.val
              omega
            simpa only [he] using support0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using support0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using support0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using support0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using support0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using support0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using support0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using support0415

private theorem supportGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h432 : i.val < 432
  ·
    by_cases h424 : i.val < 424
    ·
      by_cases h420 : i.val < 420
      ·
        by_cases h418 : i.val < 418
        ·
          by_cases h417 : i.val < 417
          ·
            have he : (⟨416, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 416 = i.val
              omega
            simpa only [he] using support0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using support0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using support0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using support0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using support0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using support0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using support0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using support0423
    ·
      by_cases h428 : i.val < 428
      ·
        by_cases h426 : i.val < 426
        ·
          by_cases h425 : i.val < 425
          ·
            have he : (⟨424, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 424 = i.val
              omega
            simpa only [he] using support0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using support0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using support0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using support0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using support0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using support0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using support0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using support0431
  ·
    by_cases h440 : i.val < 440
    ·
      by_cases h436 : i.val < 436
      ·
        by_cases h434 : i.val < 434
        ·
          by_cases h433 : i.val < 433
          ·
            have he : (⟨432, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 432 = i.val
              omega
            simpa only [he] using support0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using support0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using support0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using support0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using support0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using support0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using support0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using support0439
    ·
      by_cases h444 : i.val < 444
      ·
        by_cases h442 : i.val < 442
        ·
          by_cases h441 : i.val < 441
          ·
            have he : (⟨440, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 440 = i.val
              omega
            simpa only [he] using support0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using support0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using support0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using support0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using support0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using support0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using support0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using support0447

private theorem supportGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h464 : i.val < 464
  ·
    by_cases h456 : i.val < 456
    ·
      by_cases h452 : i.val < 452
      ·
        by_cases h450 : i.val < 450
        ·
          by_cases h449 : i.val < 449
          ·
            have he : (⟨448, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 448 = i.val
              omega
            simpa only [he] using support0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using support0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using support0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using support0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using support0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using support0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using support0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using support0455
    ·
      by_cases h460 : i.val < 460
      ·
        by_cases h458 : i.val < 458
        ·
          by_cases h457 : i.val < 457
          ·
            have he : (⟨456, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 456 = i.val
              omega
            simpa only [he] using support0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using support0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using support0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using support0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using support0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using support0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using support0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using support0463
  ·
    by_cases h472 : i.val < 472
    ·
      by_cases h468 : i.val < 468
      ·
        by_cases h466 : i.val < 466
        ·
          by_cases h465 : i.val < 465
          ·
            have he : (⟨464, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 464 = i.val
              omega
            simpa only [he] using support0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using support0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using support0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using support0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using support0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using support0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using support0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using support0471
    ·
      by_cases h476 : i.val < 476
      ·
        by_cases h474 : i.val < 474
        ·
          by_cases h473 : i.val < 473
          ·
            have he : (⟨472, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 472 = i.val
              omega
            simpa only [he] using support0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using support0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using support0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using support0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using support0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using support0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using support0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using support0479

private theorem supportGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h496 : i.val < 496
  ·
    by_cases h488 : i.val < 488
    ·
      by_cases h484 : i.val < 484
      ·
        by_cases h482 : i.val < 482
        ·
          by_cases h481 : i.val < 481
          ·
            have he : (⟨480, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 480 = i.val
              omega
            simpa only [he] using support0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using support0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using support0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using support0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using support0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using support0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using support0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using support0487
    ·
      by_cases h492 : i.val < 492
      ·
        by_cases h490 : i.val < 490
        ·
          by_cases h489 : i.val < 489
          ·
            have he : (⟨488, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 488 = i.val
              omega
            simpa only [he] using support0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using support0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using support0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using support0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using support0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using support0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using support0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using support0495
  ·
    by_cases h504 : i.val < 504
    ·
      by_cases h500 : i.val < 500
      ·
        by_cases h498 : i.val < 498
        ·
          by_cases h497 : i.val < 497
          ·
            have he : (⟨496, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 496 = i.val
              omega
            simpa only [he] using support0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using support0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using support0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using support0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using support0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using support0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using support0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using support0503
    ·
      by_cases h508 : i.val < 508
      ·
        by_cases h506 : i.val < 506
        ·
          by_cases h505 : i.val < 505
          ·
            have he : (⟨504, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 504 = i.val
              omega
            simpa only [he] using support0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using support0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using support0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using support0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using support0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using support0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using support0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using support0511

private theorem supportGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h528 : i.val < 528
  ·
    by_cases h520 : i.val < 520
    ·
      by_cases h516 : i.val < 516
      ·
        by_cases h514 : i.val < 514
        ·
          by_cases h513 : i.val < 513
          ·
            have he : (⟨512, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 512 = i.val
              omega
            simpa only [he] using support0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using support0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using support0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using support0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using support0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using support0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using support0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using support0519
    ·
      by_cases h524 : i.val < 524
      ·
        by_cases h522 : i.val < 522
        ·
          by_cases h521 : i.val < 521
          ·
            have he : (⟨520, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 520 = i.val
              omega
            simpa only [he] using support0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using support0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using support0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using support0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using support0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using support0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using support0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using support0527
  ·
    by_cases h536 : i.val < 536
    ·
      by_cases h532 : i.val < 532
      ·
        by_cases h530 : i.val < 530
        ·
          by_cases h529 : i.val < 529
          ·
            have he : (⟨528, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 528 = i.val
              omega
            simpa only [he] using support0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using support0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using support0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using support0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using support0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using support0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using support0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using support0535
    ·
      by_cases h540 : i.val < 540
      ·
        by_cases h538 : i.val < 538
        ·
          by_cases h537 : i.val < 537
          ·
            have he : (⟨536, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 536 = i.val
              omega
            simpa only [he] using support0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using support0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using support0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using support0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using support0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using support0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using support0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using support0543

private theorem supportGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h560 : i.val < 560
  ·
    by_cases h552 : i.val < 552
    ·
      by_cases h548 : i.val < 548
      ·
        by_cases h546 : i.val < 546
        ·
          by_cases h545 : i.val < 545
          ·
            have he : (⟨544, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 544 = i.val
              omega
            simpa only [he] using support0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using support0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using support0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using support0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using support0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using support0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using support0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using support0551
    ·
      by_cases h556 : i.val < 556
      ·
        by_cases h554 : i.val < 554
        ·
          by_cases h553 : i.val < 553
          ·
            have he : (⟨552, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 552 = i.val
              omega
            simpa only [he] using support0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using support0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using support0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using support0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using support0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using support0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using support0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using support0559
  ·
    by_cases h568 : i.val < 568
    ·
      by_cases h564 : i.val < 564
      ·
        by_cases h562 : i.val < 562
        ·
          by_cases h561 : i.val < 561
          ·
            have he : (⟨560, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 560 = i.val
              omega
            simpa only [he] using support0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using support0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using support0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using support0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using support0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using support0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using support0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using support0567
    ·
      by_cases h572 : i.val < 572
      ·
        by_cases h570 : i.val < 570
        ·
          by_cases h569 : i.val < 569
          ·
            have he : (⟨568, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 568 = i.val
              omega
            simpa only [he] using support0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using support0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using support0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using support0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using support0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using support0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using support0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using support0575

private theorem supportGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h592 : i.val < 592
  ·
    by_cases h584 : i.val < 584
    ·
      by_cases h580 : i.val < 580
      ·
        by_cases h578 : i.val < 578
        ·
          by_cases h577 : i.val < 577
          ·
            have he : (⟨576, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 576 = i.val
              omega
            simpa only [he] using support0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using support0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using support0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using support0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using support0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using support0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using support0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using support0583
    ·
      by_cases h588 : i.val < 588
      ·
        by_cases h586 : i.val < 586
        ·
          by_cases h585 : i.val < 585
          ·
            have he : (⟨584, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 584 = i.val
              omega
            simpa only [he] using support0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using support0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using support0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using support0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using support0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using support0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using support0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using support0591
  ·
    by_cases h600 : i.val < 600
    ·
      by_cases h596 : i.val < 596
      ·
        by_cases h594 : i.val < 594
        ·
          by_cases h593 : i.val < 593
          ·
            have he : (⟨592, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 592 = i.val
              omega
            simpa only [he] using support0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using support0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using support0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using support0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using support0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using support0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using support0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using support0599
    ·
      by_cases h604 : i.val < 604
      ·
        by_cases h602 : i.val < 602
        ·
          by_cases h601 : i.val < 601
          ·
            have he : (⟨600, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 600 = i.val
              omega
            simpa only [he] using support0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using support0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using support0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using support0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using support0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using support0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using support0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using support0607

private theorem supportGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h624 : i.val < 624
  ·
    by_cases h616 : i.val < 616
    ·
      by_cases h612 : i.val < 612
      ·
        by_cases h610 : i.val < 610
        ·
          by_cases h609 : i.val < 609
          ·
            have he : (⟨608, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 608 = i.val
              omega
            simpa only [he] using support0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using support0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using support0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using support0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using support0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using support0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using support0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using support0615
    ·
      by_cases h620 : i.val < 620
      ·
        by_cases h618 : i.val < 618
        ·
          by_cases h617 : i.val < 617
          ·
            have he : (⟨616, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 616 = i.val
              omega
            simpa only [he] using support0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using support0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using support0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using support0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using support0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using support0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using support0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using support0623
  ·
    by_cases h632 : i.val < 632
    ·
      by_cases h628 : i.val < 628
      ·
        by_cases h626 : i.val < 626
        ·
          by_cases h625 : i.val < 625
          ·
            have he : (⟨624, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 624 = i.val
              omega
            simpa only [he] using support0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using support0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using support0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using support0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using support0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using support0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using support0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using support0631
    ·
      by_cases h636 : i.val < 636
      ·
        by_cases h634 : i.val < 634
        ·
          by_cases h633 : i.val < 633
          ·
            have he : (⟨632, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 632 = i.val
              omega
            simpa only [he] using support0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using support0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using support0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using support0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using support0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using support0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using support0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using support0639

private theorem supportGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h656 : i.val < 656
  ·
    by_cases h648 : i.val < 648
    ·
      by_cases h644 : i.val < 644
      ·
        by_cases h642 : i.val < 642
        ·
          by_cases h641 : i.val < 641
          ·
            have he : (⟨640, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 640 = i.val
              omega
            simpa only [he] using support0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using support0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using support0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using support0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using support0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using support0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using support0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using support0647
    ·
      by_cases h652 : i.val < 652
      ·
        by_cases h650 : i.val < 650
        ·
          by_cases h649 : i.val < 649
          ·
            have he : (⟨648, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 648 = i.val
              omega
            simpa only [he] using support0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using support0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using support0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using support0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using support0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using support0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using support0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using support0655
  ·
    by_cases h664 : i.val < 664
    ·
      by_cases h660 : i.val < 660
      ·
        by_cases h658 : i.val < 658
        ·
          by_cases h657 : i.val < 657
          ·
            have he : (⟨656, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 656 = i.val
              omega
            simpa only [he] using support0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using support0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using support0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using support0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using support0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using support0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using support0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using support0663
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h666 : i.val < 666
        ·
          by_cases h665 : i.val < 665
          ·
            have he : (⟨664, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 664 = i.val
              omega
            simpa only [he] using support0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using support0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using support0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using support0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using support0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using support0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using support0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using support0671

private theorem supportGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h688 : i.val < 688
  ·
    by_cases h680 : i.val < 680
    ·
      by_cases h676 : i.val < 676
      ·
        by_cases h674 : i.val < 674
        ·
          by_cases h673 : i.val < 673
          ·
            have he : (⟨672, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 672 = i.val
              omega
            simpa only [he] using support0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using support0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using support0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using support0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using support0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using support0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using support0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using support0679
    ·
      by_cases h684 : i.val < 684
      ·
        by_cases h682 : i.val < 682
        ·
          by_cases h681 : i.val < 681
          ·
            have he : (⟨680, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 680 = i.val
              omega
            simpa only [he] using support0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using support0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using support0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using support0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using support0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using support0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using support0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using support0687
  ·
    by_cases h696 : i.val < 696
    ·
      by_cases h692 : i.val < 692
      ·
        by_cases h690 : i.val < 690
        ·
          by_cases h689 : i.val < 689
          ·
            have he : (⟨688, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 688 = i.val
              omega
            simpa only [he] using support0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using support0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using support0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using support0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using support0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using support0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using support0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using support0695
    ·
      by_cases h700 : i.val < 700
      ·
        by_cases h698 : i.val < 698
        ·
          by_cases h697 : i.val < 697
          ·
            have he : (⟨696, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 696 = i.val
              omega
            simpa only [he] using support0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using support0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using support0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using support0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using support0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using support0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using support0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using support0703

private theorem supportGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h720 : i.val < 720
  ·
    by_cases h712 : i.val < 712
    ·
      by_cases h708 : i.val < 708
      ·
        by_cases h706 : i.val < 706
        ·
          by_cases h705 : i.val < 705
          ·
            have he : (⟨704, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 704 = i.val
              omega
            simpa only [he] using support0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using support0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using support0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using support0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using support0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using support0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using support0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using support0711
    ·
      by_cases h716 : i.val < 716
      ·
        by_cases h714 : i.val < 714
        ·
          by_cases h713 : i.val < 713
          ·
            have he : (⟨712, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 712 = i.val
              omega
            simpa only [he] using support0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using support0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using support0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using support0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using support0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using support0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using support0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using support0719
  ·
    by_cases h728 : i.val < 728
    ·
      by_cases h724 : i.val < 724
      ·
        by_cases h722 : i.val < 722
        ·
          by_cases h721 : i.val < 721
          ·
            have he : (⟨720, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 720 = i.val
              omega
            simpa only [he] using support0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using support0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using support0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using support0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using support0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using support0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using support0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using support0727
    ·
      by_cases h732 : i.val < 732
      ·
        by_cases h730 : i.val < 730
        ·
          by_cases h729 : i.val < 729
          ·
            have he : (⟨728, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 728 = i.val
              omega
            simpa only [he] using support0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using support0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using support0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using support0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using support0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using support0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using support0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using support0735

private theorem supportGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h752 : i.val < 752
  ·
    by_cases h744 : i.val < 744
    ·
      by_cases h740 : i.val < 740
      ·
        by_cases h738 : i.val < 738
        ·
          by_cases h737 : i.val < 737
          ·
            have he : (⟨736, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 736 = i.val
              omega
            simpa only [he] using support0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using support0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using support0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using support0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using support0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using support0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using support0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using support0743
    ·
      by_cases h748 : i.val < 748
      ·
        by_cases h746 : i.val < 746
        ·
          by_cases h745 : i.val < 745
          ·
            have he : (⟨744, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 744 = i.val
              omega
            simpa only [he] using support0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using support0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using support0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using support0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using support0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using support0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using support0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using support0751
  ·
    by_cases h760 : i.val < 760
    ·
      by_cases h756 : i.val < 756
      ·
        by_cases h754 : i.val < 754
        ·
          by_cases h753 : i.val < 753
          ·
            have he : (⟨752, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 752 = i.val
              omega
            simpa only [he] using support0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using support0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using support0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using support0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using support0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using support0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using support0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using support0759
    ·
      by_cases h764 : i.val < 764
      ·
        by_cases h762 : i.val < 762
        ·
          by_cases h761 : i.val < 761
          ·
            have he : (⟨760, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 760 = i.val
              omega
            simpa only [he] using support0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using support0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using support0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using support0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using support0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using support0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using support0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using support0767

private theorem supportGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h784 : i.val < 784
  ·
    by_cases h776 : i.val < 776
    ·
      by_cases h772 : i.val < 772
      ·
        by_cases h770 : i.val < 770
        ·
          by_cases h769 : i.val < 769
          ·
            have he : (⟨768, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 768 = i.val
              omega
            simpa only [he] using support0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using support0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using support0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using support0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using support0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using support0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using support0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using support0775
    ·
      by_cases h780 : i.val < 780
      ·
        by_cases h778 : i.val < 778
        ·
          by_cases h777 : i.val < 777
          ·
            have he : (⟨776, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 776 = i.val
              omega
            simpa only [he] using support0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using support0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using support0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using support0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using support0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using support0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using support0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using support0783
  ·
    by_cases h792 : i.val < 792
    ·
      by_cases h788 : i.val < 788
      ·
        by_cases h786 : i.val < 786
        ·
          by_cases h785 : i.val < 785
          ·
            have he : (⟨784, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 784 = i.val
              omega
            simpa only [he] using support0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using support0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using support0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using support0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using support0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using support0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using support0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using support0791
    ·
      by_cases h796 : i.val < 796
      ·
        by_cases h794 : i.val < 794
        ·
          by_cases h793 : i.val < 793
          ·
            have he : (⟨792, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 792 = i.val
              omega
            simpa only [he] using support0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using support0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using support0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using support0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using support0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using support0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using support0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using support0799

private theorem supportGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h816 : i.val < 816
  ·
    by_cases h808 : i.val < 808
    ·
      by_cases h804 : i.val < 804
      ·
        by_cases h802 : i.val < 802
        ·
          by_cases h801 : i.val < 801
          ·
            have he : (⟨800, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 800 = i.val
              omega
            simpa only [he] using support0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using support0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using support0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using support0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using support0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using support0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using support0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using support0807
    ·
      by_cases h812 : i.val < 812
      ·
        by_cases h810 : i.val < 810
        ·
          by_cases h809 : i.val < 809
          ·
            have he : (⟨808, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 808 = i.val
              omega
            simpa only [he] using support0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using support0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using support0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using support0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using support0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using support0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using support0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using support0815
  ·
    by_cases h824 : i.val < 824
    ·
      by_cases h820 : i.val < 820
      ·
        by_cases h818 : i.val < 818
        ·
          by_cases h817 : i.val < 817
          ·
            have he : (⟨816, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 816 = i.val
              omega
            simpa only [he] using support0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using support0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using support0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using support0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using support0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using support0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using support0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using support0823
    ·
      by_cases h828 : i.val < 828
      ·
        by_cases h826 : i.val < 826
        ·
          by_cases h825 : i.val < 825
          ·
            have he : (⟨824, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 824 = i.val
              omega
            simpa only [he] using support0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using support0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using support0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using support0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using support0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using support0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using support0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using support0831

private theorem supportGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h848 : i.val < 848
  ·
    by_cases h840 : i.val < 840
    ·
      by_cases h836 : i.val < 836
      ·
        by_cases h834 : i.val < 834
        ·
          by_cases h833 : i.val < 833
          ·
            have he : (⟨832, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 832 = i.val
              omega
            simpa only [he] using support0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using support0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using support0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using support0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using support0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using support0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using support0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using support0839
    ·
      by_cases h844 : i.val < 844
      ·
        by_cases h842 : i.val < 842
        ·
          by_cases h841 : i.val < 841
          ·
            have he : (⟨840, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 840 = i.val
              omega
            simpa only [he] using support0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using support0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using support0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using support0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using support0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using support0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using support0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using support0847
  ·
    by_cases h856 : i.val < 856
    ·
      by_cases h852 : i.val < 852
      ·
        by_cases h850 : i.val < 850
        ·
          by_cases h849 : i.val < 849
          ·
            have he : (⟨848, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 848 = i.val
              omega
            simpa only [he] using support0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using support0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using support0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using support0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using support0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using support0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using support0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using support0855
    ·
      by_cases h860 : i.val < 860
      ·
        by_cases h858 : i.val < 858
        ·
          by_cases h857 : i.val < 857
          ·
            have he : (⟨856, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 856 = i.val
              omega
            simpa only [he] using support0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using support0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using support0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using support0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using support0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using support0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using support0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using support0863

private theorem supportGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h880 : i.val < 880
  ·
    by_cases h872 : i.val < 872
    ·
      by_cases h868 : i.val < 868
      ·
        by_cases h866 : i.val < 866
        ·
          by_cases h865 : i.val < 865
          ·
            have he : (⟨864, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 864 = i.val
              omega
            simpa only [he] using support0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using support0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using support0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using support0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using support0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using support0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using support0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using support0871
    ·
      by_cases h876 : i.val < 876
      ·
        by_cases h874 : i.val < 874
        ·
          by_cases h873 : i.val < 873
          ·
            have he : (⟨872, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 872 = i.val
              omega
            simpa only [he] using support0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using support0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using support0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using support0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using support0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using support0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using support0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using support0879
  ·
    by_cases h888 : i.val < 888
    ·
      by_cases h884 : i.val < 884
      ·
        by_cases h882 : i.val < 882
        ·
          by_cases h881 : i.val < 881
          ·
            have he : (⟨880, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 880 = i.val
              omega
            simpa only [he] using support0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using support0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using support0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using support0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using support0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using support0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using support0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using support0887
    ·
      by_cases h892 : i.val < 892
      ·
        by_cases h890 : i.val < 890
        ·
          by_cases h889 : i.val < 889
          ·
            have he : (⟨888, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 888 = i.val
              omega
            simpa only [he] using support0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using support0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using support0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using support0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using support0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using support0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using support0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using support0895

private theorem supportGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h912 : i.val < 912
  ·
    by_cases h904 : i.val < 904
    ·
      by_cases h900 : i.val < 900
      ·
        by_cases h898 : i.val < 898
        ·
          by_cases h897 : i.val < 897
          ·
            have he : (⟨896, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 896 = i.val
              omega
            simpa only [he] using support0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using support0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using support0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using support0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using support0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using support0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using support0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using support0903
    ·
      by_cases h908 : i.val < 908
      ·
        by_cases h906 : i.val < 906
        ·
          by_cases h905 : i.val < 905
          ·
            have he : (⟨904, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 904 = i.val
              omega
            simpa only [he] using support0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using support0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using support0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using support0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using support0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using support0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using support0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using support0911
  ·
    by_cases h920 : i.val < 920
    ·
      by_cases h916 : i.val < 916
      ·
        by_cases h914 : i.val < 914
        ·
          by_cases h913 : i.val < 913
          ·
            have he : (⟨912, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 912 = i.val
              omega
            simpa only [he] using support0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using support0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using support0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using support0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using support0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using support0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using support0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using support0919
    ·
      by_cases h924 : i.val < 924
      ·
        by_cases h922 : i.val < 922
        ·
          by_cases h921 : i.val < 921
          ·
            have he : (⟨920, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 920 = i.val
              omega
            simpa only [he] using support0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using support0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using support0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using support0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using support0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using support0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using support0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using support0927

private theorem supportGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h944 : i.val < 944
  ·
    by_cases h936 : i.val < 936
    ·
      by_cases h932 : i.val < 932
      ·
        by_cases h930 : i.val < 930
        ·
          by_cases h929 : i.val < 929
          ·
            have he : (⟨928, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 928 = i.val
              omega
            simpa only [he] using support0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using support0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using support0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using support0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using support0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using support0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using support0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using support0935
    ·
      by_cases h940 : i.val < 940
      ·
        by_cases h938 : i.val < 938
        ·
          by_cases h937 : i.val < 937
          ·
            have he : (⟨936, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 936 = i.val
              omega
            simpa only [he] using support0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using support0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using support0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using support0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using support0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using support0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using support0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using support0943
  ·
    by_cases h952 : i.val < 952
    ·
      by_cases h948 : i.val < 948
      ·
        by_cases h946 : i.val < 946
        ·
          by_cases h945 : i.val < 945
          ·
            have he : (⟨944, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 944 = i.val
              omega
            simpa only [he] using support0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using support0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using support0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using support0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using support0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using support0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using support0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using support0951
    ·
      by_cases h956 : i.val < 956
      ·
        by_cases h954 : i.val < 954
        ·
          by_cases h953 : i.val < 953
          ·
            have he : (⟨952, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 952 = i.val
              omega
            simpa only [he] using support0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using support0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using support0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using support0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using support0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using support0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using support0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using support0959

private theorem supportGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h976 : i.val < 976
  ·
    by_cases h968 : i.val < 968
    ·
      by_cases h964 : i.val < 964
      ·
        by_cases h962 : i.val < 962
        ·
          by_cases h961 : i.val < 961
          ·
            have he : (⟨960, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 960 = i.val
              omega
            simpa only [he] using support0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using support0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using support0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using support0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using support0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using support0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using support0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using support0967
    ·
      by_cases h972 : i.val < 972
      ·
        by_cases h970 : i.val < 970
        ·
          by_cases h969 : i.val < 969
          ·
            have he : (⟨968, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 968 = i.val
              omega
            simpa only [he] using support0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using support0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using support0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using support0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using support0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using support0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using support0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using support0975
  ·
    by_cases h984 : i.val < 984
    ·
      by_cases h980 : i.val < 980
      ·
        by_cases h978 : i.val < 978
        ·
          by_cases h977 : i.val < 977
          ·
            have he : (⟨976, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 976 = i.val
              omega
            simpa only [he] using support0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using support0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using support0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using support0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using support0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using support0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using support0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using support0983
    ·
      by_cases h988 : i.val < 988
      ·
        by_cases h986 : i.val < 986
        ·
          by_cases h985 : i.val < 985
          ·
            have he : (⟨984, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 984 = i.val
              omega
            simpa only [he] using support0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using support0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using support0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using support0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using support0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using support0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using support0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using support0991

private theorem supportGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h1008 : i.val < 1008
  ·
    by_cases h1000 : i.val < 1000
    ·
      by_cases h996 : i.val < 996
      ·
        by_cases h994 : i.val < 994
        ·
          by_cases h993 : i.val < 993
          ·
            have he : (⟨992, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 992 = i.val
              omega
            simpa only [he] using support0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using support0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using support0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using support0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using support0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using support0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using support0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using support0999
    ·
      by_cases h1004 : i.val < 1004
      ·
        by_cases h1002 : i.val < 1002
        ·
          by_cases h1001 : i.val < 1001
          ·
            have he : (⟨1000, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1000 = i.val
              omega
            simpa only [he] using support1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using support1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using support1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using support1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using support1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using support1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using support1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using support1007
  ·
    by_cases h1016 : i.val < 1016
    ·
      by_cases h1012 : i.val < 1012
      ·
        by_cases h1010 : i.val < 1010
        ·
          by_cases h1009 : i.val < 1009
          ·
            have he : (⟨1008, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1008 = i.val
              omega
            simpa only [he] using support1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using support1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using support1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using support1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using support1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using support1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using support1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using support1015
    ·
      by_cases h1020 : i.val < 1020
      ·
        by_cases h1018 : i.val < 1018
        ·
          by_cases h1017 : i.val < 1017
          ·
            have he : (⟨1016, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1016 = i.val
              omega
            simpa only [he] using support1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using support1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using support1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using support1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using support1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using support1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using support1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using support1023

private theorem supportGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h1040 : i.val < 1040
  ·
    by_cases h1032 : i.val < 1032
    ·
      by_cases h1028 : i.val < 1028
      ·
        by_cases h1026 : i.val < 1026
        ·
          by_cases h1025 : i.val < 1025
          ·
            have he : (⟨1024, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1024 = i.val
              omega
            simpa only [he] using support1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using support1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using support1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using support1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using support1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using support1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using support1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using support1031
    ·
      by_cases h1036 : i.val < 1036
      ·
        by_cases h1034 : i.val < 1034
        ·
          by_cases h1033 : i.val < 1033
          ·
            have he : (⟨1032, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1032 = i.val
              omega
            simpa only [he] using support1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using support1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using support1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using support1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using support1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using support1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using support1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using support1039
  ·
    by_cases h1048 : i.val < 1048
    ·
      by_cases h1044 : i.val < 1044
      ·
        by_cases h1042 : i.val < 1042
        ·
          by_cases h1041 : i.val < 1041
          ·
            have he : (⟨1040, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1040 = i.val
              omega
            simpa only [he] using support1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using support1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using support1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using support1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using support1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using support1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using support1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using support1047
    ·
      by_cases h1052 : i.val < 1052
      ·
        by_cases h1050 : i.val < 1050
        ·
          by_cases h1049 : i.val < 1049
          ·
            have he : (⟨1048, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1048 = i.val
              omega
            simpa only [he] using support1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using support1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using support1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using support1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using support1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using support1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using support1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using support1055

private theorem supportGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    supportIntersection i = faceMask i := by
  have hi_bound := i.isLt
  by_cases h1062 : i.val < 1062
  ·
    by_cases h1059 : i.val < 1059
    ·
      by_cases h1057 : i.val < 1057
      ·
        have he : (⟨1056, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1056 = i.val
          omega
        simpa only [he] using support1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using support1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using support1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using support1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using support1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using support1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using support1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using support1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using support1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using support1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using support1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using support1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using support1068

private theorem supportIntersection_eq : ∀ i : Fin 1069,
    supportIntersection i = faceMask i := by
  intro i
  have hi_bound := i.isLt
  by_cases h544 : i.val < 544
  ·
    by_cases h256 : i.val < 256
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            exact supportGroup0000 i (by omega) (by omega)
          ·
            exact supportGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact supportGroup0002 i (by omega) (by omega)
          ·
            exact supportGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact supportGroup0004 i (by omega) (by omega)
          ·
            exact supportGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact supportGroup0006 i (by omega) (by omega)
          ·
            exact supportGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact supportGroup0008 i (by omega) (by omega)
          ·
            exact supportGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact supportGroup0010 i (by omega) (by omega)
          ·
            exact supportGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact supportGroup0012 i (by omega) (by omega)
          ·
            exact supportGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact supportGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact supportGroup0015 i (by omega) (by omega)
            ·
              exact supportGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact supportGroup0017 i (by omega) (by omega)
          ·
            exact supportGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact supportGroup0019 i (by omega) (by omega)
          ·
            exact supportGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact supportGroup0021 i (by omega) (by omega)
          ·
            exact supportGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact supportGroup0023 i (by omega) (by omega)
          ·
            exact supportGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact supportGroup0025 i (by omega) (by omega)
          ·
            exact supportGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact supportGroup0027 i (by omega) (by omega)
          ·
            exact supportGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact supportGroup0029 i (by omega) (by omega)
          ·
            exact supportGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact supportGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact supportGroup0032 i (by omega) (by omega)
            ·
              exact supportGroup0033 i (by omega) (by omega)

/-- Every selected support intersection is exactly its stated face mask. -/
theorem supportRows_identity : ∀ (i : Fin 1069) (v : Fin 144),
    v ∈ faceMask i ↔ ∀ f ∈ supportRows i, incident f v := by
  intro i v
  rw [← supportIntersection_eq i]
  exact mem_supportIntersection i v

end CubicalIndecomposability
