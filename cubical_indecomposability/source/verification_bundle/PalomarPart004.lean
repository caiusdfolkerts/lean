module
public import verification_bundle.PalomarPart003
import all verification_bundle.PalomarPart003
public import foundation_bundle
public import incidence_bundle
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See VerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/LowerFacets.lean -/
section VerificationSource001




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
def bundle_7fec005515_supportIntersection (i : Fin 1069) : Finset (Fin 144) :=
  if h : (supportRows i).Nonempty then
    (supportRows i).inf' h facetLabels
  else Finset.univ

theorem bundle_7fec005515_mem_supportIntersection (i : Fin 1069) (v : Fin 144) :
    v ∈ bundle_7fec005515_supportIntersection i ↔ ∀ f ∈ supportRows i, incident f v := by
  unfold bundle_7fec005515_supportIntersection
  split_ifs with h
  · simpa only [Finset.mem_inf', incident]
  · have he : supportRows i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem bundle_7fec005515_support0000 : bundle_7fec005515_supportIntersection (⟨0, by decide⟩ : Fin 1069) = faceMask (⟨0, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0001 : bundle_7fec005515_supportIntersection (⟨1, by decide⟩ : Fin 1069) = faceMask (⟨1, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0002 : bundle_7fec005515_supportIntersection (⟨2, by decide⟩ : Fin 1069) = faceMask (⟨2, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0003 : bundle_7fec005515_supportIntersection (⟨3, by decide⟩ : Fin 1069) = faceMask (⟨3, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0004 : bundle_7fec005515_supportIntersection (⟨4, by decide⟩ : Fin 1069) = faceMask (⟨4, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0005 : bundle_7fec005515_supportIntersection (⟨5, by decide⟩ : Fin 1069) = faceMask (⟨5, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0006 : bundle_7fec005515_supportIntersection (⟨6, by decide⟩ : Fin 1069) = faceMask (⟨6, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0007 : bundle_7fec005515_supportIntersection (⟨7, by decide⟩ : Fin 1069) = faceMask (⟨7, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0008 : bundle_7fec005515_supportIntersection (⟨8, by decide⟩ : Fin 1069) = faceMask (⟨8, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0009 : bundle_7fec005515_supportIntersection (⟨9, by decide⟩ : Fin 1069) = faceMask (⟨9, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0010 : bundle_7fec005515_supportIntersection (⟨10, by decide⟩ : Fin 1069) = faceMask (⟨10, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0011 : bundle_7fec005515_supportIntersection (⟨11, by decide⟩ : Fin 1069) = faceMask (⟨11, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0012 : bundle_7fec005515_supportIntersection (⟨12, by decide⟩ : Fin 1069) = faceMask (⟨12, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0013 : bundle_7fec005515_supportIntersection (⟨13, by decide⟩ : Fin 1069) = faceMask (⟨13, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0014 : bundle_7fec005515_supportIntersection (⟨14, by decide⟩ : Fin 1069) = faceMask (⟨14, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0015 : bundle_7fec005515_supportIntersection (⟨15, by decide⟩ : Fin 1069) = faceMask (⟨15, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0016 : bundle_7fec005515_supportIntersection (⟨16, by decide⟩ : Fin 1069) = faceMask (⟨16, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0017 : bundle_7fec005515_supportIntersection (⟨17, by decide⟩ : Fin 1069) = faceMask (⟨17, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0018 : bundle_7fec005515_supportIntersection (⟨18, by decide⟩ : Fin 1069) = faceMask (⟨18, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0019 : bundle_7fec005515_supportIntersection (⟨19, by decide⟩ : Fin 1069) = faceMask (⟨19, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0020 : bundle_7fec005515_supportIntersection (⟨20, by decide⟩ : Fin 1069) = faceMask (⟨20, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0021 : bundle_7fec005515_supportIntersection (⟨21, by decide⟩ : Fin 1069) = faceMask (⟨21, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0022 : bundle_7fec005515_supportIntersection (⟨22, by decide⟩ : Fin 1069) = faceMask (⟨22, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0023 : bundle_7fec005515_supportIntersection (⟨23, by decide⟩ : Fin 1069) = faceMask (⟨23, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0024 : bundle_7fec005515_supportIntersection (⟨24, by decide⟩ : Fin 1069) = faceMask (⟨24, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0025 : bundle_7fec005515_supportIntersection (⟨25, by decide⟩ : Fin 1069) = faceMask (⟨25, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0026 : bundle_7fec005515_supportIntersection (⟨26, by decide⟩ : Fin 1069) = faceMask (⟨26, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0027 : bundle_7fec005515_supportIntersection (⟨27, by decide⟩ : Fin 1069) = faceMask (⟨27, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0028 : bundle_7fec005515_supportIntersection (⟨28, by decide⟩ : Fin 1069) = faceMask (⟨28, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0029 : bundle_7fec005515_supportIntersection (⟨29, by decide⟩ : Fin 1069) = faceMask (⟨29, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0030 : bundle_7fec005515_supportIntersection (⟨30, by decide⟩ : Fin 1069) = faceMask (⟨30, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0031 : bundle_7fec005515_supportIntersection (⟨31, by decide⟩ : Fin 1069) = faceMask (⟨31, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0032 : bundle_7fec005515_supportIntersection (⟨32, by decide⟩ : Fin 1069) = faceMask (⟨32, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0033 : bundle_7fec005515_supportIntersection (⟨33, by decide⟩ : Fin 1069) = faceMask (⟨33, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0034 : bundle_7fec005515_supportIntersection (⟨34, by decide⟩ : Fin 1069) = faceMask (⟨34, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0035 : bundle_7fec005515_supportIntersection (⟨35, by decide⟩ : Fin 1069) = faceMask (⟨35, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0036 : bundle_7fec005515_supportIntersection (⟨36, by decide⟩ : Fin 1069) = faceMask (⟨36, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0037 : bundle_7fec005515_supportIntersection (⟨37, by decide⟩ : Fin 1069) = faceMask (⟨37, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0038 : bundle_7fec005515_supportIntersection (⟨38, by decide⟩ : Fin 1069) = faceMask (⟨38, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0039 : bundle_7fec005515_supportIntersection (⟨39, by decide⟩ : Fin 1069) = faceMask (⟨39, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0040 : bundle_7fec005515_supportIntersection (⟨40, by decide⟩ : Fin 1069) = faceMask (⟨40, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0041 : bundle_7fec005515_supportIntersection (⟨41, by decide⟩ : Fin 1069) = faceMask (⟨41, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0042 : bundle_7fec005515_supportIntersection (⟨42, by decide⟩ : Fin 1069) = faceMask (⟨42, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0043 : bundle_7fec005515_supportIntersection (⟨43, by decide⟩ : Fin 1069) = faceMask (⟨43, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0044 : bundle_7fec005515_supportIntersection (⟨44, by decide⟩ : Fin 1069) = faceMask (⟨44, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0045 : bundle_7fec005515_supportIntersection (⟨45, by decide⟩ : Fin 1069) = faceMask (⟨45, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0046 : bundle_7fec005515_supportIntersection (⟨46, by decide⟩ : Fin 1069) = faceMask (⟨46, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0047 : bundle_7fec005515_supportIntersection (⟨47, by decide⟩ : Fin 1069) = faceMask (⟨47, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0048 : bundle_7fec005515_supportIntersection (⟨48, by decide⟩ : Fin 1069) = faceMask (⟨48, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0049 : bundle_7fec005515_supportIntersection (⟨49, by decide⟩ : Fin 1069) = faceMask (⟨49, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0050 : bundle_7fec005515_supportIntersection (⟨50, by decide⟩ : Fin 1069) = faceMask (⟨50, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0051 : bundle_7fec005515_supportIntersection (⟨51, by decide⟩ : Fin 1069) = faceMask (⟨51, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0052 : bundle_7fec005515_supportIntersection (⟨52, by decide⟩ : Fin 1069) = faceMask (⟨52, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0053 : bundle_7fec005515_supportIntersection (⟨53, by decide⟩ : Fin 1069) = faceMask (⟨53, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0054 : bundle_7fec005515_supportIntersection (⟨54, by decide⟩ : Fin 1069) = faceMask (⟨54, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0055 : bundle_7fec005515_supportIntersection (⟨55, by decide⟩ : Fin 1069) = faceMask (⟨55, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0056 : bundle_7fec005515_supportIntersection (⟨56, by decide⟩ : Fin 1069) = faceMask (⟨56, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0057 : bundle_7fec005515_supportIntersection (⟨57, by decide⟩ : Fin 1069) = faceMask (⟨57, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0058 : bundle_7fec005515_supportIntersection (⟨58, by decide⟩ : Fin 1069) = faceMask (⟨58, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0059 : bundle_7fec005515_supportIntersection (⟨59, by decide⟩ : Fin 1069) = faceMask (⟨59, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0060 : bundle_7fec005515_supportIntersection (⟨60, by decide⟩ : Fin 1069) = faceMask (⟨60, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0061 : bundle_7fec005515_supportIntersection (⟨61, by decide⟩ : Fin 1069) = faceMask (⟨61, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0062 : bundle_7fec005515_supportIntersection (⟨62, by decide⟩ : Fin 1069) = faceMask (⟨62, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0063 : bundle_7fec005515_supportIntersection (⟨63, by decide⟩ : Fin 1069) = faceMask (⟨63, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0064 : bundle_7fec005515_supportIntersection (⟨64, by decide⟩ : Fin 1069) = faceMask (⟨64, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0065 : bundle_7fec005515_supportIntersection (⟨65, by decide⟩ : Fin 1069) = faceMask (⟨65, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0066 : bundle_7fec005515_supportIntersection (⟨66, by decide⟩ : Fin 1069) = faceMask (⟨66, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0067 : bundle_7fec005515_supportIntersection (⟨67, by decide⟩ : Fin 1069) = faceMask (⟨67, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0068 : bundle_7fec005515_supportIntersection (⟨68, by decide⟩ : Fin 1069) = faceMask (⟨68, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0069 : bundle_7fec005515_supportIntersection (⟨69, by decide⟩ : Fin 1069) = faceMask (⟨69, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0070 : bundle_7fec005515_supportIntersection (⟨70, by decide⟩ : Fin 1069) = faceMask (⟨70, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0071 : bundle_7fec005515_supportIntersection (⟨71, by decide⟩ : Fin 1069) = faceMask (⟨71, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0072 : bundle_7fec005515_supportIntersection (⟨72, by decide⟩ : Fin 1069) = faceMask (⟨72, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0073 : bundle_7fec005515_supportIntersection (⟨73, by decide⟩ : Fin 1069) = faceMask (⟨73, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0074 : bundle_7fec005515_supportIntersection (⟨74, by decide⟩ : Fin 1069) = faceMask (⟨74, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0075 : bundle_7fec005515_supportIntersection (⟨75, by decide⟩ : Fin 1069) = faceMask (⟨75, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0076 : bundle_7fec005515_supportIntersection (⟨76, by decide⟩ : Fin 1069) = faceMask (⟨76, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0077 : bundle_7fec005515_supportIntersection (⟨77, by decide⟩ : Fin 1069) = faceMask (⟨77, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0078 : bundle_7fec005515_supportIntersection (⟨78, by decide⟩ : Fin 1069) = faceMask (⟨78, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0079 : bundle_7fec005515_supportIntersection (⟨79, by decide⟩ : Fin 1069) = faceMask (⟨79, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0080 : bundle_7fec005515_supportIntersection (⟨80, by decide⟩ : Fin 1069) = faceMask (⟨80, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0081 : bundle_7fec005515_supportIntersection (⟨81, by decide⟩ : Fin 1069) = faceMask (⟨81, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0082 : bundle_7fec005515_supportIntersection (⟨82, by decide⟩ : Fin 1069) = faceMask (⟨82, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0083 : bundle_7fec005515_supportIntersection (⟨83, by decide⟩ : Fin 1069) = faceMask (⟨83, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0084 : bundle_7fec005515_supportIntersection (⟨84, by decide⟩ : Fin 1069) = faceMask (⟨84, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0085 : bundle_7fec005515_supportIntersection (⟨85, by decide⟩ : Fin 1069) = faceMask (⟨85, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0086 : bundle_7fec005515_supportIntersection (⟨86, by decide⟩ : Fin 1069) = faceMask (⟨86, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0087 : bundle_7fec005515_supportIntersection (⟨87, by decide⟩ : Fin 1069) = faceMask (⟨87, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0088 : bundle_7fec005515_supportIntersection (⟨88, by decide⟩ : Fin 1069) = faceMask (⟨88, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0089 : bundle_7fec005515_supportIntersection (⟨89, by decide⟩ : Fin 1069) = faceMask (⟨89, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0090 : bundle_7fec005515_supportIntersection (⟨90, by decide⟩ : Fin 1069) = faceMask (⟨90, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0091 : bundle_7fec005515_supportIntersection (⟨91, by decide⟩ : Fin 1069) = faceMask (⟨91, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0092 : bundle_7fec005515_supportIntersection (⟨92, by decide⟩ : Fin 1069) = faceMask (⟨92, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0093 : bundle_7fec005515_supportIntersection (⟨93, by decide⟩ : Fin 1069) = faceMask (⟨93, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0094 : bundle_7fec005515_supportIntersection (⟨94, by decide⟩ : Fin 1069) = faceMask (⟨94, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0095 : bundle_7fec005515_supportIntersection (⟨95, by decide⟩ : Fin 1069) = faceMask (⟨95, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0096 : bundle_7fec005515_supportIntersection (⟨96, by decide⟩ : Fin 1069) = faceMask (⟨96, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0097 : bundle_7fec005515_supportIntersection (⟨97, by decide⟩ : Fin 1069) = faceMask (⟨97, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0098 : bundle_7fec005515_supportIntersection (⟨98, by decide⟩ : Fin 1069) = faceMask (⟨98, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0099 : bundle_7fec005515_supportIntersection (⟨99, by decide⟩ : Fin 1069) = faceMask (⟨99, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0100 : bundle_7fec005515_supportIntersection (⟨100, by decide⟩ : Fin 1069) = faceMask (⟨100, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0101 : bundle_7fec005515_supportIntersection (⟨101, by decide⟩ : Fin 1069) = faceMask (⟨101, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0102 : bundle_7fec005515_supportIntersection (⟨102, by decide⟩ : Fin 1069) = faceMask (⟨102, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0103 : bundle_7fec005515_supportIntersection (⟨103, by decide⟩ : Fin 1069) = faceMask (⟨103, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0104 : bundle_7fec005515_supportIntersection (⟨104, by decide⟩ : Fin 1069) = faceMask (⟨104, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0105 : bundle_7fec005515_supportIntersection (⟨105, by decide⟩ : Fin 1069) = faceMask (⟨105, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0106 : bundle_7fec005515_supportIntersection (⟨106, by decide⟩ : Fin 1069) = faceMask (⟨106, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0107 : bundle_7fec005515_supportIntersection (⟨107, by decide⟩ : Fin 1069) = faceMask (⟨107, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0108 : bundle_7fec005515_supportIntersection (⟨108, by decide⟩ : Fin 1069) = faceMask (⟨108, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0109 : bundle_7fec005515_supportIntersection (⟨109, by decide⟩ : Fin 1069) = faceMask (⟨109, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0110 : bundle_7fec005515_supportIntersection (⟨110, by decide⟩ : Fin 1069) = faceMask (⟨110, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0111 : bundle_7fec005515_supportIntersection (⟨111, by decide⟩ : Fin 1069) = faceMask (⟨111, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0112 : bundle_7fec005515_supportIntersection (⟨112, by decide⟩ : Fin 1069) = faceMask (⟨112, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0113 : bundle_7fec005515_supportIntersection (⟨113, by decide⟩ : Fin 1069) = faceMask (⟨113, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0114 : bundle_7fec005515_supportIntersection (⟨114, by decide⟩ : Fin 1069) = faceMask (⟨114, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0115 : bundle_7fec005515_supportIntersection (⟨115, by decide⟩ : Fin 1069) = faceMask (⟨115, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0116 : bundle_7fec005515_supportIntersection (⟨116, by decide⟩ : Fin 1069) = faceMask (⟨116, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0117 : bundle_7fec005515_supportIntersection (⟨117, by decide⟩ : Fin 1069) = faceMask (⟨117, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0118 : bundle_7fec005515_supportIntersection (⟨118, by decide⟩ : Fin 1069) = faceMask (⟨118, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0119 : bundle_7fec005515_supportIntersection (⟨119, by decide⟩ : Fin 1069) = faceMask (⟨119, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0120 : bundle_7fec005515_supportIntersection (⟨120, by decide⟩ : Fin 1069) = faceMask (⟨120, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0121 : bundle_7fec005515_supportIntersection (⟨121, by decide⟩ : Fin 1069) = faceMask (⟨121, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0122 : bundle_7fec005515_supportIntersection (⟨122, by decide⟩ : Fin 1069) = faceMask (⟨122, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0123 : bundle_7fec005515_supportIntersection (⟨123, by decide⟩ : Fin 1069) = faceMask (⟨123, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0124 : bundle_7fec005515_supportIntersection (⟨124, by decide⟩ : Fin 1069) = faceMask (⟨124, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0125 : bundle_7fec005515_supportIntersection (⟨125, by decide⟩ : Fin 1069) = faceMask (⟨125, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0126 : bundle_7fec005515_supportIntersection (⟨126, by decide⟩ : Fin 1069) = faceMask (⟨126, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0127 : bundle_7fec005515_supportIntersection (⟨127, by decide⟩ : Fin 1069) = faceMask (⟨127, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0128 : bundle_7fec005515_supportIntersection (⟨128, by decide⟩ : Fin 1069) = faceMask (⟨128, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0129 : bundle_7fec005515_supportIntersection (⟨129, by decide⟩ : Fin 1069) = faceMask (⟨129, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0130 : bundle_7fec005515_supportIntersection (⟨130, by decide⟩ : Fin 1069) = faceMask (⟨130, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0131 : bundle_7fec005515_supportIntersection (⟨131, by decide⟩ : Fin 1069) = faceMask (⟨131, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0132 : bundle_7fec005515_supportIntersection (⟨132, by decide⟩ : Fin 1069) = faceMask (⟨132, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0133 : bundle_7fec005515_supportIntersection (⟨133, by decide⟩ : Fin 1069) = faceMask (⟨133, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0134 : bundle_7fec005515_supportIntersection (⟨134, by decide⟩ : Fin 1069) = faceMask (⟨134, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0135 : bundle_7fec005515_supportIntersection (⟨135, by decide⟩ : Fin 1069) = faceMask (⟨135, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0136 : bundle_7fec005515_supportIntersection (⟨136, by decide⟩ : Fin 1069) = faceMask (⟨136, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0137 : bundle_7fec005515_supportIntersection (⟨137, by decide⟩ : Fin 1069) = faceMask (⟨137, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0138 : bundle_7fec005515_supportIntersection (⟨138, by decide⟩ : Fin 1069) = faceMask (⟨138, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0139 : bundle_7fec005515_supportIntersection (⟨139, by decide⟩ : Fin 1069) = faceMask (⟨139, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0140 : bundle_7fec005515_supportIntersection (⟨140, by decide⟩ : Fin 1069) = faceMask (⟨140, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0141 : bundle_7fec005515_supportIntersection (⟨141, by decide⟩ : Fin 1069) = faceMask (⟨141, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0142 : bundle_7fec005515_supportIntersection (⟨142, by decide⟩ : Fin 1069) = faceMask (⟨142, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0143 : bundle_7fec005515_supportIntersection (⟨143, by decide⟩ : Fin 1069) = faceMask (⟨143, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0144 : bundle_7fec005515_supportIntersection (⟨144, by decide⟩ : Fin 1069) = faceMask (⟨144, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0145 : bundle_7fec005515_supportIntersection (⟨145, by decide⟩ : Fin 1069) = faceMask (⟨145, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0146 : bundle_7fec005515_supportIntersection (⟨146, by decide⟩ : Fin 1069) = faceMask (⟨146, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0147 : bundle_7fec005515_supportIntersection (⟨147, by decide⟩ : Fin 1069) = faceMask (⟨147, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0148 : bundle_7fec005515_supportIntersection (⟨148, by decide⟩ : Fin 1069) = faceMask (⟨148, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0149 : bundle_7fec005515_supportIntersection (⟨149, by decide⟩ : Fin 1069) = faceMask (⟨149, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0150 : bundle_7fec005515_supportIntersection (⟨150, by decide⟩ : Fin 1069) = faceMask (⟨150, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0151 : bundle_7fec005515_supportIntersection (⟨151, by decide⟩ : Fin 1069) = faceMask (⟨151, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0152 : bundle_7fec005515_supportIntersection (⟨152, by decide⟩ : Fin 1069) = faceMask (⟨152, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0153 : bundle_7fec005515_supportIntersection (⟨153, by decide⟩ : Fin 1069) = faceMask (⟨153, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0154 : bundle_7fec005515_supportIntersection (⟨154, by decide⟩ : Fin 1069) = faceMask (⟨154, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0155 : bundle_7fec005515_supportIntersection (⟨155, by decide⟩ : Fin 1069) = faceMask (⟨155, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0156 : bundle_7fec005515_supportIntersection (⟨156, by decide⟩ : Fin 1069) = faceMask (⟨156, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0157 : bundle_7fec005515_supportIntersection (⟨157, by decide⟩ : Fin 1069) = faceMask (⟨157, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0158 : bundle_7fec005515_supportIntersection (⟨158, by decide⟩ : Fin 1069) = faceMask (⟨158, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0159 : bundle_7fec005515_supportIntersection (⟨159, by decide⟩ : Fin 1069) = faceMask (⟨159, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0160 : bundle_7fec005515_supportIntersection (⟨160, by decide⟩ : Fin 1069) = faceMask (⟨160, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0161 : bundle_7fec005515_supportIntersection (⟨161, by decide⟩ : Fin 1069) = faceMask (⟨161, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0162 : bundle_7fec005515_supportIntersection (⟨162, by decide⟩ : Fin 1069) = faceMask (⟨162, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0163 : bundle_7fec005515_supportIntersection (⟨163, by decide⟩ : Fin 1069) = faceMask (⟨163, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0164 : bundle_7fec005515_supportIntersection (⟨164, by decide⟩ : Fin 1069) = faceMask (⟨164, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0165 : bundle_7fec005515_supportIntersection (⟨165, by decide⟩ : Fin 1069) = faceMask (⟨165, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0166 : bundle_7fec005515_supportIntersection (⟨166, by decide⟩ : Fin 1069) = faceMask (⟨166, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0167 : bundle_7fec005515_supportIntersection (⟨167, by decide⟩ : Fin 1069) = faceMask (⟨167, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0168 : bundle_7fec005515_supportIntersection (⟨168, by decide⟩ : Fin 1069) = faceMask (⟨168, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0169 : bundle_7fec005515_supportIntersection (⟨169, by decide⟩ : Fin 1069) = faceMask (⟨169, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0170 : bundle_7fec005515_supportIntersection (⟨170, by decide⟩ : Fin 1069) = faceMask (⟨170, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0171 : bundle_7fec005515_supportIntersection (⟨171, by decide⟩ : Fin 1069) = faceMask (⟨171, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0172 : bundle_7fec005515_supportIntersection (⟨172, by decide⟩ : Fin 1069) = faceMask (⟨172, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0173 : bundle_7fec005515_supportIntersection (⟨173, by decide⟩ : Fin 1069) = faceMask (⟨173, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0174 : bundle_7fec005515_supportIntersection (⟨174, by decide⟩ : Fin 1069) = faceMask (⟨174, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0175 : bundle_7fec005515_supportIntersection (⟨175, by decide⟩ : Fin 1069) = faceMask (⟨175, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0176 : bundle_7fec005515_supportIntersection (⟨176, by decide⟩ : Fin 1069) = faceMask (⟨176, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0177 : bundle_7fec005515_supportIntersection (⟨177, by decide⟩ : Fin 1069) = faceMask (⟨177, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0178 : bundle_7fec005515_supportIntersection (⟨178, by decide⟩ : Fin 1069) = faceMask (⟨178, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0179 : bundle_7fec005515_supportIntersection (⟨179, by decide⟩ : Fin 1069) = faceMask (⟨179, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0180 : bundle_7fec005515_supportIntersection (⟨180, by decide⟩ : Fin 1069) = faceMask (⟨180, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0181 : bundle_7fec005515_supportIntersection (⟨181, by decide⟩ : Fin 1069) = faceMask (⟨181, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0182 : bundle_7fec005515_supportIntersection (⟨182, by decide⟩ : Fin 1069) = faceMask (⟨182, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0183 : bundle_7fec005515_supportIntersection (⟨183, by decide⟩ : Fin 1069) = faceMask (⟨183, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0184 : bundle_7fec005515_supportIntersection (⟨184, by decide⟩ : Fin 1069) = faceMask (⟨184, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0185 : bundle_7fec005515_supportIntersection (⟨185, by decide⟩ : Fin 1069) = faceMask (⟨185, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0186 : bundle_7fec005515_supportIntersection (⟨186, by decide⟩ : Fin 1069) = faceMask (⟨186, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0187 : bundle_7fec005515_supportIntersection (⟨187, by decide⟩ : Fin 1069) = faceMask (⟨187, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0188 : bundle_7fec005515_supportIntersection (⟨188, by decide⟩ : Fin 1069) = faceMask (⟨188, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0189 : bundle_7fec005515_supportIntersection (⟨189, by decide⟩ : Fin 1069) = faceMask (⟨189, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0190 : bundle_7fec005515_supportIntersection (⟨190, by decide⟩ : Fin 1069) = faceMask (⟨190, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0191 : bundle_7fec005515_supportIntersection (⟨191, by decide⟩ : Fin 1069) = faceMask (⟨191, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0192 : bundle_7fec005515_supportIntersection (⟨192, by decide⟩ : Fin 1069) = faceMask (⟨192, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0193 : bundle_7fec005515_supportIntersection (⟨193, by decide⟩ : Fin 1069) = faceMask (⟨193, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0194 : bundle_7fec005515_supportIntersection (⟨194, by decide⟩ : Fin 1069) = faceMask (⟨194, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0195 : bundle_7fec005515_supportIntersection (⟨195, by decide⟩ : Fin 1069) = faceMask (⟨195, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0196 : bundle_7fec005515_supportIntersection (⟨196, by decide⟩ : Fin 1069) = faceMask (⟨196, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0197 : bundle_7fec005515_supportIntersection (⟨197, by decide⟩ : Fin 1069) = faceMask (⟨197, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0198 : bundle_7fec005515_supportIntersection (⟨198, by decide⟩ : Fin 1069) = faceMask (⟨198, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0199 : bundle_7fec005515_supportIntersection (⟨199, by decide⟩ : Fin 1069) = faceMask (⟨199, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0200 : bundle_7fec005515_supportIntersection (⟨200, by decide⟩ : Fin 1069) = faceMask (⟨200, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0201 : bundle_7fec005515_supportIntersection (⟨201, by decide⟩ : Fin 1069) = faceMask (⟨201, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0202 : bundle_7fec005515_supportIntersection (⟨202, by decide⟩ : Fin 1069) = faceMask (⟨202, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0203 : bundle_7fec005515_supportIntersection (⟨203, by decide⟩ : Fin 1069) = faceMask (⟨203, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0204 : bundle_7fec005515_supportIntersection (⟨204, by decide⟩ : Fin 1069) = faceMask (⟨204, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0205 : bundle_7fec005515_supportIntersection (⟨205, by decide⟩ : Fin 1069) = faceMask (⟨205, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0206 : bundle_7fec005515_supportIntersection (⟨206, by decide⟩ : Fin 1069) = faceMask (⟨206, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0207 : bundle_7fec005515_supportIntersection (⟨207, by decide⟩ : Fin 1069) = faceMask (⟨207, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0208 : bundle_7fec005515_supportIntersection (⟨208, by decide⟩ : Fin 1069) = faceMask (⟨208, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0209 : bundle_7fec005515_supportIntersection (⟨209, by decide⟩ : Fin 1069) = faceMask (⟨209, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0210 : bundle_7fec005515_supportIntersection (⟨210, by decide⟩ : Fin 1069) = faceMask (⟨210, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0211 : bundle_7fec005515_supportIntersection (⟨211, by decide⟩ : Fin 1069) = faceMask (⟨211, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0212 : bundle_7fec005515_supportIntersection (⟨212, by decide⟩ : Fin 1069) = faceMask (⟨212, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0213 : bundle_7fec005515_supportIntersection (⟨213, by decide⟩ : Fin 1069) = faceMask (⟨213, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0214 : bundle_7fec005515_supportIntersection (⟨214, by decide⟩ : Fin 1069) = faceMask (⟨214, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0215 : bundle_7fec005515_supportIntersection (⟨215, by decide⟩ : Fin 1069) = faceMask (⟨215, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0216 : bundle_7fec005515_supportIntersection (⟨216, by decide⟩ : Fin 1069) = faceMask (⟨216, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0217 : bundle_7fec005515_supportIntersection (⟨217, by decide⟩ : Fin 1069) = faceMask (⟨217, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0218 : bundle_7fec005515_supportIntersection (⟨218, by decide⟩ : Fin 1069) = faceMask (⟨218, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0219 : bundle_7fec005515_supportIntersection (⟨219, by decide⟩ : Fin 1069) = faceMask (⟨219, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0220 : bundle_7fec005515_supportIntersection (⟨220, by decide⟩ : Fin 1069) = faceMask (⟨220, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0221 : bundle_7fec005515_supportIntersection (⟨221, by decide⟩ : Fin 1069) = faceMask (⟨221, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0222 : bundle_7fec005515_supportIntersection (⟨222, by decide⟩ : Fin 1069) = faceMask (⟨222, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0223 : bundle_7fec005515_supportIntersection (⟨223, by decide⟩ : Fin 1069) = faceMask (⟨223, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0224 : bundle_7fec005515_supportIntersection (⟨224, by decide⟩ : Fin 1069) = faceMask (⟨224, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0225 : bundle_7fec005515_supportIntersection (⟨225, by decide⟩ : Fin 1069) = faceMask (⟨225, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0226 : bundle_7fec005515_supportIntersection (⟨226, by decide⟩ : Fin 1069) = faceMask (⟨226, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0227 : bundle_7fec005515_supportIntersection (⟨227, by decide⟩ : Fin 1069) = faceMask (⟨227, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0228 : bundle_7fec005515_supportIntersection (⟨228, by decide⟩ : Fin 1069) = faceMask (⟨228, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0229 : bundle_7fec005515_supportIntersection (⟨229, by decide⟩ : Fin 1069) = faceMask (⟨229, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0230 : bundle_7fec005515_supportIntersection (⟨230, by decide⟩ : Fin 1069) = faceMask (⟨230, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0231 : bundle_7fec005515_supportIntersection (⟨231, by decide⟩ : Fin 1069) = faceMask (⟨231, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0232 : bundle_7fec005515_supportIntersection (⟨232, by decide⟩ : Fin 1069) = faceMask (⟨232, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0233 : bundle_7fec005515_supportIntersection (⟨233, by decide⟩ : Fin 1069) = faceMask (⟨233, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0234 : bundle_7fec005515_supportIntersection (⟨234, by decide⟩ : Fin 1069) = faceMask (⟨234, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0235 : bundle_7fec005515_supportIntersection (⟨235, by decide⟩ : Fin 1069) = faceMask (⟨235, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0236 : bundle_7fec005515_supportIntersection (⟨236, by decide⟩ : Fin 1069) = faceMask (⟨236, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0237 : bundle_7fec005515_supportIntersection (⟨237, by decide⟩ : Fin 1069) = faceMask (⟨237, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0238 : bundle_7fec005515_supportIntersection (⟨238, by decide⟩ : Fin 1069) = faceMask (⟨238, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0239 : bundle_7fec005515_supportIntersection (⟨239, by decide⟩ : Fin 1069) = faceMask (⟨239, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0240 : bundle_7fec005515_supportIntersection (⟨240, by decide⟩ : Fin 1069) = faceMask (⟨240, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0241 : bundle_7fec005515_supportIntersection (⟨241, by decide⟩ : Fin 1069) = faceMask (⟨241, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0242 : bundle_7fec005515_supportIntersection (⟨242, by decide⟩ : Fin 1069) = faceMask (⟨242, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0243 : bundle_7fec005515_supportIntersection (⟨243, by decide⟩ : Fin 1069) = faceMask (⟨243, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0244 : bundle_7fec005515_supportIntersection (⟨244, by decide⟩ : Fin 1069) = faceMask (⟨244, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0245 : bundle_7fec005515_supportIntersection (⟨245, by decide⟩ : Fin 1069) = faceMask (⟨245, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0246 : bundle_7fec005515_supportIntersection (⟨246, by decide⟩ : Fin 1069) = faceMask (⟨246, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0247 : bundle_7fec005515_supportIntersection (⟨247, by decide⟩ : Fin 1069) = faceMask (⟨247, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0248 : bundle_7fec005515_supportIntersection (⟨248, by decide⟩ : Fin 1069) = faceMask (⟨248, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0249 : bundle_7fec005515_supportIntersection (⟨249, by decide⟩ : Fin 1069) = faceMask (⟨249, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0250 : bundle_7fec005515_supportIntersection (⟨250, by decide⟩ : Fin 1069) = faceMask (⟨250, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0251 : bundle_7fec005515_supportIntersection (⟨251, by decide⟩ : Fin 1069) = faceMask (⟨251, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0252 : bundle_7fec005515_supportIntersection (⟨252, by decide⟩ : Fin 1069) = faceMask (⟨252, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0253 : bundle_7fec005515_supportIntersection (⟨253, by decide⟩ : Fin 1069) = faceMask (⟨253, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0254 : bundle_7fec005515_supportIntersection (⟨254, by decide⟩ : Fin 1069) = faceMask (⟨254, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0255 : bundle_7fec005515_supportIntersection (⟨255, by decide⟩ : Fin 1069) = faceMask (⟨255, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0256 : bundle_7fec005515_supportIntersection (⟨256, by decide⟩ : Fin 1069) = faceMask (⟨256, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0257 : bundle_7fec005515_supportIntersection (⟨257, by decide⟩ : Fin 1069) = faceMask (⟨257, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0258 : bundle_7fec005515_supportIntersection (⟨258, by decide⟩ : Fin 1069) = faceMask (⟨258, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0259 : bundle_7fec005515_supportIntersection (⟨259, by decide⟩ : Fin 1069) = faceMask (⟨259, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0260 : bundle_7fec005515_supportIntersection (⟨260, by decide⟩ : Fin 1069) = faceMask (⟨260, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0261 : bundle_7fec005515_supportIntersection (⟨261, by decide⟩ : Fin 1069) = faceMask (⟨261, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0262 : bundle_7fec005515_supportIntersection (⟨262, by decide⟩ : Fin 1069) = faceMask (⟨262, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0263 : bundle_7fec005515_supportIntersection (⟨263, by decide⟩ : Fin 1069) = faceMask (⟨263, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0264 : bundle_7fec005515_supportIntersection (⟨264, by decide⟩ : Fin 1069) = faceMask (⟨264, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0265 : bundle_7fec005515_supportIntersection (⟨265, by decide⟩ : Fin 1069) = faceMask (⟨265, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0266 : bundle_7fec005515_supportIntersection (⟨266, by decide⟩ : Fin 1069) = faceMask (⟨266, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0267 : bundle_7fec005515_supportIntersection (⟨267, by decide⟩ : Fin 1069) = faceMask (⟨267, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0268 : bundle_7fec005515_supportIntersection (⟨268, by decide⟩ : Fin 1069) = faceMask (⟨268, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0269 : bundle_7fec005515_supportIntersection (⟨269, by decide⟩ : Fin 1069) = faceMask (⟨269, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0270 : bundle_7fec005515_supportIntersection (⟨270, by decide⟩ : Fin 1069) = faceMask (⟨270, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0271 : bundle_7fec005515_supportIntersection (⟨271, by decide⟩ : Fin 1069) = faceMask (⟨271, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0272 : bundle_7fec005515_supportIntersection (⟨272, by decide⟩ : Fin 1069) = faceMask (⟨272, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0273 : bundle_7fec005515_supportIntersection (⟨273, by decide⟩ : Fin 1069) = faceMask (⟨273, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0274 : bundle_7fec005515_supportIntersection (⟨274, by decide⟩ : Fin 1069) = faceMask (⟨274, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0275 : bundle_7fec005515_supportIntersection (⟨275, by decide⟩ : Fin 1069) = faceMask (⟨275, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0276 : bundle_7fec005515_supportIntersection (⟨276, by decide⟩ : Fin 1069) = faceMask (⟨276, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0277 : bundle_7fec005515_supportIntersection (⟨277, by decide⟩ : Fin 1069) = faceMask (⟨277, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0278 : bundle_7fec005515_supportIntersection (⟨278, by decide⟩ : Fin 1069) = faceMask (⟨278, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0279 : bundle_7fec005515_supportIntersection (⟨279, by decide⟩ : Fin 1069) = faceMask (⟨279, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0280 : bundle_7fec005515_supportIntersection (⟨280, by decide⟩ : Fin 1069) = faceMask (⟨280, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0281 : bundle_7fec005515_supportIntersection (⟨281, by decide⟩ : Fin 1069) = faceMask (⟨281, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0282 : bundle_7fec005515_supportIntersection (⟨282, by decide⟩ : Fin 1069) = faceMask (⟨282, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0283 : bundle_7fec005515_supportIntersection (⟨283, by decide⟩ : Fin 1069) = faceMask (⟨283, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0284 : bundle_7fec005515_supportIntersection (⟨284, by decide⟩ : Fin 1069) = faceMask (⟨284, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0285 : bundle_7fec005515_supportIntersection (⟨285, by decide⟩ : Fin 1069) = faceMask (⟨285, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0286 : bundle_7fec005515_supportIntersection (⟨286, by decide⟩ : Fin 1069) = faceMask (⟨286, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0287 : bundle_7fec005515_supportIntersection (⟨287, by decide⟩ : Fin 1069) = faceMask (⟨287, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0288 : bundle_7fec005515_supportIntersection (⟨288, by decide⟩ : Fin 1069) = faceMask (⟨288, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0289 : bundle_7fec005515_supportIntersection (⟨289, by decide⟩ : Fin 1069) = faceMask (⟨289, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0290 : bundle_7fec005515_supportIntersection (⟨290, by decide⟩ : Fin 1069) = faceMask (⟨290, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0291 : bundle_7fec005515_supportIntersection (⟨291, by decide⟩ : Fin 1069) = faceMask (⟨291, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0292 : bundle_7fec005515_supportIntersection (⟨292, by decide⟩ : Fin 1069) = faceMask (⟨292, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0293 : bundle_7fec005515_supportIntersection (⟨293, by decide⟩ : Fin 1069) = faceMask (⟨293, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0294 : bundle_7fec005515_supportIntersection (⟨294, by decide⟩ : Fin 1069) = faceMask (⟨294, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0295 : bundle_7fec005515_supportIntersection (⟨295, by decide⟩ : Fin 1069) = faceMask (⟨295, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0296 : bundle_7fec005515_supportIntersection (⟨296, by decide⟩ : Fin 1069) = faceMask (⟨296, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0297 : bundle_7fec005515_supportIntersection (⟨297, by decide⟩ : Fin 1069) = faceMask (⟨297, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0298 : bundle_7fec005515_supportIntersection (⟨298, by decide⟩ : Fin 1069) = faceMask (⟨298, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0299 : bundle_7fec005515_supportIntersection (⟨299, by decide⟩ : Fin 1069) = faceMask (⟨299, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0300 : bundle_7fec005515_supportIntersection (⟨300, by decide⟩ : Fin 1069) = faceMask (⟨300, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0301 : bundle_7fec005515_supportIntersection (⟨301, by decide⟩ : Fin 1069) = faceMask (⟨301, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0302 : bundle_7fec005515_supportIntersection (⟨302, by decide⟩ : Fin 1069) = faceMask (⟨302, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0303 : bundle_7fec005515_supportIntersection (⟨303, by decide⟩ : Fin 1069) = faceMask (⟨303, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0304 : bundle_7fec005515_supportIntersection (⟨304, by decide⟩ : Fin 1069) = faceMask (⟨304, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0305 : bundle_7fec005515_supportIntersection (⟨305, by decide⟩ : Fin 1069) = faceMask (⟨305, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0306 : bundle_7fec005515_supportIntersection (⟨306, by decide⟩ : Fin 1069) = faceMask (⟨306, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0307 : bundle_7fec005515_supportIntersection (⟨307, by decide⟩ : Fin 1069) = faceMask (⟨307, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0308 : bundle_7fec005515_supportIntersection (⟨308, by decide⟩ : Fin 1069) = faceMask (⟨308, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0309 : bundle_7fec005515_supportIntersection (⟨309, by decide⟩ : Fin 1069) = faceMask (⟨309, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0310 : bundle_7fec005515_supportIntersection (⟨310, by decide⟩ : Fin 1069) = faceMask (⟨310, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0311 : bundle_7fec005515_supportIntersection (⟨311, by decide⟩ : Fin 1069) = faceMask (⟨311, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0312 : bundle_7fec005515_supportIntersection (⟨312, by decide⟩ : Fin 1069) = faceMask (⟨312, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0313 : bundle_7fec005515_supportIntersection (⟨313, by decide⟩ : Fin 1069) = faceMask (⟨313, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0314 : bundle_7fec005515_supportIntersection (⟨314, by decide⟩ : Fin 1069) = faceMask (⟨314, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0315 : bundle_7fec005515_supportIntersection (⟨315, by decide⟩ : Fin 1069) = faceMask (⟨315, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0316 : bundle_7fec005515_supportIntersection (⟨316, by decide⟩ : Fin 1069) = faceMask (⟨316, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0317 : bundle_7fec005515_supportIntersection (⟨317, by decide⟩ : Fin 1069) = faceMask (⟨317, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0318 : bundle_7fec005515_supportIntersection (⟨318, by decide⟩ : Fin 1069) = faceMask (⟨318, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0319 : bundle_7fec005515_supportIntersection (⟨319, by decide⟩ : Fin 1069) = faceMask (⟨319, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0320 : bundle_7fec005515_supportIntersection (⟨320, by decide⟩ : Fin 1069) = faceMask (⟨320, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0321 : bundle_7fec005515_supportIntersection (⟨321, by decide⟩ : Fin 1069) = faceMask (⟨321, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0322 : bundle_7fec005515_supportIntersection (⟨322, by decide⟩ : Fin 1069) = faceMask (⟨322, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0323 : bundle_7fec005515_supportIntersection (⟨323, by decide⟩ : Fin 1069) = faceMask (⟨323, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0324 : bundle_7fec005515_supportIntersection (⟨324, by decide⟩ : Fin 1069) = faceMask (⟨324, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0325 : bundle_7fec005515_supportIntersection (⟨325, by decide⟩ : Fin 1069) = faceMask (⟨325, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0326 : bundle_7fec005515_supportIntersection (⟨326, by decide⟩ : Fin 1069) = faceMask (⟨326, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0327 : bundle_7fec005515_supportIntersection (⟨327, by decide⟩ : Fin 1069) = faceMask (⟨327, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0328 : bundle_7fec005515_supportIntersection (⟨328, by decide⟩ : Fin 1069) = faceMask (⟨328, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0329 : bundle_7fec005515_supportIntersection (⟨329, by decide⟩ : Fin 1069) = faceMask (⟨329, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0330 : bundle_7fec005515_supportIntersection (⟨330, by decide⟩ : Fin 1069) = faceMask (⟨330, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0331 : bundle_7fec005515_supportIntersection (⟨331, by decide⟩ : Fin 1069) = faceMask (⟨331, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0332 : bundle_7fec005515_supportIntersection (⟨332, by decide⟩ : Fin 1069) = faceMask (⟨332, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0333 : bundle_7fec005515_supportIntersection (⟨333, by decide⟩ : Fin 1069) = faceMask (⟨333, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0334 : bundle_7fec005515_supportIntersection (⟨334, by decide⟩ : Fin 1069) = faceMask (⟨334, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0335 : bundle_7fec005515_supportIntersection (⟨335, by decide⟩ : Fin 1069) = faceMask (⟨335, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0336 : bundle_7fec005515_supportIntersection (⟨336, by decide⟩ : Fin 1069) = faceMask (⟨336, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0337 : bundle_7fec005515_supportIntersection (⟨337, by decide⟩ : Fin 1069) = faceMask (⟨337, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0338 : bundle_7fec005515_supportIntersection (⟨338, by decide⟩ : Fin 1069) = faceMask (⟨338, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0339 : bundle_7fec005515_supportIntersection (⟨339, by decide⟩ : Fin 1069) = faceMask (⟨339, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0340 : bundle_7fec005515_supportIntersection (⟨340, by decide⟩ : Fin 1069) = faceMask (⟨340, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0341 : bundle_7fec005515_supportIntersection (⟨341, by decide⟩ : Fin 1069) = faceMask (⟨341, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0342 : bundle_7fec005515_supportIntersection (⟨342, by decide⟩ : Fin 1069) = faceMask (⟨342, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0343 : bundle_7fec005515_supportIntersection (⟨343, by decide⟩ : Fin 1069) = faceMask (⟨343, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0344 : bundle_7fec005515_supportIntersection (⟨344, by decide⟩ : Fin 1069) = faceMask (⟨344, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0345 : bundle_7fec005515_supportIntersection (⟨345, by decide⟩ : Fin 1069) = faceMask (⟨345, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0346 : bundle_7fec005515_supportIntersection (⟨346, by decide⟩ : Fin 1069) = faceMask (⟨346, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0347 : bundle_7fec005515_supportIntersection (⟨347, by decide⟩ : Fin 1069) = faceMask (⟨347, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0348 : bundle_7fec005515_supportIntersection (⟨348, by decide⟩ : Fin 1069) = faceMask (⟨348, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0349 : bundle_7fec005515_supportIntersection (⟨349, by decide⟩ : Fin 1069) = faceMask (⟨349, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0350 : bundle_7fec005515_supportIntersection (⟨350, by decide⟩ : Fin 1069) = faceMask (⟨350, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0351 : bundle_7fec005515_supportIntersection (⟨351, by decide⟩ : Fin 1069) = faceMask (⟨351, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0352 : bundle_7fec005515_supportIntersection (⟨352, by decide⟩ : Fin 1069) = faceMask (⟨352, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0353 : bundle_7fec005515_supportIntersection (⟨353, by decide⟩ : Fin 1069) = faceMask (⟨353, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0354 : bundle_7fec005515_supportIntersection (⟨354, by decide⟩ : Fin 1069) = faceMask (⟨354, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0355 : bundle_7fec005515_supportIntersection (⟨355, by decide⟩ : Fin 1069) = faceMask (⟨355, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0356 : bundle_7fec005515_supportIntersection (⟨356, by decide⟩ : Fin 1069) = faceMask (⟨356, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0357 : bundle_7fec005515_supportIntersection (⟨357, by decide⟩ : Fin 1069) = faceMask (⟨357, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0358 : bundle_7fec005515_supportIntersection (⟨358, by decide⟩ : Fin 1069) = faceMask (⟨358, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0359 : bundle_7fec005515_supportIntersection (⟨359, by decide⟩ : Fin 1069) = faceMask (⟨359, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0360 : bundle_7fec005515_supportIntersection (⟨360, by decide⟩ : Fin 1069) = faceMask (⟨360, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0361 : bundle_7fec005515_supportIntersection (⟨361, by decide⟩ : Fin 1069) = faceMask (⟨361, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0362 : bundle_7fec005515_supportIntersection (⟨362, by decide⟩ : Fin 1069) = faceMask (⟨362, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0363 : bundle_7fec005515_supportIntersection (⟨363, by decide⟩ : Fin 1069) = faceMask (⟨363, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0364 : bundle_7fec005515_supportIntersection (⟨364, by decide⟩ : Fin 1069) = faceMask (⟨364, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0365 : bundle_7fec005515_supportIntersection (⟨365, by decide⟩ : Fin 1069) = faceMask (⟨365, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0366 : bundle_7fec005515_supportIntersection (⟨366, by decide⟩ : Fin 1069) = faceMask (⟨366, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0367 : bundle_7fec005515_supportIntersection (⟨367, by decide⟩ : Fin 1069) = faceMask (⟨367, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0368 : bundle_7fec005515_supportIntersection (⟨368, by decide⟩ : Fin 1069) = faceMask (⟨368, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0369 : bundle_7fec005515_supportIntersection (⟨369, by decide⟩ : Fin 1069) = faceMask (⟨369, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0370 : bundle_7fec005515_supportIntersection (⟨370, by decide⟩ : Fin 1069) = faceMask (⟨370, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0371 : bundle_7fec005515_supportIntersection (⟨371, by decide⟩ : Fin 1069) = faceMask (⟨371, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0372 : bundle_7fec005515_supportIntersection (⟨372, by decide⟩ : Fin 1069) = faceMask (⟨372, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0373 : bundle_7fec005515_supportIntersection (⟨373, by decide⟩ : Fin 1069) = faceMask (⟨373, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0374 : bundle_7fec005515_supportIntersection (⟨374, by decide⟩ : Fin 1069) = faceMask (⟨374, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0375 : bundle_7fec005515_supportIntersection (⟨375, by decide⟩ : Fin 1069) = faceMask (⟨375, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0376 : bundle_7fec005515_supportIntersection (⟨376, by decide⟩ : Fin 1069) = faceMask (⟨376, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0377 : bundle_7fec005515_supportIntersection (⟨377, by decide⟩ : Fin 1069) = faceMask (⟨377, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0378 : bundle_7fec005515_supportIntersection (⟨378, by decide⟩ : Fin 1069) = faceMask (⟨378, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0379 : bundle_7fec005515_supportIntersection (⟨379, by decide⟩ : Fin 1069) = faceMask (⟨379, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0380 : bundle_7fec005515_supportIntersection (⟨380, by decide⟩ : Fin 1069) = faceMask (⟨380, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0381 : bundle_7fec005515_supportIntersection (⟨381, by decide⟩ : Fin 1069) = faceMask (⟨381, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0382 : bundle_7fec005515_supportIntersection (⟨382, by decide⟩ : Fin 1069) = faceMask (⟨382, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0383 : bundle_7fec005515_supportIntersection (⟨383, by decide⟩ : Fin 1069) = faceMask (⟨383, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0384 : bundle_7fec005515_supportIntersection (⟨384, by decide⟩ : Fin 1069) = faceMask (⟨384, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0385 : bundle_7fec005515_supportIntersection (⟨385, by decide⟩ : Fin 1069) = faceMask (⟨385, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0386 : bundle_7fec005515_supportIntersection (⟨386, by decide⟩ : Fin 1069) = faceMask (⟨386, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0387 : bundle_7fec005515_supportIntersection (⟨387, by decide⟩ : Fin 1069) = faceMask (⟨387, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0388 : bundle_7fec005515_supportIntersection (⟨388, by decide⟩ : Fin 1069) = faceMask (⟨388, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0389 : bundle_7fec005515_supportIntersection (⟨389, by decide⟩ : Fin 1069) = faceMask (⟨389, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0390 : bundle_7fec005515_supportIntersection (⟨390, by decide⟩ : Fin 1069) = faceMask (⟨390, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0391 : bundle_7fec005515_supportIntersection (⟨391, by decide⟩ : Fin 1069) = faceMask (⟨391, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0392 : bundle_7fec005515_supportIntersection (⟨392, by decide⟩ : Fin 1069) = faceMask (⟨392, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0393 : bundle_7fec005515_supportIntersection (⟨393, by decide⟩ : Fin 1069) = faceMask (⟨393, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0394 : bundle_7fec005515_supportIntersection (⟨394, by decide⟩ : Fin 1069) = faceMask (⟨394, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0395 : bundle_7fec005515_supportIntersection (⟨395, by decide⟩ : Fin 1069) = faceMask (⟨395, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0396 : bundle_7fec005515_supportIntersection (⟨396, by decide⟩ : Fin 1069) = faceMask (⟨396, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0397 : bundle_7fec005515_supportIntersection (⟨397, by decide⟩ : Fin 1069) = faceMask (⟨397, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0398 : bundle_7fec005515_supportIntersection (⟨398, by decide⟩ : Fin 1069) = faceMask (⟨398, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0399 : bundle_7fec005515_supportIntersection (⟨399, by decide⟩ : Fin 1069) = faceMask (⟨399, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0400 : bundle_7fec005515_supportIntersection (⟨400, by decide⟩ : Fin 1069) = faceMask (⟨400, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0401 : bundle_7fec005515_supportIntersection (⟨401, by decide⟩ : Fin 1069) = faceMask (⟨401, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0402 : bundle_7fec005515_supportIntersection (⟨402, by decide⟩ : Fin 1069) = faceMask (⟨402, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0403 : bundle_7fec005515_supportIntersection (⟨403, by decide⟩ : Fin 1069) = faceMask (⟨403, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0404 : bundle_7fec005515_supportIntersection (⟨404, by decide⟩ : Fin 1069) = faceMask (⟨404, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0405 : bundle_7fec005515_supportIntersection (⟨405, by decide⟩ : Fin 1069) = faceMask (⟨405, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0406 : bundle_7fec005515_supportIntersection (⟨406, by decide⟩ : Fin 1069) = faceMask (⟨406, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0407 : bundle_7fec005515_supportIntersection (⟨407, by decide⟩ : Fin 1069) = faceMask (⟨407, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0408 : bundle_7fec005515_supportIntersection (⟨408, by decide⟩ : Fin 1069) = faceMask (⟨408, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0409 : bundle_7fec005515_supportIntersection (⟨409, by decide⟩ : Fin 1069) = faceMask (⟨409, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0410 : bundle_7fec005515_supportIntersection (⟨410, by decide⟩ : Fin 1069) = faceMask (⟨410, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0411 : bundle_7fec005515_supportIntersection (⟨411, by decide⟩ : Fin 1069) = faceMask (⟨411, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0412 : bundle_7fec005515_supportIntersection (⟨412, by decide⟩ : Fin 1069) = faceMask (⟨412, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0413 : bundle_7fec005515_supportIntersection (⟨413, by decide⟩ : Fin 1069) = faceMask (⟨413, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0414 : bundle_7fec005515_supportIntersection (⟨414, by decide⟩ : Fin 1069) = faceMask (⟨414, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0415 : bundle_7fec005515_supportIntersection (⟨415, by decide⟩ : Fin 1069) = faceMask (⟨415, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0416 : bundle_7fec005515_supportIntersection (⟨416, by decide⟩ : Fin 1069) = faceMask (⟨416, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0417 : bundle_7fec005515_supportIntersection (⟨417, by decide⟩ : Fin 1069) = faceMask (⟨417, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0418 : bundle_7fec005515_supportIntersection (⟨418, by decide⟩ : Fin 1069) = faceMask (⟨418, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0419 : bundle_7fec005515_supportIntersection (⟨419, by decide⟩ : Fin 1069) = faceMask (⟨419, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0420 : bundle_7fec005515_supportIntersection (⟨420, by decide⟩ : Fin 1069) = faceMask (⟨420, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0421 : bundle_7fec005515_supportIntersection (⟨421, by decide⟩ : Fin 1069) = faceMask (⟨421, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0422 : bundle_7fec005515_supportIntersection (⟨422, by decide⟩ : Fin 1069) = faceMask (⟨422, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0423 : bundle_7fec005515_supportIntersection (⟨423, by decide⟩ : Fin 1069) = faceMask (⟨423, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0424 : bundle_7fec005515_supportIntersection (⟨424, by decide⟩ : Fin 1069) = faceMask (⟨424, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0425 : bundle_7fec005515_supportIntersection (⟨425, by decide⟩ : Fin 1069) = faceMask (⟨425, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0426 : bundle_7fec005515_supportIntersection (⟨426, by decide⟩ : Fin 1069) = faceMask (⟨426, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0427 : bundle_7fec005515_supportIntersection (⟨427, by decide⟩ : Fin 1069) = faceMask (⟨427, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0428 : bundle_7fec005515_supportIntersection (⟨428, by decide⟩ : Fin 1069) = faceMask (⟨428, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0429 : bundle_7fec005515_supportIntersection (⟨429, by decide⟩ : Fin 1069) = faceMask (⟨429, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0430 : bundle_7fec005515_supportIntersection (⟨430, by decide⟩ : Fin 1069) = faceMask (⟨430, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0431 : bundle_7fec005515_supportIntersection (⟨431, by decide⟩ : Fin 1069) = faceMask (⟨431, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0432 : bundle_7fec005515_supportIntersection (⟨432, by decide⟩ : Fin 1069) = faceMask (⟨432, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0433 : bundle_7fec005515_supportIntersection (⟨433, by decide⟩ : Fin 1069) = faceMask (⟨433, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0434 : bundle_7fec005515_supportIntersection (⟨434, by decide⟩ : Fin 1069) = faceMask (⟨434, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0435 : bundle_7fec005515_supportIntersection (⟨435, by decide⟩ : Fin 1069) = faceMask (⟨435, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0436 : bundle_7fec005515_supportIntersection (⟨436, by decide⟩ : Fin 1069) = faceMask (⟨436, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0437 : bundle_7fec005515_supportIntersection (⟨437, by decide⟩ : Fin 1069) = faceMask (⟨437, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0438 : bundle_7fec005515_supportIntersection (⟨438, by decide⟩ : Fin 1069) = faceMask (⟨438, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0439 : bundle_7fec005515_supportIntersection (⟨439, by decide⟩ : Fin 1069) = faceMask (⟨439, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0440 : bundle_7fec005515_supportIntersection (⟨440, by decide⟩ : Fin 1069) = faceMask (⟨440, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0441 : bundle_7fec005515_supportIntersection (⟨441, by decide⟩ : Fin 1069) = faceMask (⟨441, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0442 : bundle_7fec005515_supportIntersection (⟨442, by decide⟩ : Fin 1069) = faceMask (⟨442, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0443 : bundle_7fec005515_supportIntersection (⟨443, by decide⟩ : Fin 1069) = faceMask (⟨443, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0444 : bundle_7fec005515_supportIntersection (⟨444, by decide⟩ : Fin 1069) = faceMask (⟨444, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0445 : bundle_7fec005515_supportIntersection (⟨445, by decide⟩ : Fin 1069) = faceMask (⟨445, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0446 : bundle_7fec005515_supportIntersection (⟨446, by decide⟩ : Fin 1069) = faceMask (⟨446, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0447 : bundle_7fec005515_supportIntersection (⟨447, by decide⟩ : Fin 1069) = faceMask (⟨447, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0448 : bundle_7fec005515_supportIntersection (⟨448, by decide⟩ : Fin 1069) = faceMask (⟨448, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0449 : bundle_7fec005515_supportIntersection (⟨449, by decide⟩ : Fin 1069) = faceMask (⟨449, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0450 : bundle_7fec005515_supportIntersection (⟨450, by decide⟩ : Fin 1069) = faceMask (⟨450, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0451 : bundle_7fec005515_supportIntersection (⟨451, by decide⟩ : Fin 1069) = faceMask (⟨451, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0452 : bundle_7fec005515_supportIntersection (⟨452, by decide⟩ : Fin 1069) = faceMask (⟨452, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0453 : bundle_7fec005515_supportIntersection (⟨453, by decide⟩ : Fin 1069) = faceMask (⟨453, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0454 : bundle_7fec005515_supportIntersection (⟨454, by decide⟩ : Fin 1069) = faceMask (⟨454, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0455 : bundle_7fec005515_supportIntersection (⟨455, by decide⟩ : Fin 1069) = faceMask (⟨455, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0456 : bundle_7fec005515_supportIntersection (⟨456, by decide⟩ : Fin 1069) = faceMask (⟨456, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0457 : bundle_7fec005515_supportIntersection (⟨457, by decide⟩ : Fin 1069) = faceMask (⟨457, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0458 : bundle_7fec005515_supportIntersection (⟨458, by decide⟩ : Fin 1069) = faceMask (⟨458, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0459 : bundle_7fec005515_supportIntersection (⟨459, by decide⟩ : Fin 1069) = faceMask (⟨459, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0460 : bundle_7fec005515_supportIntersection (⟨460, by decide⟩ : Fin 1069) = faceMask (⟨460, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0461 : bundle_7fec005515_supportIntersection (⟨461, by decide⟩ : Fin 1069) = faceMask (⟨461, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0462 : bundle_7fec005515_supportIntersection (⟨462, by decide⟩ : Fin 1069) = faceMask (⟨462, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0463 : bundle_7fec005515_supportIntersection (⟨463, by decide⟩ : Fin 1069) = faceMask (⟨463, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0464 : bundle_7fec005515_supportIntersection (⟨464, by decide⟩ : Fin 1069) = faceMask (⟨464, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0465 : bundle_7fec005515_supportIntersection (⟨465, by decide⟩ : Fin 1069) = faceMask (⟨465, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0466 : bundle_7fec005515_supportIntersection (⟨466, by decide⟩ : Fin 1069) = faceMask (⟨466, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0467 : bundle_7fec005515_supportIntersection (⟨467, by decide⟩ : Fin 1069) = faceMask (⟨467, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0468 : bundle_7fec005515_supportIntersection (⟨468, by decide⟩ : Fin 1069) = faceMask (⟨468, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0469 : bundle_7fec005515_supportIntersection (⟨469, by decide⟩ : Fin 1069) = faceMask (⟨469, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0470 : bundle_7fec005515_supportIntersection (⟨470, by decide⟩ : Fin 1069) = faceMask (⟨470, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0471 : bundle_7fec005515_supportIntersection (⟨471, by decide⟩ : Fin 1069) = faceMask (⟨471, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0472 : bundle_7fec005515_supportIntersection (⟨472, by decide⟩ : Fin 1069) = faceMask (⟨472, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0473 : bundle_7fec005515_supportIntersection (⟨473, by decide⟩ : Fin 1069) = faceMask (⟨473, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0474 : bundle_7fec005515_supportIntersection (⟨474, by decide⟩ : Fin 1069) = faceMask (⟨474, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0475 : bundle_7fec005515_supportIntersection (⟨475, by decide⟩ : Fin 1069) = faceMask (⟨475, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0476 : bundle_7fec005515_supportIntersection (⟨476, by decide⟩ : Fin 1069) = faceMask (⟨476, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0477 : bundle_7fec005515_supportIntersection (⟨477, by decide⟩ : Fin 1069) = faceMask (⟨477, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0478 : bundle_7fec005515_supportIntersection (⟨478, by decide⟩ : Fin 1069) = faceMask (⟨478, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0479 : bundle_7fec005515_supportIntersection (⟨479, by decide⟩ : Fin 1069) = faceMask (⟨479, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0480 : bundle_7fec005515_supportIntersection (⟨480, by decide⟩ : Fin 1069) = faceMask (⟨480, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0481 : bundle_7fec005515_supportIntersection (⟨481, by decide⟩ : Fin 1069) = faceMask (⟨481, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0482 : bundle_7fec005515_supportIntersection (⟨482, by decide⟩ : Fin 1069) = faceMask (⟨482, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0483 : bundle_7fec005515_supportIntersection (⟨483, by decide⟩ : Fin 1069) = faceMask (⟨483, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0484 : bundle_7fec005515_supportIntersection (⟨484, by decide⟩ : Fin 1069) = faceMask (⟨484, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0485 : bundle_7fec005515_supportIntersection (⟨485, by decide⟩ : Fin 1069) = faceMask (⟨485, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0486 : bundle_7fec005515_supportIntersection (⟨486, by decide⟩ : Fin 1069) = faceMask (⟨486, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0487 : bundle_7fec005515_supportIntersection (⟨487, by decide⟩ : Fin 1069) = faceMask (⟨487, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0488 : bundle_7fec005515_supportIntersection (⟨488, by decide⟩ : Fin 1069) = faceMask (⟨488, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0489 : bundle_7fec005515_supportIntersection (⟨489, by decide⟩ : Fin 1069) = faceMask (⟨489, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0490 : bundle_7fec005515_supportIntersection (⟨490, by decide⟩ : Fin 1069) = faceMask (⟨490, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0491 : bundle_7fec005515_supportIntersection (⟨491, by decide⟩ : Fin 1069) = faceMask (⟨491, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0492 : bundle_7fec005515_supportIntersection (⟨492, by decide⟩ : Fin 1069) = faceMask (⟨492, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0493 : bundle_7fec005515_supportIntersection (⟨493, by decide⟩ : Fin 1069) = faceMask (⟨493, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0494 : bundle_7fec005515_supportIntersection (⟨494, by decide⟩ : Fin 1069) = faceMask (⟨494, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0495 : bundle_7fec005515_supportIntersection (⟨495, by decide⟩ : Fin 1069) = faceMask (⟨495, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0496 : bundle_7fec005515_supportIntersection (⟨496, by decide⟩ : Fin 1069) = faceMask (⟨496, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0497 : bundle_7fec005515_supportIntersection (⟨497, by decide⟩ : Fin 1069) = faceMask (⟨497, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0498 : bundle_7fec005515_supportIntersection (⟨498, by decide⟩ : Fin 1069) = faceMask (⟨498, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0499 : bundle_7fec005515_supportIntersection (⟨499, by decide⟩ : Fin 1069) = faceMask (⟨499, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0500 : bundle_7fec005515_supportIntersection (⟨500, by decide⟩ : Fin 1069) = faceMask (⟨500, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0501 : bundle_7fec005515_supportIntersection (⟨501, by decide⟩ : Fin 1069) = faceMask (⟨501, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0502 : bundle_7fec005515_supportIntersection (⟨502, by decide⟩ : Fin 1069) = faceMask (⟨502, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0503 : bundle_7fec005515_supportIntersection (⟨503, by decide⟩ : Fin 1069) = faceMask (⟨503, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0504 : bundle_7fec005515_supportIntersection (⟨504, by decide⟩ : Fin 1069) = faceMask (⟨504, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0505 : bundle_7fec005515_supportIntersection (⟨505, by decide⟩ : Fin 1069) = faceMask (⟨505, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0506 : bundle_7fec005515_supportIntersection (⟨506, by decide⟩ : Fin 1069) = faceMask (⟨506, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0507 : bundle_7fec005515_supportIntersection (⟨507, by decide⟩ : Fin 1069) = faceMask (⟨507, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0508 : bundle_7fec005515_supportIntersection (⟨508, by decide⟩ : Fin 1069) = faceMask (⟨508, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0509 : bundle_7fec005515_supportIntersection (⟨509, by decide⟩ : Fin 1069) = faceMask (⟨509, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0510 : bundle_7fec005515_supportIntersection (⟨510, by decide⟩ : Fin 1069) = faceMask (⟨510, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0511 : bundle_7fec005515_supportIntersection (⟨511, by decide⟩ : Fin 1069) = faceMask (⟨511, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0512 : bundle_7fec005515_supportIntersection (⟨512, by decide⟩ : Fin 1069) = faceMask (⟨512, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0513 : bundle_7fec005515_supportIntersection (⟨513, by decide⟩ : Fin 1069) = faceMask (⟨513, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0514 : bundle_7fec005515_supportIntersection (⟨514, by decide⟩ : Fin 1069) = faceMask (⟨514, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0515 : bundle_7fec005515_supportIntersection (⟨515, by decide⟩ : Fin 1069) = faceMask (⟨515, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0516 : bundle_7fec005515_supportIntersection (⟨516, by decide⟩ : Fin 1069) = faceMask (⟨516, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0517 : bundle_7fec005515_supportIntersection (⟨517, by decide⟩ : Fin 1069) = faceMask (⟨517, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0518 : bundle_7fec005515_supportIntersection (⟨518, by decide⟩ : Fin 1069) = faceMask (⟨518, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0519 : bundle_7fec005515_supportIntersection (⟨519, by decide⟩ : Fin 1069) = faceMask (⟨519, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0520 : bundle_7fec005515_supportIntersection (⟨520, by decide⟩ : Fin 1069) = faceMask (⟨520, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0521 : bundle_7fec005515_supportIntersection (⟨521, by decide⟩ : Fin 1069) = faceMask (⟨521, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0522 : bundle_7fec005515_supportIntersection (⟨522, by decide⟩ : Fin 1069) = faceMask (⟨522, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0523 : bundle_7fec005515_supportIntersection (⟨523, by decide⟩ : Fin 1069) = faceMask (⟨523, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0524 : bundle_7fec005515_supportIntersection (⟨524, by decide⟩ : Fin 1069) = faceMask (⟨524, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0525 : bundle_7fec005515_supportIntersection (⟨525, by decide⟩ : Fin 1069) = faceMask (⟨525, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0526 : bundle_7fec005515_supportIntersection (⟨526, by decide⟩ : Fin 1069) = faceMask (⟨526, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0527 : bundle_7fec005515_supportIntersection (⟨527, by decide⟩ : Fin 1069) = faceMask (⟨527, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0528 : bundle_7fec005515_supportIntersection (⟨528, by decide⟩ : Fin 1069) = faceMask (⟨528, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0529 : bundle_7fec005515_supportIntersection (⟨529, by decide⟩ : Fin 1069) = faceMask (⟨529, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0530 : bundle_7fec005515_supportIntersection (⟨530, by decide⟩ : Fin 1069) = faceMask (⟨530, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0531 : bundle_7fec005515_supportIntersection (⟨531, by decide⟩ : Fin 1069) = faceMask (⟨531, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0532 : bundle_7fec005515_supportIntersection (⟨532, by decide⟩ : Fin 1069) = faceMask (⟨532, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0533 : bundle_7fec005515_supportIntersection (⟨533, by decide⟩ : Fin 1069) = faceMask (⟨533, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0534 : bundle_7fec005515_supportIntersection (⟨534, by decide⟩ : Fin 1069) = faceMask (⟨534, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0535 : bundle_7fec005515_supportIntersection (⟨535, by decide⟩ : Fin 1069) = faceMask (⟨535, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0536 : bundle_7fec005515_supportIntersection (⟨536, by decide⟩ : Fin 1069) = faceMask (⟨536, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0537 : bundle_7fec005515_supportIntersection (⟨537, by decide⟩ : Fin 1069) = faceMask (⟨537, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0538 : bundle_7fec005515_supportIntersection (⟨538, by decide⟩ : Fin 1069) = faceMask (⟨538, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0539 : bundle_7fec005515_supportIntersection (⟨539, by decide⟩ : Fin 1069) = faceMask (⟨539, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0540 : bundle_7fec005515_supportIntersection (⟨540, by decide⟩ : Fin 1069) = faceMask (⟨540, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0541 : bundle_7fec005515_supportIntersection (⟨541, by decide⟩ : Fin 1069) = faceMask (⟨541, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0542 : bundle_7fec005515_supportIntersection (⟨542, by decide⟩ : Fin 1069) = faceMask (⟨542, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0543 : bundle_7fec005515_supportIntersection (⟨543, by decide⟩ : Fin 1069) = faceMask (⟨543, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0544 : bundle_7fec005515_supportIntersection (⟨544, by decide⟩ : Fin 1069) = faceMask (⟨544, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0545 : bundle_7fec005515_supportIntersection (⟨545, by decide⟩ : Fin 1069) = faceMask (⟨545, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0546 : bundle_7fec005515_supportIntersection (⟨546, by decide⟩ : Fin 1069) = faceMask (⟨546, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0547 : bundle_7fec005515_supportIntersection (⟨547, by decide⟩ : Fin 1069) = faceMask (⟨547, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0548 : bundle_7fec005515_supportIntersection (⟨548, by decide⟩ : Fin 1069) = faceMask (⟨548, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0549 : bundle_7fec005515_supportIntersection (⟨549, by decide⟩ : Fin 1069) = faceMask (⟨549, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0550 : bundle_7fec005515_supportIntersection (⟨550, by decide⟩ : Fin 1069) = faceMask (⟨550, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0551 : bundle_7fec005515_supportIntersection (⟨551, by decide⟩ : Fin 1069) = faceMask (⟨551, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0552 : bundle_7fec005515_supportIntersection (⟨552, by decide⟩ : Fin 1069) = faceMask (⟨552, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0553 : bundle_7fec005515_supportIntersection (⟨553, by decide⟩ : Fin 1069) = faceMask (⟨553, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0554 : bundle_7fec005515_supportIntersection (⟨554, by decide⟩ : Fin 1069) = faceMask (⟨554, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0555 : bundle_7fec005515_supportIntersection (⟨555, by decide⟩ : Fin 1069) = faceMask (⟨555, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0556 : bundle_7fec005515_supportIntersection (⟨556, by decide⟩ : Fin 1069) = faceMask (⟨556, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0557 : bundle_7fec005515_supportIntersection (⟨557, by decide⟩ : Fin 1069) = faceMask (⟨557, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0558 : bundle_7fec005515_supportIntersection (⟨558, by decide⟩ : Fin 1069) = faceMask (⟨558, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0559 : bundle_7fec005515_supportIntersection (⟨559, by decide⟩ : Fin 1069) = faceMask (⟨559, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0560 : bundle_7fec005515_supportIntersection (⟨560, by decide⟩ : Fin 1069) = faceMask (⟨560, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0561 : bundle_7fec005515_supportIntersection (⟨561, by decide⟩ : Fin 1069) = faceMask (⟨561, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0562 : bundle_7fec005515_supportIntersection (⟨562, by decide⟩ : Fin 1069) = faceMask (⟨562, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0563 : bundle_7fec005515_supportIntersection (⟨563, by decide⟩ : Fin 1069) = faceMask (⟨563, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0564 : bundle_7fec005515_supportIntersection (⟨564, by decide⟩ : Fin 1069) = faceMask (⟨564, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0565 : bundle_7fec005515_supportIntersection (⟨565, by decide⟩ : Fin 1069) = faceMask (⟨565, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0566 : bundle_7fec005515_supportIntersection (⟨566, by decide⟩ : Fin 1069) = faceMask (⟨566, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0567 : bundle_7fec005515_supportIntersection (⟨567, by decide⟩ : Fin 1069) = faceMask (⟨567, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0568 : bundle_7fec005515_supportIntersection (⟨568, by decide⟩ : Fin 1069) = faceMask (⟨568, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0569 : bundle_7fec005515_supportIntersection (⟨569, by decide⟩ : Fin 1069) = faceMask (⟨569, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0570 : bundle_7fec005515_supportIntersection (⟨570, by decide⟩ : Fin 1069) = faceMask (⟨570, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0571 : bundle_7fec005515_supportIntersection (⟨571, by decide⟩ : Fin 1069) = faceMask (⟨571, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0572 : bundle_7fec005515_supportIntersection (⟨572, by decide⟩ : Fin 1069) = faceMask (⟨572, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0573 : bundle_7fec005515_supportIntersection (⟨573, by decide⟩ : Fin 1069) = faceMask (⟨573, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0574 : bundle_7fec005515_supportIntersection (⟨574, by decide⟩ : Fin 1069) = faceMask (⟨574, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0575 : bundle_7fec005515_supportIntersection (⟨575, by decide⟩ : Fin 1069) = faceMask (⟨575, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0576 : bundle_7fec005515_supportIntersection (⟨576, by decide⟩ : Fin 1069) = faceMask (⟨576, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0577 : bundle_7fec005515_supportIntersection (⟨577, by decide⟩ : Fin 1069) = faceMask (⟨577, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0578 : bundle_7fec005515_supportIntersection (⟨578, by decide⟩ : Fin 1069) = faceMask (⟨578, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0579 : bundle_7fec005515_supportIntersection (⟨579, by decide⟩ : Fin 1069) = faceMask (⟨579, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0580 : bundle_7fec005515_supportIntersection (⟨580, by decide⟩ : Fin 1069) = faceMask (⟨580, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0581 : bundle_7fec005515_supportIntersection (⟨581, by decide⟩ : Fin 1069) = faceMask (⟨581, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0582 : bundle_7fec005515_supportIntersection (⟨582, by decide⟩ : Fin 1069) = faceMask (⟨582, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0583 : bundle_7fec005515_supportIntersection (⟨583, by decide⟩ : Fin 1069) = faceMask (⟨583, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0584 : bundle_7fec005515_supportIntersection (⟨584, by decide⟩ : Fin 1069) = faceMask (⟨584, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0585 : bundle_7fec005515_supportIntersection (⟨585, by decide⟩ : Fin 1069) = faceMask (⟨585, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0586 : bundle_7fec005515_supportIntersection (⟨586, by decide⟩ : Fin 1069) = faceMask (⟨586, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0587 : bundle_7fec005515_supportIntersection (⟨587, by decide⟩ : Fin 1069) = faceMask (⟨587, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0588 : bundle_7fec005515_supportIntersection (⟨588, by decide⟩ : Fin 1069) = faceMask (⟨588, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0589 : bundle_7fec005515_supportIntersection (⟨589, by decide⟩ : Fin 1069) = faceMask (⟨589, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0590 : bundle_7fec005515_supportIntersection (⟨590, by decide⟩ : Fin 1069) = faceMask (⟨590, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0591 : bundle_7fec005515_supportIntersection (⟨591, by decide⟩ : Fin 1069) = faceMask (⟨591, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0592 : bundle_7fec005515_supportIntersection (⟨592, by decide⟩ : Fin 1069) = faceMask (⟨592, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0593 : bundle_7fec005515_supportIntersection (⟨593, by decide⟩ : Fin 1069) = faceMask (⟨593, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0594 : bundle_7fec005515_supportIntersection (⟨594, by decide⟩ : Fin 1069) = faceMask (⟨594, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0595 : bundle_7fec005515_supportIntersection (⟨595, by decide⟩ : Fin 1069) = faceMask (⟨595, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0596 : bundle_7fec005515_supportIntersection (⟨596, by decide⟩ : Fin 1069) = faceMask (⟨596, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0597 : bundle_7fec005515_supportIntersection (⟨597, by decide⟩ : Fin 1069) = faceMask (⟨597, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0598 : bundle_7fec005515_supportIntersection (⟨598, by decide⟩ : Fin 1069) = faceMask (⟨598, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0599 : bundle_7fec005515_supportIntersection (⟨599, by decide⟩ : Fin 1069) = faceMask (⟨599, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0600 : bundle_7fec005515_supportIntersection (⟨600, by decide⟩ : Fin 1069) = faceMask (⟨600, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0601 : bundle_7fec005515_supportIntersection (⟨601, by decide⟩ : Fin 1069) = faceMask (⟨601, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0602 : bundle_7fec005515_supportIntersection (⟨602, by decide⟩ : Fin 1069) = faceMask (⟨602, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0603 : bundle_7fec005515_supportIntersection (⟨603, by decide⟩ : Fin 1069) = faceMask (⟨603, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0604 : bundle_7fec005515_supportIntersection (⟨604, by decide⟩ : Fin 1069) = faceMask (⟨604, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0605 : bundle_7fec005515_supportIntersection (⟨605, by decide⟩ : Fin 1069) = faceMask (⟨605, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0606 : bundle_7fec005515_supportIntersection (⟨606, by decide⟩ : Fin 1069) = faceMask (⟨606, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0607 : bundle_7fec005515_supportIntersection (⟨607, by decide⟩ : Fin 1069) = faceMask (⟨607, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0608 : bundle_7fec005515_supportIntersection (⟨608, by decide⟩ : Fin 1069) = faceMask (⟨608, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0609 : bundle_7fec005515_supportIntersection (⟨609, by decide⟩ : Fin 1069) = faceMask (⟨609, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0610 : bundle_7fec005515_supportIntersection (⟨610, by decide⟩ : Fin 1069) = faceMask (⟨610, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0611 : bundle_7fec005515_supportIntersection (⟨611, by decide⟩ : Fin 1069) = faceMask (⟨611, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0612 : bundle_7fec005515_supportIntersection (⟨612, by decide⟩ : Fin 1069) = faceMask (⟨612, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0613 : bundle_7fec005515_supportIntersection (⟨613, by decide⟩ : Fin 1069) = faceMask (⟨613, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0614 : bundle_7fec005515_supportIntersection (⟨614, by decide⟩ : Fin 1069) = faceMask (⟨614, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0615 : bundle_7fec005515_supportIntersection (⟨615, by decide⟩ : Fin 1069) = faceMask (⟨615, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0616 : bundle_7fec005515_supportIntersection (⟨616, by decide⟩ : Fin 1069) = faceMask (⟨616, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0617 : bundle_7fec005515_supportIntersection (⟨617, by decide⟩ : Fin 1069) = faceMask (⟨617, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0618 : bundle_7fec005515_supportIntersection (⟨618, by decide⟩ : Fin 1069) = faceMask (⟨618, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0619 : bundle_7fec005515_supportIntersection (⟨619, by decide⟩ : Fin 1069) = faceMask (⟨619, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0620 : bundle_7fec005515_supportIntersection (⟨620, by decide⟩ : Fin 1069) = faceMask (⟨620, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0621 : bundle_7fec005515_supportIntersection (⟨621, by decide⟩ : Fin 1069) = faceMask (⟨621, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0622 : bundle_7fec005515_supportIntersection (⟨622, by decide⟩ : Fin 1069) = faceMask (⟨622, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0623 : bundle_7fec005515_supportIntersection (⟨623, by decide⟩ : Fin 1069) = faceMask (⟨623, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0624 : bundle_7fec005515_supportIntersection (⟨624, by decide⟩ : Fin 1069) = faceMask (⟨624, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0625 : bundle_7fec005515_supportIntersection (⟨625, by decide⟩ : Fin 1069) = faceMask (⟨625, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0626 : bundle_7fec005515_supportIntersection (⟨626, by decide⟩ : Fin 1069) = faceMask (⟨626, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0627 : bundle_7fec005515_supportIntersection (⟨627, by decide⟩ : Fin 1069) = faceMask (⟨627, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0628 : bundle_7fec005515_supportIntersection (⟨628, by decide⟩ : Fin 1069) = faceMask (⟨628, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0629 : bundle_7fec005515_supportIntersection (⟨629, by decide⟩ : Fin 1069) = faceMask (⟨629, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0630 : bundle_7fec005515_supportIntersection (⟨630, by decide⟩ : Fin 1069) = faceMask (⟨630, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0631 : bundle_7fec005515_supportIntersection (⟨631, by decide⟩ : Fin 1069) = faceMask (⟨631, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0632 : bundle_7fec005515_supportIntersection (⟨632, by decide⟩ : Fin 1069) = faceMask (⟨632, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0633 : bundle_7fec005515_supportIntersection (⟨633, by decide⟩ : Fin 1069) = faceMask (⟨633, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0634 : bundle_7fec005515_supportIntersection (⟨634, by decide⟩ : Fin 1069) = faceMask (⟨634, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0635 : bundle_7fec005515_supportIntersection (⟨635, by decide⟩ : Fin 1069) = faceMask (⟨635, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0636 : bundle_7fec005515_supportIntersection (⟨636, by decide⟩ : Fin 1069) = faceMask (⟨636, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0637 : bundle_7fec005515_supportIntersection (⟨637, by decide⟩ : Fin 1069) = faceMask (⟨637, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0638 : bundle_7fec005515_supportIntersection (⟨638, by decide⟩ : Fin 1069) = faceMask (⟨638, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0639 : bundle_7fec005515_supportIntersection (⟨639, by decide⟩ : Fin 1069) = faceMask (⟨639, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0640 : bundle_7fec005515_supportIntersection (⟨640, by decide⟩ : Fin 1069) = faceMask (⟨640, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0641 : bundle_7fec005515_supportIntersection (⟨641, by decide⟩ : Fin 1069) = faceMask (⟨641, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0642 : bundle_7fec005515_supportIntersection (⟨642, by decide⟩ : Fin 1069) = faceMask (⟨642, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0643 : bundle_7fec005515_supportIntersection (⟨643, by decide⟩ : Fin 1069) = faceMask (⟨643, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0644 : bundle_7fec005515_supportIntersection (⟨644, by decide⟩ : Fin 1069) = faceMask (⟨644, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0645 : bundle_7fec005515_supportIntersection (⟨645, by decide⟩ : Fin 1069) = faceMask (⟨645, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0646 : bundle_7fec005515_supportIntersection (⟨646, by decide⟩ : Fin 1069) = faceMask (⟨646, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0647 : bundle_7fec005515_supportIntersection (⟨647, by decide⟩ : Fin 1069) = faceMask (⟨647, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0648 : bundle_7fec005515_supportIntersection (⟨648, by decide⟩ : Fin 1069) = faceMask (⟨648, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0649 : bundle_7fec005515_supportIntersection (⟨649, by decide⟩ : Fin 1069) = faceMask (⟨649, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0650 : bundle_7fec005515_supportIntersection (⟨650, by decide⟩ : Fin 1069) = faceMask (⟨650, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0651 : bundle_7fec005515_supportIntersection (⟨651, by decide⟩ : Fin 1069) = faceMask (⟨651, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0652 : bundle_7fec005515_supportIntersection (⟨652, by decide⟩ : Fin 1069) = faceMask (⟨652, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0653 : bundle_7fec005515_supportIntersection (⟨653, by decide⟩ : Fin 1069) = faceMask (⟨653, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0654 : bundle_7fec005515_supportIntersection (⟨654, by decide⟩ : Fin 1069) = faceMask (⟨654, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0655 : bundle_7fec005515_supportIntersection (⟨655, by decide⟩ : Fin 1069) = faceMask (⟨655, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0656 : bundle_7fec005515_supportIntersection (⟨656, by decide⟩ : Fin 1069) = faceMask (⟨656, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0657 : bundle_7fec005515_supportIntersection (⟨657, by decide⟩ : Fin 1069) = faceMask (⟨657, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0658 : bundle_7fec005515_supportIntersection (⟨658, by decide⟩ : Fin 1069) = faceMask (⟨658, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0659 : bundle_7fec005515_supportIntersection (⟨659, by decide⟩ : Fin 1069) = faceMask (⟨659, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0660 : bundle_7fec005515_supportIntersection (⟨660, by decide⟩ : Fin 1069) = faceMask (⟨660, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0661 : bundle_7fec005515_supportIntersection (⟨661, by decide⟩ : Fin 1069) = faceMask (⟨661, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0662 : bundle_7fec005515_supportIntersection (⟨662, by decide⟩ : Fin 1069) = faceMask (⟨662, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0663 : bundle_7fec005515_supportIntersection (⟨663, by decide⟩ : Fin 1069) = faceMask (⟨663, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0664 : bundle_7fec005515_supportIntersection (⟨664, by decide⟩ : Fin 1069) = faceMask (⟨664, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0665 : bundle_7fec005515_supportIntersection (⟨665, by decide⟩ : Fin 1069) = faceMask (⟨665, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0666 : bundle_7fec005515_supportIntersection (⟨666, by decide⟩ : Fin 1069) = faceMask (⟨666, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0667 : bundle_7fec005515_supportIntersection (⟨667, by decide⟩ : Fin 1069) = faceMask (⟨667, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0668 : bundle_7fec005515_supportIntersection (⟨668, by decide⟩ : Fin 1069) = faceMask (⟨668, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0669 : bundle_7fec005515_supportIntersection (⟨669, by decide⟩ : Fin 1069) = faceMask (⟨669, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0670 : bundle_7fec005515_supportIntersection (⟨670, by decide⟩ : Fin 1069) = faceMask (⟨670, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0671 : bundle_7fec005515_supportIntersection (⟨671, by decide⟩ : Fin 1069) = faceMask (⟨671, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0672 : bundle_7fec005515_supportIntersection (⟨672, by decide⟩ : Fin 1069) = faceMask (⟨672, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0673 : bundle_7fec005515_supportIntersection (⟨673, by decide⟩ : Fin 1069) = faceMask (⟨673, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0674 : bundle_7fec005515_supportIntersection (⟨674, by decide⟩ : Fin 1069) = faceMask (⟨674, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0675 : bundle_7fec005515_supportIntersection (⟨675, by decide⟩ : Fin 1069) = faceMask (⟨675, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0676 : bundle_7fec005515_supportIntersection (⟨676, by decide⟩ : Fin 1069) = faceMask (⟨676, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0677 : bundle_7fec005515_supportIntersection (⟨677, by decide⟩ : Fin 1069) = faceMask (⟨677, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0678 : bundle_7fec005515_supportIntersection (⟨678, by decide⟩ : Fin 1069) = faceMask (⟨678, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0679 : bundle_7fec005515_supportIntersection (⟨679, by decide⟩ : Fin 1069) = faceMask (⟨679, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0680 : bundle_7fec005515_supportIntersection (⟨680, by decide⟩ : Fin 1069) = faceMask (⟨680, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0681 : bundle_7fec005515_supportIntersection (⟨681, by decide⟩ : Fin 1069) = faceMask (⟨681, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0682 : bundle_7fec005515_supportIntersection (⟨682, by decide⟩ : Fin 1069) = faceMask (⟨682, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0683 : bundle_7fec005515_supportIntersection (⟨683, by decide⟩ : Fin 1069) = faceMask (⟨683, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0684 : bundle_7fec005515_supportIntersection (⟨684, by decide⟩ : Fin 1069) = faceMask (⟨684, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0685 : bundle_7fec005515_supportIntersection (⟨685, by decide⟩ : Fin 1069) = faceMask (⟨685, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0686 : bundle_7fec005515_supportIntersection (⟨686, by decide⟩ : Fin 1069) = faceMask (⟨686, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0687 : bundle_7fec005515_supportIntersection (⟨687, by decide⟩ : Fin 1069) = faceMask (⟨687, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0688 : bundle_7fec005515_supportIntersection (⟨688, by decide⟩ : Fin 1069) = faceMask (⟨688, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0689 : bundle_7fec005515_supportIntersection (⟨689, by decide⟩ : Fin 1069) = faceMask (⟨689, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0690 : bundle_7fec005515_supportIntersection (⟨690, by decide⟩ : Fin 1069) = faceMask (⟨690, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0691 : bundle_7fec005515_supportIntersection (⟨691, by decide⟩ : Fin 1069) = faceMask (⟨691, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0692 : bundle_7fec005515_supportIntersection (⟨692, by decide⟩ : Fin 1069) = faceMask (⟨692, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0693 : bundle_7fec005515_supportIntersection (⟨693, by decide⟩ : Fin 1069) = faceMask (⟨693, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0694 : bundle_7fec005515_supportIntersection (⟨694, by decide⟩ : Fin 1069) = faceMask (⟨694, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0695 : bundle_7fec005515_supportIntersection (⟨695, by decide⟩ : Fin 1069) = faceMask (⟨695, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0696 : bundle_7fec005515_supportIntersection (⟨696, by decide⟩ : Fin 1069) = faceMask (⟨696, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0697 : bundle_7fec005515_supportIntersection (⟨697, by decide⟩ : Fin 1069) = faceMask (⟨697, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0698 : bundle_7fec005515_supportIntersection (⟨698, by decide⟩ : Fin 1069) = faceMask (⟨698, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0699 : bundle_7fec005515_supportIntersection (⟨699, by decide⟩ : Fin 1069) = faceMask (⟨699, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0700 : bundle_7fec005515_supportIntersection (⟨700, by decide⟩ : Fin 1069) = faceMask (⟨700, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0701 : bundle_7fec005515_supportIntersection (⟨701, by decide⟩ : Fin 1069) = faceMask (⟨701, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0702 : bundle_7fec005515_supportIntersection (⟨702, by decide⟩ : Fin 1069) = faceMask (⟨702, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0703 : bundle_7fec005515_supportIntersection (⟨703, by decide⟩ : Fin 1069) = faceMask (⟨703, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0704 : bundle_7fec005515_supportIntersection (⟨704, by decide⟩ : Fin 1069) = faceMask (⟨704, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0705 : bundle_7fec005515_supportIntersection (⟨705, by decide⟩ : Fin 1069) = faceMask (⟨705, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0706 : bundle_7fec005515_supportIntersection (⟨706, by decide⟩ : Fin 1069) = faceMask (⟨706, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0707 : bundle_7fec005515_supportIntersection (⟨707, by decide⟩ : Fin 1069) = faceMask (⟨707, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0708 : bundle_7fec005515_supportIntersection (⟨708, by decide⟩ : Fin 1069) = faceMask (⟨708, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0709 : bundle_7fec005515_supportIntersection (⟨709, by decide⟩ : Fin 1069) = faceMask (⟨709, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0710 : bundle_7fec005515_supportIntersection (⟨710, by decide⟩ : Fin 1069) = faceMask (⟨710, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0711 : bundle_7fec005515_supportIntersection (⟨711, by decide⟩ : Fin 1069) = faceMask (⟨711, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0712 : bundle_7fec005515_supportIntersection (⟨712, by decide⟩ : Fin 1069) = faceMask (⟨712, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0713 : bundle_7fec005515_supportIntersection (⟨713, by decide⟩ : Fin 1069) = faceMask (⟨713, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0714 : bundle_7fec005515_supportIntersection (⟨714, by decide⟩ : Fin 1069) = faceMask (⟨714, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0715 : bundle_7fec005515_supportIntersection (⟨715, by decide⟩ : Fin 1069) = faceMask (⟨715, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0716 : bundle_7fec005515_supportIntersection (⟨716, by decide⟩ : Fin 1069) = faceMask (⟨716, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0717 : bundle_7fec005515_supportIntersection (⟨717, by decide⟩ : Fin 1069) = faceMask (⟨717, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0718 : bundle_7fec005515_supportIntersection (⟨718, by decide⟩ : Fin 1069) = faceMask (⟨718, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0719 : bundle_7fec005515_supportIntersection (⟨719, by decide⟩ : Fin 1069) = faceMask (⟨719, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0720 : bundle_7fec005515_supportIntersection (⟨720, by decide⟩ : Fin 1069) = faceMask (⟨720, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0721 : bundle_7fec005515_supportIntersection (⟨721, by decide⟩ : Fin 1069) = faceMask (⟨721, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0722 : bundle_7fec005515_supportIntersection (⟨722, by decide⟩ : Fin 1069) = faceMask (⟨722, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0723 : bundle_7fec005515_supportIntersection (⟨723, by decide⟩ : Fin 1069) = faceMask (⟨723, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0724 : bundle_7fec005515_supportIntersection (⟨724, by decide⟩ : Fin 1069) = faceMask (⟨724, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0725 : bundle_7fec005515_supportIntersection (⟨725, by decide⟩ : Fin 1069) = faceMask (⟨725, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0726 : bundle_7fec005515_supportIntersection (⟨726, by decide⟩ : Fin 1069) = faceMask (⟨726, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0727 : bundle_7fec005515_supportIntersection (⟨727, by decide⟩ : Fin 1069) = faceMask (⟨727, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0728 : bundle_7fec005515_supportIntersection (⟨728, by decide⟩ : Fin 1069) = faceMask (⟨728, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0729 : bundle_7fec005515_supportIntersection (⟨729, by decide⟩ : Fin 1069) = faceMask (⟨729, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0730 : bundle_7fec005515_supportIntersection (⟨730, by decide⟩ : Fin 1069) = faceMask (⟨730, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0731 : bundle_7fec005515_supportIntersection (⟨731, by decide⟩ : Fin 1069) = faceMask (⟨731, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0732 : bundle_7fec005515_supportIntersection (⟨732, by decide⟩ : Fin 1069) = faceMask (⟨732, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0733 : bundle_7fec005515_supportIntersection (⟨733, by decide⟩ : Fin 1069) = faceMask (⟨733, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0734 : bundle_7fec005515_supportIntersection (⟨734, by decide⟩ : Fin 1069) = faceMask (⟨734, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0735 : bundle_7fec005515_supportIntersection (⟨735, by decide⟩ : Fin 1069) = faceMask (⟨735, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0736 : bundle_7fec005515_supportIntersection (⟨736, by decide⟩ : Fin 1069) = faceMask (⟨736, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0737 : bundle_7fec005515_supportIntersection (⟨737, by decide⟩ : Fin 1069) = faceMask (⟨737, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0738 : bundle_7fec005515_supportIntersection (⟨738, by decide⟩ : Fin 1069) = faceMask (⟨738, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0739 : bundle_7fec005515_supportIntersection (⟨739, by decide⟩ : Fin 1069) = faceMask (⟨739, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0740 : bundle_7fec005515_supportIntersection (⟨740, by decide⟩ : Fin 1069) = faceMask (⟨740, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0741 : bundle_7fec005515_supportIntersection (⟨741, by decide⟩ : Fin 1069) = faceMask (⟨741, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0742 : bundle_7fec005515_supportIntersection (⟨742, by decide⟩ : Fin 1069) = faceMask (⟨742, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0743 : bundle_7fec005515_supportIntersection (⟨743, by decide⟩ : Fin 1069) = faceMask (⟨743, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0744 : bundle_7fec005515_supportIntersection (⟨744, by decide⟩ : Fin 1069) = faceMask (⟨744, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0745 : bundle_7fec005515_supportIntersection (⟨745, by decide⟩ : Fin 1069) = faceMask (⟨745, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0746 : bundle_7fec005515_supportIntersection (⟨746, by decide⟩ : Fin 1069) = faceMask (⟨746, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0747 : bundle_7fec005515_supportIntersection (⟨747, by decide⟩ : Fin 1069) = faceMask (⟨747, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0748 : bundle_7fec005515_supportIntersection (⟨748, by decide⟩ : Fin 1069) = faceMask (⟨748, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0749 : bundle_7fec005515_supportIntersection (⟨749, by decide⟩ : Fin 1069) = faceMask (⟨749, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0750 : bundle_7fec005515_supportIntersection (⟨750, by decide⟩ : Fin 1069) = faceMask (⟨750, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0751 : bundle_7fec005515_supportIntersection (⟨751, by decide⟩ : Fin 1069) = faceMask (⟨751, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0752 : bundle_7fec005515_supportIntersection (⟨752, by decide⟩ : Fin 1069) = faceMask (⟨752, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0753 : bundle_7fec005515_supportIntersection (⟨753, by decide⟩ : Fin 1069) = faceMask (⟨753, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0754 : bundle_7fec005515_supportIntersection (⟨754, by decide⟩ : Fin 1069) = faceMask (⟨754, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0755 : bundle_7fec005515_supportIntersection (⟨755, by decide⟩ : Fin 1069) = faceMask (⟨755, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0756 : bundle_7fec005515_supportIntersection (⟨756, by decide⟩ : Fin 1069) = faceMask (⟨756, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0757 : bundle_7fec005515_supportIntersection (⟨757, by decide⟩ : Fin 1069) = faceMask (⟨757, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0758 : bundle_7fec005515_supportIntersection (⟨758, by decide⟩ : Fin 1069) = faceMask (⟨758, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0759 : bundle_7fec005515_supportIntersection (⟨759, by decide⟩ : Fin 1069) = faceMask (⟨759, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0760 : bundle_7fec005515_supportIntersection (⟨760, by decide⟩ : Fin 1069) = faceMask (⟨760, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0761 : bundle_7fec005515_supportIntersection (⟨761, by decide⟩ : Fin 1069) = faceMask (⟨761, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0762 : bundle_7fec005515_supportIntersection (⟨762, by decide⟩ : Fin 1069) = faceMask (⟨762, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0763 : bundle_7fec005515_supportIntersection (⟨763, by decide⟩ : Fin 1069) = faceMask (⟨763, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0764 : bundle_7fec005515_supportIntersection (⟨764, by decide⟩ : Fin 1069) = faceMask (⟨764, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0765 : bundle_7fec005515_supportIntersection (⟨765, by decide⟩ : Fin 1069) = faceMask (⟨765, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0766 : bundle_7fec005515_supportIntersection (⟨766, by decide⟩ : Fin 1069) = faceMask (⟨766, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0767 : bundle_7fec005515_supportIntersection (⟨767, by decide⟩ : Fin 1069) = faceMask (⟨767, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0768 : bundle_7fec005515_supportIntersection (⟨768, by decide⟩ : Fin 1069) = faceMask (⟨768, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0769 : bundle_7fec005515_supportIntersection (⟨769, by decide⟩ : Fin 1069) = faceMask (⟨769, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0770 : bundle_7fec005515_supportIntersection (⟨770, by decide⟩ : Fin 1069) = faceMask (⟨770, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0771 : bundle_7fec005515_supportIntersection (⟨771, by decide⟩ : Fin 1069) = faceMask (⟨771, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0772 : bundle_7fec005515_supportIntersection (⟨772, by decide⟩ : Fin 1069) = faceMask (⟨772, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0773 : bundle_7fec005515_supportIntersection (⟨773, by decide⟩ : Fin 1069) = faceMask (⟨773, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0774 : bundle_7fec005515_supportIntersection (⟨774, by decide⟩ : Fin 1069) = faceMask (⟨774, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0775 : bundle_7fec005515_supportIntersection (⟨775, by decide⟩ : Fin 1069) = faceMask (⟨775, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0776 : bundle_7fec005515_supportIntersection (⟨776, by decide⟩ : Fin 1069) = faceMask (⟨776, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0777 : bundle_7fec005515_supportIntersection (⟨777, by decide⟩ : Fin 1069) = faceMask (⟨777, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0778 : bundle_7fec005515_supportIntersection (⟨778, by decide⟩ : Fin 1069) = faceMask (⟨778, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0779 : bundle_7fec005515_supportIntersection (⟨779, by decide⟩ : Fin 1069) = faceMask (⟨779, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0780 : bundle_7fec005515_supportIntersection (⟨780, by decide⟩ : Fin 1069) = faceMask (⟨780, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0781 : bundle_7fec005515_supportIntersection (⟨781, by decide⟩ : Fin 1069) = faceMask (⟨781, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0782 : bundle_7fec005515_supportIntersection (⟨782, by decide⟩ : Fin 1069) = faceMask (⟨782, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0783 : bundle_7fec005515_supportIntersection (⟨783, by decide⟩ : Fin 1069) = faceMask (⟨783, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0784 : bundle_7fec005515_supportIntersection (⟨784, by decide⟩ : Fin 1069) = faceMask (⟨784, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0785 : bundle_7fec005515_supportIntersection (⟨785, by decide⟩ : Fin 1069) = faceMask (⟨785, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0786 : bundle_7fec005515_supportIntersection (⟨786, by decide⟩ : Fin 1069) = faceMask (⟨786, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0787 : bundle_7fec005515_supportIntersection (⟨787, by decide⟩ : Fin 1069) = faceMask (⟨787, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0788 : bundle_7fec005515_supportIntersection (⟨788, by decide⟩ : Fin 1069) = faceMask (⟨788, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0789 : bundle_7fec005515_supportIntersection (⟨789, by decide⟩ : Fin 1069) = faceMask (⟨789, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0790 : bundle_7fec005515_supportIntersection (⟨790, by decide⟩ : Fin 1069) = faceMask (⟨790, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0791 : bundle_7fec005515_supportIntersection (⟨791, by decide⟩ : Fin 1069) = faceMask (⟨791, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0792 : bundle_7fec005515_supportIntersection (⟨792, by decide⟩ : Fin 1069) = faceMask (⟨792, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0793 : bundle_7fec005515_supportIntersection (⟨793, by decide⟩ : Fin 1069) = faceMask (⟨793, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0794 : bundle_7fec005515_supportIntersection (⟨794, by decide⟩ : Fin 1069) = faceMask (⟨794, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0795 : bundle_7fec005515_supportIntersection (⟨795, by decide⟩ : Fin 1069) = faceMask (⟨795, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0796 : bundle_7fec005515_supportIntersection (⟨796, by decide⟩ : Fin 1069) = faceMask (⟨796, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0797 : bundle_7fec005515_supportIntersection (⟨797, by decide⟩ : Fin 1069) = faceMask (⟨797, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0798 : bundle_7fec005515_supportIntersection (⟨798, by decide⟩ : Fin 1069) = faceMask (⟨798, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0799 : bundle_7fec005515_supportIntersection (⟨799, by decide⟩ : Fin 1069) = faceMask (⟨799, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0800 : bundle_7fec005515_supportIntersection (⟨800, by decide⟩ : Fin 1069) = faceMask (⟨800, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0801 : bundle_7fec005515_supportIntersection (⟨801, by decide⟩ : Fin 1069) = faceMask (⟨801, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0802 : bundle_7fec005515_supportIntersection (⟨802, by decide⟩ : Fin 1069) = faceMask (⟨802, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0803 : bundle_7fec005515_supportIntersection (⟨803, by decide⟩ : Fin 1069) = faceMask (⟨803, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0804 : bundle_7fec005515_supportIntersection (⟨804, by decide⟩ : Fin 1069) = faceMask (⟨804, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0805 : bundle_7fec005515_supportIntersection (⟨805, by decide⟩ : Fin 1069) = faceMask (⟨805, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0806 : bundle_7fec005515_supportIntersection (⟨806, by decide⟩ : Fin 1069) = faceMask (⟨806, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0807 : bundle_7fec005515_supportIntersection (⟨807, by decide⟩ : Fin 1069) = faceMask (⟨807, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0808 : bundle_7fec005515_supportIntersection (⟨808, by decide⟩ : Fin 1069) = faceMask (⟨808, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0809 : bundle_7fec005515_supportIntersection (⟨809, by decide⟩ : Fin 1069) = faceMask (⟨809, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0810 : bundle_7fec005515_supportIntersection (⟨810, by decide⟩ : Fin 1069) = faceMask (⟨810, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0811 : bundle_7fec005515_supportIntersection (⟨811, by decide⟩ : Fin 1069) = faceMask (⟨811, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0812 : bundle_7fec005515_supportIntersection (⟨812, by decide⟩ : Fin 1069) = faceMask (⟨812, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0813 : bundle_7fec005515_supportIntersection (⟨813, by decide⟩ : Fin 1069) = faceMask (⟨813, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0814 : bundle_7fec005515_supportIntersection (⟨814, by decide⟩ : Fin 1069) = faceMask (⟨814, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0815 : bundle_7fec005515_supportIntersection (⟨815, by decide⟩ : Fin 1069) = faceMask (⟨815, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0816 : bundle_7fec005515_supportIntersection (⟨816, by decide⟩ : Fin 1069) = faceMask (⟨816, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0817 : bundle_7fec005515_supportIntersection (⟨817, by decide⟩ : Fin 1069) = faceMask (⟨817, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0818 : bundle_7fec005515_supportIntersection (⟨818, by decide⟩ : Fin 1069) = faceMask (⟨818, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0819 : bundle_7fec005515_supportIntersection (⟨819, by decide⟩ : Fin 1069) = faceMask (⟨819, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0820 : bundle_7fec005515_supportIntersection (⟨820, by decide⟩ : Fin 1069) = faceMask (⟨820, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0821 : bundle_7fec005515_supportIntersection (⟨821, by decide⟩ : Fin 1069) = faceMask (⟨821, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0822 : bundle_7fec005515_supportIntersection (⟨822, by decide⟩ : Fin 1069) = faceMask (⟨822, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0823 : bundle_7fec005515_supportIntersection (⟨823, by decide⟩ : Fin 1069) = faceMask (⟨823, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0824 : bundle_7fec005515_supportIntersection (⟨824, by decide⟩ : Fin 1069) = faceMask (⟨824, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0825 : bundle_7fec005515_supportIntersection (⟨825, by decide⟩ : Fin 1069) = faceMask (⟨825, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0826 : bundle_7fec005515_supportIntersection (⟨826, by decide⟩ : Fin 1069) = faceMask (⟨826, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0827 : bundle_7fec005515_supportIntersection (⟨827, by decide⟩ : Fin 1069) = faceMask (⟨827, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0828 : bundle_7fec005515_supportIntersection (⟨828, by decide⟩ : Fin 1069) = faceMask (⟨828, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0829 : bundle_7fec005515_supportIntersection (⟨829, by decide⟩ : Fin 1069) = faceMask (⟨829, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0830 : bundle_7fec005515_supportIntersection (⟨830, by decide⟩ : Fin 1069) = faceMask (⟨830, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0831 : bundle_7fec005515_supportIntersection (⟨831, by decide⟩ : Fin 1069) = faceMask (⟨831, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0832 : bundle_7fec005515_supportIntersection (⟨832, by decide⟩ : Fin 1069) = faceMask (⟨832, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0833 : bundle_7fec005515_supportIntersection (⟨833, by decide⟩ : Fin 1069) = faceMask (⟨833, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0834 : bundle_7fec005515_supportIntersection (⟨834, by decide⟩ : Fin 1069) = faceMask (⟨834, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0835 : bundle_7fec005515_supportIntersection (⟨835, by decide⟩ : Fin 1069) = faceMask (⟨835, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0836 : bundle_7fec005515_supportIntersection (⟨836, by decide⟩ : Fin 1069) = faceMask (⟨836, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0837 : bundle_7fec005515_supportIntersection (⟨837, by decide⟩ : Fin 1069) = faceMask (⟨837, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0838 : bundle_7fec005515_supportIntersection (⟨838, by decide⟩ : Fin 1069) = faceMask (⟨838, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0839 : bundle_7fec005515_supportIntersection (⟨839, by decide⟩ : Fin 1069) = faceMask (⟨839, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0840 : bundle_7fec005515_supportIntersection (⟨840, by decide⟩ : Fin 1069) = faceMask (⟨840, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0841 : bundle_7fec005515_supportIntersection (⟨841, by decide⟩ : Fin 1069) = faceMask (⟨841, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0842 : bundle_7fec005515_supportIntersection (⟨842, by decide⟩ : Fin 1069) = faceMask (⟨842, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0843 : bundle_7fec005515_supportIntersection (⟨843, by decide⟩ : Fin 1069) = faceMask (⟨843, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0844 : bundle_7fec005515_supportIntersection (⟨844, by decide⟩ : Fin 1069) = faceMask (⟨844, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0845 : bundle_7fec005515_supportIntersection (⟨845, by decide⟩ : Fin 1069) = faceMask (⟨845, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0846 : bundle_7fec005515_supportIntersection (⟨846, by decide⟩ : Fin 1069) = faceMask (⟨846, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0847 : bundle_7fec005515_supportIntersection (⟨847, by decide⟩ : Fin 1069) = faceMask (⟨847, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0848 : bundle_7fec005515_supportIntersection (⟨848, by decide⟩ : Fin 1069) = faceMask (⟨848, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0849 : bundle_7fec005515_supportIntersection (⟨849, by decide⟩ : Fin 1069) = faceMask (⟨849, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0850 : bundle_7fec005515_supportIntersection (⟨850, by decide⟩ : Fin 1069) = faceMask (⟨850, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0851 : bundle_7fec005515_supportIntersection (⟨851, by decide⟩ : Fin 1069) = faceMask (⟨851, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0852 : bundle_7fec005515_supportIntersection (⟨852, by decide⟩ : Fin 1069) = faceMask (⟨852, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0853 : bundle_7fec005515_supportIntersection (⟨853, by decide⟩ : Fin 1069) = faceMask (⟨853, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0854 : bundle_7fec005515_supportIntersection (⟨854, by decide⟩ : Fin 1069) = faceMask (⟨854, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0855 : bundle_7fec005515_supportIntersection (⟨855, by decide⟩ : Fin 1069) = faceMask (⟨855, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0856 : bundle_7fec005515_supportIntersection (⟨856, by decide⟩ : Fin 1069) = faceMask (⟨856, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0857 : bundle_7fec005515_supportIntersection (⟨857, by decide⟩ : Fin 1069) = faceMask (⟨857, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0858 : bundle_7fec005515_supportIntersection (⟨858, by decide⟩ : Fin 1069) = faceMask (⟨858, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0859 : bundle_7fec005515_supportIntersection (⟨859, by decide⟩ : Fin 1069) = faceMask (⟨859, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0860 : bundle_7fec005515_supportIntersection (⟨860, by decide⟩ : Fin 1069) = faceMask (⟨860, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0861 : bundle_7fec005515_supportIntersection (⟨861, by decide⟩ : Fin 1069) = faceMask (⟨861, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0862 : bundle_7fec005515_supportIntersection (⟨862, by decide⟩ : Fin 1069) = faceMask (⟨862, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0863 : bundle_7fec005515_supportIntersection (⟨863, by decide⟩ : Fin 1069) = faceMask (⟨863, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0864 : bundle_7fec005515_supportIntersection (⟨864, by decide⟩ : Fin 1069) = faceMask (⟨864, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0865 : bundle_7fec005515_supportIntersection (⟨865, by decide⟩ : Fin 1069) = faceMask (⟨865, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0866 : bundle_7fec005515_supportIntersection (⟨866, by decide⟩ : Fin 1069) = faceMask (⟨866, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0867 : bundle_7fec005515_supportIntersection (⟨867, by decide⟩ : Fin 1069) = faceMask (⟨867, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0868 : bundle_7fec005515_supportIntersection (⟨868, by decide⟩ : Fin 1069) = faceMask (⟨868, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0869 : bundle_7fec005515_supportIntersection (⟨869, by decide⟩ : Fin 1069) = faceMask (⟨869, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0870 : bundle_7fec005515_supportIntersection (⟨870, by decide⟩ : Fin 1069) = faceMask (⟨870, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0871 : bundle_7fec005515_supportIntersection (⟨871, by decide⟩ : Fin 1069) = faceMask (⟨871, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0872 : bundle_7fec005515_supportIntersection (⟨872, by decide⟩ : Fin 1069) = faceMask (⟨872, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0873 : bundle_7fec005515_supportIntersection (⟨873, by decide⟩ : Fin 1069) = faceMask (⟨873, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0874 : bundle_7fec005515_supportIntersection (⟨874, by decide⟩ : Fin 1069) = faceMask (⟨874, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0875 : bundle_7fec005515_supportIntersection (⟨875, by decide⟩ : Fin 1069) = faceMask (⟨875, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0876 : bundle_7fec005515_supportIntersection (⟨876, by decide⟩ : Fin 1069) = faceMask (⟨876, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0877 : bundle_7fec005515_supportIntersection (⟨877, by decide⟩ : Fin 1069) = faceMask (⟨877, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0878 : bundle_7fec005515_supportIntersection (⟨878, by decide⟩ : Fin 1069) = faceMask (⟨878, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0879 : bundle_7fec005515_supportIntersection (⟨879, by decide⟩ : Fin 1069) = faceMask (⟨879, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0880 : bundle_7fec005515_supportIntersection (⟨880, by decide⟩ : Fin 1069) = faceMask (⟨880, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0881 : bundle_7fec005515_supportIntersection (⟨881, by decide⟩ : Fin 1069) = faceMask (⟨881, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0882 : bundle_7fec005515_supportIntersection (⟨882, by decide⟩ : Fin 1069) = faceMask (⟨882, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0883 : bundle_7fec005515_supportIntersection (⟨883, by decide⟩ : Fin 1069) = faceMask (⟨883, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0884 : bundle_7fec005515_supportIntersection (⟨884, by decide⟩ : Fin 1069) = faceMask (⟨884, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0885 : bundle_7fec005515_supportIntersection (⟨885, by decide⟩ : Fin 1069) = faceMask (⟨885, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0886 : bundle_7fec005515_supportIntersection (⟨886, by decide⟩ : Fin 1069) = faceMask (⟨886, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0887 : bundle_7fec005515_supportIntersection (⟨887, by decide⟩ : Fin 1069) = faceMask (⟨887, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0888 : bundle_7fec005515_supportIntersection (⟨888, by decide⟩ : Fin 1069) = faceMask (⟨888, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0889 : bundle_7fec005515_supportIntersection (⟨889, by decide⟩ : Fin 1069) = faceMask (⟨889, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0890 : bundle_7fec005515_supportIntersection (⟨890, by decide⟩ : Fin 1069) = faceMask (⟨890, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0891 : bundle_7fec005515_supportIntersection (⟨891, by decide⟩ : Fin 1069) = faceMask (⟨891, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0892 : bundle_7fec005515_supportIntersection (⟨892, by decide⟩ : Fin 1069) = faceMask (⟨892, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0893 : bundle_7fec005515_supportIntersection (⟨893, by decide⟩ : Fin 1069) = faceMask (⟨893, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0894 : bundle_7fec005515_supportIntersection (⟨894, by decide⟩ : Fin 1069) = faceMask (⟨894, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0895 : bundle_7fec005515_supportIntersection (⟨895, by decide⟩ : Fin 1069) = faceMask (⟨895, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0896 : bundle_7fec005515_supportIntersection (⟨896, by decide⟩ : Fin 1069) = faceMask (⟨896, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0897 : bundle_7fec005515_supportIntersection (⟨897, by decide⟩ : Fin 1069) = faceMask (⟨897, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0898 : bundle_7fec005515_supportIntersection (⟨898, by decide⟩ : Fin 1069) = faceMask (⟨898, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0899 : bundle_7fec005515_supportIntersection (⟨899, by decide⟩ : Fin 1069) = faceMask (⟨899, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0900 : bundle_7fec005515_supportIntersection (⟨900, by decide⟩ : Fin 1069) = faceMask (⟨900, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0901 : bundle_7fec005515_supportIntersection (⟨901, by decide⟩ : Fin 1069) = faceMask (⟨901, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0902 : bundle_7fec005515_supportIntersection (⟨902, by decide⟩ : Fin 1069) = faceMask (⟨902, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0903 : bundle_7fec005515_supportIntersection (⟨903, by decide⟩ : Fin 1069) = faceMask (⟨903, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0904 : bundle_7fec005515_supportIntersection (⟨904, by decide⟩ : Fin 1069) = faceMask (⟨904, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0905 : bundle_7fec005515_supportIntersection (⟨905, by decide⟩ : Fin 1069) = faceMask (⟨905, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0906 : bundle_7fec005515_supportIntersection (⟨906, by decide⟩ : Fin 1069) = faceMask (⟨906, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0907 : bundle_7fec005515_supportIntersection (⟨907, by decide⟩ : Fin 1069) = faceMask (⟨907, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0908 : bundle_7fec005515_supportIntersection (⟨908, by decide⟩ : Fin 1069) = faceMask (⟨908, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0909 : bundle_7fec005515_supportIntersection (⟨909, by decide⟩ : Fin 1069) = faceMask (⟨909, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0910 : bundle_7fec005515_supportIntersection (⟨910, by decide⟩ : Fin 1069) = faceMask (⟨910, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0911 : bundle_7fec005515_supportIntersection (⟨911, by decide⟩ : Fin 1069) = faceMask (⟨911, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0912 : bundle_7fec005515_supportIntersection (⟨912, by decide⟩ : Fin 1069) = faceMask (⟨912, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0913 : bundle_7fec005515_supportIntersection (⟨913, by decide⟩ : Fin 1069) = faceMask (⟨913, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0914 : bundle_7fec005515_supportIntersection (⟨914, by decide⟩ : Fin 1069) = faceMask (⟨914, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0915 : bundle_7fec005515_supportIntersection (⟨915, by decide⟩ : Fin 1069) = faceMask (⟨915, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0916 : bundle_7fec005515_supportIntersection (⟨916, by decide⟩ : Fin 1069) = faceMask (⟨916, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0917 : bundle_7fec005515_supportIntersection (⟨917, by decide⟩ : Fin 1069) = faceMask (⟨917, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0918 : bundle_7fec005515_supportIntersection (⟨918, by decide⟩ : Fin 1069) = faceMask (⟨918, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0919 : bundle_7fec005515_supportIntersection (⟨919, by decide⟩ : Fin 1069) = faceMask (⟨919, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0920 : bundle_7fec005515_supportIntersection (⟨920, by decide⟩ : Fin 1069) = faceMask (⟨920, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0921 : bundle_7fec005515_supportIntersection (⟨921, by decide⟩ : Fin 1069) = faceMask (⟨921, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0922 : bundle_7fec005515_supportIntersection (⟨922, by decide⟩ : Fin 1069) = faceMask (⟨922, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0923 : bundle_7fec005515_supportIntersection (⟨923, by decide⟩ : Fin 1069) = faceMask (⟨923, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0924 : bundle_7fec005515_supportIntersection (⟨924, by decide⟩ : Fin 1069) = faceMask (⟨924, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0925 : bundle_7fec005515_supportIntersection (⟨925, by decide⟩ : Fin 1069) = faceMask (⟨925, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0926 : bundle_7fec005515_supportIntersection (⟨926, by decide⟩ : Fin 1069) = faceMask (⟨926, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0927 : bundle_7fec005515_supportIntersection (⟨927, by decide⟩ : Fin 1069) = faceMask (⟨927, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0928 : bundle_7fec005515_supportIntersection (⟨928, by decide⟩ : Fin 1069) = faceMask (⟨928, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0929 : bundle_7fec005515_supportIntersection (⟨929, by decide⟩ : Fin 1069) = faceMask (⟨929, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0930 : bundle_7fec005515_supportIntersection (⟨930, by decide⟩ : Fin 1069) = faceMask (⟨930, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0931 : bundle_7fec005515_supportIntersection (⟨931, by decide⟩ : Fin 1069) = faceMask (⟨931, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0932 : bundle_7fec005515_supportIntersection (⟨932, by decide⟩ : Fin 1069) = faceMask (⟨932, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0933 : bundle_7fec005515_supportIntersection (⟨933, by decide⟩ : Fin 1069) = faceMask (⟨933, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0934 : bundle_7fec005515_supportIntersection (⟨934, by decide⟩ : Fin 1069) = faceMask (⟨934, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0935 : bundle_7fec005515_supportIntersection (⟨935, by decide⟩ : Fin 1069) = faceMask (⟨935, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0936 : bundle_7fec005515_supportIntersection (⟨936, by decide⟩ : Fin 1069) = faceMask (⟨936, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0937 : bundle_7fec005515_supportIntersection (⟨937, by decide⟩ : Fin 1069) = faceMask (⟨937, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0938 : bundle_7fec005515_supportIntersection (⟨938, by decide⟩ : Fin 1069) = faceMask (⟨938, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0939 : bundle_7fec005515_supportIntersection (⟨939, by decide⟩ : Fin 1069) = faceMask (⟨939, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0940 : bundle_7fec005515_supportIntersection (⟨940, by decide⟩ : Fin 1069) = faceMask (⟨940, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0941 : bundle_7fec005515_supportIntersection (⟨941, by decide⟩ : Fin 1069) = faceMask (⟨941, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0942 : bundle_7fec005515_supportIntersection (⟨942, by decide⟩ : Fin 1069) = faceMask (⟨942, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0943 : bundle_7fec005515_supportIntersection (⟨943, by decide⟩ : Fin 1069) = faceMask (⟨943, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0944 : bundle_7fec005515_supportIntersection (⟨944, by decide⟩ : Fin 1069) = faceMask (⟨944, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0945 : bundle_7fec005515_supportIntersection (⟨945, by decide⟩ : Fin 1069) = faceMask (⟨945, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0946 : bundle_7fec005515_supportIntersection (⟨946, by decide⟩ : Fin 1069) = faceMask (⟨946, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0947 : bundle_7fec005515_supportIntersection (⟨947, by decide⟩ : Fin 1069) = faceMask (⟨947, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0948 : bundle_7fec005515_supportIntersection (⟨948, by decide⟩ : Fin 1069) = faceMask (⟨948, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0949 : bundle_7fec005515_supportIntersection (⟨949, by decide⟩ : Fin 1069) = faceMask (⟨949, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0950 : bundle_7fec005515_supportIntersection (⟨950, by decide⟩ : Fin 1069) = faceMask (⟨950, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0951 : bundle_7fec005515_supportIntersection (⟨951, by decide⟩ : Fin 1069) = faceMask (⟨951, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0952 : bundle_7fec005515_supportIntersection (⟨952, by decide⟩ : Fin 1069) = faceMask (⟨952, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0953 : bundle_7fec005515_supportIntersection (⟨953, by decide⟩ : Fin 1069) = faceMask (⟨953, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0954 : bundle_7fec005515_supportIntersection (⟨954, by decide⟩ : Fin 1069) = faceMask (⟨954, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0955 : bundle_7fec005515_supportIntersection (⟨955, by decide⟩ : Fin 1069) = faceMask (⟨955, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0956 : bundle_7fec005515_supportIntersection (⟨956, by decide⟩ : Fin 1069) = faceMask (⟨956, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0957 : bundle_7fec005515_supportIntersection (⟨957, by decide⟩ : Fin 1069) = faceMask (⟨957, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0958 : bundle_7fec005515_supportIntersection (⟨958, by decide⟩ : Fin 1069) = faceMask (⟨958, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0959 : bundle_7fec005515_supportIntersection (⟨959, by decide⟩ : Fin 1069) = faceMask (⟨959, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0960 : bundle_7fec005515_supportIntersection (⟨960, by decide⟩ : Fin 1069) = faceMask (⟨960, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0961 : bundle_7fec005515_supportIntersection (⟨961, by decide⟩ : Fin 1069) = faceMask (⟨961, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0962 : bundle_7fec005515_supportIntersection (⟨962, by decide⟩ : Fin 1069) = faceMask (⟨962, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0963 : bundle_7fec005515_supportIntersection (⟨963, by decide⟩ : Fin 1069) = faceMask (⟨963, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0964 : bundle_7fec005515_supportIntersection (⟨964, by decide⟩ : Fin 1069) = faceMask (⟨964, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0965 : bundle_7fec005515_supportIntersection (⟨965, by decide⟩ : Fin 1069) = faceMask (⟨965, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0966 : bundle_7fec005515_supportIntersection (⟨966, by decide⟩ : Fin 1069) = faceMask (⟨966, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0967 : bundle_7fec005515_supportIntersection (⟨967, by decide⟩ : Fin 1069) = faceMask (⟨967, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0968 : bundle_7fec005515_supportIntersection (⟨968, by decide⟩ : Fin 1069) = faceMask (⟨968, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0969 : bundle_7fec005515_supportIntersection (⟨969, by decide⟩ : Fin 1069) = faceMask (⟨969, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0970 : bundle_7fec005515_supportIntersection (⟨970, by decide⟩ : Fin 1069) = faceMask (⟨970, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0971 : bundle_7fec005515_supportIntersection (⟨971, by decide⟩ : Fin 1069) = faceMask (⟨971, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0972 : bundle_7fec005515_supportIntersection (⟨972, by decide⟩ : Fin 1069) = faceMask (⟨972, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0973 : bundle_7fec005515_supportIntersection (⟨973, by decide⟩ : Fin 1069) = faceMask (⟨973, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0974 : bundle_7fec005515_supportIntersection (⟨974, by decide⟩ : Fin 1069) = faceMask (⟨974, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0975 : bundle_7fec005515_supportIntersection (⟨975, by decide⟩ : Fin 1069) = faceMask (⟨975, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0976 : bundle_7fec005515_supportIntersection (⟨976, by decide⟩ : Fin 1069) = faceMask (⟨976, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0977 : bundle_7fec005515_supportIntersection (⟨977, by decide⟩ : Fin 1069) = faceMask (⟨977, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0978 : bundle_7fec005515_supportIntersection (⟨978, by decide⟩ : Fin 1069) = faceMask (⟨978, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0979 : bundle_7fec005515_supportIntersection (⟨979, by decide⟩ : Fin 1069) = faceMask (⟨979, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0980 : bundle_7fec005515_supportIntersection (⟨980, by decide⟩ : Fin 1069) = faceMask (⟨980, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0981 : bundle_7fec005515_supportIntersection (⟨981, by decide⟩ : Fin 1069) = faceMask (⟨981, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0982 : bundle_7fec005515_supportIntersection (⟨982, by decide⟩ : Fin 1069) = faceMask (⟨982, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0983 : bundle_7fec005515_supportIntersection (⟨983, by decide⟩ : Fin 1069) = faceMask (⟨983, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0984 : bundle_7fec005515_supportIntersection (⟨984, by decide⟩ : Fin 1069) = faceMask (⟨984, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0985 : bundle_7fec005515_supportIntersection (⟨985, by decide⟩ : Fin 1069) = faceMask (⟨985, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0986 : bundle_7fec005515_supportIntersection (⟨986, by decide⟩ : Fin 1069) = faceMask (⟨986, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0987 : bundle_7fec005515_supportIntersection (⟨987, by decide⟩ : Fin 1069) = faceMask (⟨987, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0988 : bundle_7fec005515_supportIntersection (⟨988, by decide⟩ : Fin 1069) = faceMask (⟨988, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0989 : bundle_7fec005515_supportIntersection (⟨989, by decide⟩ : Fin 1069) = faceMask (⟨989, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0990 : bundle_7fec005515_supportIntersection (⟨990, by decide⟩ : Fin 1069) = faceMask (⟨990, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0991 : bundle_7fec005515_supportIntersection (⟨991, by decide⟩ : Fin 1069) = faceMask (⟨991, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0992 : bundle_7fec005515_supportIntersection (⟨992, by decide⟩ : Fin 1069) = faceMask (⟨992, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0993 : bundle_7fec005515_supportIntersection (⟨993, by decide⟩ : Fin 1069) = faceMask (⟨993, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0994 : bundle_7fec005515_supportIntersection (⟨994, by decide⟩ : Fin 1069) = faceMask (⟨994, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0995 : bundle_7fec005515_supportIntersection (⟨995, by decide⟩ : Fin 1069) = faceMask (⟨995, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0996 : bundle_7fec005515_supportIntersection (⟨996, by decide⟩ : Fin 1069) = faceMask (⟨996, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0997 : bundle_7fec005515_supportIntersection (⟨997, by decide⟩ : Fin 1069) = faceMask (⟨997, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0998 : bundle_7fec005515_supportIntersection (⟨998, by decide⟩ : Fin 1069) = faceMask (⟨998, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support0999 : bundle_7fec005515_supportIntersection (⟨999, by decide⟩ : Fin 1069) = faceMask (⟨999, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1000 : bundle_7fec005515_supportIntersection (⟨1000, by decide⟩ : Fin 1069) = faceMask (⟨1000, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1001 : bundle_7fec005515_supportIntersection (⟨1001, by decide⟩ : Fin 1069) = faceMask (⟨1001, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1002 : bundle_7fec005515_supportIntersection (⟨1002, by decide⟩ : Fin 1069) = faceMask (⟨1002, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1003 : bundle_7fec005515_supportIntersection (⟨1003, by decide⟩ : Fin 1069) = faceMask (⟨1003, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1004 : bundle_7fec005515_supportIntersection (⟨1004, by decide⟩ : Fin 1069) = faceMask (⟨1004, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1005 : bundle_7fec005515_supportIntersection (⟨1005, by decide⟩ : Fin 1069) = faceMask (⟨1005, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1006 : bundle_7fec005515_supportIntersection (⟨1006, by decide⟩ : Fin 1069) = faceMask (⟨1006, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1007 : bundle_7fec005515_supportIntersection (⟨1007, by decide⟩ : Fin 1069) = faceMask (⟨1007, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1008 : bundle_7fec005515_supportIntersection (⟨1008, by decide⟩ : Fin 1069) = faceMask (⟨1008, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1009 : bundle_7fec005515_supportIntersection (⟨1009, by decide⟩ : Fin 1069) = faceMask (⟨1009, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1010 : bundle_7fec005515_supportIntersection (⟨1010, by decide⟩ : Fin 1069) = faceMask (⟨1010, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1011 : bundle_7fec005515_supportIntersection (⟨1011, by decide⟩ : Fin 1069) = faceMask (⟨1011, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1012 : bundle_7fec005515_supportIntersection (⟨1012, by decide⟩ : Fin 1069) = faceMask (⟨1012, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1013 : bundle_7fec005515_supportIntersection (⟨1013, by decide⟩ : Fin 1069) = faceMask (⟨1013, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1014 : bundle_7fec005515_supportIntersection (⟨1014, by decide⟩ : Fin 1069) = faceMask (⟨1014, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1015 : bundle_7fec005515_supportIntersection (⟨1015, by decide⟩ : Fin 1069) = faceMask (⟨1015, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1016 : bundle_7fec005515_supportIntersection (⟨1016, by decide⟩ : Fin 1069) = faceMask (⟨1016, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1017 : bundle_7fec005515_supportIntersection (⟨1017, by decide⟩ : Fin 1069) = faceMask (⟨1017, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1018 : bundle_7fec005515_supportIntersection (⟨1018, by decide⟩ : Fin 1069) = faceMask (⟨1018, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1019 : bundle_7fec005515_supportIntersection (⟨1019, by decide⟩ : Fin 1069) = faceMask (⟨1019, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1020 : bundle_7fec005515_supportIntersection (⟨1020, by decide⟩ : Fin 1069) = faceMask (⟨1020, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1021 : bundle_7fec005515_supportIntersection (⟨1021, by decide⟩ : Fin 1069) = faceMask (⟨1021, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1022 : bundle_7fec005515_supportIntersection (⟨1022, by decide⟩ : Fin 1069) = faceMask (⟨1022, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1023 : bundle_7fec005515_supportIntersection (⟨1023, by decide⟩ : Fin 1069) = faceMask (⟨1023, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1024 : bundle_7fec005515_supportIntersection (⟨1024, by decide⟩ : Fin 1069) = faceMask (⟨1024, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1025 : bundle_7fec005515_supportIntersection (⟨1025, by decide⟩ : Fin 1069) = faceMask (⟨1025, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1026 : bundle_7fec005515_supportIntersection (⟨1026, by decide⟩ : Fin 1069) = faceMask (⟨1026, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1027 : bundle_7fec005515_supportIntersection (⟨1027, by decide⟩ : Fin 1069) = faceMask (⟨1027, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1028 : bundle_7fec005515_supportIntersection (⟨1028, by decide⟩ : Fin 1069) = faceMask (⟨1028, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1029 : bundle_7fec005515_supportIntersection (⟨1029, by decide⟩ : Fin 1069) = faceMask (⟨1029, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1030 : bundle_7fec005515_supportIntersection (⟨1030, by decide⟩ : Fin 1069) = faceMask (⟨1030, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1031 : bundle_7fec005515_supportIntersection (⟨1031, by decide⟩ : Fin 1069) = faceMask (⟨1031, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1032 : bundle_7fec005515_supportIntersection (⟨1032, by decide⟩ : Fin 1069) = faceMask (⟨1032, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1033 : bundle_7fec005515_supportIntersection (⟨1033, by decide⟩ : Fin 1069) = faceMask (⟨1033, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1034 : bundle_7fec005515_supportIntersection (⟨1034, by decide⟩ : Fin 1069) = faceMask (⟨1034, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1035 : bundle_7fec005515_supportIntersection (⟨1035, by decide⟩ : Fin 1069) = faceMask (⟨1035, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1036 : bundle_7fec005515_supportIntersection (⟨1036, by decide⟩ : Fin 1069) = faceMask (⟨1036, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1037 : bundle_7fec005515_supportIntersection (⟨1037, by decide⟩ : Fin 1069) = faceMask (⟨1037, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1038 : bundle_7fec005515_supportIntersection (⟨1038, by decide⟩ : Fin 1069) = faceMask (⟨1038, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1039 : bundle_7fec005515_supportIntersection (⟨1039, by decide⟩ : Fin 1069) = faceMask (⟨1039, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1040 : bundle_7fec005515_supportIntersection (⟨1040, by decide⟩ : Fin 1069) = faceMask (⟨1040, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1041 : bundle_7fec005515_supportIntersection (⟨1041, by decide⟩ : Fin 1069) = faceMask (⟨1041, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1042 : bundle_7fec005515_supportIntersection (⟨1042, by decide⟩ : Fin 1069) = faceMask (⟨1042, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1043 : bundle_7fec005515_supportIntersection (⟨1043, by decide⟩ : Fin 1069) = faceMask (⟨1043, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1044 : bundle_7fec005515_supportIntersection (⟨1044, by decide⟩ : Fin 1069) = faceMask (⟨1044, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1045 : bundle_7fec005515_supportIntersection (⟨1045, by decide⟩ : Fin 1069) = faceMask (⟨1045, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1046 : bundle_7fec005515_supportIntersection (⟨1046, by decide⟩ : Fin 1069) = faceMask (⟨1046, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1047 : bundle_7fec005515_supportIntersection (⟨1047, by decide⟩ : Fin 1069) = faceMask (⟨1047, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1048 : bundle_7fec005515_supportIntersection (⟨1048, by decide⟩ : Fin 1069) = faceMask (⟨1048, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1049 : bundle_7fec005515_supportIntersection (⟨1049, by decide⟩ : Fin 1069) = faceMask (⟨1049, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1050 : bundle_7fec005515_supportIntersection (⟨1050, by decide⟩ : Fin 1069) = faceMask (⟨1050, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1051 : bundle_7fec005515_supportIntersection (⟨1051, by decide⟩ : Fin 1069) = faceMask (⟨1051, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1052 : bundle_7fec005515_supportIntersection (⟨1052, by decide⟩ : Fin 1069) = faceMask (⟨1052, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1053 : bundle_7fec005515_supportIntersection (⟨1053, by decide⟩ : Fin 1069) = faceMask (⟨1053, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1054 : bundle_7fec005515_supportIntersection (⟨1054, by decide⟩ : Fin 1069) = faceMask (⟨1054, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1055 : bundle_7fec005515_supportIntersection (⟨1055, by decide⟩ : Fin 1069) = faceMask (⟨1055, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1056 : bundle_7fec005515_supportIntersection (⟨1056, by decide⟩ : Fin 1069) = faceMask (⟨1056, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1057 : bundle_7fec005515_supportIntersection (⟨1057, by decide⟩ : Fin 1069) = faceMask (⟨1057, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1058 : bundle_7fec005515_supportIntersection (⟨1058, by decide⟩ : Fin 1069) = faceMask (⟨1058, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1059 : bundle_7fec005515_supportIntersection (⟨1059, by decide⟩ : Fin 1069) = faceMask (⟨1059, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1060 : bundle_7fec005515_supportIntersection (⟨1060, by decide⟩ : Fin 1069) = faceMask (⟨1060, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1061 : bundle_7fec005515_supportIntersection (⟨1061, by decide⟩ : Fin 1069) = faceMask (⟨1061, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1062 : bundle_7fec005515_supportIntersection (⟨1062, by decide⟩ : Fin 1069) = faceMask (⟨1062, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1063 : bundle_7fec005515_supportIntersection (⟨1063, by decide⟩ : Fin 1069) = faceMask (⟨1063, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1064 : bundle_7fec005515_supportIntersection (⟨1064, by decide⟩ : Fin 1069) = faceMask (⟨1064, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1065 : bundle_7fec005515_supportIntersection (⟨1065, by decide⟩ : Fin 1069) = faceMask (⟨1065, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1066 : bundle_7fec005515_supportIntersection (⟨1066, by decide⟩ : Fin 1069) = faceMask (⟨1066, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1067 : bundle_7fec005515_supportIntersection (⟨1067, by decide⟩ : Fin 1069) = faceMask (⟨1067, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_support1068 : bundle_7fec005515_supportIntersection (⟨1068, by decide⟩ : Fin 1069) = faceMask (⟨1068, by decide⟩ : Fin 1069) := by
  decide +kernel

theorem bundle_7fec005515_supportGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0007
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
            simpa only [he] using bundle_7fec005515_support0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0015
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
            simpa only [he] using bundle_7fec005515_support0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0023
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
            simpa only [he] using bundle_7fec005515_support0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0031

theorem bundle_7fec005515_supportGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0039
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
            simpa only [he] using bundle_7fec005515_support0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0047
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
            simpa only [he] using bundle_7fec005515_support0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0055
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
            simpa only [he] using bundle_7fec005515_support0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0063

theorem bundle_7fec005515_supportGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0071
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
            simpa only [he] using bundle_7fec005515_support0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0079
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
            simpa only [he] using bundle_7fec005515_support0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0087
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
            simpa only [he] using bundle_7fec005515_support0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0095

theorem bundle_7fec005515_supportGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0103
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
            simpa only [he] using bundle_7fec005515_support0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0111
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
            simpa only [he] using bundle_7fec005515_support0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0119
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
            simpa only [he] using bundle_7fec005515_support0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0127

theorem bundle_7fec005515_supportGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0135
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
            simpa only [he] using bundle_7fec005515_support0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0143
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
            simpa only [he] using bundle_7fec005515_support0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0151
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
            simpa only [he] using bundle_7fec005515_support0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0159

theorem bundle_7fec005515_supportGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0167
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
            simpa only [he] using bundle_7fec005515_support0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0175
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
            simpa only [he] using bundle_7fec005515_support0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0183
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
            simpa only [he] using bundle_7fec005515_support0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0191

theorem bundle_7fec005515_supportGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0199
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
            simpa only [he] using bundle_7fec005515_support0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0207
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
            simpa only [he] using bundle_7fec005515_support0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0215
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
            simpa only [he] using bundle_7fec005515_support0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0223

theorem bundle_7fec005515_supportGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0231
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
            simpa only [he] using bundle_7fec005515_support0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0239
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
            simpa only [he] using bundle_7fec005515_support0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0247
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
            simpa only [he] using bundle_7fec005515_support0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0255

theorem bundle_7fec005515_supportGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0263
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
            simpa only [he] using bundle_7fec005515_support0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0271
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
            simpa only [he] using bundle_7fec005515_support0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0279
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
            simpa only [he] using bundle_7fec005515_support0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0287

theorem bundle_7fec005515_supportGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0295
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
            simpa only [he] using bundle_7fec005515_support0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0303
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
            simpa only [he] using bundle_7fec005515_support0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0311
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
            simpa only [he] using bundle_7fec005515_support0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0319

theorem bundle_7fec005515_supportGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0327
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
            simpa only [he] using bundle_7fec005515_support0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0335
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
            simpa only [he] using bundle_7fec005515_support0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0343
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
            simpa only [he] using bundle_7fec005515_support0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0351

theorem bundle_7fec005515_supportGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0359
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
            simpa only [he] using bundle_7fec005515_support0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0367
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
            simpa only [he] using bundle_7fec005515_support0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0375
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
            simpa only [he] using bundle_7fec005515_support0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0383

theorem bundle_7fec005515_supportGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0391
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
            simpa only [he] using bundle_7fec005515_support0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0399
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
            simpa only [he] using bundle_7fec005515_support0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0407
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
            simpa only [he] using bundle_7fec005515_support0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0415

theorem bundle_7fec005515_supportGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0423
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
            simpa only [he] using bundle_7fec005515_support0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0431
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
            simpa only [he] using bundle_7fec005515_support0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0439
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
            simpa only [he] using bundle_7fec005515_support0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0447

theorem bundle_7fec005515_supportGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0455
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
            simpa only [he] using bundle_7fec005515_support0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0463
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
            simpa only [he] using bundle_7fec005515_support0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0471
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
            simpa only [he] using bundle_7fec005515_support0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0479

theorem bundle_7fec005515_supportGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0487
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
            simpa only [he] using bundle_7fec005515_support0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0495
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
            simpa only [he] using bundle_7fec005515_support0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0503
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
            simpa only [he] using bundle_7fec005515_support0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0511

theorem bundle_7fec005515_supportGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0519
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
            simpa only [he] using bundle_7fec005515_support0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0527
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
            simpa only [he] using bundle_7fec005515_support0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0535
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
            simpa only [he] using bundle_7fec005515_support0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0543

theorem bundle_7fec005515_supportGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0551
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
            simpa only [he] using bundle_7fec005515_support0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0559
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
            simpa only [he] using bundle_7fec005515_support0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0567
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
            simpa only [he] using bundle_7fec005515_support0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0575

theorem bundle_7fec005515_supportGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0583
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
            simpa only [he] using bundle_7fec005515_support0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0591
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
            simpa only [he] using bundle_7fec005515_support0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0599
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
            simpa only [he] using bundle_7fec005515_support0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0607

theorem bundle_7fec005515_supportGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    bundle_7fec005515_supportIntersection i = faceMask i := by
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
            simpa only [he] using bundle_7fec005515_support0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0615
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
            simpa only [he] using bundle_7fec005515_support0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0623
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
            simpa only [he] using bundle_7fec005515_support0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0631
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
            simpa only [he] using bundle_7fec005515_support0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using bundle_7fec005515_support0639

end CubicalIndecomposability
end VerificationSource001

/- Original source: CubicalIndecomposability/FaceDataChecks/Injective.lean -/

end -- global noncomputable section
end -- global public section
