module
public import block_verification_bundle.PalomarPart002
import all block_verification_bundle.PalomarPart002
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Module
public import verification_bundle
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See BlockVerificationBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/DeformationDimension.lean -/
section VerificationSource013




/-!
# Kernel checks for the complete finite face catalogue

Every fact in this file is a finite statement about explicit label sets.
The proofs use `decide +kernel`, whose resulting proof terms are checked
by Lean's kernel.  No native-decision axiom or external verifier is used.
The geometric interpretation and completeness proof are separate.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

theorem bundle_2098644a87_supportRows_identity_row0000 : ∀ v : Fin 32, v ∈ faceMask (⟨0, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨0, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0001 : ∀ v : Fin 32, v ∈ faceMask (⟨1, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨1, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0002 : ∀ v : Fin 32, v ∈ faceMask (⟨2, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨2, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0003 : ∀ v : Fin 32, v ∈ faceMask (⟨3, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨3, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0004 : ∀ v : Fin 32, v ∈ faceMask (⟨4, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨4, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0005 : ∀ v : Fin 32, v ∈ faceMask (⟨5, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨5, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0006 : ∀ v : Fin 32, v ∈ faceMask (⟨6, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨6, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0007 : ∀ v : Fin 32, v ∈ faceMask (⟨7, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨7, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0008 : ∀ v : Fin 32, v ∈ faceMask (⟨8, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨8, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0009 : ∀ v : Fin 32, v ∈ faceMask (⟨9, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨9, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0010 : ∀ v : Fin 32, v ∈ faceMask (⟨10, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨10, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0011 : ∀ v : Fin 32, v ∈ faceMask (⟨11, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨11, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0012 : ∀ v : Fin 32, v ∈ faceMask (⟨12, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨12, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0013 : ∀ v : Fin 32, v ∈ faceMask (⟨13, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨13, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0014 : ∀ v : Fin 32, v ∈ faceMask (⟨14, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨14, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0015 : ∀ v : Fin 32, v ∈ faceMask (⟨15, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨15, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0016 : ∀ v : Fin 32, v ∈ faceMask (⟨16, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨16, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0017 : ∀ v : Fin 32, v ∈ faceMask (⟨17, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨17, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0018 : ∀ v : Fin 32, v ∈ faceMask (⟨18, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨18, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0019 : ∀ v : Fin 32, v ∈ faceMask (⟨19, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨19, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0020 : ∀ v : Fin 32, v ∈ faceMask (⟨20, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨20, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0021 : ∀ v : Fin 32, v ∈ faceMask (⟨21, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨21, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0022 : ∀ v : Fin 32, v ∈ faceMask (⟨22, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨22, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0023 : ∀ v : Fin 32, v ∈ faceMask (⟨23, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨23, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0024 : ∀ v : Fin 32, v ∈ faceMask (⟨24, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨24, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0025 : ∀ v : Fin 32, v ∈ faceMask (⟨25, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨25, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0026 : ∀ v : Fin 32, v ∈ faceMask (⟨26, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨26, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0027 : ∀ v : Fin 32, v ∈ faceMask (⟨27, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨27, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0028 : ∀ v : Fin 32, v ∈ faceMask (⟨28, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨28, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0029 : ∀ v : Fin 32, v ∈ faceMask (⟨29, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨29, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0030 : ∀ v : Fin 32, v ∈ faceMask (⟨30, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨30, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0031 : ∀ v : Fin 32, v ∈ faceMask (⟨31, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨31, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0032 : ∀ v : Fin 32, v ∈ faceMask (⟨32, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨32, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0033 : ∀ v : Fin 32, v ∈ faceMask (⟨33, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨33, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0034 : ∀ v : Fin 32, v ∈ faceMask (⟨34, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨34, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0035 : ∀ v : Fin 32, v ∈ faceMask (⟨35, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨35, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0036 : ∀ v : Fin 32, v ∈ faceMask (⟨36, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨36, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0037 : ∀ v : Fin 32, v ∈ faceMask (⟨37, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨37, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0038 : ∀ v : Fin 32, v ∈ faceMask (⟨38, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨38, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0039 : ∀ v : Fin 32, v ∈ faceMask (⟨39, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨39, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0040 : ∀ v : Fin 32, v ∈ faceMask (⟨40, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨40, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0041 : ∀ v : Fin 32, v ∈ faceMask (⟨41, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨41, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0042 : ∀ v : Fin 32, v ∈ faceMask (⟨42, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨42, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0043 : ∀ v : Fin 32, v ∈ faceMask (⟨43, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨43, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0044 : ∀ v : Fin 32, v ∈ faceMask (⟨44, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨44, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0045 : ∀ v : Fin 32, v ∈ faceMask (⟨45, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨45, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0046 : ∀ v : Fin 32, v ∈ faceMask (⟨46, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨46, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0047 : ∀ v : Fin 32, v ∈ faceMask (⟨47, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨47, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0048 : ∀ v : Fin 32, v ∈ faceMask (⟨48, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨48, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0049 : ∀ v : Fin 32, v ∈ faceMask (⟨49, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨49, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0050 : ∀ v : Fin 32, v ∈ faceMask (⟨50, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨50, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0051 : ∀ v : Fin 32, v ∈ faceMask (⟨51, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨51, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0052 : ∀ v : Fin 32, v ∈ faceMask (⟨52, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨52, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0053 : ∀ v : Fin 32, v ∈ faceMask (⟨53, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨53, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0054 : ∀ v : Fin 32, v ∈ faceMask (⟨54, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨54, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0055 : ∀ v : Fin 32, v ∈ faceMask (⟨55, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨55, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0056 : ∀ v : Fin 32, v ∈ faceMask (⟨56, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨56, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0057 : ∀ v : Fin 32, v ∈ faceMask (⟨57, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨57, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0058 : ∀ v : Fin 32, v ∈ faceMask (⟨58, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨58, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0059 : ∀ v : Fin 32, v ∈ faceMask (⟨59, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨59, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0060 : ∀ v : Fin 32, v ∈ faceMask (⟨60, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨60, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0061 : ∀ v : Fin 32, v ∈ faceMask (⟨61, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨61, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0062 : ∀ v : Fin 32, v ∈ faceMask (⟨62, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨62, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0063 : ∀ v : Fin 32, v ∈ faceMask (⟨63, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨63, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0064 : ∀ v : Fin 32, v ∈ faceMask (⟨64, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨64, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0065 : ∀ v : Fin 32, v ∈ faceMask (⟨65, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨65, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0066 : ∀ v : Fin 32, v ∈ faceMask (⟨66, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨66, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0067 : ∀ v : Fin 32, v ∈ faceMask (⟨67, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨67, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0068 : ∀ v : Fin 32, v ∈ faceMask (⟨68, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨68, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0069 : ∀ v : Fin 32, v ∈ faceMask (⟨69, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨69, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0070 : ∀ v : Fin 32, v ∈ faceMask (⟨70, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨70, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0071 : ∀ v : Fin 32, v ∈ faceMask (⟨71, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨71, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0072 : ∀ v : Fin 32, v ∈ faceMask (⟨72, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨72, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0073 : ∀ v : Fin 32, v ∈ faceMask (⟨73, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨73, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0074 : ∀ v : Fin 32, v ∈ faceMask (⟨74, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨74, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0075 : ∀ v : Fin 32, v ∈ faceMask (⟨75, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨75, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0076 : ∀ v : Fin 32, v ∈ faceMask (⟨76, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨76, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0077 : ∀ v : Fin 32, v ∈ faceMask (⟨77, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨77, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0078 : ∀ v : Fin 32, v ∈ faceMask (⟨78, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨78, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0079 : ∀ v : Fin 32, v ∈ faceMask (⟨79, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨79, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0080 : ∀ v : Fin 32, v ∈ faceMask (⟨80, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨80, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0081 : ∀ v : Fin 32, v ∈ faceMask (⟨81, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨81, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0082 : ∀ v : Fin 32, v ∈ faceMask (⟨82, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨82, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0083 : ∀ v : Fin 32, v ∈ faceMask (⟨83, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨83, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0084 : ∀ v : Fin 32, v ∈ faceMask (⟨84, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨84, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0085 : ∀ v : Fin 32, v ∈ faceMask (⟨85, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨85, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0086 : ∀ v : Fin 32, v ∈ faceMask (⟨86, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨86, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0087 : ∀ v : Fin 32, v ∈ faceMask (⟨87, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨87, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0088 : ∀ v : Fin 32, v ∈ faceMask (⟨88, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨88, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0089 : ∀ v : Fin 32, v ∈ faceMask (⟨89, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨89, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0090 : ∀ v : Fin 32, v ∈ faceMask (⟨90, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨90, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0091 : ∀ v : Fin 32, v ∈ faceMask (⟨91, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨91, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0092 : ∀ v : Fin 32, v ∈ faceMask (⟨92, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨92, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0093 : ∀ v : Fin 32, v ∈ faceMask (⟨93, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨93, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0094 : ∀ v : Fin 32, v ∈ faceMask (⟨94, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨94, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0095 : ∀ v : Fin 32, v ∈ faceMask (⟨95, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨95, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0096 : ∀ v : Fin 32, v ∈ faceMask (⟨96, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨96, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0097 : ∀ v : Fin 32, v ∈ faceMask (⟨97, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨97, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0098 : ∀ v : Fin 32, v ∈ faceMask (⟨98, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨98, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0099 : ∀ v : Fin 32, v ∈ faceMask (⟨99, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨99, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0100 : ∀ v : Fin 32, v ∈ faceMask (⟨100, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨100, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0101 : ∀ v : Fin 32, v ∈ faceMask (⟨101, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨101, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0102 : ∀ v : Fin 32, v ∈ faceMask (⟨102, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨102, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0103 : ∀ v : Fin 32, v ∈ faceMask (⟨103, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨103, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0104 : ∀ v : Fin 32, v ∈ faceMask (⟨104, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨104, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0105 : ∀ v : Fin 32, v ∈ faceMask (⟨105, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨105, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0106 : ∀ v : Fin 32, v ∈ faceMask (⟨106, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨106, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0107 : ∀ v : Fin 32, v ∈ faceMask (⟨107, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨107, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0108 : ∀ v : Fin 32, v ∈ faceMask (⟨108, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨108, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0109 : ∀ v : Fin 32, v ∈ faceMask (⟨109, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨109, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0110 : ∀ v : Fin 32, v ∈ faceMask (⟨110, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨110, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0111 : ∀ v : Fin 32, v ∈ faceMask (⟨111, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨111, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0112 : ∀ v : Fin 32, v ∈ faceMask (⟨112, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨112, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0113 : ∀ v : Fin 32, v ∈ faceMask (⟨113, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨113, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0114 : ∀ v : Fin 32, v ∈ faceMask (⟨114, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨114, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0115 : ∀ v : Fin 32, v ∈ faceMask (⟨115, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨115, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0116 : ∀ v : Fin 32, v ∈ faceMask (⟨116, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨116, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0117 : ∀ v : Fin 32, v ∈ faceMask (⟨117, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨117, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0118 : ∀ v : Fin 32, v ∈ faceMask (⟨118, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨118, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0119 : ∀ v : Fin 32, v ∈ faceMask (⟨119, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨119, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0120 : ∀ v : Fin 32, v ∈ faceMask (⟨120, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨120, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0121 : ∀ v : Fin 32, v ∈ faceMask (⟨121, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨121, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0122 : ∀ v : Fin 32, v ∈ faceMask (⟨122, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨122, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0123 : ∀ v : Fin 32, v ∈ faceMask (⟨123, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨123, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0124 : ∀ v : Fin 32, v ∈ faceMask (⟨124, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨124, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0125 : ∀ v : Fin 32, v ∈ faceMask (⟨125, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨125, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0126 : ∀ v : Fin 32, v ∈ faceMask (⟨126, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨126, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0127 : ∀ v : Fin 32, v ∈ faceMask (⟨127, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨127, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0128 : ∀ v : Fin 32, v ∈ faceMask (⟨128, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨128, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0129 : ∀ v : Fin 32, v ∈ faceMask (⟨129, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨129, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0130 : ∀ v : Fin 32, v ∈ faceMask (⟨130, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨130, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0131 : ∀ v : Fin 32, v ∈ faceMask (⟨131, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨131, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0132 : ∀ v : Fin 32, v ∈ faceMask (⟨132, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨132, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0133 : ∀ v : Fin 32, v ∈ faceMask (⟨133, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨133, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0134 : ∀ v : Fin 32, v ∈ faceMask (⟨134, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨134, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0135 : ∀ v : Fin 32, v ∈ faceMask (⟨135, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨135, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0136 : ∀ v : Fin 32, v ∈ faceMask (⟨136, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨136, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0137 : ∀ v : Fin 32, v ∈ faceMask (⟨137, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨137, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0138 : ∀ v : Fin 32, v ∈ faceMask (⟨138, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨138, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0139 : ∀ v : Fin 32, v ∈ faceMask (⟨139, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨139, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0140 : ∀ v : Fin 32, v ∈ faceMask (⟨140, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨140, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0141 : ∀ v : Fin 32, v ∈ faceMask (⟨141, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨141, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0142 : ∀ v : Fin 32, v ∈ faceMask (⟨142, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨142, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0143 : ∀ v : Fin 32, v ∈ faceMask (⟨143, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨143, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0144 : ∀ v : Fin 32, v ∈ faceMask (⟨144, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨144, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0145 : ∀ v : Fin 32, v ∈ faceMask (⟨145, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨145, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0146 : ∀ v : Fin 32, v ∈ faceMask (⟨146, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨146, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0147 : ∀ v : Fin 32, v ∈ faceMask (⟨147, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨147, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0148 : ∀ v : Fin 32, v ∈ faceMask (⟨148, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨148, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0149 : ∀ v : Fin 32, v ∈ faceMask (⟨149, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨149, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0150 : ∀ v : Fin 32, v ∈ faceMask (⟨150, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨150, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0151 : ∀ v : Fin 32, v ∈ faceMask (⟨151, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨151, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0152 : ∀ v : Fin 32, v ∈ faceMask (⟨152, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨152, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0153 : ∀ v : Fin 32, v ∈ faceMask (⟨153, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨153, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0154 : ∀ v : Fin 32, v ∈ faceMask (⟨154, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨154, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0155 : ∀ v : Fin 32, v ∈ faceMask (⟨155, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨155, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0156 : ∀ v : Fin 32, v ∈ faceMask (⟨156, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨156, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0157 : ∀ v : Fin 32, v ∈ faceMask (⟨157, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨157, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0158 : ∀ v : Fin 32, v ∈ faceMask (⟨158, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨158, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0159 : ∀ v : Fin 32, v ∈ faceMask (⟨159, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨159, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0160 : ∀ v : Fin 32, v ∈ faceMask (⟨160, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨160, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0161 : ∀ v : Fin 32, v ∈ faceMask (⟨161, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨161, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0162 : ∀ v : Fin 32, v ∈ faceMask (⟨162, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨162, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0163 : ∀ v : Fin 32, v ∈ faceMask (⟨163, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨163, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0164 : ∀ v : Fin 32, v ∈ faceMask (⟨164, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨164, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0165 : ∀ v : Fin 32, v ∈ faceMask (⟨165, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨165, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0166 : ∀ v : Fin 32, v ∈ faceMask (⟨166, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨166, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0167 : ∀ v : Fin 32, v ∈ faceMask (⟨167, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨167, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0168 : ∀ v : Fin 32, v ∈ faceMask (⟨168, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨168, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0169 : ∀ v : Fin 32, v ∈ faceMask (⟨169, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨169, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0170 : ∀ v : Fin 32, v ∈ faceMask (⟨170, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨170, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0171 : ∀ v : Fin 32, v ∈ faceMask (⟨171, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨171, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0172 : ∀ v : Fin 32, v ∈ faceMask (⟨172, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨172, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0173 : ∀ v : Fin 32, v ∈ faceMask (⟨173, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨173, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0174 : ∀ v : Fin 32, v ∈ faceMask (⟨174, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨174, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0175 : ∀ v : Fin 32, v ∈ faceMask (⟨175, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨175, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0176 : ∀ v : Fin 32, v ∈ faceMask (⟨176, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨176, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0177 : ∀ v : Fin 32, v ∈ faceMask (⟨177, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨177, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0178 : ∀ v : Fin 32, v ∈ faceMask (⟨178, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨178, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0179 : ∀ v : Fin 32, v ∈ faceMask (⟨179, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨179, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0180 : ∀ v : Fin 32, v ∈ faceMask (⟨180, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨180, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0181 : ∀ v : Fin 32, v ∈ faceMask (⟨181, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨181, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0182 : ∀ v : Fin 32, v ∈ faceMask (⟨182, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨182, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0183 : ∀ v : Fin 32, v ∈ faceMask (⟨183, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨183, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0184 : ∀ v : Fin 32, v ∈ faceMask (⟨184, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨184, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0185 : ∀ v : Fin 32, v ∈ faceMask (⟨185, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨185, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0186 : ∀ v : Fin 32, v ∈ faceMask (⟨186, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨186, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0187 : ∀ v : Fin 32, v ∈ faceMask (⟨187, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨187, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0188 : ∀ v : Fin 32, v ∈ faceMask (⟨188, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨188, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0189 : ∀ v : Fin 32, v ∈ faceMask (⟨189, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨189, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0190 : ∀ v : Fin 32, v ∈ faceMask (⟨190, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨190, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0191 : ∀ v : Fin 32, v ∈ faceMask (⟨191, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨191, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0192 : ∀ v : Fin 32, v ∈ faceMask (⟨192, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨192, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0193 : ∀ v : Fin 32, v ∈ faceMask (⟨193, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨193, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0194 : ∀ v : Fin 32, v ∈ faceMask (⟨194, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨194, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0195 : ∀ v : Fin 32, v ∈ faceMask (⟨195, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨195, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0196 : ∀ v : Fin 32, v ∈ faceMask (⟨196, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨196, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0197 : ∀ v : Fin 32, v ∈ faceMask (⟨197, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨197, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0198 : ∀ v : Fin 32, v ∈ faceMask (⟨198, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨198, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0199 : ∀ v : Fin 32, v ∈ faceMask (⟨199, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨199, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0200 : ∀ v : Fin 32, v ∈ faceMask (⟨200, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨200, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0201 : ∀ v : Fin 32, v ∈ faceMask (⟨201, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨201, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0202 : ∀ v : Fin 32, v ∈ faceMask (⟨202, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨202, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0203 : ∀ v : Fin 32, v ∈ faceMask (⟨203, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨203, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0204 : ∀ v : Fin 32, v ∈ faceMask (⟨204, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨204, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0205 : ∀ v : Fin 32, v ∈ faceMask (⟨205, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨205, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0206 : ∀ v : Fin 32, v ∈ faceMask (⟨206, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨206, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0207 : ∀ v : Fin 32, v ∈ faceMask (⟨207, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨207, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem bundle_2098644a87_supportRows_identity_row0208 : ∀ v : Fin 32, v ∈ faceMask (⟨208, by decide⟩ : Fin 209) ↔ ∀ f ∈ supportRows (⟨208, by decide⟩ : Fin 209), incident f v := by decide +kernel

theorem supportRows_identity : ∀ (i : Fin 209) (v : Fin 32),
    v ∈ faceMask i ↔ ∀ f ∈ supportRows i, incident f v := by
  intro i
  have hi_bound := i.isLt
  by_cases h104 : i.val < 104
  ·
    by_cases h52 : i.val < 52
    ·
      by_cases h26 : i.val < 26
      ·
        by_cases h13 : i.val < 13
        ·
          by_cases h6 : i.val < 6
          ·
            by_cases h3 : i.val < 3
            ·
              by_cases h1 : i.val < 1
              ·
                have he : (⟨0, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 0 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0000
              ·
                by_cases h2 : i.val < 2
                ·
                  have he : (⟨1, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 1 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0001
                ·
                  have he : (⟨2, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 2 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0002
            ·
              by_cases h4 : i.val < 4
              ·
                have he : (⟨3, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 3 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0003
              ·
                by_cases h5 : i.val < 5
                ·
                  have he : (⟨4, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 4 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0004
                ·
                  have he : (⟨5, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 5 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0005
          ·
            by_cases h9 : i.val < 9
            ·
              by_cases h7 : i.val < 7
              ·
                have he : (⟨6, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 6 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0006
              ·
                by_cases h8 : i.val < 8
                ·
                  have he : (⟨7, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 7 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0007
                ·
                  have he : (⟨8, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 8 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0008
            ·
              by_cases h11 : i.val < 11
              ·
                by_cases h10 : i.val < 10
                ·
                  have he : (⟨9, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 9 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0009
                ·
                  have he : (⟨10, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 10 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0010
              ·
                by_cases h12 : i.val < 12
                ·
                  have he : (⟨11, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 11 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0011
                ·
                  have he : (⟨12, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 12 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0012
        ·
          by_cases h19 : i.val < 19
          ·
            by_cases h16 : i.val < 16
            ·
              by_cases h14 : i.val < 14
              ·
                have he : (⟨13, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 13 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0013
              ·
                by_cases h15 : i.val < 15
                ·
                  have he : (⟨14, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 14 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0014
                ·
                  have he : (⟨15, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 15 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0015
            ·
              by_cases h17 : i.val < 17
              ·
                have he : (⟨16, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 16 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0016
              ·
                by_cases h18 : i.val < 18
                ·
                  have he : (⟨17, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 17 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0017
                ·
                  have he : (⟨18, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 18 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0018
          ·
            by_cases h22 : i.val < 22
            ·
              by_cases h20 : i.val < 20
              ·
                have he : (⟨19, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 19 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0019
              ·
                by_cases h21 : i.val < 21
                ·
                  have he : (⟨20, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 20 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0020
                ·
                  have he : (⟨21, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 21 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0021
            ·
              by_cases h24 : i.val < 24
              ·
                by_cases h23 : i.val < 23
                ·
                  have he : (⟨22, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 22 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0022
                ·
                  have he : (⟨23, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 23 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0023
              ·
                by_cases h25 : i.val < 25
                ·
                  have he : (⟨24, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 24 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0024
                ·
                  have he : (⟨25, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 25 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0025
      ·
        by_cases h39 : i.val < 39
        ·
          by_cases h32 : i.val < 32
          ·
            by_cases h29 : i.val < 29
            ·
              by_cases h27 : i.val < 27
              ·
                have he : (⟨26, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 26 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0026
              ·
                by_cases h28 : i.val < 28
                ·
                  have he : (⟨27, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 27 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0027
                ·
                  have he : (⟨28, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 28 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0028
            ·
              by_cases h30 : i.val < 30
              ·
                have he : (⟨29, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 29 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0029
              ·
                by_cases h31 : i.val < 31
                ·
                  have he : (⟨30, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 30 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0030
                ·
                  have he : (⟨31, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 31 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0031
          ·
            by_cases h35 : i.val < 35
            ·
              by_cases h33 : i.val < 33
              ·
                have he : (⟨32, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 32 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0032
              ·
                by_cases h34 : i.val < 34
                ·
                  have he : (⟨33, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 33 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0033
                ·
                  have he : (⟨34, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 34 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0034
            ·
              by_cases h37 : i.val < 37
              ·
                by_cases h36 : i.val < 36
                ·
                  have he : (⟨35, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 35 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0035
                ·
                  have he : (⟨36, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 36 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0036
              ·
                by_cases h38 : i.val < 38
                ·
                  have he : (⟨37, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 37 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0037
                ·
                  have he : (⟨38, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 38 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0038
        ·
          by_cases h45 : i.val < 45
          ·
            by_cases h42 : i.val < 42
            ·
              by_cases h40 : i.val < 40
              ·
                have he : (⟨39, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 39 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0039
              ·
                by_cases h41 : i.val < 41
                ·
                  have he : (⟨40, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 40 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0040
                ·
                  have he : (⟨41, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 41 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0041
            ·
              by_cases h43 : i.val < 43
              ·
                have he : (⟨42, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 42 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0042
              ·
                by_cases h44 : i.val < 44
                ·
                  have he : (⟨43, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 43 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0043
                ·
                  have he : (⟨44, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 44 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0044
          ·
            by_cases h48 : i.val < 48
            ·
              by_cases h46 : i.val < 46
              ·
                have he : (⟨45, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 45 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0045
              ·
                by_cases h47 : i.val < 47
                ·
                  have he : (⟨46, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 46 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0046
                ·
                  have he : (⟨47, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 47 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0047
            ·
              by_cases h50 : i.val < 50
              ·
                by_cases h49 : i.val < 49
                ·
                  have he : (⟨48, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 48 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0048
                ·
                  have he : (⟨49, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 49 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0049
              ·
                by_cases h51 : i.val < 51
                ·
                  have he : (⟨50, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 50 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0050
                ·
                  have he : (⟨51, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 51 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0051
    ·
      by_cases h78 : i.val < 78
      ·
        by_cases h65 : i.val < 65
        ·
          by_cases h58 : i.val < 58
          ·
            by_cases h55 : i.val < 55
            ·
              by_cases h53 : i.val < 53
              ·
                have he : (⟨52, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 52 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0052
              ·
                by_cases h54 : i.val < 54
                ·
                  have he : (⟨53, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 53 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0053
                ·
                  have he : (⟨54, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 54 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0054
            ·
              by_cases h56 : i.val < 56
              ·
                have he : (⟨55, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 55 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0055
              ·
                by_cases h57 : i.val < 57
                ·
                  have he : (⟨56, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 56 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0056
                ·
                  have he : (⟨57, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 57 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0057
          ·
            by_cases h61 : i.val < 61
            ·
              by_cases h59 : i.val < 59
              ·
                have he : (⟨58, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 58 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0058
              ·
                by_cases h60 : i.val < 60
                ·
                  have he : (⟨59, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 59 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0059
                ·
                  have he : (⟨60, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 60 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0060
            ·
              by_cases h63 : i.val < 63
              ·
                by_cases h62 : i.val < 62
                ·
                  have he : (⟨61, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 61 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0061
                ·
                  have he : (⟨62, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 62 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0062
              ·
                by_cases h64 : i.val < 64
                ·
                  have he : (⟨63, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 63 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0063
                ·
                  have he : (⟨64, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 64 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0064
        ·
          by_cases h71 : i.val < 71
          ·
            by_cases h68 : i.val < 68
            ·
              by_cases h66 : i.val < 66
              ·
                have he : (⟨65, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 65 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0065
              ·
                by_cases h67 : i.val < 67
                ·
                  have he : (⟨66, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 66 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0066
                ·
                  have he : (⟨67, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 67 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0067
            ·
              by_cases h69 : i.val < 69
              ·
                have he : (⟨68, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 68 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0068
              ·
                by_cases h70 : i.val < 70
                ·
                  have he : (⟨69, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 69 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0069
                ·
                  have he : (⟨70, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 70 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0070
          ·
            by_cases h74 : i.val < 74
            ·
              by_cases h72 : i.val < 72
              ·
                have he : (⟨71, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 71 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0071
              ·
                by_cases h73 : i.val < 73
                ·
                  have he : (⟨72, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 72 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0072
                ·
                  have he : (⟨73, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 73 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0073
            ·
              by_cases h76 : i.val < 76
              ·
                by_cases h75 : i.val < 75
                ·
                  have he : (⟨74, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 74 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0074
                ·
                  have he : (⟨75, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 75 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0075
              ·
                by_cases h77 : i.val < 77
                ·
                  have he : (⟨76, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 76 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0076
                ·
                  have he : (⟨77, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 77 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0077
      ·
        by_cases h91 : i.val < 91
        ·
          by_cases h84 : i.val < 84
          ·
            by_cases h81 : i.val < 81
            ·
              by_cases h79 : i.val < 79
              ·
                have he : (⟨78, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 78 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0078
              ·
                by_cases h80 : i.val < 80
                ·
                  have he : (⟨79, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 79 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0079
                ·
                  have he : (⟨80, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 80 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0080
            ·
              by_cases h82 : i.val < 82
              ·
                have he : (⟨81, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 81 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0081
              ·
                by_cases h83 : i.val < 83
                ·
                  have he : (⟨82, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 82 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0082
                ·
                  have he : (⟨83, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 83 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0083
          ·
            by_cases h87 : i.val < 87
            ·
              by_cases h85 : i.val < 85
              ·
                have he : (⟨84, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 84 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0084
              ·
                by_cases h86 : i.val < 86
                ·
                  have he : (⟨85, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 85 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0085
                ·
                  have he : (⟨86, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 86 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0086
            ·
              by_cases h89 : i.val < 89
              ·
                by_cases h88 : i.val < 88
                ·
                  have he : (⟨87, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 87 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0087
                ·
                  have he : (⟨88, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 88 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0088
              ·
                by_cases h90 : i.val < 90
                ·
                  have he : (⟨89, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 89 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0089
                ·
                  have he : (⟨90, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 90 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0090
        ·
          by_cases h97 : i.val < 97
          ·
            by_cases h94 : i.val < 94
            ·
              by_cases h92 : i.val < 92
              ·
                have he : (⟨91, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 91 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0091
              ·
                by_cases h93 : i.val < 93
                ·
                  have he : (⟨92, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 92 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0092
                ·
                  have he : (⟨93, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 93 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0093
            ·
              by_cases h95 : i.val < 95
              ·
                have he : (⟨94, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 94 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0094
              ·
                by_cases h96 : i.val < 96
                ·
                  have he : (⟨95, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 95 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0095
                ·
                  have he : (⟨96, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 96 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0096
          ·
            by_cases h100 : i.val < 100
            ·
              by_cases h98 : i.val < 98
              ·
                have he : (⟨97, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 97 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0097
              ·
                by_cases h99 : i.val < 99
                ·
                  have he : (⟨98, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 98 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0098
                ·
                  have he : (⟨99, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 99 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0099
            ·
              by_cases h102 : i.val < 102
              ·
                by_cases h101 : i.val < 101
                ·
                  have he : (⟨100, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 100 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0100
                ·
                  have he : (⟨101, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 101 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0101
              ·
                by_cases h103 : i.val < 103
                ·
                  have he : (⟨102, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 102 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0102
                ·
                  have he : (⟨103, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 103 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0103
  ·
    by_cases h156 : i.val < 156
    ·
      by_cases h130 : i.val < 130
      ·
        by_cases h117 : i.val < 117
        ·
          by_cases h110 : i.val < 110
          ·
            by_cases h107 : i.val < 107
            ·
              by_cases h105 : i.val < 105
              ·
                have he : (⟨104, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 104 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0104
              ·
                by_cases h106 : i.val < 106
                ·
                  have he : (⟨105, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 105 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0105
                ·
                  have he : (⟨106, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 106 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0106
            ·
              by_cases h108 : i.val < 108
              ·
                have he : (⟨107, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 107 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0107
              ·
                by_cases h109 : i.val < 109
                ·
                  have he : (⟨108, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 108 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0108
                ·
                  have he : (⟨109, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 109 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0109
          ·
            by_cases h113 : i.val < 113
            ·
              by_cases h111 : i.val < 111
              ·
                have he : (⟨110, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 110 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0110
              ·
                by_cases h112 : i.val < 112
                ·
                  have he : (⟨111, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 111 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0111
                ·
                  have he : (⟨112, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 112 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0112
            ·
              by_cases h115 : i.val < 115
              ·
                by_cases h114 : i.val < 114
                ·
                  have he : (⟨113, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 113 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0113
                ·
                  have he : (⟨114, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 114 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0114
              ·
                by_cases h116 : i.val < 116
                ·
                  have he : (⟨115, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 115 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0115
                ·
                  have he : (⟨116, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 116 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0116
        ·
          by_cases h123 : i.val < 123
          ·
            by_cases h120 : i.val < 120
            ·
              by_cases h118 : i.val < 118
              ·
                have he : (⟨117, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 117 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0117
              ·
                by_cases h119 : i.val < 119
                ·
                  have he : (⟨118, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 118 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0118
                ·
                  have he : (⟨119, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 119 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0119
            ·
              by_cases h121 : i.val < 121
              ·
                have he : (⟨120, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 120 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0120
              ·
                by_cases h122 : i.val < 122
                ·
                  have he : (⟨121, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 121 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0121
                ·
                  have he : (⟨122, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 122 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0122
          ·
            by_cases h126 : i.val < 126
            ·
              by_cases h124 : i.val < 124
              ·
                have he : (⟨123, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 123 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0123
              ·
                by_cases h125 : i.val < 125
                ·
                  have he : (⟨124, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 124 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0124
                ·
                  have he : (⟨125, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 125 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0125
            ·
              by_cases h128 : i.val < 128
              ·
                by_cases h127 : i.val < 127
                ·
                  have he : (⟨126, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 126 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0126
                ·
                  have he : (⟨127, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 127 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0127
              ·
                by_cases h129 : i.val < 129
                ·
                  have he : (⟨128, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 128 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0128
                ·
                  have he : (⟨129, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 129 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0129
      ·
        by_cases h143 : i.val < 143
        ·
          by_cases h136 : i.val < 136
          ·
            by_cases h133 : i.val < 133
            ·
              by_cases h131 : i.val < 131
              ·
                have he : (⟨130, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 130 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0130
              ·
                by_cases h132 : i.val < 132
                ·
                  have he : (⟨131, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 131 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0131
                ·
                  have he : (⟨132, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 132 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0132
            ·
              by_cases h134 : i.val < 134
              ·
                have he : (⟨133, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 133 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0133
              ·
                by_cases h135 : i.val < 135
                ·
                  have he : (⟨134, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 134 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0134
                ·
                  have he : (⟨135, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 135 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0135
          ·
            by_cases h139 : i.val < 139
            ·
              by_cases h137 : i.val < 137
              ·
                have he : (⟨136, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 136 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0136
              ·
                by_cases h138 : i.val < 138
                ·
                  have he : (⟨137, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 137 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0137
                ·
                  have he : (⟨138, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 138 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0138
            ·
              by_cases h141 : i.val < 141
              ·
                by_cases h140 : i.val < 140
                ·
                  have he : (⟨139, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 139 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0139
                ·
                  have he : (⟨140, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 140 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0140
              ·
                by_cases h142 : i.val < 142
                ·
                  have he : (⟨141, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 141 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0141
                ·
                  have he : (⟨142, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 142 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0142
        ·
          by_cases h149 : i.val < 149
          ·
            by_cases h146 : i.val < 146
            ·
              by_cases h144 : i.val < 144
              ·
                have he : (⟨143, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 143 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0143
              ·
                by_cases h145 : i.val < 145
                ·
                  have he : (⟨144, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 144 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0144
                ·
                  have he : (⟨145, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 145 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0145
            ·
              by_cases h147 : i.val < 147
              ·
                have he : (⟨146, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 146 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0146
              ·
                by_cases h148 : i.val < 148
                ·
                  have he : (⟨147, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 147 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0147
                ·
                  have he : (⟨148, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 148 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0148
          ·
            by_cases h152 : i.val < 152
            ·
              by_cases h150 : i.val < 150
              ·
                have he : (⟨149, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 149 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0149
              ·
                by_cases h151 : i.val < 151
                ·
                  have he : (⟨150, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 150 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0150
                ·
                  have he : (⟨151, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 151 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0151
            ·
              by_cases h154 : i.val < 154
              ·
                by_cases h153 : i.val < 153
                ·
                  have he : (⟨152, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 152 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0152
                ·
                  have he : (⟨153, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 153 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0153
              ·
                by_cases h155 : i.val < 155
                ·
                  have he : (⟨154, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 154 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0154
                ·
                  have he : (⟨155, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 155 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0155
    ·
      by_cases h182 : i.val < 182
      ·
        by_cases h169 : i.val < 169
        ·
          by_cases h162 : i.val < 162
          ·
            by_cases h159 : i.val < 159
            ·
              by_cases h157 : i.val < 157
              ·
                have he : (⟨156, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 156 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0156
              ·
                by_cases h158 : i.val < 158
                ·
                  have he : (⟨157, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 157 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0157
                ·
                  have he : (⟨158, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 158 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0158
            ·
              by_cases h160 : i.val < 160
              ·
                have he : (⟨159, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 159 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0159
              ·
                by_cases h161 : i.val < 161
                ·
                  have he : (⟨160, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 160 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0160
                ·
                  have he : (⟨161, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 161 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0161
          ·
            by_cases h165 : i.val < 165
            ·
              by_cases h163 : i.val < 163
              ·
                have he : (⟨162, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 162 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0162
              ·
                by_cases h164 : i.val < 164
                ·
                  have he : (⟨163, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 163 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0163
                ·
                  have he : (⟨164, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 164 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0164
            ·
              by_cases h167 : i.val < 167
              ·
                by_cases h166 : i.val < 166
                ·
                  have he : (⟨165, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 165 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0165
                ·
                  have he : (⟨166, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 166 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0166
              ·
                by_cases h168 : i.val < 168
                ·
                  have he : (⟨167, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 167 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0167
                ·
                  have he : (⟨168, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 168 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0168
        ·
          by_cases h175 : i.val < 175
          ·
            by_cases h172 : i.val < 172
            ·
              by_cases h170 : i.val < 170
              ·
                have he : (⟨169, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 169 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0169
              ·
                by_cases h171 : i.val < 171
                ·
                  have he : (⟨170, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 170 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0170
                ·
                  have he : (⟨171, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 171 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0171
            ·
              by_cases h173 : i.val < 173
              ·
                have he : (⟨172, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 172 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0172
              ·
                by_cases h174 : i.val < 174
                ·
                  have he : (⟨173, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 173 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0173
                ·
                  have he : (⟨174, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 174 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0174
          ·
            by_cases h178 : i.val < 178
            ·
              by_cases h176 : i.val < 176
              ·
                have he : (⟨175, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 175 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0175
              ·
                by_cases h177 : i.val < 177
                ·
                  have he : (⟨176, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 176 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0176
                ·
                  have he : (⟨177, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 177 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0177
            ·
              by_cases h180 : i.val < 180
              ·
                by_cases h179 : i.val < 179
                ·
                  have he : (⟨178, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 178 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0178
                ·
                  have he : (⟨179, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 179 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0179
              ·
                by_cases h181 : i.val < 181
                ·
                  have he : (⟨180, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 180 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0180
                ·
                  have he : (⟨181, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 181 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0181
      ·
        by_cases h195 : i.val < 195
        ·
          by_cases h188 : i.val < 188
          ·
            by_cases h185 : i.val < 185
            ·
              by_cases h183 : i.val < 183
              ·
                have he : (⟨182, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 182 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0182
              ·
                by_cases h184 : i.val < 184
                ·
                  have he : (⟨183, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 183 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0183
                ·
                  have he : (⟨184, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 184 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0184
            ·
              by_cases h186 : i.val < 186
              ·
                have he : (⟨185, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 185 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0185
              ·
                by_cases h187 : i.val < 187
                ·
                  have he : (⟨186, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 186 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0186
                ·
                  have he : (⟨187, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 187 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0187
          ·
            by_cases h191 : i.val < 191
            ·
              by_cases h189 : i.val < 189
              ·
                have he : (⟨188, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 188 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0188
              ·
                by_cases h190 : i.val < 190
                ·
                  have he : (⟨189, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 189 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0189
                ·
                  have he : (⟨190, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 190 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0190
            ·
              by_cases h193 : i.val < 193
              ·
                by_cases h192 : i.val < 192
                ·
                  have he : (⟨191, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 191 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0191
                ·
                  have he : (⟨192, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 192 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0192
              ·
                by_cases h194 : i.val < 194
                ·
                  have he : (⟨193, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 193 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0193
                ·
                  have he : (⟨194, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 194 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0194
        ·
          by_cases h202 : i.val < 202
          ·
            by_cases h198 : i.val < 198
            ·
              by_cases h196 : i.val < 196
              ·
                have he : (⟨195, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 195 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0195
              ·
                by_cases h197 : i.val < 197
                ·
                  have he : (⟨196, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 196 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0196
                ·
                  have he : (⟨197, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 197 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0197
            ·
              by_cases h200 : i.val < 200
              ·
                by_cases h199 : i.val < 199
                ·
                  have he : (⟨198, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 198 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0198
                ·
                  have he : (⟨199, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 199 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0199
              ·
                by_cases h201 : i.val < 201
                ·
                  have he : (⟨200, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 200 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0200
                ·
                  have he : (⟨201, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 201 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0201
          ·
            by_cases h205 : i.val < 205
            ·
              by_cases h203 : i.val < 203
              ·
                have he : (⟨202, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 202 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_supportRows_identity_row0202
              ·
                by_cases h204 : i.val < 204
                ·
                  have he : (⟨203, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 203 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0203
                ·
                  have he : (⟨204, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 204 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0204
            ·
              by_cases h207 : i.val < 207
              ·
                by_cases h206 : i.val < 206
                ·
                  have he : (⟨205, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 205 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0205
                ·
                  have he : (⟨206, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 206 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0206
              ·
                by_cases h208 : i.val < 208
                ·
                  have he : (⟨207, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 207 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0207
                ·
                  have he : (⟨208, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 208 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_supportRows_identity_row0208

theorem bundle_2098644a87_lowerFacets_iff_row0000 : ∀ j : Fin 209, j ∈ lowerFacets (⟨0, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨0, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨0, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0001 : ∀ j : Fin 209, j ∈ lowerFacets (⟨1, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨1, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨1, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0002 : ∀ j : Fin 209, j ∈ lowerFacets (⟨2, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨2, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨2, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0003 : ∀ j : Fin 209, j ∈ lowerFacets (⟨3, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨3, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨3, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0004 : ∀ j : Fin 209, j ∈ lowerFacets (⟨4, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨4, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨4, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0005 : ∀ j : Fin 209, j ∈ lowerFacets (⟨5, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨5, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨5, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0006 : ∀ j : Fin 209, j ∈ lowerFacets (⟨6, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨6, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨6, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0007 : ∀ j : Fin 209, j ∈ lowerFacets (⟨7, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨7, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨7, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0008 : ∀ j : Fin 209, j ∈ lowerFacets (⟨8, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨8, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨8, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0009 : ∀ j : Fin 209, j ∈ lowerFacets (⟨9, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨9, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨9, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0010 : ∀ j : Fin 209, j ∈ lowerFacets (⟨10, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨10, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨10, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0011 : ∀ j : Fin 209, j ∈ lowerFacets (⟨11, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨11, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨11, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0012 : ∀ j : Fin 209, j ∈ lowerFacets (⟨12, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨12, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨12, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0013 : ∀ j : Fin 209, j ∈ lowerFacets (⟨13, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨13, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨13, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0014 : ∀ j : Fin 209, j ∈ lowerFacets (⟨14, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨14, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨14, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0015 : ∀ j : Fin 209, j ∈ lowerFacets (⟨15, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨15, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨15, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0016 : ∀ j : Fin 209, j ∈ lowerFacets (⟨16, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨16, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨16, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0017 : ∀ j : Fin 209, j ∈ lowerFacets (⟨17, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨17, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨17, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0018 : ∀ j : Fin 209, j ∈ lowerFacets (⟨18, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨18, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨18, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0019 : ∀ j : Fin 209, j ∈ lowerFacets (⟨19, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨19, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨19, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0020 : ∀ j : Fin 209, j ∈ lowerFacets (⟨20, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨20, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨20, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0021 : ∀ j : Fin 209, j ∈ lowerFacets (⟨21, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨21, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨21, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0022 : ∀ j : Fin 209, j ∈ lowerFacets (⟨22, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨22, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨22, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0023 : ∀ j : Fin 209, j ∈ lowerFacets (⟨23, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨23, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨23, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0024 : ∀ j : Fin 209, j ∈ lowerFacets (⟨24, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨24, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨24, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0025 : ∀ j : Fin 209, j ∈ lowerFacets (⟨25, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨25, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨25, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0026 : ∀ j : Fin 209, j ∈ lowerFacets (⟨26, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨26, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨26, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0027 : ∀ j : Fin 209, j ∈ lowerFacets (⟨27, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨27, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨27, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0028 : ∀ j : Fin 209, j ∈ lowerFacets (⟨28, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨28, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨28, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0029 : ∀ j : Fin 209, j ∈ lowerFacets (⟨29, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨29, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨29, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0030 : ∀ j : Fin 209, j ∈ lowerFacets (⟨30, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨30, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨30, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0031 : ∀ j : Fin 209, j ∈ lowerFacets (⟨31, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨31, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨31, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0032 : ∀ j : Fin 209, j ∈ lowerFacets (⟨32, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨32, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨32, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0033 : ∀ j : Fin 209, j ∈ lowerFacets (⟨33, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨33, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨33, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0034 : ∀ j : Fin 209, j ∈ lowerFacets (⟨34, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨34, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨34, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0035 : ∀ j : Fin 209, j ∈ lowerFacets (⟨35, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨35, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨35, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0036 : ∀ j : Fin 209, j ∈ lowerFacets (⟨36, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨36, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨36, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0037 : ∀ j : Fin 209, j ∈ lowerFacets (⟨37, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨37, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨37, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0038 : ∀ j : Fin 209, j ∈ lowerFacets (⟨38, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨38, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨38, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0039 : ∀ j : Fin 209, j ∈ lowerFacets (⟨39, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨39, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨39, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0040 : ∀ j : Fin 209, j ∈ lowerFacets (⟨40, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨40, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨40, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0041 : ∀ j : Fin 209, j ∈ lowerFacets (⟨41, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨41, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨41, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0042 : ∀ j : Fin 209, j ∈ lowerFacets (⟨42, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨42, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨42, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0043 : ∀ j : Fin 209, j ∈ lowerFacets (⟨43, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨43, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨43, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0044 : ∀ j : Fin 209, j ∈ lowerFacets (⟨44, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨44, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨44, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0045 : ∀ j : Fin 209, j ∈ lowerFacets (⟨45, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨45, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨45, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0046 : ∀ j : Fin 209, j ∈ lowerFacets (⟨46, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨46, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨46, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0047 : ∀ j : Fin 209, j ∈ lowerFacets (⟨47, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨47, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨47, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0048 : ∀ j : Fin 209, j ∈ lowerFacets (⟨48, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨48, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨48, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0049 : ∀ j : Fin 209, j ∈ lowerFacets (⟨49, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨49, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨49, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0050 : ∀ j : Fin 209, j ∈ lowerFacets (⟨50, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨50, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨50, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0051 : ∀ j : Fin 209, j ∈ lowerFacets (⟨51, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨51, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨51, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0052 : ∀ j : Fin 209, j ∈ lowerFacets (⟨52, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨52, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨52, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0053 : ∀ j : Fin 209, j ∈ lowerFacets (⟨53, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨53, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨53, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0054 : ∀ j : Fin 209, j ∈ lowerFacets (⟨54, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨54, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨54, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0055 : ∀ j : Fin 209, j ∈ lowerFacets (⟨55, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨55, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨55, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0056 : ∀ j : Fin 209, j ∈ lowerFacets (⟨56, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨56, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨56, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0057 : ∀ j : Fin 209, j ∈ lowerFacets (⟨57, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨57, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨57, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0058 : ∀ j : Fin 209, j ∈ lowerFacets (⟨58, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨58, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨58, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0059 : ∀ j : Fin 209, j ∈ lowerFacets (⟨59, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨59, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨59, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0060 : ∀ j : Fin 209, j ∈ lowerFacets (⟨60, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨60, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨60, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0061 : ∀ j : Fin 209, j ∈ lowerFacets (⟨61, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨61, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨61, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0062 : ∀ j : Fin 209, j ∈ lowerFacets (⟨62, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨62, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨62, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0063 : ∀ j : Fin 209, j ∈ lowerFacets (⟨63, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨63, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨63, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0064 : ∀ j : Fin 209, j ∈ lowerFacets (⟨64, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨64, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨64, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0065 : ∀ j : Fin 209, j ∈ lowerFacets (⟨65, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨65, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨65, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0066 : ∀ j : Fin 209, j ∈ lowerFacets (⟨66, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨66, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨66, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0067 : ∀ j : Fin 209, j ∈ lowerFacets (⟨67, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨67, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨67, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0068 : ∀ j : Fin 209, j ∈ lowerFacets (⟨68, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨68, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨68, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0069 : ∀ j : Fin 209, j ∈ lowerFacets (⟨69, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨69, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨69, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0070 : ∀ j : Fin 209, j ∈ lowerFacets (⟨70, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨70, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨70, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0071 : ∀ j : Fin 209, j ∈ lowerFacets (⟨71, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨71, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨71, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0072 : ∀ j : Fin 209, j ∈ lowerFacets (⟨72, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨72, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨72, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0073 : ∀ j : Fin 209, j ∈ lowerFacets (⟨73, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨73, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨73, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0074 : ∀ j : Fin 209, j ∈ lowerFacets (⟨74, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨74, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨74, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0075 : ∀ j : Fin 209, j ∈ lowerFacets (⟨75, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨75, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨75, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0076 : ∀ j : Fin 209, j ∈ lowerFacets (⟨76, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨76, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨76, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0077 : ∀ j : Fin 209, j ∈ lowerFacets (⟨77, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨77, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨77, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0078 : ∀ j : Fin 209, j ∈ lowerFacets (⟨78, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨78, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨78, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0079 : ∀ j : Fin 209, j ∈ lowerFacets (⟨79, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨79, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨79, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0080 : ∀ j : Fin 209, j ∈ lowerFacets (⟨80, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨80, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨80, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0081 : ∀ j : Fin 209, j ∈ lowerFacets (⟨81, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨81, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨81, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0082 : ∀ j : Fin 209, j ∈ lowerFacets (⟨82, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨82, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨82, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0083 : ∀ j : Fin 209, j ∈ lowerFacets (⟨83, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨83, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨83, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0084 : ∀ j : Fin 209, j ∈ lowerFacets (⟨84, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨84, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨84, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0085 : ∀ j : Fin 209, j ∈ lowerFacets (⟨85, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨85, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨85, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0086 : ∀ j : Fin 209, j ∈ lowerFacets (⟨86, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨86, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨86, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0087 : ∀ j : Fin 209, j ∈ lowerFacets (⟨87, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨87, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨87, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0088 : ∀ j : Fin 209, j ∈ lowerFacets (⟨88, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨88, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨88, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0089 : ∀ j : Fin 209, j ∈ lowerFacets (⟨89, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨89, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨89, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0090 : ∀ j : Fin 209, j ∈ lowerFacets (⟨90, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨90, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨90, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0091 : ∀ j : Fin 209, j ∈ lowerFacets (⟨91, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨91, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨91, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0092 : ∀ j : Fin 209, j ∈ lowerFacets (⟨92, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨92, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨92, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0093 : ∀ j : Fin 209, j ∈ lowerFacets (⟨93, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨93, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨93, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0094 : ∀ j : Fin 209, j ∈ lowerFacets (⟨94, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨94, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨94, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0095 : ∀ j : Fin 209, j ∈ lowerFacets (⟨95, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨95, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨95, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0096 : ∀ j : Fin 209, j ∈ lowerFacets (⟨96, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨96, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨96, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0097 : ∀ j : Fin 209, j ∈ lowerFacets (⟨97, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨97, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨97, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0098 : ∀ j : Fin 209, j ∈ lowerFacets (⟨98, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨98, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨98, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0099 : ∀ j : Fin 209, j ∈ lowerFacets (⟨99, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨99, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨99, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0100 : ∀ j : Fin 209, j ∈ lowerFacets (⟨100, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨100, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨100, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0101 : ∀ j : Fin 209, j ∈ lowerFacets (⟨101, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨101, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨101, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0102 : ∀ j : Fin 209, j ∈ lowerFacets (⟨102, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨102, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨102, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0103 : ∀ j : Fin 209, j ∈ lowerFacets (⟨103, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨103, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨103, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0104 : ∀ j : Fin 209, j ∈ lowerFacets (⟨104, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨104, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨104, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0105 : ∀ j : Fin 209, j ∈ lowerFacets (⟨105, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨105, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨105, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0106 : ∀ j : Fin 209, j ∈ lowerFacets (⟨106, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨106, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨106, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0107 : ∀ j : Fin 209, j ∈ lowerFacets (⟨107, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨107, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨107, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0108 : ∀ j : Fin 209, j ∈ lowerFacets (⟨108, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨108, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨108, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0109 : ∀ j : Fin 209, j ∈ lowerFacets (⟨109, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨109, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨109, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0110 : ∀ j : Fin 209, j ∈ lowerFacets (⟨110, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨110, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨110, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0111 : ∀ j : Fin 209, j ∈ lowerFacets (⟨111, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨111, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨111, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0112 : ∀ j : Fin 209, j ∈ lowerFacets (⟨112, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨112, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨112, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0113 : ∀ j : Fin 209, j ∈ lowerFacets (⟨113, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨113, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨113, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0114 : ∀ j : Fin 209, j ∈ lowerFacets (⟨114, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨114, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨114, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0115 : ∀ j : Fin 209, j ∈ lowerFacets (⟨115, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨115, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨115, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0116 : ∀ j : Fin 209, j ∈ lowerFacets (⟨116, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨116, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨116, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0117 : ∀ j : Fin 209, j ∈ lowerFacets (⟨117, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨117, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨117, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0118 : ∀ j : Fin 209, j ∈ lowerFacets (⟨118, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨118, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨118, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0119 : ∀ j : Fin 209, j ∈ lowerFacets (⟨119, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨119, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨119, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0120 : ∀ j : Fin 209, j ∈ lowerFacets (⟨120, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨120, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨120, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0121 : ∀ j : Fin 209, j ∈ lowerFacets (⟨121, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨121, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨121, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0122 : ∀ j : Fin 209, j ∈ lowerFacets (⟨122, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨122, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨122, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0123 : ∀ j : Fin 209, j ∈ lowerFacets (⟨123, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨123, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨123, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0124 : ∀ j : Fin 209, j ∈ lowerFacets (⟨124, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨124, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨124, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0125 : ∀ j : Fin 209, j ∈ lowerFacets (⟨125, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨125, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨125, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0126 : ∀ j : Fin 209, j ∈ lowerFacets (⟨126, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨126, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨126, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0127 : ∀ j : Fin 209, j ∈ lowerFacets (⟨127, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨127, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨127, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0128 : ∀ j : Fin 209, j ∈ lowerFacets (⟨128, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨128, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨128, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0129 : ∀ j : Fin 209, j ∈ lowerFacets (⟨129, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨129, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨129, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0130 : ∀ j : Fin 209, j ∈ lowerFacets (⟨130, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨130, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨130, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0131 : ∀ j : Fin 209, j ∈ lowerFacets (⟨131, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨131, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨131, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0132 : ∀ j : Fin 209, j ∈ lowerFacets (⟨132, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨132, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨132, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0133 : ∀ j : Fin 209, j ∈ lowerFacets (⟨133, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨133, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨133, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0134 : ∀ j : Fin 209, j ∈ lowerFacets (⟨134, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨134, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨134, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0135 : ∀ j : Fin 209, j ∈ lowerFacets (⟨135, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨135, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨135, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0136 : ∀ j : Fin 209, j ∈ lowerFacets (⟨136, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨136, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨136, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0137 : ∀ j : Fin 209, j ∈ lowerFacets (⟨137, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨137, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨137, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0138 : ∀ j : Fin 209, j ∈ lowerFacets (⟨138, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨138, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨138, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0139 : ∀ j : Fin 209, j ∈ lowerFacets (⟨139, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨139, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨139, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0140 : ∀ j : Fin 209, j ∈ lowerFacets (⟨140, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨140, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨140, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0141 : ∀ j : Fin 209, j ∈ lowerFacets (⟨141, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨141, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨141, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0142 : ∀ j : Fin 209, j ∈ lowerFacets (⟨142, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨142, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨142, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0143 : ∀ j : Fin 209, j ∈ lowerFacets (⟨143, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨143, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨143, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0144 : ∀ j : Fin 209, j ∈ lowerFacets (⟨144, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨144, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨144, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0145 : ∀ j : Fin 209, j ∈ lowerFacets (⟨145, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨145, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨145, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0146 : ∀ j : Fin 209, j ∈ lowerFacets (⟨146, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨146, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨146, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0147 : ∀ j : Fin 209, j ∈ lowerFacets (⟨147, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨147, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨147, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0148 : ∀ j : Fin 209, j ∈ lowerFacets (⟨148, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨148, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨148, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0149 : ∀ j : Fin 209, j ∈ lowerFacets (⟨149, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨149, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨149, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0150 : ∀ j : Fin 209, j ∈ lowerFacets (⟨150, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨150, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨150, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0151 : ∀ j : Fin 209, j ∈ lowerFacets (⟨151, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨151, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨151, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0152 : ∀ j : Fin 209, j ∈ lowerFacets (⟨152, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨152, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨152, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0153 : ∀ j : Fin 209, j ∈ lowerFacets (⟨153, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨153, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨153, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0154 : ∀ j : Fin 209, j ∈ lowerFacets (⟨154, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨154, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨154, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0155 : ∀ j : Fin 209, j ∈ lowerFacets (⟨155, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨155, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨155, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0156 : ∀ j : Fin 209, j ∈ lowerFacets (⟨156, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨156, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨156, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0157 : ∀ j : Fin 209, j ∈ lowerFacets (⟨157, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨157, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨157, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0158 : ∀ j : Fin 209, j ∈ lowerFacets (⟨158, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨158, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨158, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0159 : ∀ j : Fin 209, j ∈ lowerFacets (⟨159, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨159, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨159, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0160 : ∀ j : Fin 209, j ∈ lowerFacets (⟨160, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨160, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨160, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0161 : ∀ j : Fin 209, j ∈ lowerFacets (⟨161, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨161, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨161, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0162 : ∀ j : Fin 209, j ∈ lowerFacets (⟨162, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨162, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨162, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0163 : ∀ j : Fin 209, j ∈ lowerFacets (⟨163, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨163, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨163, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0164 : ∀ j : Fin 209, j ∈ lowerFacets (⟨164, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨164, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨164, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0165 : ∀ j : Fin 209, j ∈ lowerFacets (⟨165, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨165, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨165, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0166 : ∀ j : Fin 209, j ∈ lowerFacets (⟨166, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨166, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨166, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0167 : ∀ j : Fin 209, j ∈ lowerFacets (⟨167, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨167, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨167, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0168 : ∀ j : Fin 209, j ∈ lowerFacets (⟨168, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨168, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨168, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0169 : ∀ j : Fin 209, j ∈ lowerFacets (⟨169, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨169, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨169, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0170 : ∀ j : Fin 209, j ∈ lowerFacets (⟨170, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨170, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨170, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0171 : ∀ j : Fin 209, j ∈ lowerFacets (⟨171, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨171, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨171, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0172 : ∀ j : Fin 209, j ∈ lowerFacets (⟨172, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨172, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨172, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0173 : ∀ j : Fin 209, j ∈ lowerFacets (⟨173, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨173, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨173, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0174 : ∀ j : Fin 209, j ∈ lowerFacets (⟨174, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨174, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨174, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0175 : ∀ j : Fin 209, j ∈ lowerFacets (⟨175, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨175, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨175, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0176 : ∀ j : Fin 209, j ∈ lowerFacets (⟨176, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨176, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨176, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0177 : ∀ j : Fin 209, j ∈ lowerFacets (⟨177, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨177, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨177, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0178 : ∀ j : Fin 209, j ∈ lowerFacets (⟨178, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨178, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨178, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0179 : ∀ j : Fin 209, j ∈ lowerFacets (⟨179, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨179, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨179, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0180 : ∀ j : Fin 209, j ∈ lowerFacets (⟨180, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨180, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨180, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0181 : ∀ j : Fin 209, j ∈ lowerFacets (⟨181, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨181, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨181, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0182 : ∀ j : Fin 209, j ∈ lowerFacets (⟨182, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨182, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨182, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0183 : ∀ j : Fin 209, j ∈ lowerFacets (⟨183, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨183, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨183, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0184 : ∀ j : Fin 209, j ∈ lowerFacets (⟨184, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨184, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨184, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0185 : ∀ j : Fin 209, j ∈ lowerFacets (⟨185, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨185, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨185, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0186 : ∀ j : Fin 209, j ∈ lowerFacets (⟨186, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨186, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨186, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0187 : ∀ j : Fin 209, j ∈ lowerFacets (⟨187, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨187, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨187, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0188 : ∀ j : Fin 209, j ∈ lowerFacets (⟨188, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨188, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨188, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0189 : ∀ j : Fin 209, j ∈ lowerFacets (⟨189, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨189, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨189, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0190 : ∀ j : Fin 209, j ∈ lowerFacets (⟨190, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨190, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨190, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0191 : ∀ j : Fin 209, j ∈ lowerFacets (⟨191, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨191, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨191, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0192 : ∀ j : Fin 209, j ∈ lowerFacets (⟨192, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨192, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨192, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0193 : ∀ j : Fin 209, j ∈ lowerFacets (⟨193, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨193, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨193, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0194 : ∀ j : Fin 209, j ∈ lowerFacets (⟨194, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨194, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨194, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0195 : ∀ j : Fin 209, j ∈ lowerFacets (⟨195, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨195, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨195, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0196 : ∀ j : Fin 209, j ∈ lowerFacets (⟨196, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨196, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨196, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0197 : ∀ j : Fin 209, j ∈ lowerFacets (⟨197, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨197, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨197, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0198 : ∀ j : Fin 209, j ∈ lowerFacets (⟨198, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨198, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨198, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0199 : ∀ j : Fin 209, j ∈ lowerFacets (⟨199, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨199, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨199, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0200 : ∀ j : Fin 209, j ∈ lowerFacets (⟨200, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨200, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨200, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0201 : ∀ j : Fin 209, j ∈ lowerFacets (⟨201, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨201, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨201, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0202 : ∀ j : Fin 209, j ∈ lowerFacets (⟨202, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨202, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨202, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0203 : ∀ j : Fin 209, j ∈ lowerFacets (⟨203, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨203, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨203, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0204 : ∀ j : Fin 209, j ∈ lowerFacets (⟨204, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨204, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨204, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0205 : ∀ j : Fin 209, j ∈ lowerFacets (⟨205, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨205, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨205, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0206 : ∀ j : Fin 209, j ∈ lowerFacets (⟨206, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨206, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨206, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0207 : ∀ j : Fin 209, j ∈ lowerFacets (⟨207, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨207, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨207, by decide⟩ : Fin 209) := by decide +kernel

theorem bundle_2098644a87_lowerFacets_iff_row0208 : ∀ j : Fin 209, j ∈ lowerFacets (⟨208, by decide⟩ : Fin 209) ↔ (faceRank j).val + 1 = (faceRank (⟨208, by decide⟩ : Fin 209)).val ∧ faceMask j ⊆ faceMask (⟨208, by decide⟩ : Fin 209) := by decide +kernel

theorem lowerFacets_iff : ∀ i j : Fin 209,
    j ∈ lowerFacets i ↔
      (faceRank j).val + 1 = (faceRank i).val ∧ faceMask j ⊆ faceMask i := by
  intro i
  have hi_bound := i.isLt
  by_cases h104 : i.val < 104
  ·
    by_cases h52 : i.val < 52
    ·
      by_cases h26 : i.val < 26
      ·
        by_cases h13 : i.val < 13
        ·
          by_cases h6 : i.val < 6
          ·
            by_cases h3 : i.val < 3
            ·
              by_cases h1 : i.val < 1
              ·
                have he : (⟨0, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 0 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0000
              ·
                by_cases h2 : i.val < 2
                ·
                  have he : (⟨1, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 1 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0001
                ·
                  have he : (⟨2, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 2 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0002
            ·
              by_cases h4 : i.val < 4
              ·
                have he : (⟨3, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 3 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0003
              ·
                by_cases h5 : i.val < 5
                ·
                  have he : (⟨4, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 4 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0004
                ·
                  have he : (⟨5, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 5 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0005
          ·
            by_cases h9 : i.val < 9
            ·
              by_cases h7 : i.val < 7
              ·
                have he : (⟨6, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 6 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0006
              ·
                by_cases h8 : i.val < 8
                ·
                  have he : (⟨7, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 7 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0007
                ·
                  have he : (⟨8, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 8 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0008
            ·
              by_cases h11 : i.val < 11
              ·
                by_cases h10 : i.val < 10
                ·
                  have he : (⟨9, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 9 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0009
                ·
                  have he : (⟨10, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 10 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0010
              ·
                by_cases h12 : i.val < 12
                ·
                  have he : (⟨11, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 11 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0011
                ·
                  have he : (⟨12, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 12 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0012
        ·
          by_cases h19 : i.val < 19
          ·
            by_cases h16 : i.val < 16
            ·
              by_cases h14 : i.val < 14
              ·
                have he : (⟨13, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 13 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0013
              ·
                by_cases h15 : i.val < 15
                ·
                  have he : (⟨14, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 14 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0014
                ·
                  have he : (⟨15, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 15 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0015
            ·
              by_cases h17 : i.val < 17
              ·
                have he : (⟨16, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 16 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0016
              ·
                by_cases h18 : i.val < 18
                ·
                  have he : (⟨17, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 17 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0017
                ·
                  have he : (⟨18, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 18 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0018
          ·
            by_cases h22 : i.val < 22
            ·
              by_cases h20 : i.val < 20
              ·
                have he : (⟨19, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 19 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0019
              ·
                by_cases h21 : i.val < 21
                ·
                  have he : (⟨20, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 20 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0020
                ·
                  have he : (⟨21, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 21 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0021
            ·
              by_cases h24 : i.val < 24
              ·
                by_cases h23 : i.val < 23
                ·
                  have he : (⟨22, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 22 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0022
                ·
                  have he : (⟨23, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 23 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0023
              ·
                by_cases h25 : i.val < 25
                ·
                  have he : (⟨24, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 24 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0024
                ·
                  have he : (⟨25, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 25 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0025
      ·
        by_cases h39 : i.val < 39
        ·
          by_cases h32 : i.val < 32
          ·
            by_cases h29 : i.val < 29
            ·
              by_cases h27 : i.val < 27
              ·
                have he : (⟨26, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 26 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0026
              ·
                by_cases h28 : i.val < 28
                ·
                  have he : (⟨27, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 27 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0027
                ·
                  have he : (⟨28, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 28 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0028
            ·
              by_cases h30 : i.val < 30
              ·
                have he : (⟨29, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 29 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0029
              ·
                by_cases h31 : i.val < 31
                ·
                  have he : (⟨30, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 30 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0030
                ·
                  have he : (⟨31, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 31 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0031
          ·
            by_cases h35 : i.val < 35
            ·
              by_cases h33 : i.val < 33
              ·
                have he : (⟨32, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 32 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0032
              ·
                by_cases h34 : i.val < 34
                ·
                  have he : (⟨33, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 33 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0033
                ·
                  have he : (⟨34, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 34 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0034
            ·
              by_cases h37 : i.val < 37
              ·
                by_cases h36 : i.val < 36
                ·
                  have he : (⟨35, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 35 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0035
                ·
                  have he : (⟨36, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 36 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0036
              ·
                by_cases h38 : i.val < 38
                ·
                  have he : (⟨37, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 37 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0037
                ·
                  have he : (⟨38, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 38 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0038
        ·
          by_cases h45 : i.val < 45
          ·
            by_cases h42 : i.val < 42
            ·
              by_cases h40 : i.val < 40
              ·
                have he : (⟨39, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 39 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0039
              ·
                by_cases h41 : i.val < 41
                ·
                  have he : (⟨40, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 40 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0040
                ·
                  have he : (⟨41, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 41 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0041
            ·
              by_cases h43 : i.val < 43
              ·
                have he : (⟨42, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 42 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0042
              ·
                by_cases h44 : i.val < 44
                ·
                  have he : (⟨43, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 43 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0043
                ·
                  have he : (⟨44, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 44 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0044
          ·
            by_cases h48 : i.val < 48
            ·
              by_cases h46 : i.val < 46
              ·
                have he : (⟨45, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 45 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0045
              ·
                by_cases h47 : i.val < 47
                ·
                  have he : (⟨46, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 46 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0046
                ·
                  have he : (⟨47, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 47 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0047
            ·
              by_cases h50 : i.val < 50
              ·
                by_cases h49 : i.val < 49
                ·
                  have he : (⟨48, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 48 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0048
                ·
                  have he : (⟨49, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 49 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0049
              ·
                by_cases h51 : i.val < 51
                ·
                  have he : (⟨50, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 50 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0050
                ·
                  have he : (⟨51, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 51 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0051
    ·
      by_cases h78 : i.val < 78
      ·
        by_cases h65 : i.val < 65
        ·
          by_cases h58 : i.val < 58
          ·
            by_cases h55 : i.val < 55
            ·
              by_cases h53 : i.val < 53
              ·
                have he : (⟨52, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 52 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0052
              ·
                by_cases h54 : i.val < 54
                ·
                  have he : (⟨53, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 53 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0053
                ·
                  have he : (⟨54, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 54 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0054
            ·
              by_cases h56 : i.val < 56
              ·
                have he : (⟨55, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 55 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0055
              ·
                by_cases h57 : i.val < 57
                ·
                  have he : (⟨56, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 56 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0056
                ·
                  have he : (⟨57, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 57 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0057
          ·
            by_cases h61 : i.val < 61
            ·
              by_cases h59 : i.val < 59
              ·
                have he : (⟨58, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 58 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0058
              ·
                by_cases h60 : i.val < 60
                ·
                  have he : (⟨59, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 59 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0059
                ·
                  have he : (⟨60, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 60 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0060
            ·
              by_cases h63 : i.val < 63
              ·
                by_cases h62 : i.val < 62
                ·
                  have he : (⟨61, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 61 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0061
                ·
                  have he : (⟨62, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 62 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0062
              ·
                by_cases h64 : i.val < 64
                ·
                  have he : (⟨63, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 63 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0063
                ·
                  have he : (⟨64, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 64 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0064
        ·
          by_cases h71 : i.val < 71
          ·
            by_cases h68 : i.val < 68
            ·
              by_cases h66 : i.val < 66
              ·
                have he : (⟨65, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 65 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0065
              ·
                by_cases h67 : i.val < 67
                ·
                  have he : (⟨66, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 66 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0066
                ·
                  have he : (⟨67, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 67 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0067
            ·
              by_cases h69 : i.val < 69
              ·
                have he : (⟨68, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 68 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0068
              ·
                by_cases h70 : i.val < 70
                ·
                  have he : (⟨69, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 69 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0069
                ·
                  have he : (⟨70, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 70 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0070
          ·
            by_cases h74 : i.val < 74
            ·
              by_cases h72 : i.val < 72
              ·
                have he : (⟨71, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 71 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0071
              ·
                by_cases h73 : i.val < 73
                ·
                  have he : (⟨72, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 72 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0072
                ·
                  have he : (⟨73, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 73 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0073
            ·
              by_cases h76 : i.val < 76
              ·
                by_cases h75 : i.val < 75
                ·
                  have he : (⟨74, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 74 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0074
                ·
                  have he : (⟨75, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 75 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0075
              ·
                by_cases h77 : i.val < 77
                ·
                  have he : (⟨76, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 76 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0076
                ·
                  have he : (⟨77, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 77 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0077
      ·
        by_cases h91 : i.val < 91
        ·
          by_cases h84 : i.val < 84
          ·
            by_cases h81 : i.val < 81
            ·
              by_cases h79 : i.val < 79
              ·
                have he : (⟨78, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 78 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0078
              ·
                by_cases h80 : i.val < 80
                ·
                  have he : (⟨79, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 79 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0079
                ·
                  have he : (⟨80, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 80 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0080
            ·
              by_cases h82 : i.val < 82
              ·
                have he : (⟨81, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 81 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0081
              ·
                by_cases h83 : i.val < 83
                ·
                  have he : (⟨82, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 82 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0082
                ·
                  have he : (⟨83, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 83 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0083
          ·
            by_cases h87 : i.val < 87
            ·
              by_cases h85 : i.val < 85
              ·
                have he : (⟨84, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 84 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0084
              ·
                by_cases h86 : i.val < 86
                ·
                  have he : (⟨85, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 85 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0085
                ·
                  have he : (⟨86, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 86 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0086
            ·
              by_cases h89 : i.val < 89
              ·
                by_cases h88 : i.val < 88
                ·
                  have he : (⟨87, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 87 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0087
                ·
                  have he : (⟨88, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 88 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0088
              ·
                by_cases h90 : i.val < 90
                ·
                  have he : (⟨89, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 89 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0089
                ·
                  have he : (⟨90, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 90 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0090
        ·
          by_cases h97 : i.val < 97
          ·
            by_cases h94 : i.val < 94
            ·
              by_cases h92 : i.val < 92
              ·
                have he : (⟨91, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 91 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0091
              ·
                by_cases h93 : i.val < 93
                ·
                  have he : (⟨92, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 92 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0092
                ·
                  have he : (⟨93, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 93 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0093
            ·
              by_cases h95 : i.val < 95
              ·
                have he : (⟨94, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 94 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0094
              ·
                by_cases h96 : i.val < 96
                ·
                  have he : (⟨95, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 95 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0095
                ·
                  have he : (⟨96, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 96 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0096
          ·
            by_cases h100 : i.val < 100
            ·
              by_cases h98 : i.val < 98
              ·
                have he : (⟨97, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 97 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0097
              ·
                by_cases h99 : i.val < 99
                ·
                  have he : (⟨98, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 98 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0098
                ·
                  have he : (⟨99, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 99 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0099
            ·
              by_cases h102 : i.val < 102
              ·
                by_cases h101 : i.val < 101
                ·
                  have he : (⟨100, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 100 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0100
                ·
                  have he : (⟨101, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 101 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0101
              ·
                by_cases h103 : i.val < 103
                ·
                  have he : (⟨102, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 102 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0102
                ·
                  have he : (⟨103, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 103 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0103
  ·
    by_cases h156 : i.val < 156
    ·
      by_cases h130 : i.val < 130
      ·
        by_cases h117 : i.val < 117
        ·
          by_cases h110 : i.val < 110
          ·
            by_cases h107 : i.val < 107
            ·
              by_cases h105 : i.val < 105
              ·
                have he : (⟨104, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 104 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0104
              ·
                by_cases h106 : i.val < 106
                ·
                  have he : (⟨105, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 105 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0105
                ·
                  have he : (⟨106, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 106 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0106
            ·
              by_cases h108 : i.val < 108
              ·
                have he : (⟨107, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 107 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0107
              ·
                by_cases h109 : i.val < 109
                ·
                  have he : (⟨108, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 108 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0108
                ·
                  have he : (⟨109, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 109 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0109
          ·
            by_cases h113 : i.val < 113
            ·
              by_cases h111 : i.val < 111
              ·
                have he : (⟨110, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 110 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0110
              ·
                by_cases h112 : i.val < 112
                ·
                  have he : (⟨111, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 111 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0111
                ·
                  have he : (⟨112, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 112 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0112
            ·
              by_cases h115 : i.val < 115
              ·
                by_cases h114 : i.val < 114
                ·
                  have he : (⟨113, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 113 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0113
                ·
                  have he : (⟨114, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 114 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0114
              ·
                by_cases h116 : i.val < 116
                ·
                  have he : (⟨115, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 115 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0115
                ·
                  have he : (⟨116, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 116 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0116
        ·
          by_cases h123 : i.val < 123
          ·
            by_cases h120 : i.val < 120
            ·
              by_cases h118 : i.val < 118
              ·
                have he : (⟨117, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 117 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0117
              ·
                by_cases h119 : i.val < 119
                ·
                  have he : (⟨118, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 118 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0118
                ·
                  have he : (⟨119, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 119 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0119
            ·
              by_cases h121 : i.val < 121
              ·
                have he : (⟨120, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 120 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0120
              ·
                by_cases h122 : i.val < 122
                ·
                  have he : (⟨121, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 121 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0121
                ·
                  have he : (⟨122, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 122 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0122
          ·
            by_cases h126 : i.val < 126
            ·
              by_cases h124 : i.val < 124
              ·
                have he : (⟨123, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 123 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0123
              ·
                by_cases h125 : i.val < 125
                ·
                  have he : (⟨124, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 124 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0124
                ·
                  have he : (⟨125, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 125 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0125
            ·
              by_cases h128 : i.val < 128
              ·
                by_cases h127 : i.val < 127
                ·
                  have he : (⟨126, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 126 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0126
                ·
                  have he : (⟨127, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 127 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0127
              ·
                by_cases h129 : i.val < 129
                ·
                  have he : (⟨128, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 128 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0128
                ·
                  have he : (⟨129, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 129 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0129
      ·
        by_cases h143 : i.val < 143
        ·
          by_cases h136 : i.val < 136
          ·
            by_cases h133 : i.val < 133
            ·
              by_cases h131 : i.val < 131
              ·
                have he : (⟨130, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 130 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0130
              ·
                by_cases h132 : i.val < 132
                ·
                  have he : (⟨131, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 131 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0131
                ·
                  have he : (⟨132, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 132 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0132
            ·
              by_cases h134 : i.val < 134
              ·
                have he : (⟨133, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 133 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0133
              ·
                by_cases h135 : i.val < 135
                ·
                  have he : (⟨134, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 134 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0134
                ·
                  have he : (⟨135, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 135 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0135
          ·
            by_cases h139 : i.val < 139
            ·
              by_cases h137 : i.val < 137
              ·
                have he : (⟨136, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 136 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0136
              ·
                by_cases h138 : i.val < 138
                ·
                  have he : (⟨137, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 137 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0137
                ·
                  have he : (⟨138, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 138 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0138
            ·
              by_cases h141 : i.val < 141
              ·
                by_cases h140 : i.val < 140
                ·
                  have he : (⟨139, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 139 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0139
                ·
                  have he : (⟨140, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 140 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0140
              ·
                by_cases h142 : i.val < 142
                ·
                  have he : (⟨141, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 141 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0141
                ·
                  have he : (⟨142, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 142 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0142
        ·
          by_cases h149 : i.val < 149
          ·
            by_cases h146 : i.val < 146
            ·
              by_cases h144 : i.val < 144
              ·
                have he : (⟨143, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 143 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0143
              ·
                by_cases h145 : i.val < 145
                ·
                  have he : (⟨144, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 144 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0144
                ·
                  have he : (⟨145, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 145 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0145
            ·
              by_cases h147 : i.val < 147
              ·
                have he : (⟨146, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 146 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0146
              ·
                by_cases h148 : i.val < 148
                ·
                  have he : (⟨147, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 147 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0147
                ·
                  have he : (⟨148, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 148 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0148
          ·
            by_cases h152 : i.val < 152
            ·
              by_cases h150 : i.val < 150
              ·
                have he : (⟨149, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 149 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0149
              ·
                by_cases h151 : i.val < 151
                ·
                  have he : (⟨150, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 150 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0150
                ·
                  have he : (⟨151, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 151 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0151
            ·
              by_cases h154 : i.val < 154
              ·
                by_cases h153 : i.val < 153
                ·
                  have he : (⟨152, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 152 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0152
                ·
                  have he : (⟨153, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 153 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0153
              ·
                by_cases h155 : i.val < 155
                ·
                  have he : (⟨154, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 154 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0154
                ·
                  have he : (⟨155, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 155 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0155
    ·
      by_cases h182 : i.val < 182
      ·
        by_cases h169 : i.val < 169
        ·
          by_cases h162 : i.val < 162
          ·
            by_cases h159 : i.val < 159
            ·
              by_cases h157 : i.val < 157
              ·
                have he : (⟨156, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 156 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0156
              ·
                by_cases h158 : i.val < 158
                ·
                  have he : (⟨157, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 157 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0157
                ·
                  have he : (⟨158, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 158 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0158
            ·
              by_cases h160 : i.val < 160
              ·
                have he : (⟨159, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 159 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0159
              ·
                by_cases h161 : i.val < 161
                ·
                  have he : (⟨160, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 160 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0160
                ·
                  have he : (⟨161, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 161 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0161
          ·
            by_cases h165 : i.val < 165
            ·
              by_cases h163 : i.val < 163
              ·
                have he : (⟨162, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 162 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0162
              ·
                by_cases h164 : i.val < 164
                ·
                  have he : (⟨163, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 163 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0163
                ·
                  have he : (⟨164, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 164 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0164
            ·
              by_cases h167 : i.val < 167
              ·
                by_cases h166 : i.val < 166
                ·
                  have he : (⟨165, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 165 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0165
                ·
                  have he : (⟨166, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 166 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0166
              ·
                by_cases h168 : i.val < 168
                ·
                  have he : (⟨167, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 167 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0167
                ·
                  have he : (⟨168, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 168 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0168
        ·
          by_cases h175 : i.val < 175
          ·
            by_cases h172 : i.val < 172
            ·
              by_cases h170 : i.val < 170
              ·
                have he : (⟨169, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 169 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0169
              ·
                by_cases h171 : i.val < 171
                ·
                  have he : (⟨170, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 170 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0170
                ·
                  have he : (⟨171, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 171 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0171
            ·
              by_cases h173 : i.val < 173
              ·
                have he : (⟨172, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 172 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0172
              ·
                by_cases h174 : i.val < 174
                ·
                  have he : (⟨173, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 173 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0173
                ·
                  have he : (⟨174, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 174 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0174
          ·
            by_cases h178 : i.val < 178
            ·
              by_cases h176 : i.val < 176
              ·
                have he : (⟨175, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 175 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0175
              ·
                by_cases h177 : i.val < 177
                ·
                  have he : (⟨176, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 176 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0176
                ·
                  have he : (⟨177, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 177 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0177
            ·
              by_cases h180 : i.val < 180
              ·
                by_cases h179 : i.val < 179
                ·
                  have he : (⟨178, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 178 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0178
                ·
                  have he : (⟨179, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 179 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0179
              ·
                by_cases h181 : i.val < 181
                ·
                  have he : (⟨180, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 180 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0180
                ·
                  have he : (⟨181, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 181 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0181
      ·
        by_cases h195 : i.val < 195
        ·
          by_cases h188 : i.val < 188
          ·
            by_cases h185 : i.val < 185
            ·
              by_cases h183 : i.val < 183
              ·
                have he : (⟨182, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 182 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0182
              ·
                by_cases h184 : i.val < 184
                ·
                  have he : (⟨183, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 183 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0183
                ·
                  have he : (⟨184, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 184 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0184
            ·
              by_cases h186 : i.val < 186
              ·
                have he : (⟨185, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 185 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0185
              ·
                by_cases h187 : i.val < 187
                ·
                  have he : (⟨186, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 186 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0186
                ·
                  have he : (⟨187, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 187 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0187
          ·
            by_cases h191 : i.val < 191
            ·
              by_cases h189 : i.val < 189
              ·
                have he : (⟨188, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 188 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0188
              ·
                by_cases h190 : i.val < 190
                ·
                  have he : (⟨189, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 189 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0189
                ·
                  have he : (⟨190, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 190 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0190
            ·
              by_cases h193 : i.val < 193
              ·
                by_cases h192 : i.val < 192
                ·
                  have he : (⟨191, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 191 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0191
                ·
                  have he : (⟨192, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 192 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0192
              ·
                by_cases h194 : i.val < 194
                ·
                  have he : (⟨193, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 193 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0193
                ·
                  have he : (⟨194, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 194 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0194
        ·
          by_cases h202 : i.val < 202
          ·
            by_cases h198 : i.val < 198
            ·
              by_cases h196 : i.val < 196
              ·
                have he : (⟨195, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 195 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0195
              ·
                by_cases h197 : i.val < 197
                ·
                  have he : (⟨196, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 196 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0196
                ·
                  have he : (⟨197, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 197 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0197
            ·
              by_cases h200 : i.val < 200
              ·
                by_cases h199 : i.val < 199
                ·
                  have he : (⟨198, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 198 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0198
                ·
                  have he : (⟨199, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 199 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0199
              ·
                by_cases h201 : i.val < 201
                ·
                  have he : (⟨200, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 200 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0200
                ·
                  have he : (⟨201, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 201 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0201
          ·
            by_cases h205 : i.val < 205
            ·
              by_cases h203 : i.val < 203
              ·
                have he : (⟨202, by decide⟩ : Fin 209) = i := by
                  apply Fin.ext
                  change 202 = i.val
                  omega
                simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0202
              ·
                by_cases h204 : i.val < 204
                ·
                  have he : (⟨203, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 203 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0203
                ·
                  have he : (⟨204, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 204 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0204
            ·
              by_cases h207 : i.val < 207
              ·
                by_cases h206 : i.val < 206
                ·
                  have he : (⟨205, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 205 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0205
                ·
                  have he : (⟨206, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 206 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0206
              ·
                by_cases h208 : i.val < 208
                ·
                  have he : (⟨207, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 207 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0207
                ·
                  have he : (⟨208, by decide⟩ : Fin 209) = i := by
                    apply Fin.ext
                    change 208 = i.val
                    omega
                  simpa only [he] using bundle_2098644a87_lowerFacets_iff_row0208

theorem bundle_2098644a87_codeFace_complete_row0000 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨0, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨0, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0001 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨1, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨1, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0002 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨2, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨2, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0003 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨3, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨3, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0004 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨4, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨4, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0005 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨5, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨5, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0006 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨6, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨6, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0007 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨7, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨7, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0008 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨8, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨8, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0009 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨9, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨9, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0010 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨10, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨10, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0011 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨11, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨11, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0012 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨12, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨12, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0013 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨13, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨13, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0014 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨14, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨14, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0015 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨15, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨15, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0016 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨16, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨16, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0017 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨17, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨17, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0018 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨18, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨18, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0019 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨19, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨19, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0020 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨20, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨20, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0021 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨21, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨21, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0022 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨22, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨22, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem bundle_2098644a87_codeFace_complete_row0023 : ∀ i : Fin 209, faceMask i ⊆ facetLabels (⟨23, by decide⟩ : Fin 24) → ∃ c : Fin 27, codeFace (⟨23, by decide⟩ : Fin 24) c = i := by decide +kernel

theorem codeFace_complete : ∀ (f : Fin 24) (i : Fin 209),
    faceMask i ⊆ facetLabels f → ∃ c : Fin 27, codeFace f c = i := by
  intro i
  have hi_bound := i.isLt
  by_cases h12 : i.val < 12
  ·
    by_cases h6 : i.val < 6
    ·
      by_cases h3 : i.val < 3
      ·
        by_cases h1 : i.val < 1
        ·
          have he : (⟨0, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 0 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0000
        ·
          by_cases h2 : i.val < 2
          ·
            have he : (⟨1, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0001
          ·
            have he : (⟨2, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0002
      ·
        by_cases h4 : i.val < 4
        ·
          have he : (⟨3, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 3 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0003
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0004
          ·
            have he : (⟨5, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0005
    ·
      by_cases h9 : i.val < 9
      ·
        by_cases h7 : i.val < 7
        ·
          have he : (⟨6, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 6 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0006
        ·
          by_cases h8 : i.val < 8
          ·
            have he : (⟨7, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0007
          ·
            have he : (⟨8, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0008
      ·
        by_cases h10 : i.val < 10
        ·
          have he : (⟨9, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 9 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0010
          ·
            have he : (⟨11, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0011
  ·
    by_cases h18 : i.val < 18
    ·
      by_cases h15 : i.val < 15
      ·
        by_cases h13 : i.val < 13
        ·
          have he : (⟨12, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 12 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0012
        ·
          by_cases h14 : i.val < 14
          ·
            have he : (⟨13, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0013
          ·
            have he : (⟨14, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0014
      ·
        by_cases h16 : i.val < 16
        ·
          have he : (⟨15, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 15 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0015
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0016
          ·
            have he : (⟨17, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0017
    ·
      by_cases h21 : i.val < 21
      ·
        by_cases h19 : i.val < 19
        ·
          have he : (⟨18, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 18 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0018
        ·
          by_cases h20 : i.val < 20
          ·
            have he : (⟨19, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0019
          ·
            have he : (⟨20, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0020
      ·
        by_cases h22 : i.val < 22
        ·
          have he : (⟨21, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 21 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_complete_row0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0022
          ·
            have he : (⟨23, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_complete_row0023

def bundle_2098644a87_faceSortKey (s : Finset (Fin 32)) : ℕ :=
  s.card * 2 ^ 33 + 2 ^ 32 - s.sum (fun v => 2 ^ (31 - v.val))

theorem bundle_2098644a87_faceSortKey_adjacent : ∀ i : Fin 208,
    bundle_2098644a87_faceSortKey (faceMask i.castSucc) < bundle_2098644a87_faceSortKey (faceMask i.succ) := by decide +kernel

theorem faceMask_injective : Function.Injective faceMask := by
  have hmono : StrictMono (fun i : Fin 209 => bundle_2098644a87_faceSortKey (faceMask i)) :=
    Fin.strictMono_iff_lt_succ.mpr bundle_2098644a87_faceSortKey_adjacent
  intro i j h
  exact hmono.injective (congrArg bundle_2098644a87_faceSortKey h)

theorem faceMask_nonempty : ∀ i : Fin 209, (faceMask i).Nonempty := by decide +kernel

theorem faceMask_top : faceMask 208 = Finset.univ := by decide +kernel

theorem faceMask_vertex : ∀ v : Fin 32,
    faceMask (v.castLE (by decide)) = {v} := by decide +kernel

theorem faceFlag_self : ∀ i : Fin 209, faceFlag i (faceRank i) = i := by decide +kernel

/- BEGIN bounded block faceFlag_strict certificate -/


/- A command checks at most eight flags, hence 32 strict inclusions.
The index map and its coverage proof preserve the full finite domain. -/
def bundle_2098644a87_flagStrictIndex {lo width : ℕ} (h : lo + width ≤ 209)
    (j : Fin width) : Fin 209 :=
  ⟨lo + j.val, by have hj := j.isLt; omega⟩

theorem bundle_2098644a87_flagStrictCover {lo width : ℕ} (h : lo + width ≤ 209)
    {P : Fin 209 → Prop} (hp : ∀ j : Fin width, P (bundle_2098644a87_flagStrictIndex h j))
    (i : Fin 209) (hlo : lo ≤ i.val) (hhi : i.val < lo + width) : P i := by
  let j : Fin width := ⟨i.val - lo, by omega⟩
  have he : bundle_2098644a87_flagStrictIndex h j = i := by
    apply Fin.ext
    dsimp [bundle_2098644a87_flagStrictIndex, j]
    omega
  simpa only [he] using hp j


theorem bundle_2098644a87_faceFlag_strict_batch0000 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 0) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 0) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0001 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 8) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 8) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0002 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 16) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 16) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0003 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 24) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 24) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0004 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 32) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 32) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0005 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 40) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 40) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0006 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 48) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 48) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0007 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 56) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 56) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0008 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 64) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 64) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0009 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 72) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 72) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0010 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 80) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 80) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0011 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 88) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 88) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0012 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 96) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 96) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0013 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 104) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 104) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0014 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 112) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 112) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0015 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 120) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 120) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0016 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 128) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 128) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0017 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 136) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 136) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0018 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 144) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 144) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0019 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 152) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 152) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0020 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 160) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 160) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0021 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 168) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 168) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0022 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 176) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 176) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0023 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 184) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 184) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0024 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 192) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 192) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0025 : ∀ j : Fin 8, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 200) (width := 8) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 200) (width := 8) (by decide) j) k.succ) := by
  decide +kernel


theorem bundle_2098644a87_faceFlag_strict_batch0026 : ∀ j : Fin 1, ∀ k : Fin 4,
    faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 208) (width := 1) (by decide) j) k.castSucc) ⊂
      faceMask (faceFlag (bundle_2098644a87_flagStrictIndex (lo := 208) (width := 1) (by decide) j) k.succ) := by
  decide +kernel


theorem faceFlag_strict : ∀ (i : Fin 209) (k : Fin 4),
    faceMask (faceFlag i k.castSucc) ⊂ faceMask (faceFlag i k.succ) := by
  intro i
  have hi_bound := i.isLt
  by_cases h104 : i.val < 104
  ·
    by_cases h48 : i.val < 48
    ·
      by_cases h24 : i.val < 24
      ·
        by_cases h8 : i.val < 8
        ·
          exact bundle_2098644a87_flagStrictCover (lo := 0) (width := 8)
            (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
              faceMask (faceFlag checkedIndex k.castSucc) ⊂
                faceMask (faceFlag checkedIndex k.succ))
            (by decide) bundle_2098644a87_faceFlag_strict_batch0000 i (by omega) (by omega)
        ·
          by_cases h16 : i.val < 16
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 8) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0001 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 16) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0002 i (by omega) (by omega)
      ·
        by_cases h32 : i.val < 32
        ·
          exact bundle_2098644a87_flagStrictCover (lo := 24) (width := 8)
            (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
              faceMask (faceFlag checkedIndex k.castSucc) ⊂
                faceMask (faceFlag checkedIndex k.succ))
            (by decide) bundle_2098644a87_faceFlag_strict_batch0003 i (by omega) (by omega)
        ·
          by_cases h40 : i.val < 40
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 32) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0004 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 40) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0005 i (by omega) (by omega)
    ·
      by_cases h72 : i.val < 72
      ·
        by_cases h56 : i.val < 56
        ·
          exact bundle_2098644a87_flagStrictCover (lo := 48) (width := 8)
            (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
              faceMask (faceFlag checkedIndex k.castSucc) ⊂
                faceMask (faceFlag checkedIndex k.succ))
            (by decide) bundle_2098644a87_faceFlag_strict_batch0006 i (by omega) (by omega)
        ·
          by_cases h64 : i.val < 64
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 56) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0007 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 64) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0008 i (by omega) (by omega)
      ·
        by_cases h88 : i.val < 88
        ·
          by_cases h80 : i.val < 80
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 72) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0009 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 80) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0010 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 88) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0011 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 96) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0012 i (by omega) (by omega)
  ·
    by_cases h160 : i.val < 160
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h112 : i.val < 112
        ·
          exact bundle_2098644a87_flagStrictCover (lo := 104) (width := 8)
            (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
              faceMask (faceFlag checkedIndex k.castSucc) ⊂
                faceMask (faceFlag checkedIndex k.succ))
            (by decide) bundle_2098644a87_faceFlag_strict_batch0013 i (by omega) (by omega)
        ·
          by_cases h120 : i.val < 120
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 112) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0014 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 120) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0015 i (by omega) (by omega)
      ·
        by_cases h144 : i.val < 144
        ·
          by_cases h136 : i.val < 136
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 128) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0016 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 136) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0017 i (by omega) (by omega)
        ·
          by_cases h152 : i.val < 152
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 144) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0018 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 152) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0019 i (by omega) (by omega)
    ·
      by_cases h184 : i.val < 184
      ·
        by_cases h168 : i.val < 168
        ·
          exact bundle_2098644a87_flagStrictCover (lo := 160) (width := 8)
            (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
              faceMask (faceFlag checkedIndex k.castSucc) ⊂
                faceMask (faceFlag checkedIndex k.succ))
            (by decide) bundle_2098644a87_faceFlag_strict_batch0020 i (by omega) (by omega)
        ·
          by_cases h176 : i.val < 176
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 168) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0021 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 176) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0022 i (by omega) (by omega)
      ·
        by_cases h200 : i.val < 200
        ·
          by_cases h192 : i.val < 192
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 184) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0023 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 192) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0024 i (by omega) (by omega)
        ·
          by_cases h208 : i.val < 208
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 200) (width := 8)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0025 i (by omega) (by omega)
          ·
            exact bundle_2098644a87_flagStrictCover (lo := 208) (width := 1)
              (P := fun checkedIndex : Fin 209 => ∀ k : Fin 4,
                faceMask (faceFlag checkedIndex k.castSucc) ⊂
                  faceMask (faceFlag checkedIndex k.succ))
              (by decide) bundle_2098644a87_faceFlag_strict_batch0026 i (by omega) (by omega)

/- END bounded block faceFlag_strict certificate -/

theorem faceFlag_rank : ∀ (i : Fin 209) (k : Fin 5),
    faceRank (faceFlag i k) = k := by decide +kernel

theorem lowerFacets_nonempty : ∀ i : Fin 209,
    1 ≤ (faceRank i).val → (lowerFacets i).Nonempty := by decide +kernel

theorem faceRank_zero : ∀ i : Fin 209, faceRank i = 0 →
    ∃ v : Fin 32, v.castLE (by decide) = i := by decide +kernel

theorem faceRank_three : ∀ i : Fin 209, faceRank i = 3 →
    ∃ f : Fin 24, codeFace f 0 = i := by decide +kernel

theorem codeFace_rank_zero : ∀ f : Fin 24, faceRank (codeFace f 0) = 3 := by decide +kernel

theorem faceRank_four : ∀ i : Fin 209, faceRank i = 4 ↔ i = 208 := by decide +kernel

theorem faceRank_cardinality : ∀ k : Fin 5,
    (Finset.univ.filter (fun i : Fin 209 => faceRank i = k)).card =
      (![32, 80, 72, 24, 1] : Fin 5 → ℕ) k := by decide +kernel

/-- The edge list used by the direction equations is the rank-one part
of the face catalogue, in the same lexicographic order. -/
theorem edgeMask : ∀ e : Fin 80,
    faceMask ⟨32 + e.val, by omega⟩ = {edgeVertex e 0, edgeVertex e 1} := by decide +kernel

/-- The ordinary coordinate-face code represented by three base-three digits. -/
def codeOfFin27 (c : Fin 27) : Cubical.Cube.FaceCode 3 := fun k =>
  match c.val / 3 ^ k.val % 3 with
  | 0 => .free
  | 1 => .fixed false
  | _ => .fixed true

/-- Binary labels of the eight vertices of a cube. -/
def bitsOfFin8 (b : Fin 8) : Cubical.Cube.Vertex 3 := fun k =>
  b.val / 2 ^ k.val % 2 == 1

local instance (a b : Cubical.Cube.FaceCoordinate) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (b = .free ∨ a = b))

local instance (c : Cubical.Cube.FaceCode 3) (b : Cubical.Cube.Vertex 3) :
    Decidable (Cubical.Cube.Matches c b) :=
  inferInstanceAs (Decidable (∀ k, c k = .free ∨ c k = .fixed (b k)))

def cubeCodeVertices (c : Fin 27) : Finset (Fin 8) :=
  Finset.univ.filter (fun b => Cubical.Cube.Matches (codeOfFin27 c) (bitsOfFin8 b))

theorem bundle_2098644a87_codeFace_mask_row0000 : ∀ c : Fin 27, faceMask (codeFace (⟨0, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨0, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0001 : ∀ c : Fin 27, faceMask (codeFace (⟨1, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨1, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0002 : ∀ c : Fin 27, faceMask (codeFace (⟨2, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨2, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0003 : ∀ c : Fin 27, faceMask (codeFace (⟨3, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨3, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0004 : ∀ c : Fin 27, faceMask (codeFace (⟨4, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨4, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0005 : ∀ c : Fin 27, faceMask (codeFace (⟨5, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨5, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0006 : ∀ c : Fin 27, faceMask (codeFace (⟨6, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨6, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0007 : ∀ c : Fin 27, faceMask (codeFace (⟨7, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨7, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0008 : ∀ c : Fin 27, faceMask (codeFace (⟨8, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨8, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0009 : ∀ c : Fin 27, faceMask (codeFace (⟨9, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨9, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0010 : ∀ c : Fin 27, faceMask (codeFace (⟨10, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨10, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0011 : ∀ c : Fin 27, faceMask (codeFace (⟨11, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨11, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0012 : ∀ c : Fin 27, faceMask (codeFace (⟨12, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨12, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0013 : ∀ c : Fin 27, faceMask (codeFace (⟨13, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨13, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0014 : ∀ c : Fin 27, faceMask (codeFace (⟨14, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨14, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0015 : ∀ c : Fin 27, faceMask (codeFace (⟨15, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨15, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0016 : ∀ c : Fin 27, faceMask (codeFace (⟨16, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨16, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0017 : ∀ c : Fin 27, faceMask (codeFace (⟨17, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨17, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0018 : ∀ c : Fin 27, faceMask (codeFace (⟨18, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨18, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0019 : ∀ c : Fin 27, faceMask (codeFace (⟨19, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨19, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0020 : ∀ c : Fin 27, faceMask (codeFace (⟨20, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨20, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0021 : ∀ c : Fin 27, faceMask (codeFace (⟨21, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨21, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0022 : ∀ c : Fin 27, faceMask (codeFace (⟨22, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨22, by decide⟩ : Fin 24)) := by decide +kernel

theorem bundle_2098644a87_codeFace_mask_row0023 : ∀ c : Fin 27, faceMask (codeFace (⟨23, by decide⟩ : Fin 24) c) = (cubeCodeVertices c).image (cubeVertex (⟨23, by decide⟩ : Fin 24)) := by decide +kernel

theorem codeFace_mask : ∀ (f : Fin 24) (c : Fin 27),
    faceMask (codeFace f c) = (cubeCodeVertices c).image (cubeVertex f) := by
  intro i
  have hi_bound := i.isLt
  by_cases h12 : i.val < 12
  ·
    by_cases h6 : i.val < 6
    ·
      by_cases h3 : i.val < 3
      ·
        by_cases h1 : i.val < 1
        ·
          have he : (⟨0, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 0 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0000
        ·
          by_cases h2 : i.val < 2
          ·
            have he : (⟨1, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0001
          ·
            have he : (⟨2, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0002
      ·
        by_cases h4 : i.val < 4
        ·
          have he : (⟨3, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 3 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0003
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0004
          ·
            have he : (⟨5, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0005
    ·
      by_cases h9 : i.val < 9
      ·
        by_cases h7 : i.val < 7
        ·
          have he : (⟨6, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 6 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0006
        ·
          by_cases h8 : i.val < 8
          ·
            have he : (⟨7, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0007
          ·
            have he : (⟨8, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0008
      ·
        by_cases h10 : i.val < 10
        ·
          have he : (⟨9, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 9 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0010
          ·
            have he : (⟨11, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0011
  ·
    by_cases h18 : i.val < 18
    ·
      by_cases h15 : i.val < 15
      ·
        by_cases h13 : i.val < 13
        ·
          have he : (⟨12, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 12 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0012
        ·
          by_cases h14 : i.val < 14
          ·
            have he : (⟨13, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0013
          ·
            have he : (⟨14, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0014
      ·
        by_cases h16 : i.val < 16
        ·
          have he : (⟨15, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 15 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0015
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0016
          ·
            have he : (⟨17, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0017
    ·
      by_cases h21 : i.val < 21
      ·
        by_cases h19 : i.val < 19
        ·
          have he : (⟨18, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 18 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0018
        ·
          by_cases h20 : i.val < 20
          ·
            have he : (⟨19, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0019
          ·
            have he : (⟨20, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0020
      ·
        by_cases h22 : i.val < 22
        ·
          have he : (⟨21, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 21 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_mask_row0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0022
          ·
            have he : (⟨23, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_mask_row0023

theorem codeFace_top : ∀ f : Fin 24,
    faceMask (codeFace f 0) = facetLabels f := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0000 : ∀ c : Fin 27, faceMask (codeFace (⟨0, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨0, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0001 : ∀ c : Fin 27, faceMask (codeFace (⟨1, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨1, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0002 : ∀ c : Fin 27, faceMask (codeFace (⟨2, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨2, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0003 : ∀ c : Fin 27, faceMask (codeFace (⟨3, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨3, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0004 : ∀ c : Fin 27, faceMask (codeFace (⟨4, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨4, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0005 : ∀ c : Fin 27, faceMask (codeFace (⟨5, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨5, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0006 : ∀ c : Fin 27, faceMask (codeFace (⟨6, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨6, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0007 : ∀ c : Fin 27, faceMask (codeFace (⟨7, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨7, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0008 : ∀ c : Fin 27, faceMask (codeFace (⟨8, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨8, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0009 : ∀ c : Fin 27, faceMask (codeFace (⟨9, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨9, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0010 : ∀ c : Fin 27, faceMask (codeFace (⟨10, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨10, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0011 : ∀ c : Fin 27, faceMask (codeFace (⟨11, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨11, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0012 : ∀ c : Fin 27, faceMask (codeFace (⟨12, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨12, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0013 : ∀ c : Fin 27, faceMask (codeFace (⟨13, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨13, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0014 : ∀ c : Fin 27, faceMask (codeFace (⟨14, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨14, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0015 : ∀ c : Fin 27, faceMask (codeFace (⟨15, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨15, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0016 : ∀ c : Fin 27, faceMask (codeFace (⟨16, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨16, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0017 : ∀ c : Fin 27, faceMask (codeFace (⟨17, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨17, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0018 : ∀ c : Fin 27, faceMask (codeFace (⟨18, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨18, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0019 : ∀ c : Fin 27, faceMask (codeFace (⟨19, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨19, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0020 : ∀ c : Fin 27, faceMask (codeFace (⟨20, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨20, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0021 : ∀ c : Fin 27, faceMask (codeFace (⟨21, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨21, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0022 : ∀ c : Fin 27, faceMask (codeFace (⟨22, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨22, by decide⟩ : Fin 24) := by decide +kernel

theorem bundle_2098644a87_codeFace_subset_facet_row0023 : ∀ c : Fin 27, faceMask (codeFace (⟨23, by decide⟩ : Fin 24) c) ⊆ facetLabels (⟨23, by decide⟩ : Fin 24) := by decide +kernel

theorem codeFace_subset_facet : ∀ (f : Fin 24) (c : Fin 27),
    faceMask (codeFace f c) ⊆ facetLabels f := by
  intro i
  have hi_bound := i.isLt
  by_cases h12 : i.val < 12
  ·
    by_cases h6 : i.val < 6
    ·
      by_cases h3 : i.val < 3
      ·
        by_cases h1 : i.val < 1
        ·
          have he : (⟨0, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 0 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0000
        ·
          by_cases h2 : i.val < 2
          ·
            have he : (⟨1, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0001
          ·
            have he : (⟨2, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0002
      ·
        by_cases h4 : i.val < 4
        ·
          have he : (⟨3, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 3 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0003
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0004
          ·
            have he : (⟨5, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0005
    ·
      by_cases h9 : i.val < 9
      ·
        by_cases h7 : i.val < 7
        ·
          have he : (⟨6, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 6 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0006
        ·
          by_cases h8 : i.val < 8
          ·
            have he : (⟨7, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0007
          ·
            have he : (⟨8, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0008
      ·
        by_cases h10 : i.val < 10
        ·
          have he : (⟨9, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 9 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0010
          ·
            have he : (⟨11, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0011
  ·
    by_cases h18 : i.val < 18
    ·
      by_cases h15 : i.val < 15
      ·
        by_cases h13 : i.val < 13
        ·
          have he : (⟨12, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 12 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0012
        ·
          by_cases h14 : i.val < 14
          ·
            have he : (⟨13, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0013
          ·
            have he : (⟨14, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0014
      ·
        by_cases h16 : i.val < 16
        ·
          have he : (⟨15, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 15 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0015
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0016
          ·
            have he : (⟨17, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0017
    ·
      by_cases h21 : i.val < 21
      ·
        by_cases h19 : i.val < 19
        ·
          have he : (⟨18, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 18 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0018
        ·
          by_cases h20 : i.val < 20
          ·
            have he : (⟨19, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0019
          ·
            have he : (⟨20, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0020
      ·
        by_cases h22 : i.val < 22
        ·
          have he : (⟨21, by decide⟩ : Fin 24) = i := by
            apply Fin.ext
            change 21 = i.val
            omega
          simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0022
          ·
            have he : (⟨23, by decide⟩ : Fin 24) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_2098644a87_codeFace_subset_facet_row0023

-- BEGIN generated generic cube order
-- Regenerate this proof with `python3 scripts/generic_block_cube_order.py`.
-- The finite vertex-label correspondence has already been checked above.
-- Cube order now follows once from the coordinate-face order theorem.

theorem codeOfFin27_bijective : Function.Bijective codeOfFin27 := by decide +kernel

theorem bitsOfFin8_bijective : Function.Bijective bitsOfFin8 := by decide +kernel

theorem bundle_2098644a87_cubeCodeVertices_le_iff (c d : Fin 27) :
    cubeCodeVertices c ⊆ cubeCodeVertices d ↔ codeOfFin27 c ≤ codeOfFin27 d := by
  rw [Cubical.Cube.faceCode_le_iff]
  constructor
  · intro h s hs
    obtain ⟨b, rfl⟩ := bitsOfFin8_bijective.2 s
    have hb : b ∈ cubeCodeVertices c := by simpa [cubeCodeVertices] using hs
    have hd := h hb
    simpa [cubeCodeVertices] using hd
  · intro h b hb
    have hs : Cubical.Cube.Matches (codeOfFin27 c) (bitsOfFin8 b) := by
      simpa [cubeCodeVertices] using hb
    have hd := h (bitsOfFin8 b) hs
    simpa [cubeCodeVertices] using hd

theorem codeFace_le_iff : ∀ (f : Fin 24) (c d : Fin 27),
    faceMask (codeFace f c) ⊆ faceMask (codeFace f d) ↔
      codeOfFin27 c ≤ codeOfFin27 d := by
  intro f c d
  rw [codeFace_mask, codeFace_mask,
    Finset.image_subset_image_iff (cubeVertex_injective f)]
  exact bundle_2098644a87_cubeCodeVertices_le_iff c d

theorem codeFace_injective : ∀ f : Fin 24, Function.Injective (codeFace f) := by
  intro f c d h
  apply codeOfFin27_bijective.1
  apply le_antisymm
  · apply (codeFace_le_iff f c d).mp
    intro v hv
    simpa only [h] using hv
  · apply (codeFace_le_iff f d c).mp
    intro v hv
    simpa only [h] using hv

-- END generated generic cube order

end CubicalIndecomposability.Block
end VerificationSource013

/- Original source: CubicalIndecomposability/Block/FaceRealization.lean -/
section VerificationSource014




/-!
# The complete geometric face lattice of the normalized auxiliary block

Each finite mask is realized by intersecting supporting hyperplanes.  Exact
vertex membership identifies its convex hull.  Five-element incidence flags
prove all dimensions.  Finally the rank-two pairing certificate proves
that every ordinary exposed face is in the catalogue.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

theorem bundle_6423e304d4_support_bound_on_vertices (f : Fin 24) (x : E 4)
    (hx : x ∈ polytope.vertices) : offset f ≤ form f x := by
  rw [polytope_vertices] at hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact support_nonneg f v

/-- The exposed face associated with a mask in the finite catalogue. -/
def indexedFace (i : Fin 209) : Set (E 4) :=
  supportIntersection polytope form offset (supportRows i)

theorem indexedFace_isFace (i : Fin 209) : polytope.IsFace (indexedFace i) := by
  apply supportIntersection_isFace polytope form offset (supportRows i)
    bundle_6423e304d4_support_bound_on_vertices
  obtain ⟨v, hv⟩ := faceMask_nonempty i
  refine ⟨p v, vertex_mem v, ?_⟩
  intro f hf
  apply (support_eq_iff f v).mpr
  exact (supportRows_identity i v).mp hv f hf

@[simp] theorem vertex_mem_indexedFace (i : Fin 209) (v : Fin 32) :
    p v ∈ indexedFace i ↔ v ∈ faceMask i := by
  rw [indexedFace, vertex_mem_supportIntersection polytope form offset
    (supportRows i) bundle_6423e304d4_support_bound_on_vertices (p v) (vertex_mem v)]
  constructor
  · intro h
    apply (supportRows_identity i v).mpr
    intro f hf
    exact (support_eq_iff f v).mp (h f hf)
  · intro h f hf
    exact (support_eq_iff f v).mpr ((supportRows_identity i v).mp h f hf)

theorem indexedFace_eq_hull (i : Fin 209) :
    indexedFace i = convexHull ℝ (p '' (faceMask i : Set (Fin 32))) :=
  face_eq_label_hull polytope p polytope_vertices (indexedFace_isFace i)
    (faceMask i) (vertex_mem_indexedFace i)

theorem indexedFace_subset_iff (i j : Fin 209) :
    indexedFace i ⊆ indexedFace j ↔ faceMask i ⊆ faceMask j :=
  face_subset_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)

theorem indexedFace_ssubset_iff (i j : Fin 209) :
    indexedFace i ⊂ indexedFace j ↔ faceMask i ⊂ faceMask j :=
  face_ssubset_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)

theorem indexedFace_injective : Function.Injective indexedFace := by
  intro i j hij
  apply faceMask_injective
  exact (face_eq_iff_labels polytope p polytope_vertices
    (indexedFace_isFace i) (indexedFace_isFace j)
    (faceMask i) (faceMask j) (vertex_mem_indexedFace i) (vertex_mem_indexedFace j)).mp hij

theorem indexedFace_top : indexedFace 208 = polytope.toSet := by
  rw [indexedFace_eq_hull, faceMask_top]
  change convexHull ℝ (p '' (Finset.univ : Finset (Fin 32))) =
    convexHull ℝ (polytope.vertices : Set (E 4))
  rw [polytope_vertices, Finset.coe_image]

theorem indexedFace_vertex (v : Fin 32) :
    indexedFace (v.castLE (by decide)) = {p v} := by
  rw [indexedFace_eq_hull, faceMask_vertex, Finset.coe_singleton,
    Set.image_singleton, convexHull_singleton]

/-- All 209 dimensions follow from strict geometric face flags. -/
theorem indexedFace_dimension (i : Fin 209) :
    faceDim (indexedFace i) = (faceRank i : ℕ) := by
  have h := dimension_of_five_face_flag polytope
    (fun k => indexedFace (faceFlag i k))
    (fun k => indexedFace_isFace (faceFlag i k))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 0))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 1))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 2))
    ((indexedFace_ssubset_iff _ _).mpr (faceFlag_strict i 3))
  simpa only [faceFlag_self] using h (faceRank i)

theorem polytope_dimension : polytope.dim = 4 := by
  have h := indexedFace_dimension 208
  rw [indexedFace_top] at h
  exact h

/-- The finite catalogue, now interpreted as actual geometric faces. -/
def geometricFaceCatalogue : IndexedFaceCatalogue polytope (Fin 209) where
  face i := ⟨indexedFace i, indexedFace_isFace i⟩
  rank i := faceRank i
  dimension := indexedFace_dimension
  injective := by
    intro i j hij
    exact indexedFace_injective (congrArg Subtype.val hij)
  top := ⟨208, indexedFace_top⟩
  vertices := by
    intro x hx
    rw [polytope_vertices] at hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v.castLE (by decide), indexedFace_vertex v⟩
  facet := by
    intro a ha
    obtain ⟨b, hb⟩ := lowerFacets_nonempty a (by omega)
    obtain ⟨hrank, hsub⟩ := (lowerFacets_iff a b).mp hb
    exact ⟨b, (indexedFace_subset_iff b a).mpr hsub, hrank⟩
  ridgePartner := by
    intro a b r hba hrb hdb hdr
    have hb : b ∈ lowerFacets a := (lowerFacets_iff a b).mpr
      ⟨hdb, (indexedFace_subset_iff b a).mp hba⟩
    have hr : r ∈ lowerFacets b := (lowerFacets_iff b r).mpr
      ⟨by omega, (indexedFace_subset_iff r b).mp hrb⟩
    obtain ⟨c, hc, hcb, hrc⟩ := lowerFacets_pairing a b hb r hr
    obtain ⟨hdc, hca⟩ := (lowerFacets_iff a c).mp hc
    obtain ⟨_hdr', hrc'⟩ := (lowerFacets_iff c r).mp hrc
    exact ⟨c, (indexedFace_subset_iff c a).mpr hca,
      (indexedFace_subset_iff r c).mpr hrc', hdc, hcb⟩

/-- Every nonempty exposed face occurs, with no missing geometric faces. -/
theorem indexedFace_complete {F : Set (E 4)} (hF : polytope.IsFace F) :
    ∃ i, indexedFace i = F := by
  obtain ⟨i, hi⟩ := geometricFaceCatalogue.surjective ⟨F, hF⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem faceNumber_eq_rank_card (k : ℕ) :
    faceNumber polytope k =
      Fintype.card {i : Fin 209 // (faceRank i : ℕ) = k} :=
  geometricFaceCatalogue.faceNumber_eq k

/-- Count every rank, including the whole polytope in rank four. -/
theorem faceNumber_eq_catalogue_count (k : Fin 5) :
    faceNumber polytope k.val = (![32, 80, 72, 24, 1] : Fin 5 → ℕ) k := by
  rw [faceNumber_eq_rank_card, Fintype.card_subtype]
  simpa only [Fin.ext_iff] using faceRank_cardinality k

/-- The auxiliary block's complete face vector, counting ordinary geometric faces. -/
theorem face_vector :
    faceNumber polytope 0 = 32 ∧ faceNumber polytope 1 = 80 ∧
    faceNumber polytope 2 = 72 ∧ faceNumber polytope 3 = 24 := by
  exact ⟨faceNumber_eq_catalogue_count 0, faceNumber_eq_catalogue_count 1,
    faceNumber_eq_catalogue_count 2, faceNumber_eq_catalogue_count 3⟩

end CubicalIndecomposability.Block
end
end VerificationSource014

/- Original source: CubicalIndecomposability/Block/CubeRealization.lean -/
section VerificationSource015


/-!
# The facets are combinatorial three-cubes

For every facet we construct an order isomorphism between its ordinary
geometric face poset and the face poset of the standard geometric cube.
The intermediate coordinate-face codes have three coordinates, each free
or fixed at either of its two endpoint values.  The empty face may be adjoined on both
sides without changing this notion of combinatorial equivalence.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Cubical.Cube

/-- The 27 finite codes are exactly the ordinary coordinate faces. -/
def cubeCodeEquiv : Fin 27 ≃ FaceCode 3 :=
  Equiv.ofBijective codeOfFin27 codeOfFin27_bijective

@[simp] theorem cubeCodeEquiv_apply (c : Fin 27) :
    cubeCodeEquiv c = codeOfFin27 c := rfl

theorem indexedFace_code_top (f : Fin 24) :
    indexedFace (codeFace f 0) = facet f := by
  rw [indexedFace_eq_hull, codeFace_top, facet_eq_hull]

theorem indexedFace_code_subset (f : Fin 24) (c : Fin 27) :
    indexedFace (codeFace f c) ⊆ facet f := by
  rw [← indexedFace_code_top f, indexedFace_subset_iff, codeFace_top]
  exact codeFace_subset_facet f c

/-- The actual geometric face named by a coordinate code inside a facet. -/
def cubeFaceMap (f : Fin 24) (c : FaceCode 3) :
    FaceType (facePolytope polytope (facet_isFace f)) :=
  ⟨indexedFace (codeFace f (cubeCodeEquiv.symm c)),
    facePolytope_isFace_of polytope (facet_isFace f)
      (indexedFace_isFace _) (indexedFace_code_subset f _)⟩

theorem cubeFaceMap_le_iff (f : Fin 24) (c d : FaceCode 3) :
    cubeFaceMap f c ≤ cubeFaceMap f d ↔ c ≤ d := by
  change indexedFace (codeFace f (cubeCodeEquiv.symm c)) ⊆
      indexedFace (codeFace f (cubeCodeEquiv.symm d)) ↔ c ≤ d
  rw [indexedFace_subset_iff, codeFace_le_iff]
  have hc : codeOfFin27 (cubeCodeEquiv.symm c) = c :=
    cubeCodeEquiv.apply_symm_apply c
  have hd : codeOfFin27 (cubeCodeEquiv.symm d) = d :=
    cubeCodeEquiv.apply_symm_apply d
  rw [hc, hd]

theorem cubeFaceMap_injective (f : Fin 24) : Function.Injective (cubeFaceMap f) := by
  intro c d h
  apply le_antisymm
  · exact (cubeFaceMap_le_iff f c d).mp h.le
  · exact (cubeFaceMap_le_iff f d c).mp h.ge

theorem cubeFaceMap_surjective (f : Fin 24) : Function.Surjective (cubeFaceMap f) := by
  intro F
  have hFP : polytope.IsFace F.val :=
    isFace_of_facePolytope polytope (facet_isFace f) F.property
  obtain ⟨i, hi⟩ := indexedFace_complete hFP
  have hif : indexedFace i ⊆ facet f := by
    rw [hi]
    simpa only [facePolytope_toSet] using
      face_subset_toSet (facePolytope polytope (facet_isFace f)) F.property
  have himask : faceMask i ⊆ facetLabels f := by
    rw [← indexedFace_code_top f] at hif
    have h := (indexedFace_subset_iff i (codeFace f 0)).mp hif
    simpa only [codeFace_top] using h
  obtain ⟨c, hci⟩ := codeFace_complete f i himask
  refine ⟨cubeCodeEquiv c, Subtype.ext ?_⟩
  change indexedFace (codeFace f (cubeCodeEquiv.symm (cubeCodeEquiv c))) = F.val
  rw [cubeCodeEquiv.symm_apply_apply, hci, hi]

/-- Exact order correspondence between coordinate codes and actual faces. -/
def cubeFaceOrderIso (f : Fin 24) :
    FaceCode 3 ≃o FaceType (facePolytope polytope (facet_isFace f)) where
  toEquiv := Equiv.ofBijective (cubeFaceMap f)
    ⟨cubeFaceMap_injective f, cubeFaceMap_surjective f⟩
  map_rel_iff' := fun {c d} => cubeFaceMap_le_iff f c d

/-- Every displayed facet has the face lattice of the standard three-cube. -/
def facetCubeOrderIso (f : Fin 24) :
    FaceType (facePolytope polytope (facet_isFace f)) ≃o
      FaceType (standardCube 3) :=
  (cubeFaceOrderIso f).symm.trans (cubeFacesOrderIso 3 (by decide)).symm

/-- The same equivalence including the empty face on both sides. -/
def facetCubeCompleteOrderIso (f : Fin 24) :
    Papers.Polytopes.CompleteFaceType (facePolytope polytope (facet_isFace f)) ≃o
      Papers.Polytopes.CompleteFaceType (standardCube 3) :=
  Papers.Polytopes.extendFaceOrderIso (facetCubeOrderIso f)

theorem facet_dimension (f : Fin 24) : faceDim (facet f) = 3 := by
  rw [← indexedFace_code_top f, indexedFace_dimension]
  exact congrArg Fin.val (codeFace_rank_zero f)

/-- Every geometric facet is one of the displayed 24 facets. -/
theorem facets_complete {F : Set (E 4)} (hF : polytope.IsFace F)
    (hdF : faceDim F + 1 = polytope.dim) : ∃ f, F = facet f := by
  obtain ⟨i, hi⟩ := indexedFace_complete hF
  have hrank : faceRank i = 3 := by
    apply Fin.ext
    have h := indexedFace_dimension i
    rw [hi] at h
    rw [polytope_dimension] at hdF
    omega
  obtain ⟨f, hfi⟩ := faceRank_three i hrank
  exact ⟨f, hi.symm.trans (hfi ▸ indexedFace_code_top f)⟩

/-- The ordinary geometric meaning of the paper's word “cubical”. -/
theorem polytope_isCubical : IsCubical polytope := by
  intro F hF hdF
  obtain ⟨f, rfl⟩ := facets_complete hF hdF
  rw [polytope_dimension]
  exact ⟨facetCubeOrderIso f⟩

end CubicalIndecomposability.Block
end
end VerificationSource015

/- Original source: CubicalIndecomposability/Block/Interfaces.lean -/
section VerificationSource016


/-!
# The three distinguished facets of the auxiliary block

The normalized block has facets F, H and G from Proposition 5. Their
intersection and separation are proved for actual geometric faces, using
exact vertex membership and the exposed-face hull theorem. The common
face Q is a two-dimensional polytope with exactly four extreme vertices.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- The facet whose deformation restrictions have dimension at most two. -/
def F : Set (E 4) := facet 5
/-- The first determining facet. -/
def H : Set (E 4) := facet 21
/-- The disjoint determining facet, already a geometric parallelepiped. -/
def G : Set (E 4) := facet 1
/-- The common quadrilateral of F and H. -/
def Q : Set (E 4) := indexedFace 180

def FLabels : Finset (Fin 32) := {24, 25, 26, 27, 28, 29, 30, 31}
def HLabels : Finset (Fin 32) := {8, 10, 12, 14, 24, 26, 28, 30}
def GLabels : Finset (Fin 32) := {1, 3, 5, 7, 9, 11, 13, 15}
def QLabels : Finset (Fin 32) := {24, 26, 28, 30}

theorem F_labels : facetLabels 5 = FLabels := by decide
theorem H_labels : facetLabels 21 = HLabels := by decide
theorem G_labels : facetLabels 1 = GLabels := by decide
theorem Q_labels : faceMask 180 = QLabels := by decide

theorem F_isFace : polytope.IsFace F := facet_isFace 5
theorem H_isFace : polytope.IsFace H := facet_isFace 21
theorem G_isFace : polytope.IsFace G := facet_isFace 1
theorem Q_isFace : polytope.IsFace Q := indexedFace_isFace 180

@[simp] theorem vertex_mem_F (v : Fin 32) : p v ∈ F ↔ v ∈ FLabels := by
  rw [F, vertex_mem_facet_iff, incident, F_labels]
@[simp] theorem vertex_mem_H (v : Fin 32) : p v ∈ H ↔ v ∈ HLabels := by
  rw [H, vertex_mem_facet_iff, incident, H_labels]
@[simp] theorem vertex_mem_G (v : Fin 32) : p v ∈ G ↔ v ∈ GLabels := by
  rw [G, vertex_mem_facet_iff, incident, G_labels]
@[simp] theorem vertex_mem_Q (v : Fin 32) : p v ∈ Q ↔ v ∈ QLabels := by
  rw [Q, vertex_mem_indexedFace, Q_labels]

theorem F_dimension : faceDim F = 3 := facet_dimension 5
theorem H_dimension : faceDim H = 3 := facet_dimension 21
theorem G_dimension : faceDim G = 3 := facet_dimension 1
theorem Q_dimension : faceDim Q = 2 := by
  rw [Q, indexedFace_dimension]
  rfl

def F_facet : FacetType polytope :=
  ⟨⟨F, F_isFace⟩, by simp only [F_dimension, polytope_dimension]⟩
def H_facet : FacetType polytope :=
  ⟨⟨H, H_isFace⟩, by simp only [H_dimension, polytope_dimension]⟩
def G_facet : FacetType polytope :=
  ⟨⟨G, G_isFace⟩, by simp only [G_dimension, polytope_dimension]⟩

theorem vertex_mem_F_inter_H (v : Fin 32) :
    p v ∈ F ∩ H ↔ v ∈ QLabels := by
  rw [Set.mem_inter_iff, vertex_mem_F, vertex_mem_H, ← Finset.mem_inter]
  rw [show FLabels ∩ HLabels = QLabels by decide]

/-- The listed common quadrilateral is the actual intersection of the facets. -/
theorem F_inter_H : F ∩ H = Q := by
  have h24 : p 24 ∈ F ∩ H :=
    (vertex_mem_F_inter_H 24).mpr (by decide)
  have hI : polytope.IsFace (F ∩ H) :=
    isFace_inter polytope F_isFace H_isFace ⟨p 24, h24⟩
  exact (face_eq_iff_labels polytope p polytope_vertices hI Q_isFace
    QLabels QLabels vertex_mem_F_inter_H vertex_mem_Q).mpr rfl

/-- Disjoint vertex masks imply disjoint actual faces of this polytope. -/
theorem disjoint_faces_of_disjoint_labels {A B : Set (E 4)}
    (hA : polytope.IsFace A) (hB : polytope.IsFace B)
    (s t : Finset (Fin 32))
    (hs : ∀ v, p v ∈ A ↔ v ∈ s) (ht : ∀ v, p v ∈ B ↔ v ∈ t)
    (hst : Disjoint s t) : Disjoint A B := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  have hI : polytope.IsFace (A ∩ B) :=
    isFace_inter polytope hA hB ⟨x, hxA, hxB⟩
  have hmask : ∀ v, p v ∈ A ∩ B ↔ v ∈ (∅ : Finset (Fin 32)) := by
    intro v
    constructor
    · intro hv
      exact False.elim ((Finset.disjoint_left.mp hst)
        ((hs v).mp hv.1) ((ht v).mp hv.2))
    · intro hv
      exact False.elim (Finset.notMem_empty v hv)
  have hempty := face_eq_label_hull polytope p polytope_vertices hI ∅ hmask
  simp only [Finset.coe_empty, Set.image_empty, convexHull_empty] at hempty
  have hx : x ∈ A ∩ B := ⟨hxA, hxB⟩
  rw [hempty] at hx
  exact hx

theorem G_disjoint_F : Disjoint G F :=
  disjoint_faces_of_disjoint_labels G_isFace F_isFace GLabels FLabels
    vertex_mem_G vertex_mem_F (by decide)

theorem G_disjoint_H : Disjoint G H :=
  disjoint_faces_of_disjoint_labels G_isFace H_isFace GLabels HLabels
    vertex_mem_G vertex_mem_H (by decide)

/-- The third distinguished facet misses both facets at the common ridge. -/
theorem G_disjoint_F_union_H : Disjoint G (F ∪ H) := by
  apply Set.disjoint_left.mpr
  intro x hxG hx
  rcases hx with hxF | hxH
  · exact Set.disjoint_left.mp G_disjoint_F hxG hxF
  · exact Set.disjoint_left.mp G_disjoint_H hxG hxH

/-- The vertices of a face are precisely the labelled vertices that it contains. -/
theorem facePolytope_vertices_labels {A : Set (E 4)} (hA : polytope.IsFace A)
    (s : Finset (Fin 32)) (hs : ∀ v, p v ∈ A ↔ v ∈ s) :
    (facePolytope polytope hA).vertices = s.image p := by
  classical
  change polytope.vertices.filter (· ∈ A) = s.image p
  ext x
  simp only [polytope_vertices, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, rfl⟩, hv⟩
    exact ⟨v, (hs v).mp hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, (hs v).mpr hv⟩

/-- Q is a genuine quadrilateral: a two-dimensional face with four vertices. -/
theorem Q_vertices_card : (facePolytope polytope Q_isFace).vertices.card = 4 := by
  rw [facePolytope_vertices_labels Q_isFace QLabels vertex_mem_Q,
    Finset.card_image_of_injective _ p_injective]
  decide

theorem Q_quadrilateral :
    faceDim Q = 2 ∧ (facePolytope polytope Q_isFace).vertices.card = 4 :=
  ⟨Q_dimension, Q_vertices_card⟩

end CubicalIndecomposability.Block
end
end VerificationSource016

/- Original source: CubicalIndecomposability/Block/AffineInterfaces.lean -/
section VerificationSource017



/-!
# An affine equivalence of the two interfaces

The normalized block admits a rank-one affine shear carrying F onto H and
fixing their common quadrilateral pointwise. Invertibility is proved from
the exact kernel relation between its direction and its linear functional.
The body equality follows from affine transport of convex hulls.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- The linear functional in the interface shear. -/
def interfaceLinear : E 4 →ₗ[ℝ] ℝ :=
  (-1 / 165 : ℝ) • (EuclideanSpace.proj (0 : Fin 4)).toLinearMap +
  (-4468 / 156585 : ℝ) • (EuclideanSpace.proj (2 : Fin 4)).toLinearMap +
  (-77459 / 7985835 : ℝ) • (EuclideanSpace.proj (3 : Fin 4)).toLinearMap

def interfaceDirection : E 4 := WithLp.toLp 2 ![-11, 11, -15, 51]

def interfaceConstant : ℝ := 18851 / 313170

theorem interface_kernel : interfaceLinear interfaceDirection = 0 := by
  change (-1 / 165 : ℝ) * (-11) + (-4468 / 156585) * (-15) +
    (-77459 / 7985835) * 51 = 0
  norm_num

/-- The ambient affine equivalence, with an explicit inverse shear. -/
def interfaceShear : E 4 ≃ᵃ[ℝ] E 4 :=
  affineShear interfaceLinear interfaceDirection interfaceConstant interface_kernel

def interfaceSource : Fin 8 → Fin 32 := ![24, 25, 26, 27, 28, 29, 30, 31]
def interfaceTarget : Fin 8 → Fin 32 := ![24, 8, 26, 10, 28, 12, 30, 14]

theorem interfaceSource_image : Finset.univ.image interfaceSource = FLabels := by decide
theorem interfaceTarget_image : Finset.univ.image interfaceTarget = HLabels := by decide

/-- The exact correspondence between all eight interface vertices. -/
theorem interfaceShear_vertex (b : Fin 8) :
    interfaceShear (p (interfaceSource b)) = p (interfaceTarget b) := by
  fin_cases b
  · ext i
    fin_cases i
    · change ((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((-306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
    · change ((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((306306 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((1813815 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((1040757 : ℤ) : ℝ) / ((1058354 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((0 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((-51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((0 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((51 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
    · change ((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((51 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((408 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((102 : ℤ) : ℝ) / ((292 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((51 : ℤ) : ℝ) / ((44 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((-2388959 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-2388959 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
    · change ((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((4529684 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((14443030 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((7917648 : ℤ) : ℝ) / ((8578376 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((272 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((-357 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((-17 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((510 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
    · change ((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((1598 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((2856 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((714 : ℤ) : ℝ) / ((2044 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((408 : ℤ) : ℝ) / ((420 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((3096445 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((3096445 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
    · change ((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((612612 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((3627630 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((2081514 : ℤ) : ℝ) / ((2116708 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((0 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((701 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((121 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((102 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
    · change ((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((102 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((816 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((204 : ℤ) : ℝ) / ((584 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((102 : ℤ) : ℝ) / ((88 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((24668895 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((24668895 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
    · change ((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((9059368 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((28886060 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((15835296 : ℤ) : ℝ) / ((17156752 : ℤ) : ℝ)
      norm_num
  · ext i
    fin_cases i
    · change ((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (-11) = ((544 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((4907 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (11) = ((1121 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (-15) = ((1020 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num
    · change ((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ) +
        ((-1 / 165 : ℝ) * (((3196 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-4468 / 156585) * (((5712 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          (-77459 / 7985835) * (((1428 : ℤ) : ℝ) / ((4088 : ℤ) : ℝ)) +
          18851 / 313170) * (51) = ((816 : ℤ) : ℝ) / ((840 : ℤ) : ℝ)
      norm_num

/-- The shear maps the complete set of F vertices onto the H vertices. -/
theorem interfaceShear_image_vertices :
    interfaceShear '' (p '' (FLabels : Set (Fin 32))) =
      p '' (HLabels : Set (Fin 32)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hv' : v ∈ Finset.univ.image interfaceSource := by
      rwa [interfaceSource_image]
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv'
    refine ⟨interfaceTarget b, ?_, (interfaceShear_vertex b).symm⟩
    change interfaceTarget b ∈ HLabels
    rw [← interfaceTarget_image]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Finset.univ.image interfaceTarget := by
      rwa [interfaceTarget_image]
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv'
    refine ⟨p (interfaceSource b), ⟨interfaceSource b, ?_, rfl⟩,
      interfaceShear_vertex b⟩
    change interfaceSource b ∈ FLabels
    rw [← interfaceSource_image]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

/-- Equality of entire geometric facets, obtained from their vertex hulls. -/
theorem interfaceShear_image : interfaceShear '' F = H := by
  change interfaceShear.toAffineMap '' facet 5 = facet 21
  rw [facet_eq_hull, facet_eq_hull, F_labels, H_labels,
    AffineMap.image_convexHull]
  exact congrArg (convexHull ℝ) interfaceShear_image_vertices

/-- The interface equivalence fixes the common quadrilateral pointwise. -/
theorem interfaceShear_fixes_Q : ∀ x ∈ Q, interfaceShear x = x := by
  have hvertices : (p '' (QLabels : Set (Fin 32))).EqOn
      interfaceShear.toAffineMap (AffineMap.id ℝ (E 4)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = 24 ∨ v = 26 ∨ v = 28 ∨ v = 30 := by
      simpa only [QLabels, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton] using hv
    rcases hv' with rfl | rfl | rfl | rfl
    · exact interfaceShear_vertex 0
    · exact interfaceShear_vertex 2
    · exact interfaceShear_vertex 4
    · exact interfaceShear_vertex 6
  intro x hx
  rw [Q, indexedFace_eq_hull, Q_labels] at hx
  exact AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hx)

/-- Proposition 5(iv), with the identity projectivity on this normalized block. -/
theorem affine_interface_normalization :
    HasAffineInterfaceNormalization polytope F H Q :=
  affine_interface_normalization_of_affine polytope F H Q interfaceShear
    interfaceShear_image interfaceShear_fixes_Q

end CubicalIndecomposability.Block
end
end VerificationSource017

/- Original source: CubicalIndecomposability/Block/ActualEdges.lean -/
section VerificationSource018


/-!
# The edge list consists of actual exposed edges

This is the bridge from geometric parallel redrawings to the finite linear
system used for the rigidity proof.  Each listed pair spans a proved
one-dimensional exposed face of the actual convex polytope.
-/

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- Vertex labels viewed as the ordinary extreme vertices of the polytope. -/
def labelledVertex (v : Fin 32) : VertexType polytope := ⟨p v, vertex_mem v⟩

def edgeFaceIndex (e : Fin 80) : Fin 209 := ⟨32 + e.val, by omega⟩

/-- The edge row is the complete vertex mask of its geometric face. -/
theorem edgeFace_mask (e : Fin 80) :
    faceMask (edgeFaceIndex e) = {edgeVertex e 0, edgeVertex e 1} :=
  edgeMask e

theorem edgeFace_rank (e : Fin 80) : faceRank (edgeFaceIndex e) = 1 := by
  simp only [faceRank, edgeFaceIndex]
  have h0 : ¬32 + e.val < 32 := by omega
  have h1 : 32 + e.val < 112 := by omega
  simp only [h0, h1, if_false, if_true]

theorem edgeFace_dimension (e : Fin 80) :
    faceDim (indexedFace (edgeFaceIndex e)) = 1 := by
  simpa only [edgeFace_rank, Fin.val_one] using indexedFace_dimension (edgeFaceIndex e)

/-- Rank-one catalogue entries are exactly the entries indexed by the edge list. -/
theorem faceRank_one_iff_edgeFaceIndex (i : Fin 209) :
    faceRank i = 1 ↔ ∃ e : Fin 80, edgeFaceIndex e = i := by
  constructor
  · intro hrank
    have hval := congrArg Fin.val hrank
    have hb : 32 ≤ i.val ∧ i.val < 112 := by
      simp only [faceRank] at hval
      split_ifs at hval <;> norm_num at hval <;> omega
    refine ⟨⟨i.val - 32, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [edgeFaceIndex]
    omega
  · rintro ⟨e, rfl⟩
    exact edgeFace_rank e

/-- The endpoints are distinct because their exposed hull has dimension one. -/
theorem edgeVertex_ne (e : Fin 80) : edgeVertex e 0 ≠ edgeVertex e 1 := by
  intro h
  have hmask : faceMask (edgeFaceIndex e) = {edgeVertex e 1} := by
    simpa [h] using edgeFace_mask e
  have hface : indexedFace (edgeFaceIndex e) = {p (edgeVertex e 1)} := by
    rw [indexedFace_eq_hull, hmask, Finset.coe_singleton,
      Set.image_singleton, convexHull_singleton]
  have hd := edgeFace_dimension e
  rw [hface, faceDim_singleton] at hd
  exact Nat.zero_ne_one hd

/-- Each declared edge is an edge in the standard geometric sense. -/
theorem declaredEdge (e : Fin 80) :
    GeneralVertexStep polytope (p (edgeVertex e 0)) (p (edgeVertex e 1)) := by
  refine ⟨vertex_mem _, ?_, indexedFace (edgeFaceIndex e),
    indexedFace_isFace _, edgeFace_dimension e, ?_, ?_⟩
  · exact fun h => edgeVertex_ne e (p_injective h)
  · rw [vertex_mem_indexedFace, edgeFace_mask]
    simp
  · rw [vertex_mem_indexedFace, edgeFace_mask]
    simp

theorem declaredEdge_adj (e : Fin 80) :
    (polytopeGraph polytope).Adj (labelledVertex (edgeVertex e 0))
      (labelledVertex (edgeVertex e 1)) := by
  obtain ⟨_, hne, F, hF, hdF, h0, h1⟩ := declaredEdge e
  refine ⟨?_, F, hF, hdF, h0, h1⟩
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- The finite edge list is exactly the actual geometric edge relation,
with both orientations permitted. -/
theorem generalVertexStep_iff_edge (u v : Fin 32) :
    GeneralVertexStep polytope (p u) (p v) ↔
      ∃ e : Fin 80,
        (u = edgeVertex e 0 ∧ v = edgeVertex e 1) ∨
        (u = edgeVertex e 1 ∧ v = edgeVertex e 0) := by
  constructor
  · rintro ⟨_, huv, A, hA, hdim, huA, hvA⟩
    obtain ⟨i, hi⟩ := indexedFace_complete hA
    have hrank : faceRank i = 1 := by
      apply Fin.ext
      have h := indexedFace_dimension i
      rw [hi, hdim] at h
      exact h.symm
    obtain ⟨e, he⟩ := (faceRank_one_iff_edgeFaceIndex i).mp hrank
    have hu : u ∈ faceMask (edgeFaceIndex e) :=
      (vertex_mem_indexedFace _ _).mp (by simpa only [he, hi] using huA)
    have hv : v ∈ faceMask (edgeFaceIndex e) :=
      (vertex_mem_indexedFace _ _).mp (by simpa only [he, hi] using hvA)
    rw [edgeFace_mask] at hu hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    have hne : u ≠ v := fun h => huv (congrArg p h)
    refine ⟨e, ?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact False.elim (hne (hu.trans hv.symm))
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
    · exact False.elim (hne (hu.trans hv.symm))
  · rintro ⟨e, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      exact declaredEdge e
    · rcases h with ⟨rfl, rfl⟩
      obtain ⟨_, hne, A, hA, hdim, h0, h1⟩ := declaredEdge e
      exact ⟨vertex_mem _, hne.symm, A, hA, hdim, h1, h0⟩

/-- The same exact enumeration in the standard polytope graph API. -/
theorem labelledVertex_adj_iff_edge (u v : Fin 32) :
    (polytopeGraph polytope).Adj (labelledVertex u) (labelledVertex v) ↔
      ∃ e : Fin 80,
        (u = edgeVertex e 0 ∧ v = edgeVertex e 1) ∨
        (u = edgeVertex e 1 ∧ v = edgeVertex e 0) := by
  rw [← generalVertexStep_iff_edge]
  constructor
  · rintro ⟨hne, A, hA, hdim, hu, hv⟩
    refine ⟨vertex_mem _, ?_, A, hA, hdim, hu, hv⟩
    intro heq
    exact hne (Subtype.ext heq)
  · rintro ⟨_, hne, A, hA, hdim, hu, hv⟩
    refine ⟨?_, A, hA, hdim, hu, hv⟩
    intro heq
    exact hne (congrArg Subtype.val heq)

end CubicalIndecomposability.Block
end
end VerificationSource018

/- Original source: CubicalIndecomposability/Block/Rigidity.lean -/

end -- global noncomputable section
end -- global public section
