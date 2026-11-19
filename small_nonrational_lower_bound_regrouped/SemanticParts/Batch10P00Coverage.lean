module
public import SemanticParts.Batch10P00Data
public import SemanticParts.Batch10P00Origins00
public import SemanticParts.Batch10P00Origins01
public import SemanticParts.Batch10P00Origins02
public import SemanticParts.Batch10P00Origins03
public import SemanticParts.Batch10P00Witnesses00
public import SemanticParts.Batch10P00Witnesses01
public import MatroidChecked.PublicRefutations.N8R4C67
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart0
/- Source: MatroidChecked/SemanticChunks/Cases14Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C67Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C67

noncomputable def certificates : List (Origin 70 356 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3 ++ certificates_4 ++ certificates_5 ++ certificates_6

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3
  · exact certificates_4_valid oc h4
  · exact certificates_5_valid oc h5
  · exact certificates_6_valid oc h6

theorem models_valid : ∀ w : Fin 356,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  by_cases h0 : w.val < 128
  ·
    have hh := witness_0 ⟨w.val - 0,by omega⟩
    have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 356) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh
  ·
    by_cases h1 : w.val < 256
    ·
      have hh := witness_1 ⟨w.val - 128,by omega⟩
      have heq : (⟨128 + (w.val - 128),by omega⟩ : Fin 356) = w := Fin.ext (by dsimp only; omega)
      dsimp only at hh
      rw [heq] at hh
      exact hh
    ·
      have hh := witness_2 ⟨w.val - 256,by omega⟩
      have heq : (⟨256 + (w.val - 256),by omega⟩ : Fin 356) = w := Fin.ext (by dsimp only; omega)
      dsimp only at hh
      rw [heq] at hh
      exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C67.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C67.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C67


end
end
end BundlePart0

