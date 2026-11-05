module
public import SemanticParts.Batch10P02Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases18Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C72Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72


theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 177 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 177 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 72)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_1 : ∀ j : Fin 49,
    let w : Fin 177 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 49,
      let w : Fin 177 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 72)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 24) (n := 25) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 12) (n := 12) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
    · refine (Fin.forall_fin_add (m := 12) (n := 13) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 6) (n := 7) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72



end
end
end BundlePart2

