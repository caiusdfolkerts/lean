module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins


section BundlePart2
/- Source: MatroidChecked/SemanticParts/Cases16Part00/Checks04.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C69


theorem witness_6 : ∀ j : Fin 37,
    let w : Fin 805 := ⟨768 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 37,
      let w : Fin 805 := ⟨768 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.BitsetRawWitness 8 (N7R4.familyMasks.get 69)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 18) (n := 19) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 9) (n := 9) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
    · refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.BitsetSemanticChecks.bitsetRawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C69

end
end
end BundlePart2

