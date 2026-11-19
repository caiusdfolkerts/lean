module
public import MatroidChecked.FastSemanticChecks
public import MatroidCatalogue.Definitions

@[expose] public section
noncomputable section

/-!
# Exact insertion of a coloop in the finite catalogue

The data tables place the families obtained by inserting the new label at
matching initial indices. These ordinary kernel checks compare their lists
of natural-number masks. The generic decoding identity below turns each
comparison into equality of the actual basis families.
-/

namespace Papers.RationalityTen.MatroidChecked.CatalogueColoops
open Finset BasisReconstruction BasisCertificates BasisCatalogue
open FastSemanticChecks

/-- Setting the bit for a label inserts that label in each decoded basis. -/
theorem familyOfMasks_insert (L : List ℕ) (e : Fin 8) :
    familyOfMasks (L.map (fun m => m ||| 2 ^ e.val)) =
      (familyOfMasks L).image (insert e) := by
  simp only [familyOfMasks, toFinset_map_image, Finset.image_image,
    Function.comp_def, maskPoints_or, maskPoints_pow, Finset.union_singleton]

theorem family_insert_of_masks_eq (L M : List ℕ) (e : Fin 8)
    (h : L.map (fun m => m ||| 2 ^ e.val) = M) :
    (familyOfMasks L).image (insert e) = familyOfMasks M := by
  rw [← familyOfMasks_insert, h]

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem masks_1_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N1R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 1) =
      MatroidCatalogue.N2R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_1_2 (i : Fin 1) :
    (MatroidCatalogue.family 1 1 i.val).image (insert (1 : Fin 8)) =
      MatroidCatalogue.family 2 2 i.val := by
  exact family_insert_of_masks_eq _ _ (1 : Fin 8) (masks_1_2 i)

private theorem masks_2_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N2R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 2) =
      MatroidCatalogue.N3R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_2_2 (i : Fin 1) :
    (MatroidCatalogue.family 2 1 i.val).image (insert (2 : Fin 8)) =
      MatroidCatalogue.family 3 2 i.val := by
  exact family_insert_of_masks_eq _ _ (2 : Fin 8) (masks_2_2 i)

private theorem masks_2_3 : ∀ i : Fin 1,
    (MatroidCatalogue.N2R2.familyMasks.get i.val).map (fun m => m ||| 2 ^ 2) =
      MatroidCatalogue.N3R3.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_2_3 (i : Fin 1) :
    (MatroidCatalogue.family 2 2 i.val).image (insert (2 : Fin 8)) =
      MatroidCatalogue.family 3 3 i.val := by
  exact family_insert_of_masks_eq _ _ (2 : Fin 8) (masks_2_3 i)

private theorem masks_3_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N3R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 3) =
      MatroidCatalogue.N4R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_3_2 (i : Fin 1) :
    (MatroidCatalogue.family 3 1 i.val).image (insert (3 : Fin 8)) =
      MatroidCatalogue.family 4 2 i.val := by
  exact family_insert_of_masks_eq _ _ (3 : Fin 8) (masks_3_2 i)

private theorem masks_3_3 : ∀ i : Fin 2,
    (MatroidCatalogue.N3R2.familyMasks.get i.val).map (fun m => m ||| 2 ^ 3) =
      MatroidCatalogue.N4R3.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_3_3 (i : Fin 2) :
    (MatroidCatalogue.family 3 2 i.val).image (insert (3 : Fin 8)) =
      MatroidCatalogue.family 4 3 i.val := by
  exact family_insert_of_masks_eq _ _ (3 : Fin 8) (masks_3_3 i)

private theorem masks_3_4 : ∀ i : Fin 1,
    (MatroidCatalogue.N3R3.familyMasks.get i.val).map (fun m => m ||| 2 ^ 3) =
      MatroidCatalogue.N4R4.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_3_4 (i : Fin 1) :
    (MatroidCatalogue.family 3 3 i.val).image (insert (3 : Fin 8)) =
      MatroidCatalogue.family 4 4 i.val := by
  exact family_insert_of_masks_eq _ _ (3 : Fin 8) (masks_3_4 i)

private theorem masks_4_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N4R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 4) =
      MatroidCatalogue.N5R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_4_2 (i : Fin 1) :
    (MatroidCatalogue.family 4 1 i.val).image (insert (4 : Fin 8)) =
      MatroidCatalogue.family 5 2 i.val := by
  exact family_insert_of_masks_eq _ _ (4 : Fin 8) (masks_4_2 i)

private theorem masks_4_3 : ∀ i : Fin 4,
    (MatroidCatalogue.N4R2.familyMasks.get i.val).map (fun m => m ||| 2 ^ 4) =
      MatroidCatalogue.N5R3.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_4_3 (i : Fin 4) :
    (MatroidCatalogue.family 4 2 i.val).image (insert (4 : Fin 8)) =
      MatroidCatalogue.family 5 3 i.val := by
  exact family_insert_of_masks_eq _ _ (4 : Fin 8) (masks_4_3 i)

private theorem masks_4_4 : ∀ i : Fin 3,
    (MatroidCatalogue.N4R3.familyMasks.get i.val).map (fun m => m ||| 2 ^ 4) =
      MatroidCatalogue.N5R4.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_4_4 (i : Fin 3) :
    (MatroidCatalogue.family 4 3 i.val).image (insert (4 : Fin 8)) =
      MatroidCatalogue.family 5 4 i.val := by
  exact family_insert_of_masks_eq _ _ (4 : Fin 8) (masks_4_4 i)

private theorem masks_5_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N5R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 5) =
      MatroidCatalogue.N6R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_5_2 (i : Fin 1) :
    (MatroidCatalogue.family 5 1 i.val).image (insert (5 : Fin 8)) =
      MatroidCatalogue.family 6 2 i.val := by
  exact family_insert_of_masks_eq _ _ (5 : Fin 8) (masks_5_2 i)

private theorem masks_5_3 : ∀ i : Fin 6,
    (MatroidCatalogue.N5R2.familyMasks.get i.val).map (fun m => m ||| 2 ^ 5) =
      MatroidCatalogue.N6R3.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_5_3 (i : Fin 6) :
    (MatroidCatalogue.family 5 2 i.val).image (insert (5 : Fin 8)) =
      MatroidCatalogue.family 6 3 i.val := by
  exact family_insert_of_masks_eq _ _ (5 : Fin 8) (masks_5_3 i)

private theorem masks_5_4 : ∀ i : Fin 9,
    (MatroidCatalogue.N5R3.familyMasks.get i.val).map (fun m => m ||| 2 ^ 5) =
      MatroidCatalogue.N6R4.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_5_4 (i : Fin 9) :
    (MatroidCatalogue.family 5 3 i.val).image (insert (5 : Fin 8)) =
      MatroidCatalogue.family 6 4 i.val := by
  exact family_insert_of_masks_eq _ _ (5 : Fin 8) (masks_5_4 i)

private theorem masks_6_2 : ∀ i : Fin 1,
    (MatroidCatalogue.N6R1.familyMasks.get i.val).map (fun m => m ||| 2 ^ 6) =
      MatroidCatalogue.N7R2.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_6_2 (i : Fin 1) :
    (MatroidCatalogue.family 6 1 i.val).image (insert (6 : Fin 8)) =
      MatroidCatalogue.family 7 2 i.val := by
  exact family_insert_of_masks_eq _ _ (6 : Fin 8) (masks_6_2 i)

private theorem masks_6_3 : ∀ i : Fin 10,
    (MatroidCatalogue.N6R2.familyMasks.get i.val).map (fun m => m ||| 2 ^ 6) =
      MatroidCatalogue.N7R3.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_6_3 (i : Fin 10) :
    (MatroidCatalogue.family 6 2 i.val).image (insert (6 : Fin 8)) =
      MatroidCatalogue.family 7 3 i.val := by
  exact family_insert_of_masks_eq _ _ (6 : Fin 8) (masks_6_3 i)

private theorem masks_6_4 : ∀ i : Fin 25,
    (MatroidCatalogue.N6R3.familyMasks.get i.val).map (fun m => m ||| 2 ^ 6) =
      MatroidCatalogue.N7R4.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_6_4 (i : Fin 25) :
    (MatroidCatalogue.family 6 3 i.val).image (insert (6 : Fin 8)) =
      MatroidCatalogue.family 7 4 i.val := by
  exact family_insert_of_masks_eq _ _ (6 : Fin 8) (masks_6_4 i)

private theorem masks_7_4 : ∀ i : Fin 70,
    (MatroidCatalogue.N7R3.familyMasks.get i.val).map (fun m => m ||| 2 ^ 7) =
      MatroidCatalogue.N8R4.familyMasks.get i.val := by
  decide +kernel

/-- The actual coloop extension agrees with the target catalogue family. -/
theorem family_7_4 (i : Fin 70) :
    (MatroidCatalogue.family 7 3 i.val).image (insert (7 : Fin 8)) =
      MatroidCatalogue.family 8 4 i.val := by
  exact family_insert_of_masks_eq _ _ (7 : Fin 8) (masks_7_4 i)

end Papers.RationalityTen.MatroidChecked.CatalogueColoops
