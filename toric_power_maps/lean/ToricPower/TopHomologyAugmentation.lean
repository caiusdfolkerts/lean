module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The canonical augmentation from top cohomology

When the outgoing differential in degree `n` is zero, the quotient to
opcycles gives a canonical map to the single complex of its `n`th
homology. The construction is natural for actual chain maps, and a
computed concentration of homology makes it a quasi-isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) (n : ℕ) (outgoing : K.d n (n+1) = 0)

/-- The genuine quotient from top cochains, with a specified map from
homology. -/
def augmentationOfTopHomology {M : C} (η : K.homology n ⟶ M) :
    K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M :=
  HomologicalComplex.mkHomToSingle
    (K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫ η)
    (fun j _ => by
      rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp])

/-- It induces precisely the supplied map on top homology. -/
theorem augmentationOfTopHomology_homology {M : C} (η : K.homology n ⟶ M) :
    HomologicalComplex.homologyMap (augmentationOfTopHomology K n outgoing η) n ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom = η := by
  let α := augmentationOfTopHomology K n outgoing η
  let S := (HomologicalComplex.single C (.up ℕ) n).obj M
  have component : α.f n =
      (K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫ η) ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) n M).inv := by
    simp only [α, augmentationOfTopHomology, HomologicalComplex.mkHomToSingle_f]
  apply (cancel_epi (K.homologyπ n)).mp
  change K.homologyπ n ≫ (HomologicalComplex.homologyMap α n ≫
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom) = K.homologyπ n ≫ η
  calc
    _ = HomologicalComplex.cyclesMap α n ≫ S.homologyπ n ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom := by
      rw [HomologicalComplex.homologyπ_naturality_assoc]
    _ = HomologicalComplex.cyclesMap α n ≫ S.iCycles n ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom := by
      rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom]
    _ = K.iCycles n ≫ α.f n ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom := by
      rw [HomologicalComplex.cyclesMap_i_assoc]
    _ = K.iCycles n ≫ K.pOpcycles n ≫
        (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫ η := by
      rw [component]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = K.homologyπ n ≫ η := by
      rw [← HomologicalComplex.homology_π_ι_assoc]
      simp only [Category.assoc, HomologicalComplex.isoHomologyι_hom_inv_id_assoc]

/-- Concentrated homology makes the canonical augmentation itself a
quasi-isomorphism. -/
theorem augmentationOfTopHomology_quasiIso {M : C} (e : K.homology n ≅ M)
    (vanishing : ∀ q : ℕ, q ≠ n → IsZero (K.homology q)) :
    QuasiIso (augmentationOfTopHomology K n outgoing e.hom) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases equal : q = n
  · subst q
    have comparison : IsIso (HomologicalComplex.homologyMap
        (augmentationOfTopHomology K n outgoing e.hom) n ≫
          (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom) := by
      rw [augmentationOfTopHomology_homology]
      infer_instance
    letI := comparison
    exact IsIso.of_isIso_comp_right _
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom
  · exact (vanishing q equal).isIso
      (HomologicalComplex.isZero_single_obj_homology (.up ℕ) n M q equal) _

/-- The quotient of the top term is natural for every actual cochain
map between complexes with zero outgoing differential in that degree. -/
theorem topHomologyQuotient_natural {L : CochainComplex C ℕ}
    (outgoingL : L.d n (n+1) = 0) (φ : K ⟶ L) :
    φ.f n ≫ L.pOpcycles n ≫ (L.isoHomologyι n (n+1) (by simp) outgoingL).inv =
      K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫
        HomologicalComplex.homologyMap φ n := by
  apply (cancel_mono (L.homologyι n)).mp
  rw [Category.assoc, Category.assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, Category.comp_id,
    Category.assoc, Category.assoc,
    HomologicalComplex.homologyι_naturality,
    ← Category.assoc (K.isoHomologyι n (n+1) (by simp) outgoing).inv,
    HomologicalComplex.isoHomologyι_inv_hom_id, Category.id_comp,
    HomologicalComplex.p_opcyclesMap]

/-- Naturality is an equality of complete actual cochain maps. -/
theorem augmentationOfTopHomology_naturality {L : CochainComplex C ℕ}
    (outgoingL : L.d n (n+1) = 0) (φ : K ⟶ L) {M : C} (η : L.homology n ⟶ M) :
    φ ≫ augmentationOfTopHomology L n outgoingL η =
      augmentationOfTopHomology K n outgoing (HomologicalComplex.homologyMap φ n ≫ η) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, augmentationOfTopHomology,
    HomologicalComplex.mkHomToSingle_f, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ η ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n M).inv)
    (topHomologyQuotient_natural K n outgoing outgoingL φ)

end ToricPower
