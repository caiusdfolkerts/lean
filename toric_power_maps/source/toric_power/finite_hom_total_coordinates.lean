module

public import ToricPower.NegativeFunctorTotalMap
public import ToricPower.FiniteHomTotalSigns
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex

namespace ToricPower

universe u v r

variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K : CochainComplex C ℤ)

def finiteSourceHomCoefficients : C ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj M := (((linearYoneda R C).obj M).mapHomologicalComplex (.down ℕ)).obj
    (K.restriction ComplexShape.embeddingUpNat).op
  map f := (NatTrans.mapHomologicalComplex ((linearYoneda R C).map f) (.down ℕ)).app
    (K.restriction ComplexShape.embeddingUpNat).op
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Category.comp_id x
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Category.assoc x f g).symm

instance finiteSourceHomCoefficients_additive : (finiteSourceHomCoefficients R K).Additive where
  map_add {M N} f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change z ≫ (f+g) = z ≫ f + z ≫ g
    exact Preadditive.comp_add _ _ _ z f g

variable (I : CochainComplex C ℤ) (width : ℕ)

open NegativeFunctorTotal

theorem negativeChainDegree_injective :
    Function.Injective (chainDegree (width := width)) := by
  intro p q same
  have equal : p.rev=q.rev := Fin.ext same
  simpa only [Fin.rev_rev] using congrArg Fin.rev equal

def finiteHomTotalInclusion (a : ℤ) (p : Fin width) :
    (K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) →ₗ[R]
      Cochain K I a where
  toFun f := finiteHomTotalSign (chainDegree p) a • Cochain.single f a
  map_add' f g := by
    apply Cochain.ext
    intro x y h
    simp only [Cochain.units_smul_v,Cochain.add_v,Cochain.single,Cochain.mk_v]
    split_ifs <;> simp only [comp_add,add_comp,smul_add,smul_zero,add_zero]
  map_smul' c f := by
    apply Cochain.ext
    intro x y h
    simp only [Cochain.units_smul_v,Cochain.smul_v,Cochain.single,Cochain.mk_v,
      RingHom.id_apply]
    split_ifs
    · simp only [Linear.comp_smul,Linear.smul_comp]
      exact smul_comm _ _ _
    · simp only [smul_zero]

def finiteHomTotalProjection (a : ℤ) (p : Fin width) :
    Cochain K I a →ₗ[R]
      (K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) where
  toFun f := finiteHomTotalSign (chainDegree p) a •
    f.v (chainDegree p : ℤ) (a+(chainDegree p : ℤ)) (by omega)
  map_add' f g := by simp only [Cochain.add_v,smul_add]
  map_smul' c f := by
    change finiteHomTotalSign (chainDegree p) a • (c • f.v _ _ _) =
      c • (finiteHomTotalSign (chainDegree p) a • f.v _ _ _)
    exact smul_comm _ _ _

def finiteHomTotalDegreeMap (a : ℤ) :
    (total (finiteSourceHomCoefficients R K) width I).X a ⟶
      ModuleCat.of R (Cochain K I a) :=
  biproduct.desc (fun p => ModuleCat.ofHom (finiteHomTotalInclusion R K I width a p))

def finiteHomTotalDegreeInverse (a : ℤ) :
    ModuleCat.of R (Cochain K I a) ⟶
      (total (finiteSourceHomCoefficients R K) width I).X a :=
  biproduct.lift (fun p => ModuleCat.ofHom (finiteHomTotalProjection R K I width a p))

theorem finiteHomTotalProjection_inclusion_self (a : ℤ) (p : Fin width)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    finiteHomTotalProjection R K I width a p
      (finiteHomTotalInclusion R K I width a p f) = f := by
  change finiteHomTotalSign (chainDegree p) a •
    ((finiteHomTotalSign (chainDegree p) a • Cochain.single f a).v _ _ _) = f
  rw [Cochain.units_smul_v,Cochain.single_v,smul_smul,Int.units_mul_self,one_smul]

theorem finiteHomTotalProjection_inclusion_ne (a : ℤ) (p q : Fin width) (different : p ≠ q)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    finiteHomTotalProjection R K I width a q
      (finiteHomTotalInclusion R K I width a p f) = 0 := by
  change finiteHomTotalSign (chainDegree q) a •
    ((finiteHomTotalSign (chainDegree p) a • Cochain.single f a).v _ _ _) = 0
  have unequal : (chainDegree q : ℤ) ≠ (chainDegree p : ℤ) := by
    intro same
    apply different
    exact (negativeChainDegree_injective width (Int.ofNat_inj.mp same)).symm
  rw [Cochain.units_smul_v,Cochain.single_v_eq_zero _ _ _ _ _ unequal,
    smul_zero,smul_zero]

theorem finiteHomTotalDegreeMap_inverse (a : ℤ) :
    finiteHomTotalDegreeMap R K I width a ≫ finiteHomTotalDegreeInverse R K I width a = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro p
  apply biproduct.hom_ext
  intro q
  simp only [finiteHomTotalDegreeMap,finiteHomTotalDegreeInverse,Category.assoc,
    biproduct.ι_desc_assoc,biproduct.lift_π]
  erw [Category.id_comp]
  by_cases same : p=q
  · subst q
    rw [biproduct.ι_π_self]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact finiteHomTotalProjection_inclusion_self R K I width a p f
  · rw [biproduct.ι_π_ne _ same]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact finiteHomTotalProjection_inclusion_ne R K I width a p q same f

variable (outside : ∀ p : ℤ, ¬ (0 ≤ p ∧ p < (width : ℤ)) → IsZero (K.X p))

include outside in
theorem finiteHomTotalDegreeInverse_injective (a : ℤ) :
    Function.Injective (finiteHomTotalDegreeInverse R K I width a) := by
  intro f g equal
  apply Cochain.ext
  intro p q relation
  by_cases inside : 0 ≤ p ∧ p < (width : ℤ)
  · let t : Fin width := ⟨p.toNat,by omega⟩
    let j := t.rev
    have degreeEqual : (chainDegree j : ℤ)=p := by
      simp only [j,chainDegree,Fin.rev_rev,t,Int.toNat_of_nonneg inside.1]
    have component := congrArg
      (fun z => biproduct.π
        (fun r : Fin width => (row (finiteSourceHomCoefficients R K) I r).X a) j z) equal
    change (finiteHomTotalDegreeInverse R K I width a ≫ biproduct.π _ j) f =
      (finiteHomTotalDegreeInverse R K I width a ≫ biproduct.π _ j) g at component
    simp only [finiteHomTotalDegreeInverse,biproduct.lift_π] at component
    change finiteHomTotalSign (chainDegree j) a • f.v _ _ _ =
      finiteHomTotalSign (chainDegree j) a • g.v _ _ _ at component
    have cancelled := congrArg (fun h => finiteHomTotalSign (chainDegree j) a • h) component
    simp only [smul_smul,Int.units_mul_self,one_smul] at cancelled
    have targetEqual : a+(chainDegree j : ℤ)=q := by omega
    have coordinatesEqual :
        (⟨(chainDegree j : ℤ),a+(chainDegree j : ℤ),by omega⟩ : Triplet a) =
          ⟨p,q,relation⟩ := by
      congr 1
    change f (⟨_,_,_⟩ : Triplet a) = g (⟨_,_,_⟩ : Triplet a) at cancelled
    rw [coordinatesEqual] at cancelled
    exact cancelled
  · exact (outside p inside).eq_of_src _ _

def finiteHomTotalDegreeIso (a : ℤ) :
    (total (finiteSourceHomCoefficients R K) width I).X a ≅
      ModuleCat.of R (Cochain K I a) where
  hom := finiteHomTotalDegreeMap R K I width a
  inv := finiteHomTotalDegreeInverse R K I width a
  hom_inv_id := finiteHomTotalDegreeMap_inverse R K I width a
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply finiteHomTotalDegreeInverse_injective R K I width outside a
    exact congrArg (fun h => h (finiteHomTotalDegreeInverse R K I width a f))
      (finiteHomTotalDegreeMap_inverse R K I width a)

end ToricPower

end

