module

public import PaperVerification.SegreCechCoordinates

/-!
# Exactness for the actual twisting-sheaf section tuples

The Laurent contraction is transported through the full, restriction-natural
section equivalence. The resulting differential is the actual alternating
sum of sheaf restrictions. Exactness therefore concerns all actual sections
on all coordinate intersections, rather than a formally declared model.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.CechMonomials

open CoordinateLocalization
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

theorem tupleCoordinates_delete_subset {q : ℕ} (a : Fin (q+1) → I) (j : Fin (q+1)) :
    tupleCoordinates (a ∘ j.succAbove) ⊆ tupleCoordinates a := by
  intro i hi
  rw [mem_tupleCoordinates] at hi ⊢
  obtain ⟨r,hr⟩ := hi
  exact ⟨j.succAbove r,hr⟩

/-- The coefficient differential agrees with the alternating sum of localization restrictions. -/
theorem laurentLocalEquiv_differential (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t q) (a : Fin (q+1) → I) :
    laurentLocalEquiv t (q+1)
        ⟨laurentDifferential (I := I) (K := K) t q f.val,laurentDifferential_mem f.property⟩ a =
      ∑ j : Fin (q+1), (-1 : ℤ)^j.val •
        degreeRestriction (tupleCoordinates_delete_subset a j) t
          (laurentLocalEquiv t q f (a ∘ j.succAbove)) := by
  apply (localCoefficientEquiv (tupleCoordinates a) t).injective
  apply Subtype.ext
  ext v
  simp only [map_sum,map_zsmul,localCoefficientEquiv_restriction,
    Submodule.coe_sum,Submodule.coe_smul_of_tower,
    Finset.sum_apply',Finsupp.smul_apply,coefficientRestriction_apply,
    laurentLocalEquiv_coeff,laurentDifferential_apply]
  change differential q (f.val v) a =
    ∑ j : Fin (q+1), (-1 : ℤ)^j.val • f.val v (a ∘ j.succAbove)
  simp only [differential_apply,zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]

end PaperVerification.Segre.CechMonomials

namespace PaperVerification.Segre.TwistingSections

open CoordinateLocalization CechMonomials AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

/-- The full tuple group of actual sections on coordinate intersections. -/
abbrev SectionCochain (t : ℤ) (q : ℕ) :=
  (a : Fin (q+1) → I) → Γ(Proj.twistingSheaf 𝒜 t,chartIntersection (tupleCoordinates a))

/-- The complete, canonical term equivalence to actual sheaf sections. -/
def sectionCochainEquiv (t : ℤ) (q : ℕ) :
    laurentCochains (I := I) (K := K) t (q+1) ≃+ SectionCochain (I := I) (K := K) t q :=
  (laurentLocalEquiv t (q+1)).toAddEquiv.trans
    (AddEquiv.piCongrRight (fun a =>
      sectionsEquiv (tupleCoordinates a) (tupleCoordinates_nonempty a) t))

@[simp] theorem sectionCochainEquiv_apply (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t (q+1)) (a : Fin (q+1) → I) :
    sectionCochainEquiv t q f a =
      sectionsEquiv (tupleCoordinates a) (tupleCoordinates_nonempty a) t
        (laurentLocalEquiv t (q+1) f a) := rfl

/-- The literal alternating sum of the actual sheaf restriction maps. -/
def sectionDifferential (t : ℤ) (q : ℕ) :
    SectionCochain (I := I) (K := K) t q →+
      SectionCochain (I := I) (K := K) t (q+1) where
  toFun f a := ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
    (Proj.twistingSheaf 𝒜 t).presheaf.map
      (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op
      (f (a ∘ j.succAbove))
  map_zero' := by funext a; simp
  map_add' f g := by funext a; simp only [Pi.add_apply,map_add,zsmul_add,Finset.sum_add_distrib]

@[simp] theorem sectionDifferential_apply (t : ℤ) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t q) (a : Fin (q+2) → I) :
    sectionDifferential t q f a = ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
      (Proj.twistingSheaf 𝒜 t).presheaf.map
        (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op
        (f (a ∘ j.succAbove)) := rfl

/-- The full section equivalences intertwine the literal two differentials. -/
theorem sectionCochainEquiv_differential (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := I) (K := K) t (q+1)) :
    sectionCochainEquiv t (q+1)
        ⟨laurentDifferential (I := I) (K := K) t (q+1) f.val,laurentDifferential_mem f.property⟩ =
      sectionDifferential t q (sectionCochainEquiv t q f) := by
  funext a
  rw [sectionCochainEquiv_apply,laurentLocalEquiv_differential]
  simp only [map_sum,map_zsmul,sectionDifferential_apply,sectionCochainEquiv_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => (-1 : ℤ)^j.val • z)
    (sectionsEquiv_restriction (tupleCoordinates_delete_subset a j)
      (tupleCoordinates_nonempty (a ∘ j.succAbove)) (tupleCoordinates_nonempty a) t
      (laurentLocalEquiv t (q+1) f (a ∘ j.succAbove))).symm

theorem sectionDifferential_squared (t : ℤ) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t q) :
    sectionDifferential t (q+1) (sectionDifferential t q f)=0 := by
  obtain ⟨g,rfl⟩ := (sectionCochainEquiv t q).surjective f
  rw [← sectionCochainEquiv_differential,← sectionCochainEquiv_differential]
  have hz : (⟨laurentDifferential (I := I) (K := K) t (q+2) (laurentDifferential (I := I) (K := K) t (q+1) g.val),
      laurentDifferential_mem (laurentDifferential_mem g.property)⟩ :
      laurentCochains (I := I) (K := K) t (q+3))=0 :=
    Subtype.ext (laurentDifferential_squared t (q+1) g.val)
  rw [hz,map_zero]

/-- Every actual positive-degree cocycle below projective dimension is a boundary. -/
theorem section_exact_below_dimension (t : ℤ) (q : ℕ) (hq : q+2<Fintype.card I)
    (f : SectionCochain (I := I) (K := K) t (q+1))
    (hc : sectionDifferential t (q+1) f=0) :
    ∃ g : SectionCochain (I := I) (K := K) t q, sectionDifferential t q g=f := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t (q+1)).surjective f
  have hv : laurentDifferential (I := I) (K := K) t (q+2) v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t (q+2) v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t (q+3))=0 := by
      apply (sectionCochainEquiv t (q+2)).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  obtain ⟨w,hw,hd⟩ := laurent_exact_below_dimension t (q+1) hq v.val v.property hv
  refine ⟨sectionCochainEquiv t q ⟨w,hw⟩,?_⟩
  rw [← sectionCochainEquiv_differential]
  exact congrArg (sectionCochainEquiv t (q+1)) (Subtype.ext hd)

/-- Every actual positive-degree cocycle vanishes for twists at least `-N` on `P^N`. -/
theorem section_exact_of_twist (t : ℤ) (ht : -(Fintype.card I : ℤ)<t) (q : ℕ)
    (f : SectionCochain (I := I) (K := K) t (q+1))
    (hc : sectionDifferential t (q+1) f=0) :
    ∃ g : SectionCochain (I := I) (K := K) t q, sectionDifferential t q g=f := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t (q+1)).surjective f
  have hv : laurentDifferential (I := I) (K := K) t (q+2) v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t (q+2) v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t (q+3))=0 := by
      apply (sectionCochainEquiv t (q+2)).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  obtain ⟨w,hw,hd⟩ := laurent_exact_of_twist t ht (q+1) v.val v.property hv
  refine ⟨sectionCochainEquiv t q ⟨w,hw⟩,?_⟩
  rw [← sectionCochainEquiv_differential]
  exact congrArg (sectionCochainEquiv t (q+1)) (Subtype.ext hd)

/-- Actual compatible chart sections of negative twist are zero. -/
theorem section_global_cocycle_eq_zero (hI : 1<Fintype.card I) (t : ℤ) (ht : t<0)
    (f : SectionCochain (I := I) (K := K) t 0) (hc : sectionDifferential t 0 f=0) : f=0 := by
  obtain ⟨v,rfl⟩ := (sectionCochainEquiv t 0).surjective f
  have hv : laurentDifferential (I := I) (K := K) t 1 v.val=0 := by
    have he : (⟨laurentDifferential (I := I) (K := K) t 1 v.val,laurentDifferential_mem v.property⟩ :
        laurentCochains (I := I) (K := K) t 2)=0 := by
      apply (sectionCochainEquiv t 1).injective
      simpa only [sectionCochainEquiv_differential,map_zero] using hc
    exact congrArg Subtype.val he
  have hz := laurent_global_cocycle_eq_zero hI t ht v.val v.property hv
  rw [show v=0 from Subtype.ext hz,map_zero]

end PaperVerification.Segre.TwistingSections
