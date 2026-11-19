module

public import PaperVerification.ExteriorMonomialQuotient
public import PaperVerification.QuadraticWordPBW
public import Mathlib.Data.Finset.Sort

/-!
# Ordinary Tor concentration for actual exterior monomial quotients

The quotient, its basis and its augmentation come from the ordinary
exterior algebra. A proved combinatorial description of its surviving
sets as the normal words of a transitive relation supplies the inputs to
the signed word-bar exactness theorem. The internal degree is the literal
number of exterior generators in each basis monomial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.ExteriorMonomialKoszul

open ExteriorMonomialQuotient QuadraticWordBar AugmentedAlgebraBasis

universe u
variable {K M I : Type u} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder I] (b : Module.Basis I K M) (F : Set (Finset I))
  (hF : ∀ S∈F,S.Nonempty)

def emptyAllowed : Allowed F := ⟨∅,by
  rintro ⟨S,hS,hS0⟩
  have he : S=∅ := Finset.subset_empty.mp hS0
  exact (hF S hS).ne_empty he⟩

def PositiveIndex := {S : Allowed F // S.val.Nonempty}

instance [Finite I] : Finite (PositiveIndex F) := by
  unfold PositiveIndex Allowed
  infer_instance

def positiveNeEquiv : PositiveIndex F≃{S : Allowed F // S≠emptyAllowed F hF} :=
  Equiv.subtypeEquivRight (fun S => by
    rw [Finset.nonempty_iff_ne_empty]
    constructor
    · intro h he
      exact h (congrArg Subtype.val he)
    · intro h he
      exact h (Subtype.ext he))

def optionIndexEquiv : Option (PositiveIndex F)≃Allowed F :=
  (Equiv.optionCongr (positiveNeEquiv F hF)).trans
    (Equiv.optionSubtypeNe (emptyAllowed F hF))

@[simp] theorem optionIndexEquiv_none :
    optionIndexEquiv F hF none=emptyAllowed F hF := rfl

@[simp] theorem optionIndexEquiv_some (S : PositiveIndex F) :
    optionIndexEquiv F hF (some S)=S.val := rfl

def augmentedBasis : Module.Basis (Option (PositiveIndex F)) K
    (ExteriorAlgebra K M⧸monomialIdeal b F) :=
  (quotientBasis b F).reindex (optionIndexEquiv F hF).symm

@[simp] theorem augmentedBasis_none : augmentedBasis b F hF none=1 := by
  simp only [augmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    optionIndexEquiv_none,quotientBasis_apply,emptyAllowed]
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  simp

@[simp] theorem augmentedBasis_some (S : PositiveIndex F) :
    augmentedBasis b F hF (some S)=
      Ideal.Quotient.mk (monomialIdeal b F) (b.ExteriorAlgebra S.val.val) := by
  simp only [augmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    optionIndexEquiv_some,quotientBasis_apply]

@[simp] theorem augmentation_positive (S : PositiveIndex F) :
    augmentation b F hF (augmentedBasis b F hF (some S))=0 := by
  rw [augmentedBasis_some,augmentation_mk]
  exact algebraMapInv_basis b S.val.val S.property

variable (R : I→I→Prop) [IsTrans I R]
  (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)

include hlt in
theorem normalWord_nodup (W : PositiveWord R) : W.val.Nodup := by
  have h := (List.isChain_iff_pairwise.mp W.property.2).imp
    (fun {i j} hij => ne_of_lt (hlt i j hij))
  exact h

include hlt in
theorem normalWord_sort (W : PositiveWord R) : W.val.toFinset.sort=W.val := by
  apply (List.toFinset_sort (fun a b : I => a ≤ b) (normalWord_nodup R hlt W)).mpr
  exact (List.isChain_iff_pairwise.mp W.property.2).imp
    (fun {i j} hij => (hlt i j hij).le)

def normalWordEquiv : PositiveIndex F≃PositiveWord R where
  toFun S := ⟨S.val.val.sort,by
    simpa only [Finset.length_sort] using S.property.card_pos,
    (hchain S.val.val).mp S.val.property⟩
  invFun W := ⟨⟨W.val.toFinset,(hchain W.val.toFinset).mpr (by
    rw [normalWord_sort R hlt W]
    exact W.property.2)⟩,by
      have hnonempty : W.val≠[] := List.ne_nil_of_length_pos W.property.1
      obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hnonempty
      exact ⟨i,List.mem_toFinset.mpr hi⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.sort_toFinset _ _
  right_inv W := Subtype.ext (normalWord_sort R hlt W)

@[simp] theorem normalWordEquiv_word (S : PositiveIndex F) :
    (normalWordEquiv F R hlt hchain S).val=S.val.val.sort := rfl

@[simp] theorem normalWordEquiv_degree (S : PositiveIndex F) :
    QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain) S=S.val.val.card :=
  Finset.length_sort (fun a b : I => a ≤ b)

/-- A normal concatenation has coefficient exactly one because the
actual exterior products already occur in their increasing order. -/
theorem normal_product (S T : PositiveIndex F)
    (h : ((normalWordEquiv F R hlt hchain S).val++
      (normalWordEquiv F R hlt hchain T).val).IsChain R) :
    productCoefficients (augmentedBasis b F hF) S T=
      Finsupp.single (concatenateNormal (normalWordEquiv F R hlt hchain) S T h) 1 := by
  let U := concatenateNormal (normalWordEquiv F R hlt hchain) S T h
  have hw : U.val.val.sort=S.val.val.sort++T.val.val.sort :=
    concatenateNormal_word (normalWordEquiv F R hlt hchain) S T h
  have hp : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)=
      augmentedBasis b F hF (some U) := by
    rw [augmentedBasis_some,augmentedBasis_some,augmentedBasis_some,←map_mul]
    congr 1
    rw [b.exteriorAlgebra_eq_prod_map_sort,b.exteriorAlgebra_eq_prod_map_sort,
      b.exteriorAlgebra_eq_prod_map_sort,hw,List.map_append,List.map_append,List.prod_append]
  change positiveCoordinates (augmentedBasis b F hF)
    (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T))=_
  rw [hp]
  exact positiveCoordinates_vector (augmentedBasis b F hF) U

theorem sort_union_perm_append (S T : Finset I) (hd : Disjoint S T) :
    (S∪T).sort.Perm (S.sort++T.sort) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
  · apply (Finset.sort_nodup S _).append (Finset.sort_nodup T _)
    apply List.disjoint_left.mpr
    intro i hiS hiT
    exact Finset.disjoint_left.mp hd ((Finset.mem_sort _).mp hiS)
      ((Finset.mem_sort _).mp hiT)
  · simp only [List.toFinset_append,Finset.sort_toFinset]

/-- Any nonzero product has exactly the multiset of its original exterior
letters. No dimension or normal-form hypothesis enters this assertion. -/
theorem product_perm (S T U : PositiveIndex F)
    (h : productCoefficients (augmentedBasis b F hF) S T U≠0) :
    (normalWordEquiv F R hlt hchain U).val.Perm
      ((normalWordEquiv F R hlt hchain S).val++
        (normalWordEquiv F R hlt hchain T).val) := by
  have hprod : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)≠0 := by
    intro hp
    apply h
    change positiveCoordinates (augmentedBasis b F hF)
      (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)) U=0
    rw [hp,map_zero,Finsupp.zero_apply]
  have hd : Disjoint S.val.val T.val.val := by
    by_contra hnd
    apply hprod
    rw [augmentedBasis_some,augmentedBasis_some,←map_mul,
      basis_mul_not_disjoint b _ _ hnd,map_zero]
  obtain ⟨u,hu⟩ := basis_mul_disjoint b S.val.val T.val.val hd
  have hallowed : ¬Bad F (S.val.val∪T.val.val) := by
    intro hbad
    apply hprod
    rw [augmentedBasis_some,augmentedBasis_some,←map_mul,hu]
    change Ideal.Quotient.mk (monomialIdeal b F)
      ((u : ℤ) • b.ExteriorAlgebra (S.val.val∪T.val.val))=0
    rw [map_zsmul,quotient_monomial_eq_zero_of_bad b F _ hbad,smul_zero]
  let V : PositiveIndex F := ⟨⟨S.val.val∪T.val.val,hallowed⟩,
    S.property.mono Finset.subset_union_left⟩
  have hp : augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)=
      u • augmentedBasis b F hF (some V) := by
    rw [augmentedBasis_some,augmentedBasis_some,augmentedBasis_some,←map_mul,hu]
    change Ideal.Quotient.mk (monomialIdeal b F)
      ((u : ℤ) • b.ExteriorAlgebra (S.val.val∪T.val.val))=
      (u : ℤ) • Ideal.Quotient.mk (monomialIdeal b F)
        (b.ExteriorAlgebra (S.val.val∪T.val.val))
    exact map_zsmul _ _ _
  have he : U=V := by
    by_contra hUV
    apply h
    change positiveCoordinates (augmentedBasis b F hF)
      (augmentedBasis b F hF (some S)*augmentedBasis b F hF (some T)) U=0
    rw [hp,Units.smul_def,map_zsmul]
    change ((u : ℤ) • (positiveCoordinates (augmentedBasis b F hF)
      (positiveVector (augmentedBasis b F hF) V))) U=0
    rw [positiveCoordinates_vector,Finsupp.smul_apply,Finsupp.single_eq_of_ne hUV,smul_zero]
  subst U
  exact sort_union_perm_append S.val.val T.val.val hd

variable [Fintype I]

include R hlt hchain in
/-- The degree of every actual basis monomial is its original exterior
word length. Its multiplication coefficients preserve that degree. -/
theorem product_degree (S T U : PositiveIndex F)
    (h : productCoefficients (augmentedBasis b F hF) S T U≠0) :
    U.val.val.card=S.val.val.card+T.val.val.card := by
  have hp := (product_perm b F hF R hlt hchain S T U h).length_eq
  simpa only [normalWordEquiv_word,Finset.length_sort,List.length_append] using hp

/-- A complete ordinary-Tor conclusion for the actual exterior quotient.
The only extra input is the explicit finite-set/word equivalence; its
specializations to dimensions at most four are proved separately. -/
theorem hasDiagonalTor :
    WeightedBar.HasDiagonalTor (augmentation b F hF) (augmentedBasis b F hF)
      (augmentedBasis_none b F hF) (augmentation_positive b F hF)
      (QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain))
      (QuadraticWordPBW.product_degree (augmentedBasis b F hF)
        (normalWordEquiv F R hlt hchain) (product_perm b F hF R hlt hchain)) :=
  QuadraticWordPBW.hasDiagonalTor (augmentation b F hF) (augmentedBasis b F hF)
    (augmentedBasis_none b F hF) (augmentation_positive b F hF)
    (normalWordEquiv F R hlt hchain) (normal_product b F hF R hlt hchain)
    (product_perm b F hF R hlt hchain)

end PaperVerification.ExteriorMonomialKoszul
