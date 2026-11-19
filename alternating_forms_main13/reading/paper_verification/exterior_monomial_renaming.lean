module

public import PaperVerification.ExteriorMonomialQuotient
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Hom.Basic

/-!
# Order-preserving renaming of actual exterior monomial quotients

The renaming identifies literal exterior products and ordinary generated
ideals. In particular it permits a finite index type to be lifted to the
universe of the coefficient field without changing the algebra, its
relations, or its original degrees.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.ExteriorMonomialQuotient

variable {K M I J : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder I] [LinearOrder J]
  (b : Module.Basis I K M) (e : J ≃o I) (F : Set (Finset I))

def renamedForbidden : Set (Finset J) := {S | S.map e.toEquiv.toEmbedding ∈ F}

@[simp] theorem map_inverse (S : Finset I) :
    (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding=S := by
  rw [Finset.map_map]
  have he : e.symm.toEquiv.toEmbedding.trans e.toEquiv.toEmbedding=
      Function.Embedding.refl I := by
    apply Function.Embedding.ext
    intro i
    exact e.apply_symm_apply i
  rw [he,Finset.map_refl]

theorem renamed_bad (S : Finset J) :
    Bad (renamedForbidden e F) S ↔ Bad F (S.map e.toEquiv.toEmbedding) := by
  constructor
  · rintro ⟨T,hT,hTS⟩
    exact ⟨T.map e.toEquiv.toEmbedding,hT,Finset.map_subset_map.mpr hTS⟩
  · rintro ⟨T,hT,hTS⟩
    refine ⟨T.map e.symm.toEquiv.toEmbedding,?_,?_⟩
    · change (T.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding∈F
      rw [map_inverse]
      exact hT
    · apply (Finset.map_subset_map (f := e.toEquiv.toEmbedding)).mp
      rw [map_inverse]
      exact hTS

theorem renamedForbidden_nonempty (hF : ∀ S∈F,S.Nonempty) :
    ∀ S∈renamedForbidden e F,S.Nonempty := by
  intro S hS
  exact Finset.map_nonempty.mp (hF (S.map e.toEquiv.toEmbedding) hS)

theorem sort_renamed (S : Finset J) :
    S.sort.map e=(S.map e.toEquiv.toEmbedding).sort := by
  exact Finset.map_sort e.toEquiv.toEmbedding S (· ≤ ·) (· ≤ ·)
    (fun a _ b _ => e.le_iff_le.symm)

/-- An increasing reindexing changes the index set but introduces no
exterior sign. Both sides are the same ordered generator product. -/
theorem exteriorBasis_reindex (S : Finset J) :
    (b.reindex e.toEquiv.symm).ExteriorAlgebra S=
      b.ExteriorAlgebra (S.map e.toEquiv.toEmbedding) := by
  rw [(b.reindex e.toEquiv.symm).exteriorAlgebra_eq_prod_map_sort,
    b.exteriorAlgebra_eq_prod_map_sort,←sort_renamed e S]
  simp only [List.map_map,Module.Basis.coe_reindex,Equiv.symm_symm]
  rfl

/-- Equality of the ordinary generated ideals under this genuine basis
reindexing. The quotient is not redefined by a combinatorial rule. -/
theorem monomialIdeal_reindex :
    monomialIdeal (b.reindex e.toEquiv.symm) (renamedForbidden e F)=
      monomialIdeal b F := by
  unfold monomialIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨S,hS,rfl⟩
    exact ⟨S.map e.toEquiv.toEmbedding,hS,(exteriorBasis_reindex b e S).symm⟩
  · rintro ⟨S,hS,rfl⟩
    refine ⟨S.map e.symm.toEquiv.toEmbedding,?_,?_⟩
    · change (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding∈F
      rw [map_inverse]
      exact hS
    · rw [exteriorBasis_reindex,map_inverse]

def renamedRelation (R : I→I→Prop) : J→J→Prop := fun i j => R (e i) (e j)

instance renamedRelation_trans (R : I→I→Prop) [IsTrans I R] :
    IsTrans J (renamedRelation e R) where
  trans a b c hab hbc := IsTrans.trans (e a) (e b) (e c) hab hbc

theorem renamedRelation_increasing (R : I→I→Prop)
    (hlt : ∀ i j,R i j→i<j) : ∀ i j,renamedRelation e R i j→i<j := by
  intro i j h
  exact e.lt_iff_lt.mp (hlt (e i) (e j) h)

theorem renamed_chain (R : I→I→Prop)
    (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R) :
    ∀ S : Finset J,¬Bad (renamedForbidden e F) S↔S.sort.IsChain (renamedRelation e R) := by
  intro S
  rw [renamed_bad,hchain,←sort_renamed e S]
  exact List.isChain_map e

end PaperVerification.ExteriorMonomialQuotient
