module

public import ToricPower.FiniteTriangularAcyclic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite signed total complexes

The rows are genuine, arbitrarily unbounded complexes. The remaining
differential is strictly upper triangular in their finite index and
satisfies the two bicomplex identities. All terms of the total are the
actual finite categorical biproducts. Exactness after any additive
module-valued functor follows by finite triangular elimination.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.FiniteTotal

universe u v r w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {width : ℕ} (row : Fin width → CochainComplex C ℤ)

abbrev term (a : ℤ) : C := ⨁ fun q : Fin width => (row q).X a

def diagonal (a : ℤ) : term row a ⟶ term row (a+1) :=
  biproduct.map (fun q : Fin width => (row q).d a (a+1))

theorem diagonal_sq (a : ℤ) : diagonal row a ≫ diagonal row (a+1) = 0 := by
  apply biproduct.hom_ext
  intro q
  simp [diagonal,Category.assoc]

variable (off : ∀ a : ℤ, term row a ⟶ term row (a+1))

/-- These are the actual anticommutation and square-zero identities for
the horizontal part of a signed total differential. -/
structure Coherent : Prop where
  anticommute : ∀ a : ℤ,
    diagonal row a ≫ off (a+1) + off a ≫ diagonal row (a+1) = 0
  square : ∀ a : ℤ, off a ≫ off (a+1) = 0

def differential (a : ℤ) : term row a ⟶ term row (a+1) :=
  diagonal row a + off a

theorem differential_sq (coherent : Coherent row off) (a : ℤ) :
    differential row off a ≫ differential row off (a+1) = 0 := by
  simp only [differential,add_comp,comp_add,diagonal_sq,coherent.square,zero_add,add_zero]
  simpa only [add_comm] using coherent.anticommute a

def complex (coherent : Coherent row off) : CochainComplex C ℤ :=
  CochainComplex.of (term row) (differential row off) (differential_sq row off coherent)

def StrictlyRaises : Prop :=
  ∀ (a : ℤ) (p q : Fin width), ¬p.val < q.val →
    biproduct.ι (fun r : Fin width => (row r).X a) p ≫ off a ≫
      biproduct.π (fun r : Fin width => (row r).X (a+1)) q = 0

variable {R : Type r} [Ring R] (F : C ⥤ ModuleCat.{w} R) [F.Additive]

/-- The projections of a finite biproduct remain jointly injective
after an additive functor. This uses the original biproduct identity. -/
theorem mapped_projections_injective (a : ℤ) :
    Function.Injective (fun z : F.obj (term row a) => fun q : Fin width =>
      F.map (biproduct.π (fun q : Fin width => (row q).X a) q) z) := by
  intro x y same
  have decomposition (z : F.obj (term row a)) :
      (∑ q : Fin width,
        F.map (biproduct.ι (fun q : Fin width => (row q).X a) q)
          (F.map (biproduct.π (fun q : Fin width => (row q).X a) q) z)) = z := by
    have h := congrArg (fun f : term row a ⟶ term row a => F.map f z)
      (biproduct.total (f := fun q : Fin width => (row q).X a))
    simpa only [F.map_sum,F.map_comp,F.map_id,ModuleCat.comp_apply,
      ModuleCat.hom_sum,LinearMap.sum_apply,ModuleCat.id_apply] using h
  rw [← decomposition x,← decomposition y]
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (fun z => F.map (biproduct.ι (fun q : Fin width => (row q).X a) q) z)
    (congrFun same q)

include F in
theorem mapped_insert_self (a : ℤ) (q : Fin width)
    (z : F.obj ((row q).X a)) :
    F.map (biproduct.π (fun q : Fin width => (row q).X a) q)
      (F.map (biproduct.ι (fun q : Fin width => (row q).X a) q) z) = z := by
  have h := congrArg (fun f : (row q).X a ⟶ (row q).X a => F.map f z)
    (biproduct.ι_π_self (fun q : Fin width => (row q).X a) q)
  simpa only [F.map_comp,F.map_id,ModuleCat.comp_apply,ModuleCat.id_apply] using h

theorem mapped_insert_lower (a : ℤ) (p q : Fin width) (lower : p.val < q.val)
    (z : F.obj ((row q).X a)) :
    F.map (biproduct.π (fun q : Fin width => (row q).X a) p)
      (F.map (biproduct.ι (fun q : Fin width => (row q).X a) q) z) = 0 := by
  have unequal : q ≠ p := by intro h; subst q; exact lt_irrefl _ lower
  have h := congrArg (fun f : (row q).X a ⟶ (row p).X a => F.map f z)
    (biproduct.ι_π_ne (fun q : Fin width => (row q).X a) unequal)
  simpa only [F.map_comp,F.map_zero,ModuleCat.comp_apply,ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

theorem mapped_off_zero (raises : StrictlyRaises row off)
    (a : ℤ) (q : Fin width) (z : F.obj (term row a))
    (lower : ∀ p : Fin width, p.val < q.val →
      F.map (biproduct.π (fun q : Fin width => (row q).X a) p) z = 0) :
    F.map (biproduct.π (fun q : Fin width => (row q).X (a+1)) q) (F.map (off a) z) = 0 := by
  have decomposition : off a ≫ biproduct.π (fun q : Fin width => (row q).X (a+1)) q =
      ∑ p : Fin width,
        biproduct.π (fun p : Fin width => (row p).X a) p ≫
          (biproduct.ι (fun p : Fin width => (row p).X a) p ≫ off a ≫
            biproduct.π (fun q : Fin width => (row q).X (a+1)) q) := by
    have h := congrArg
      (fun f : term row a ⟶ term row a =>
        f ≫ off a ≫ biproduct.π (fun q : Fin width => (row q).X (a+1)) q)
      (biproduct.total (f := fun q : Fin width => (row q).X a))
    simpa only [sum_comp,Category.assoc,Category.id_comp] using h.symm
  have h := congrArg (fun f : term row a ⟶ (row q).X (a+1) => F.map f z) decomposition
  simp only [F.map_sum,F.map_comp,ModuleCat.hom_sum,LinearMap.sum_apply,
    ModuleCat.comp_apply] at h
  rw [h]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p.val < q.val
  · simp only [lower p hp,map_zero]
  · have vanish := congrArg
      (fun f : (row p).X a ⟶ (row q).X (a+1) =>
        F.map f (F.map (biproduct.π (fun p : Fin width => (row p).X a) p) z))
      (raises a p q hp)
    simpa only [F.map_comp,F.map_zero,ModuleCat.comp_apply,ModuleCat.hom_zero,
      LinearMap.zero_apply] using vanish

/-- A signed total of finite width is acyclic whenever its actual rows
are acyclic after the indicated additive functor. -/
theorem mapped_complex_acyclic (coherent : Coherent row off)
    (raises : StrictlyRaises row off)
    (rowsAcyclic : ∀ q : Fin width,
      ((F.mapHomologicalComplex (.up ℤ)).obj (row q)).Acyclic) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (complex row off coherent)).Acyclic := by
  apply finiteTriangular_acyclic
    ((F.mapHomologicalComplex (.up ℤ)).obj (complex row off coherent))
    (fun q => (F.mapHomologicalComplex (.up ℤ)).obj (row q))
    (fun a q => F.map (biproduct.π (fun q : Fin width => (row q).X a) q))
    (fun a q => F.map (biproduct.ι (fun q : Fin width => (row q).X a) q))
    ?_ (mapped_insert_self row F) (mapped_insert_lower row F)
    (mapped_projections_injective row F) rowsAcyclic
  intro a q z lower
  change F.map (biproduct.π (fun q : Fin width => (row q).X (a+1)) q)
    (F.map ((complex row off coherent).d a (a+1)) z) = _
  change F.map (biproduct.π (fun q : Fin width => (row q).X (a+1)) q)
    (F.map (CochainComplex.of.d (term row) (differential row off) a (a+1)) z) = _
  rw [CochainComplex.of_d]
  have h := congrArg (fun f : term row a ⟶ (row q).X (a+1) => F.map f z)
    (biproduct.map_π (fun q : Fin width => (row q).d a (a+1)) q)
  simp only [F.map_comp,ModuleCat.comp_apply] at h
  simp only [differential,F.map_add,ModuleCat.hom_add,LinearMap.add_apply,map_add]
  rw [mapped_off_zero row off F raises a q z lower,add_zero]
  exact h

end ToricPower.FiniteTotal

end
