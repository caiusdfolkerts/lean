module

public import PaperVerification.ToricCartierCharacterModules
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

@[expose] public section

/-!
# Rank-one principal chart modules and the actual transition units

The local module is a module over its genuine semigroup chart algebra.
Multiplication by its Laurent character gives an explicit linear
equivalence with that chart algebra. On overlaps, agreeing Cartier
pairings give an actual unit and its explicit inverse.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Classical

variable (k : Type*) [CommSemiring k]
variable {G : Type*} [AddCommGroup G]

def principalChartGeneratorMap (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S →ₗ[monoidChartAlgebra k S] AddMonoidAlgebra k G :=
  (LinearMap.mul (monoidChartAlgebra k S) (AddMonoidAlgebra k G)
    (single v (1 : k))).comp
      (Algebra.linearMap (monoidChartAlgebra k S) (AddMonoidAlgebra k G))

@[simp] theorem principalChartGeneratorMap_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    principalChartGeneratorMap k S v f = single v (1 : k) * (f : AddMonoidAlgebra k G) := rfl

theorem principalChartGeneratorMap_injective (S : AddSubmonoid G) (v : G) :
    Function.Injective (principalChartGeneratorMap k S v) :=
  (characterTranslation k v).injective.comp Subtype.val_injective

def principalChartModule (S : AddSubmonoid G) (v : G) :
    Submodule (monoidChartAlgebra k S) (AddMonoidAlgebra k G) :=
  LinearMap.range (principalChartGeneratorMap k S v)

/-- Actual rank-one local triviality, over the chart algebra itself. -/
def principalChartTrivialization (S : AddSubmonoid G) (v : G) :
    monoidChartAlgebra k S ≃ₗ[monoidChartAlgebra k S] principalChartModule k S v :=
  LinearEquiv.ofInjective (principalChartGeneratorMap k S v)
    (principalChartGeneratorMap_injective k S v)

@[simp] theorem principalChartTrivialization_apply (S : AddSubmonoid G) (v : G)
    (f : monoidChartAlgebra k S) :
    ((principalChartTrivialization k S v f : principalChartModule k S v) :
      AddMonoidAlgebra k G) = single v (1 : k) * f := rfl

theorem principalChartModule_restrictScalars (S : AddSubmonoid G) (v : G) :
    (principalChartModule k S v).restrictScalars k =
      (characterModule k (S : Set G)).map (characterTranslation k v).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨(g : AddMonoidAlgebra k G), ?_, rfl⟩
    rw [← monoidChartAlgebra_toSubmodule k S]
    exact g.property
  · rintro ⟨g, hg, rfl⟩
    have hg' : g ∈ monoidChartAlgebra k S := by
      change g ∈ (monoidChartAlgebra k S).toSubmodule
      rw [monoidChartAlgebra_toSubmodule]
      exact hg
    exact ⟨⟨g, hg'⟩, rfl⟩

/-- A character and its inverse both in the semigroup give an actual
unit of the chart algebra, not merely a unit in the ambient function field. -/
def chartCharacterUnit (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) : (monoidChartAlgebra k S)ˣ where
  val := ⟨single v (1 : k), ⟨single ⟨v, hv⟩ (1 : k), by simp⟩⟩
  inv := ⟨single (-v) (1 : k), ⟨single ⟨-v, hneg⟩ (1 : k), by simp⟩⟩
  val_inv := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]
  inv_val := by apply Subtype.ext; simp [← AddMonoidAlgebra.one_def]

@[simp] theorem chartCharacterUnit_val (S : AddSubmonoid G) (v : G)
    (hv : v ∈ S) (hneg : -v ∈ S) :
    (((chartCharacterUnit k S v hv hneg : (monoidChartAlgebra k S)ˣ) :
      monoidChartAlgebra k S) : AddMonoidAlgebra k G) = single v (1 : k) := rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (k : Type*) [CommSemiring k]

/-- The difference of two actual Cartier characters pairs to zero on
the intersection cone, so it and its negative are both regular there. -/
theorem cartier_difference_mem_overlap (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    «Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) ∧
    -(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) ∈
      dualConeMonoid ((s : Finset (Lattice n)) ∩ t) := by
  have hz (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n)) ∩ t) :
      integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) = 0 := by
    rw [integerPairing_sub,
      «Σ».cartierLatticePoint_pairing a s u (Finset.mem_inter.mp hu).1,
      «Σ».cartierLatticePoint_pairing a t u (Finset.mem_inter.mp hu).2, sub_self]
  constructor
  · intro u hu
    rw [hz u hu]
  · intro u hu
    have he : integerPairing u (-(«Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)) =
        -integerPairing u («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) := by
      simp only [integerPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [he, hz u hu, neg_zero]

def cartierTransitionUnit (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ :=
  chartCharacterUnit k _ («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t)
    («Σ».cartier_difference_mem_overlap a s t).1
    («Σ».cartier_difference_mem_overlap a s t).2

theorem cartierTransitionUnit_character (a : Lattice n → ℤ) (s t : «Σ».fullCones) :
    (((«Σ».cartierTransitionUnit k a s t :
      (monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t)))ˣ) :
      monoidChartAlgebra k (dualConeMonoid ((s : Finset (Lattice n)) ∩ t))) :
      AddMonoidAlgebra k (Lattice n)) =
        single («Σ».cartierLatticePoint a s - «Σ».cartierLatticePoint a t) (1 : k) := rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricCharacters.principalChartTrivialization
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierTransitionUnit
