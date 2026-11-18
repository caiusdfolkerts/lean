module

public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing
public import Recovery.Unimodular.GraphicSectionRing.GradedCharacters
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPolyhedronBounds

/-!
# The genuine toric section ring and its full graded lattice semigroup

Every homogeneous coefficient is an actual global section of the ordinary
Cartier tensor power. The all-degree character dictionary is proved from the
actual sheaf on the glued smooth complete fan scheme. No normal generation,
nefness, projectivity, or homological statement is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open Unimodular.GraphicSectionRing
open scoped BaseSections Pointwise

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

 theorem cartierLatticePoint_zero (s : F.fullCones) :
    F.cartierLatticePoint (0 : Lattice n → ℤ) s = 0 := by
  symm
  apply F.eq_cartierLatticePoint_of_pairings
  intro v hv
  simp [integerPairing]

 theorem cartierLatticePoint_nsmul (a : Lattice n → ℤ) (s : F.fullCones) (d : ℕ) :
    F.cartierLatticePoint (d • a) s = d • F.cartierLatticePoint a s := by
  induction d with
  | zero => simp [cartierLatticePoint_zero]
  | succ d ih => rw [succ_nsmul, cartierLatticePoint_add_coefficients, ih, succ_nsmul]

 theorem rationalCharacter_nsmul (m : Lattice n) (d : ℕ) :
    F.rationalCharacter k (d • m) = F.rationalCharacter k m ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, rationalCharacter_add, ih, pow_succ]

/-- Powers of the actual local Cartier generators are exactly the integral
coefficient multiples, on the same genuine affine chart cover. -/
theorem fanCartierCocycle_pow (a : Lattice n → ℤ) (d : ℕ) :
    (F.fanCartierCocycle k F.isPure a).pow d =
      F.fanCartierCocycle k F.isPure (d • a) := by
  unfold RationalCartierCocycle.pow fanCartierCocycle
  congr 1
  funext i
  rw [cartierLatticePoint_nsmul, rationalCharacter_nsmul]

/-- The original lattice-exponent semigroup in every degree, including zero. -/
def fanSectionSemigroup (a : Lattice n → ℤ) : AddSubmonoid (ℕ × Lattice n) where
  carrier := {z | z.2 ∈ F.fanIntegralExponents (z.1 • a)}
  zero_mem' := by
    change (0 : Lattice n) ∈ F.fanIntegralExponents (0 • a)
    simp only [zero_smul]
    change (0 : Lattice n) ∈ F.fanIntegralExponents (fun _ => 0)
    rw [F.fanIntegralExponents_zero]
    rfl
  add_mem' := by
    intro x y hx hy
    have h := F.fanIntegralExponents_add_subset (x.1 • a) (y.1 • a)
      (Set.mem_add.mpr ⟨x.2, hx, y.2, hy, rfl⟩)
    change x.2 + y.2 ∈ F.fanIntegralExponents ((x.1 + y.1) • a)
    rw [add_nsmul]
    exact h

 theorem fanSectionSemigroup_degree_zero (a : Lattice n → ℤ) (m : Lattice n) :
    (0, m) ∈ F.fanSectionSemigroup a ↔ m = 0 := by
  change m ∈ F.fanIntegralExponents (0 • a) ↔ _
  rw [zero_smul]
  change m ∈ F.fanIntegralExponents (fun _ => 0) ↔ m = 0
  rw [F.fanIntegralExponents_zero]
  rfl

/-- The actual degree-d rational values equal precisely the allowed Laurent
character polynomials. This statement covers every d, including d=0. -/
theorem fan_powerValues_eq_characterRange (a : Lattice n → ℤ) (d : ℕ) :
    ActualSections.powerValues k (F.fanCartierCocycle k F.isPure a) d =
      (F.fanCharacterValue k (d • a)).range := by
  unfold ActualSections.powerValues
  rw [F.fanCartierCocycle_pow k a d]
  exact F.fanCartier_globalSectionValue_range k F.isPure (d • a)

 theorem fan_powerValues_iff_character (a : Lattice n → ℤ) (d : ℕ)
    (r : (F.fanScheme k).functionField) :
    r ∈ ActualSections.powerValues k (F.fanCartierCocycle k F.isPure a) d ↔
      ∃ q : AddMonoidAlgebra k (Lattice n),
        (∀ m, (d, m) ∉ F.fanSectionSemigroup a → q.coeff m = 0) ∧
        F.torusRationalAlgHom k q = r := by
  rw [F.fan_powerValues_eq_characterRange k a d]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.val, ?_, hq⟩
    exact (AddMonoidAlgebra.mem_supported').mp q.property
  · rintro ⟨q, hq, heq⟩
    refine ⟨⟨q, ?_⟩, heq⟩
    exact (AddMonoidAlgebra.mem_supported').mpr hq

/-- A proved isomorphism from the full lattice semigroup algebra to the
independently defined genuine section ring, with its actual multiplication. -/
def fanSectionRingEquiv (a : Lattice n → ℤ) :
    AddMonoidAlgebra k (F.fanSectionSemigroup a) ≃ₐ[k]
      ActualSections.sectionRing k (F.fanCartierCocycle k F.isPure a) :=
  GradedCharacters.equivActual (F.fanSectionSemigroup a) (F.torusRationalAlgHom k)
    (F.torusRationalAlgHom_injective k)
    (ActualSections.sectionRing k (F.fanCartierCocycle k F.isPure a)) (by
      intro p
      change (∀ d, p.coeff d ∈ ActualSections.powerValues k
        (F.fanCartierCocycle k F.isPure a) d) ↔ _
      exact forall_congr' (fun d => F.fan_powerValues_iff_character k a d (p.coeff d)))

#print axioms fanCartierCocycle_pow
#print axioms fanSectionSemigroup_degree_zero
#print axioms fan_powerValues_iff_character
#print axioms fanSectionRingEquiv

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.fanSectionRingEquiv
