module

public import Unimodular.Geometry

public import Continuation.Divisor.AnticanonicalBundle

/-!
# Literal anticanonical divisibility from an integral character relation

An equality of boundary coefficients modulo an actual integral character
is converted into an isomorphism of ordinary line bundles. The character
multiplies the local rational generators, and the coefficient multiple
is compared with the ordinary sheaf tensor power. The result concerns
the intrinsic dual canonical bundle, not only a formal divisor vector.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

lemma integerPairing_comm (m u : Lattice n) : integerPairing m u = integerPairing u m := by
  unfold integerPairing
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Integral character translation changes the local Cartier equation by
that same character on every chart. The coefficient hypothesis is only
on the actual fan rays, as for an ordinary invariant divisor. -/
lemma cartierLatticePoint_of_character_difference
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ u ∈ F.rays, b u = a u + integerPairing m u)
    (s : F.fullCones) :
    F.cartierLatticePoint b s = F.cartierLatticePoint a s - m := by
  symm
  apply F.eq_cartierLatticePoint_of_pairings
  intro u hu
  rw [integerPairing_sub, F.cartierLatticePoint_pairing a s u hu,
    h u (F.ray_mem_of_mem_cone (F.fullCones_mem s) hu), integerPairing_comm m u]
  simp only [Unimodular.integerPairing, PaperVerification.ToricGeometry.integerPairing]
  ring

lemma fanCartierCocycle_of_character_difference
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ u ∈ F.rays, b u = a u + integerPairing m u) :
    F.fanCartierCocycle k F.isPure b =
      (F.fanCartierCocycle k F.isPure a).scale (F.rationalCharacter k m)⁻¹ := by
  unfold PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierCocycle
    RationalCartierCocycle.scale
  congr 1
  funext i
  change F.rationalCharacter k (F.cartierLatticePoint b i.down) =
    (F.rationalCharacter k m)⁻¹ *
      F.rationalCharacter k (F.cartierLatticePoint a i.down)
  rw [cartierLatticePoint_of_character_difference F a b m h,
    F.rationalCharacter_sub k]
  exact div_eq_inv_mul _ _

/-- Character translation gives an actual sheaf isomorphism by rational
multiplication on the original open cover. -/
def fanSheafIsoOfCharacterDifference
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ u ∈ F.rays, b u = a u + integerPairing m u) :
    (F.fanCartierData k F.isPure b).sheaf ≅
      (F.fanCartierData k F.isPure a).sheaf :=
  eqToIso (congrArg RationalCartierCocycle.sheaf
      (fanCartierCocycle_of_character_difference F k a b m h)) ≪≫
    ((F.fanCartierCocycle k F.isPure a).scaleSheafIso
      (F.rationalCharacter k m)⁻¹).symm

/-- A literal coefficient relation yields divisibility of the actual
anticanonical line bundle in the ordinary Picard group: an explicit
ordinary tensor power is isomorphic to the intrinsic dual canonical
bundle. This includes every nonnegative exponent. -/
def anticanonicalTensorPowerIso (d : ℕ) (D : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ u ∈ F.rays, (1 : ℤ) = (d : ℤ) * D u + integerPairing m u) :
    (anticanonicalLineBundle F k).obj ≅
      tensorSheafPower (F.fanCartierData k F.isPure D).sheaf d := by
  have he : ∀ u ∈ F.rays, (1 : ℤ) = (d • D) u + integerPairing m u := by
    simpa only [Pi.smul_apply, nsmul_eq_mul] using h
  let e := fanSheafIsoOfCharacterDifference F k (d • D) (fun _ => 1) m he
  let C := F.fanCartierCocycle k F.isPure D
  have hp : (C.pow d).sheaf = (F.fanCartierData k F.isPure (d • D)).sheaf :=
    congrArg RationalCartierCocycle.sheaf (fanCartierCocycle_pow F k D d)
  exact anticanonical_unitBoundaryIso F k ≪≫ e ≪≫
    (eqToIso hp).symm ≪≫ (C.tensorSheafPowerIso d).symm

#print axioms fanSheafIsoOfCharacterDifference
#print axioms anticanonicalTensorPowerIso

end Unimodular.NefBig
