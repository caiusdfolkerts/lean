module

public import ToricPower.CochainFiniteSupport
public import ToricPower.SerrePairingBiproduct
public import Mathlib.Algebra.Homology.Functor

/-!
# The signed pairing of actual Hom cochains

A bounded complex of objects carrying compatible Serre pairings pairs
with an arbitrary complex. In each degree the finite-product duality is
an actual linear equivalence. The sign is the sign of the degree of
the bounded target term; it is essential for the Hom differential.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex
open scoped BigOperators

namespace ToricPower.SerrePairing

universe u v r
variable (k : Type r) [Field k]
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear k A]

def degreeSignEquiv (M : Type v) [AddCommGroup M] [Module k M] (q : ℤ) : M ≃ₗ[k] M where
  toFun x := q.negOnePow • x
  invFun x := q.negOnePow • x
  left_inv x := by
    change q.negOnePow • (q.negOnePow • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  right_inv x := by
    change q.negOnePow • (q.negOnePow • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

variable (T : A ⥤ A) [T.Additive]

abbrev mappedCochainComplex (J : CochainComplex A ℤ) : CochainComplex A ℤ :=
  (T.mapHomologicalComplex (.up ℤ)).obj J

def finiteCochainPairingEquiv (J : CochainComplex A ℤ)
    (pairing : ∀ q, CodomainPairing k T (J.X q)) (E : CochainComplex A ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q)) (n : ℤ) :
    Cochain E J n ≃ₗ[k] Module.Dual k (Cochain (mappedCochainComplex T J) E (-n)) := by
  let right : Cochain (mappedCochainComplex T J) E (-n) ≃ₗ[k]
      ∀ q : support, T.obj (J.X q) ⟶ E.X (q.val - n) :=
    cochainFiniteSourceValues k (mappedCochainComplex T J) E (-n) support
      (fun q h => T.map_isZero (outside q h))
  exact (cochainFiniteTargetValues k E J n support outside).trans
    ((LinearEquiv.piCongrRight fun q : support =>
        ((pairing q).equiv (E.X (q.val - n))).trans
          (degreeSignEquiv k _ q.val)).trans
      ((LinearMap.lsum k (fun q : support => T.obj (J.X q) ⟶ E.X (q.val - n)) k).trans
        right.dualMap))

theorem finiteCochainPairingEquiv_apply (J : CochainComplex A ℤ)
    (pairing : ∀ q, CodomainPairing k T (J.X q)) (E : CochainComplex A ℤ)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q)) (n : ℤ)
    (f : Cochain E J n) (g : Cochain (mappedCochainComplex T J) E (-n)) :
    finiteCochainPairingEquiv k T J pairing E support outside n f g =
      ∑ q : support, q.val.negOnePow •
        (pairing q).equiv (E.X (q.val - n))
          (f.v (q.val - n) q.val (by omega))
          (g.v q.val (q.val - n) (by omega)) := by
  simp only [finiteCochainPairingEquiv, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_apply, LinearEquiv.piCongrRight_apply,
    LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, cochainFiniteTargetValues_apply,
    cochainFiniteSourceValues_apply, degreeSignEquiv, LinearEquiv.coe_mk,
    LinearEquiv.coe_coe, LinearMap.smul_apply]
  rfl

end ToricPower.SerrePairing

end
