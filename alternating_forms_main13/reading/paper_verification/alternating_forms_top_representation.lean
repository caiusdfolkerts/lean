module

public import PaperVerification.AlternatingFormsTopWeightIdentity
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant

/-!
# The full representation statement of Corollary 5.2

The source representation acts on the literal bidegree of the quotient of
the exterior algebra by the two original quadrics.  Its construction,
including invariance of the ideal, is in `SymmetricPencilAction`.

The proof first identifies rational `GL₂` representations after the
necessary integral determinant twist.  It then restricts the actual
intertwining equivalence to `SL₂`, where that twist becomes trivial.
The case `p=q=0` is included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct
open Matrix

namespace PaperVerification.AlternatingForms.TopRepresentation

open SymmetricPencil TopInterlacing TauCeti

variable (K : Type) [Field K]

/-- The genuine iterated symmetric-power representation appearing in the
paper, before restriction from `GL₂` to `SL₂`. -/
def plethysmRepresentation (p q : ℕ) :
    Representation K (GL (Fin 2) K) (Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K))) :=
  (TauCeti.symPowerRep K 2 q).symmetricPower (2*p+1)

/-- Reversing the binary monomial basis makes its eigenvalues agree
directly with the interlacing coordinates.  This is a basis change within
the actual symmetric power. -/
def reversedBinaryBasis (q : ℕ) :
    Module.Basis (Fin (q+1)) K (Sym[K]^q (Fin 2 → K)) :=
  (binaryBasis K q).reindex (Fin.revPerm : Equiv.Perm (Fin (q+1)))

theorem reversedBinaryBasis_diagonal (q : ℕ) (u : Fin 2 → Kˣ) (i : Fin (q+1)) :
    TauCeti.symPowerRep K 2 q (TauCeti.diagGL u) (reversedBinaryBasis K q i) =
      ((u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val) : Kˣ) : K) •
        reversedBinaryBasis K q i := by
  simp only [reversedBinaryBasis,Module.Basis.reindex_apply,
    Fin.revPerm_symm,Fin.revPerm_apply]
  rw [binaryBasis_diagonal]
  congr 1
  have hi : i.val≤q := by have := i.isLt; omega
  have hrev : i.rev.val=q-i.val := by rw [Fin.val_rev]; omega
  simp only [bWeight,hrev]
  rw [Nat.cast_sub hi,show (q : ℤ)-((q : ℤ)-i.val)=i.val by ring]

theorem plethysm_character (p q : ℕ) (u : Fin 2 → Kˣ) :
    Representation.character (V := Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))
      (plethysmRepresentation K p q) (TauCeti.diagGL u) =
      ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  rw [Representation.character, plethysmRepresentation,
    Representation.symmetricPower_apply,
    Module.Basis.trace_map_symmetricPower_of_apply (reversedBinaryBasis K q)
      (TauCeti.symPowerRep K 2 q (TauCeti.diagGL u))
      (fun i => ((u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val) : Kˣ) : K)) (2*p+1)
      (reversedBinaryBasis_diagonal K q u)]
  apply Finset.sum_congr rfl
  intro S hS
  change _ = (Units.coeHom K)
    (((S : Multiset (Fin (q+1))).map
      (fun i => u 0^(i.val : ℤ)*u 1^((q : ℤ)-i.val))).prod)
  rw [map_multiset_prod, Multiset.map_map]
  rfl

/-- The `GL₂` target with the determinant power required by the central
character.  The untwisted assertion is only an `SL₂` assertion. -/
def twistedPlethysmRepresentation (p q : ℕ) :
    Representation K (GL (Fin 2) K)
      (K ⊗[K] (Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))) :=
  (TauCeti.detPowerRep K 2 (determinantTwist p q)).tprod
    (plethysmRepresentation K p q)

theorem twistedPlethysm_character (p q : ℕ) (u : Fin 2 → Kˣ) :
    (twistedPlethysmRepresentation K p q).character (TauCeti.diagGL u) =
      (((u 0*u 1)^(determinantTwist p q) : Kˣ) : K) *
        ∑ S : Sym (Fin (q+1)) (2*p+1), (symmetricWeight q (2*p+1) u S : K) := by
  have hc := congrFun
    (Representation.char_tensor (V := K)
      (W := Sym[K]^(2*p+1) (Sym[K]^q (Fin 2 → K)))
      (TauCeti.detPowerRep K 2 (determinantTwist p q))
      (plethysmRepresentation K p q)) (TauCeti.diagGL u)
  rw [Pi.mul_apply,TauCeti.char_detPowerRep,TauCeti.det_diagGL,Fin.prod_univ_two,
    plethysm_character] at hc
  exact hc

variable [CharZero K]

set_option maxHeartbeats 800000 in
theorem top_character_eq_twisted (p q : ℕ) (u : Fin 2 → Kˣ) :
    (naturalBigradedRepresentation K (p+q) p q).character (TauCeti.diagGL u) =
      (twistedPlethysmRepresentation K p q).character (TauCeti.diagGL u) := by
  rw [bigraded_character, twistedPlethysm_character]
  exact topWord_weight_sum p q u

theorem naturalBigraded_rational (k p q : ℕ) :
    TauCeti.IsRationalRep (naturalBigradedRepresentation ℂ k p q) := by
  cases k with
  | zero =>
      letI : Module.Finite ℂ (Bidegree.actualBigradedPiece (K := ℂ) 0 p q) :=
        Module.Finite.of_basis (bigradedBasis ℂ 0 p q)
      apply TauCeti.isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr
      intro f v
      change (fun _ : GL (Fin 2) ℂ => f v) ∈
        TauCeti.Matrix.GeneralLinearGroup.rationalFunctions ℂ 2
      exact (TauCeti.Matrix.GeneralLinearGroup.rationalFunctions ℂ 2).algebraMap_mem (f v)
  | succ t => exact RationalRepresentation.bigraded_rational t p q

theorem plethysm_rational (p q : ℕ) :
    TauCeti.IsRationalRep (plethysmRepresentation ℂ p q) :=
  ((TauCeti.isPolynomialRep_symPowerRep 2 q).symmetricPower (2*p+1)).isRationalRep

theorem twistedPlethysm_rational (p q : ℕ) :
    TauCeti.IsRationalRep (twistedPlethysmRepresentation ℂ p q) :=
  (TauCeti.isRationalRep_detPowerRep (determinantTwist p q)).tprod (plethysm_rational p q)

/-- The full auxiliary `GL₂` equivalence, with its essential determinant
twist.  It is obtained from proved rationality and equality of actual
characters, using rational complete reducibility over `ℂ`. -/
theorem top_gl2_equivalence (p q : ℕ) :
    Nonempty ((naturalBigradedRepresentation ℂ (p+q) p q).Equiv
      (twistedPlethysmRepresentation ℂ p q)) :=
  (naturalBigraded_rational (p+q) p q).nonempty_equiv_of_forall_character_diagGL_eq
    (twistedPlethysm_rational p q) (top_character_eq_twisted ℂ p q)

/-- Corollary 5.2's representation isomorphism for every `p,q ≥ 0`, on
the actual quotient piece `A_{p,q}` and the actual iterated symmetric
power.  No determinant twist remains after restriction to `SL₂`. -/
theorem paper_corollary_5_2_representation (p q : ℕ) :
    Nonempty
      (Representation.Equiv
        ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
        ((plethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL)) := by
  obtain ⟨e⟩ := top_gl2_equivalence p q
  let eSL :
      Representation.Equiv
      ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
      ((twistedPlethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL) :=
    .mk e.toLinearEquiv (fun g => e.isIntertwining' (Matrix.SpecialLinearGroup.toGL g))
  exact ⟨eSL.trans
    (TauCeti.tprodDetPowerSLEquiv ℂ 2 (determinantTwist p q) (plethysmRepresentation ℂ p q))⟩

/-- Both clauses of Corollary 5.2, with the complete parameter range. -/
theorem paper_corollary_5_2 (p q : ℕ) :
    Nonempty
      (Representation.Equiv
        ((naturalBigradedRepresentation ℂ (p+q) p q).comp Matrix.SpecialLinearGroup.toGL)
        ((plethysmRepresentation ℂ p q).comp Matrix.SpecialLinearGroup.toGL)) ∧
      Module.finrank ℂ (Bidegree.actualBigradedPiece (K := ℂ) (p+q) p q) =
        (2*p+q+1).choose q :=
  ⟨paper_corollary_5_2_representation p q, actual_top_bigraded_dimension p q⟩

end PaperVerification.AlternatingForms.TopRepresentation
