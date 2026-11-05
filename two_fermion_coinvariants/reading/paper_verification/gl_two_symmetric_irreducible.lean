module

public import PaperVerification.GLTwoSymmetricCoordinates
public import PaperVerification.GLTwoSchurCharacter
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.CharacterTwist
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Irreducibility and distinctness of the genuine binary Schur representations

The pinned Tau Ceti theorem proves irreducibility of the actual SU(2)
symmetric-power restriction. The preceding elementary restriction lemma
therefore proves irreducibility for the actual GL₂ action. Determinant
twisting preserves it. Dimension and the value of the character at diag(2,1)
distinguish every pair of labels, including zero labels.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorSchur

open PaperVerification.GLTwoSymmetricCoordinates

/-- Each displayed Schur summand is the genuine irreducible representation. -/
theorem schurRepresentation_irreducible (a b : ℕ) :
    Representation.IsIrreducible (k := ℂ) (V := SchurSpace ℂ a b)
      (schurRepresentation ℂ a b) := by
  let χ := (Matrix.GeneralLinearGroup.det :
    Matrix.GeneralLinearGroup (Fin 2) ℂ →* ℂˣ)^(b : ℤ)
  have h := (Representation.isIrreducible_charTwist_iff χ
    (TauCeti.symPowerRep ℂ 2 a)).mpr (symmetricPower_irreducible a)
  let e := Representation.tprodOfLinearCharacterEquivCharTwist χ
    (TauCeti.symPowerRep ℂ 2 a)
  rw [schurRepresentation,TauCeti.detPowerRep_def]
  exact Representation.isIrreducible_of_linearEquiv e.symm.toLinearEquiv
    (fun g v ↦ Representation.IntertwiningMap.isIntertwining _ _
      e.symm.toIntertwiningMap g v) h

theorem schurSpace_finrank (F : Type) [Field F] (a b : ℕ) :
    Module.finrank F (SchurSpace F a b)=a+1 := by
  rw [(TensorProduct.rid F (Space F a)).finrank_eq]
  rw [SymmetricPower.finrank_eq,Module.finrank_fin_fun,Nat.multichoose_two]

/-- Distinct labels give nonisomorphic actual representations. -/
theorem schurRepresentation_labels_of_equiv (a b a' b' : ℕ)
    (e : (schurRepresentation ℂ a b).Equiv (schurRepresentation ℂ a' b')) :
    a=a' ∧ b=b' := by
  have ha : a=a' := by
    have h := e.toLinearEquiv.finrank_eq
    rw [schurSpace_finrank,schurSpace_finrank] at h
    omega
  subst a'
  have hchar := congrFun (Representation.char_iso (k := ℂ)
    (V := SchurSpace ℂ a b) (W := SchurSpace ℂ a b') e)
      (TauCeti.diagGL (twoTorus ℂ))
  rw [schurRepresentation_character,schurRepresentation_character] at hchar
  have hpow : (2 : ℂ)^b=(2 : ℂ)^b' := by
    have hs : (∑ i ∈ Finset.range (a+1), (2 : ℂ)^i)≠0 := by
      have hn : 0<∑ i ∈ Finset.range (a+1), (2 : ℕ)^i := by
        exact Finset.sum_pos (fun i _ ↦ Nat.pow_pos (by decide))
          ⟨0,Finset.mem_range.mpr (Nat.succ_pos _)⟩
      exact_mod_cast hn.ne'
    apply mul_right_cancel₀ hs
    simpa [schurValue,twoTorus,twoUnit] using hchar
  have hn : (2 : ℕ)^b=(2 : ℕ)^b' := by exact_mod_cast hpow
  exact ⟨rfl,Nat.pow_right_injective (by decide : 2≤2) hn⟩

theorem schurRepresentation_equiv_iff (a b a' b' : ℕ) :
    Nonempty ((schurRepresentation ℂ a b).Equiv (schurRepresentation ℂ a' b')) ↔
      a=a' ∧ b=b' := by
  constructor
  · rintro ⟨e⟩
    exact schurRepresentation_labels_of_equiv a b a' b' e
  · rintro ⟨rfl,rfl⟩
    exact ⟨Representation.Equiv.refl _⟩

end PaperVerification.Fermion.ColorSchur
