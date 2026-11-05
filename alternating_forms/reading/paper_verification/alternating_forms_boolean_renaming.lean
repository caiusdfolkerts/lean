module

public import PaperVerification.AlternatingFormsBooleanQuotient
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finset.Sort

/-!
# Honest variable renaming for Boolean quotient pieces

Renaming transports the actual square ideal and the two linear equations,
then restricts the induced algebra equivalence to the literal homogeneous
pieces.  Parameter polynomials also pull back injectively along an inclusion
of a selected variable set into a larger set.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanQuotient

open scoped BigOperators
open MvPolynomial

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

theorem rename_linearForm (e : ι ≃ κ) (b : ι → K) :
    renameEquiv K e (linearForm b) = linearForm (fun j => b (e.symm j)) := by
  simp only [linearForm, map_sum, map_smul, renameEquiv_apply, rename_X]
  apply Fintype.sum_equiv e
  intro i
  simp only [Equiv.symm_apply_apply]

theorem map_squareIdeal_rename (e : ι ≃ κ) :
    (squareIdeal (K := K) (ι := ι)).map (renameEquiv K e).toRingHom =
      squareIdeal (K := K) (ι := κ) := by
  change Ideal.map (renameEquiv K e).toRingHom (Ideal.span
    (Set.range fun i : ι => (X i : MvPolynomial ι K) ^ 2)) =
      Ideal.span (Set.range fun j : κ => (X j : MvPolynomial κ K) ^ 2)
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
    exact ⟨e i, by simp [renameEquiv_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(X (e.symm j) : MvPolynomial ι K) ^ 2, ⟨e.symm j, rfl⟩,
      by simp [renameEquiv_apply]⟩

theorem map_quotientIdeal_rename (e : ι ≃ κ) (b c : ι → K) :
    (quotientIdeal b c).map (renameEquiv K e).toRingHom =
      quotientIdeal (fun j => b (e.symm j)) (fun j => c (e.symm j)) := by
  rw [quotientIdeal, Ideal.map_sup, map_squareIdeal_rename, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change squareIdeal ⊔ Ideal.span ({renameEquiv K e (linearForm b),
    renameEquiv K e (linearForm c)} : Set (MvPolynomial κ K)) = _
  rw [rename_linearForm, rename_linearForm]
  rfl

def quotientRenameEquiv (e : ι ≃ κ) (b c : ι → K) :
    QuotientRing b c ≃ₐ[K]
      QuotientRing (fun j => b (e.symm j)) (fun j => c (e.symm j)) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv K e) (map_quotientIdeal_rename e b c).symm

@[simp] theorem quotientRenameEquiv_mk (e : ι ≃ κ) (b c : ι → K)
    (p : MvPolynomial ι K) :
    quotientRenameEquiv e b c (Ideal.Quotient.mk (quotientIdeal b c) p) =
      Ideal.Quotient.mk (quotientIdeal (fun j => b (e.symm j)) (fun j => c (e.symm j)))
        (renameEquiv K e p) := rfl

theorem map_piece_rename (e : ι ≃ κ) (b c : ι → K) (q : ℕ) :
    (piece b c q).map (quotientRenameEquiv e b c).toLinearMap =
      piece (fun j => b (e.symm j)) (fun j => c (e.symm j)) q := by
  ext z
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨renameEquiv K e p, hp.rename_isHomogeneous, ?_⟩
    exact (quotientRenameEquiv_mk e b c p).symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Ideal.Quotient.mk (quotientIdeal b c) (renameEquiv K e.symm p),
      ⟨renameEquiv K e.symm p, hp.rename_isHomogeneous, rfl⟩, ?_⟩
    change quotientRenameEquiv e b c
      (Ideal.Quotient.mk (quotientIdeal b c) (renameEquiv K e.symm p)) =
      Ideal.Quotient.mk (quotientIdeal (fun j => b (e.symm j)) (fun j => c (e.symm j))) p
    rw [quotientRenameEquiv_mk, ← renameEquiv_symm, AlgEquiv.apply_symm_apply]

def pieceRenameEquiv (e : ι ≃ κ) (b c : ι → K) (q : ℕ) :
    piece b c q ≃ₗ[K] piece (fun j => b (e.symm j)) (fun j => c (e.symm j)) q :=
  (quotientRenameEquiv e b c).toLinearEquiv.ofSubmodules _ _ (map_piece_rename e b c q)

theorem finrank_piece_rename (e : ι ≃ κ) (b c : ι → K) (q : ℕ) :
    Module.finrank K (piece b c q) =
      Module.finrank K (piece (fun j => b (e.symm j)) (fun j => c (e.symm j)) q) :=
  (pieceRenameEquiv e b c q).finrank_eq

def pairVariableEmbedding (e : ι ↪ κ) : (Bool × ι) ↪ (Bool × κ) where
  toFun z := (z.1, e z.2)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun z : Bool × κ => z.1) h
    · exact e.injective (congrArg (fun z : Bool × κ => z.2) h)

theorem pairParameterRename_injective (e : ι ↪ κ) :
    Function.Injective (MvPolynomial.rename (pairVariableEmbedding e) :
      MvPolynomial (Bool × ι) K → MvPolynomial (Bool × κ) K) :=
  MvPolynomial.rename_injective _ (pairVariableEmbedding e).injective

theorem pairParameterRename_ne_zero (e : ι ↪ κ)
    {p : MvPolynomial (Bool × ι) K} (hp : p ≠ 0) :
    MvPolynomial.rename (pairVariableEmbedding e) p ≠ 0 := by
  intro hz
  apply hp
  apply pairParameterRename_injective e
  simpa only [map_zero] using hz

def pairParameterEvaluation (b c : ι → K) : MvPolynomial (Bool × ι) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun z => if z.1 then c z.2 else b z.2)

theorem pairParameterEvaluation_rename (e : ι ↪ κ) (b c : κ → K)
    (p : MvPolynomial (Bool × ι) K) :
    pairParameterEvaluation b c (MvPolynomial.rename (pairVariableEmbedding e) p) =
      pairParameterEvaluation (fun i => b (e i)) (fun i => c (e i)) p := by
  have he : (pairParameterEvaluation b c).comp
      (MvPolynomial.rename (pairVariableEmbedding e)).toRingHom =
        pairParameterEvaluation (fun i => b (e i)) (fun i => c (e i)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [pairParameterEvaluation]
    · intro i
      simp [pairParameterEvaluation, pairVariableEmbedding]
  exact RingHom.congr_fun he p

end PaperVerification.AlternatingForms.BooleanQuotient
