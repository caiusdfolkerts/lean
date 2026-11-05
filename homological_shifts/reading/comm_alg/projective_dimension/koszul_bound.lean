import CommAlg.KoszulComplex.Resolution
import CommAlg.Polymatroid.LinearQuotients
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Actual projective-dimension bounds from the finite Koszul resolution

These are bounds on Mathlib's Ext-defined projective dimension. No residue-Tor
vanishing criterion or local-ring hypothesis is used for the upper bound.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace CommAlg.ProjectiveDimension

universe u v w

theorem le_of_resolution {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {X : C} (P : ProjectiveResolution X) (N : ℕ)
    (h : ∀ n, N < n → IsZero (P.complex.X n)) :
    projectiveDimension X ≤ N := by
  rw [projectiveDimension_le_iff]
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hf0 : f = 0 := (h n (by omega)).eq_of_src _ _
  subst f
  exact P.extMk_zero (n + 1) rfl

variable {R : Type u} [CommRing R]

theorem exteriorPower_fin_isZero (m n : ℕ) (h : m < n) :
    IsZero (ModuleCat.of R (⋀[R]^n (Fin m → R))) := by
  letI : IsEmpty (Set.powersetCard (Fin m) n) := ⟨fun s => by
    have hc := Finset.card_le_univ s.val
    have he : s.val.card = n := s.property
    simp only [Fintype.card_fin] at hc
    omega⟩
  haveI : Subsingleton (⋀[R]^n (Fin m → R)) := ⟨fun x y =>
    ((Pi.basisFun R (Fin m)).exteriorPower n).repr.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

theorem regularSequence_quotient_le (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    projectiveDimension (ModuleCat.of R (R ⧸ Ideal.ofList l)) ≤ l.length := by
  letI := HasExt.standard (ModuleCat.{u} R)
  apply le_of_resolution (CommAlg.Koszul.regularSequenceResolution l hl) l.length
  intro n hn
  change IsZero (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
  exact exteriorPower_fin_isZero l.length n hn

variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem variableIdeal_quotient_le (A : Finset V) :
    projectiveDimension
      (ModuleCat.of (MvPolynomial V k)
        (MvPolynomial V k ⧸ CommAlg.Polymatroid.variableIdeal (k := k) A)) ≤ A.card := by
  let l : List (MvPolynomial V k) := A.toList.map MvPolynomial.X
  have hreg := CommAlg.Koszul.variables_regular (k := k) A.toList A.nodup_toList
  have he : Ideal.ofList l = CommAlg.Polymatroid.variableIdeal (k := k) A := by
    apply congrArg Ideal.span
    ext f
    simp [l, CommAlg.Polymatroid.variableIdeal]
  have h := regularSequence_quotient_le l hreg
  have hlen : l.length = A.card := by simp [l]
  rw [he, hlen] at h
  exact h

end CommAlg.ProjectiveDimension
