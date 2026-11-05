module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Artinian central product decomposition with nilpotents retained

The proof uses a sufficiently large common power of all maximal ideals and
the Chinese remainder theorem. It never replaces a ring by its reduction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped TensorProduct Classical
variable (A : Type*) [CommRing A] [IsArtinianRing A]

theorem artinian_uniform_maximal_nilpotence :
    ∃ N : ℕ,(nilradical A)^N=0 ∧
      ∀ m : MaximalSpectrum A,
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))^N=0 := by
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  obtain ⟨N₀,hN₀⟩ := IsArtinianRing.isNilpotent_nilradical (R := A)
  have hm : ∀ m : MaximalSpectrum A,
      IsNilpotent (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)) := by
    intro m
    have h := IsArtinianRing.isNilpotent_jacobson_bot
      (R := Localization.AtPrime m.asIdeal)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at h
  choose Nm hNm using hm
  let N := max N₀ (Finset.univ.sup Nm)
  refine ⟨N,pow_eq_zero_of_le (Nat.le_max_left _ _) hN₀,fun m ↦ ?_⟩
  exact pow_eq_zero_of_le
    ((Finset.le_sup (Finset.mem_univ m)).trans (Nat.le_max_right _ _)) (hNm m)

/-- The coefficient ring is the product of its actual localizations at
maximal ideals, including their complete nilpotent structures. -/
def artinianEquivPiLocalizations :
    A ≃ₐ[A] ∀ m : MaximalSpectrum A,Localization.AtPrime m.asIdeal := by
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let N := (artinian_uniform_maximal_nilpotence A).choose
  have hN := (artinian_uniform_maximal_nilpotence A).choose_spec.1
  have hNm := (artinian_uniform_maximal_nilpotence A).choose_spec.2
  exact (AlgEquiv.quotientBot A A).symm |>.trans
    ((Ideal.quotientEquivAlgOfEq A hN.symm).trans
      ((IsArtinianRing.quotNilradicalPowEquivPi A N).trans
        (AlgEquiv.piCongrRight (fun m ↦
          (IsLocalization.AtPrime.equivQuotMaximalIdealPow m.asIdeal
            (Localization.AtPrime m.asIdeal) N).trans
            ((Ideal.quotientEquivAlgOfEq A (hNm m)).trans
              (AlgEquiv.quotientBot A (Localization.AtPrime m.asIdeal)))))))

@[simp] theorem artinianEquivPiLocalizations_apply (a : A) (m : MaximalSpectrum A) :
    artinianEquivPiLocalizations A a m=algebraMap A (Localization.AtPrime m.asIdeal) a := by
  rfl

variable (B : Type*) [Ring B] [Algebra A B]

/-- Base change along the ordinary Artinian decomposition splits every
possibly noncommutative algebra over its central coefficient ring. -/
def centralArtinianProductEquiv :
    B ≃ₐ[A] ∀ m : MaximalSpectrum A,Localization.AtPrime m.asIdeal ⊗[A] B := by
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  exact (Algebra.TensorProduct.rid A A B).symm |>.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) (artinianEquivPiLocalizations A)).trans
      ((Algebra.TensorProduct.piRight A A B
        (fun m : MaximalSpectrum A ↦ Localization.AtPrime m.asIdeal)).trans
        (AlgEquiv.piCongrRight (fun m ↦
          Algebra.TensorProduct.comm A B (Localization.AtPrime m.asIdeal)))))

@[simp] theorem centralArtinianProductEquiv_apply (b : B) (m : MaximalSpectrum A) :
    centralArtinianProductEquiv A B b m=1 ⊗ₜ[A] b := by
  simp [centralArtinianProductEquiv]

end PaperVerification.Fermion

