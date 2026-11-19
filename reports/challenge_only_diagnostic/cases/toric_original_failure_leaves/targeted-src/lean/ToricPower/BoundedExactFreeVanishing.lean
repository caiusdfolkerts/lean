module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Vanishing from unrestricted free modules and a uniform upper bound

An exact complex-valued functor which vanishes on every free module
vanishes on every module if its cohomology has a common upper bound.
Each free epimorphism raises the degree by one. No finite generation,
finite projective dimension, or bounded target resolution is assumed.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

universe u v

variable (R : Type u) [Ring R]
  {D : Type v} [Category D] [Abelian D]
  (F : ModuleCat.{u} R ⥤ CochainComplex D ℤ) [F.PreservesZeroMorphisms]

def moduleFreeEpimorphism (M : ModuleCat.{u} R) :
    ModuleCat.of R (M →₀ R) ⟶ M :=
  ModuleCat.ofHom (Finsupp.linearCombination R (fun x : M => x))

instance moduleFreeEpimorphism_epi (M : ModuleCat.{u} R) :
    Epi (moduleFreeEpimorphism R M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  refine ⟨Finsupp.single x 1,?_⟩
  change Finsupp.linearCombination R (fun y : M => y) (Finsupp.single x 1) = x
  rw [Finsupp.linearCombination_single,one_smul]

/-- The long exact homology sequence supplies a finite dimension shift
for each chosen degree, although the module and its free covers may be
arbitrarily large. -/
theorem exactComplexFunctor_acyclic_of_bounded_free
    (exact : ∀ (S : ShortComplex (ModuleCat.{u} R)),
      S.ShortExact → (S.map F).ShortExact)
    (bound : ℤ)
    (above : ∀ (M : ModuleCat.{u} R) (q : ℤ), bound < q →
      IsZero ((F.obj M).homology q))
    (free : ∀ (I : Type u), (F.obj (ModuleCat.of R (I →₀ R))).Acyclic)
    (M : ModuleCat.{u} R) : (F.obj M).Acyclic := by
  have descending : ∀ depth : ℕ, ∀ (N : ModuleCat.{u} R) (q : ℤ),
      q+(depth : ℤ)=bound+1 → IsZero ((F.obj N).homology q) := by
    intro depth
    induction depth with
    | zero =>
        intro N q equality
        exact above N q (by omega)
    | succ depth ih =>
        intro N q equality
        let e := moduleFreeEpimorphism R N
        let S := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
        have shortExact : S.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel e) }
        have middle : IsZero (((S.map F).X₂).homology q) :=
          (free N q).isZero_homology
        have next : IsZero (((S.map F).X₁).homology (q+1)) :=
          ih (kernel e) (q+1) (by omega)
        exact ((exact S shortExact).homology_exact₃ q (q+1) (by simp)).isZero_of_both_zeros
          (middle.eq_of_src _ _) (next.eq_of_tgt _ _)
  intro q
  rw [exactAt_iff_isZero_homology]
  by_cases high : bound < q
  · exact above M q high
  · exact descending (bound+1-q).toNat M q (by omega)

end ToricPower

end
