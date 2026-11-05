import CommAlg.KoszulComplex.FiniteVariables
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Genuine projective-dimension detection by coefficient Koszul homology

This proves the needed vanishing theorem directly from a projective presentation and
its homology long exact sequence. No balance theorem for `Tor` and `Tor'` is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

/-- Tensor a fixed chain complex with a variable coefficient module. -/
def tensorCoefficientFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  map f := (((tensoringRight (ModuleCat R)).map f).mapHomologicalComplex
    (ComplexShape.down ℕ)).app K
  map_id M := by simp
  map_comp f g := by simp

instance tensorCoefficientFunctor_preservesZero (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (tensorCoefficientFunctor K).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (tensorLeft (K.X i)).map (0 : X ⟶ Y) = 0
    exact Functor.map_zero _ _ _

/-- Flat chain groups preserve short exact coefficient sequences degree by degree. -/
lemma tensorCoefficient_shortExact (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (tensorCoefficientFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  letI : Module.Flat R (K.X i) := hflat i
  change (S.map (tensorLeft (K.X i))).ShortExact
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (Module.Flat.lTensor_shortComplex_exact (K.X i) S hS.exact) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K.X i) S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective (K.X i)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

/-- Tensoring an exact positive-degree complex with a projective coefficient module preserves exactness. -/
lemma tensorCoefficient_isZero_of_projective
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) [Projective M] (i : ℕ) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology (i + 1)) := by
  letI : Module.Flat R M := inferInstance
  apply HomologicalComplex.ExactAt.isZero_homology
  change ((K.sc (i + 1)).map (tensorRight M)).Exact
  exact Module.Flat.rTensor_shortComplex_exact M (K.sc (i + 1)) (hexact i)

/-- If the actual projective dimension is below `n`, coefficient homology vanishes in degree `n`.
The induction uses actual projective presentations and actual homology connecting maps. -/
lemma tensorCoefficient_isZero_of_hasProjectiveDimensionLT
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (n : ℕ) (M : ModuleCat.{u} R) (hM : HasProjectiveDimensionLT M n) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology n) := by
  induction n generalizing M with
  | zero =>
      have hz : IsZero M := (hasProjectiveDimensionLT_zero_iff_isZero M).mp hM
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map_isZero
        ((tensorCoefficientFunctor K).map_isZero hz)
  | succ n ih =>
      cases n with
      | zero =>
          letI : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
          exact tensorCoefficient_isZero_of_projective K hexact M 0
      | succ n =>
          let ⟨p⟩ := EnoughProjectives.presentation M
          let S := ShortComplex.mk (kernel.ι p.f) p.f (kernel.condition p.f)
          have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
          have hKer : HasProjectiveDimensionLT S.X₁ (n + 1) :=
            (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
          have hleft := tensorCoefficient_isZero_of_projective K hexact S.X₂ (n + 1)
          have hright := ih S.X₁ hKer
          have ht := tensorCoefficient_shortExact K hflat S hS
          have he := ht.homology_exact₃ (n + 2) (n + 1) (by rfl)
          exact he.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

/-- Nonzero coefficient homology supplies a lower bound for Mathlib's actual projective dimension. -/
lemma tensorCoefficient_nonzero_le_projectiveDimension
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) (n : ℕ)
    (h : ¬ IsZero (((tensorCoefficientFunctor K).obj M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  rw [projectiveDimension_ge_iff]
  exact fun hM => h (tensorCoefficient_isZero_of_hasProjectiveDimensionLT K hflat hexact n M hM)

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Genuine coefficient Koszul homology cannot occur above the actual projective dimension. -/
lemma familyCoefficient_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply tensorCoefficient_nonzero_le_projectiveDimension
    (koszulComplex (Fintype.linearCombination (MvPolynomial V k) MvPolynomial.X))
    (fun i => by
      change Module.Flat (MvPolynomial V k) (⋀[MvPolynomial V k]^i (V → MvPolynomial V k))
      infer_instance) ?_ M n h
  intro i
  exact (koszulComplex.exactAt_of_isRegular
    (finiteVariableList (V := V) (k := k)) finite_variables_regular (i + 1) (by omega)).of_iso
    finiteVariableKoszulIso

/-- The same bound for Mathlib's actual first-factor derived Tor module. -/
lemma finitePolynomialTor_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero (finitePolynomialTor n M)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply familyCoefficient_nonzero_le_projectiveDimension M n
  exact fun hz => h ((finitePolynomialTorIso n M).isZero_iff.mpr hz)

end CommAlg.Koszul
