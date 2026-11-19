module

public import PaperVerification.ExteriorQuadraticDifferential
public import PaperVerification.AlternatingFormsExteriorCentrality
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi
import Lean.Elab.Tactic.Omega

/-!
# The actual exterior complex with two central generators

Starting with arbitrary original two-forms `f` and `g`, this file constructs
the differential on the exterior algebra of `M ⊕ R²`.  It proves all the
closedness, parity, degree, and square-zero properties from those definitions.
The additional generators satisfy `d ε₀ = f` and `d ε₁ = g`; every original
generator is closed.  No cohomology or comparison statement is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace PaperVerification.TwoStepExteriorComplex

open ExteriorQuadraticDifferential

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev ExtendedModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  M × (Fin 2 → R)

/-- Inclusion of the original degree-one vectors. -/
def inclusion : M →ₗ[R] ExtendedModule R M := LinearMap.inl R M (Fin 2 → R)

/-- The corresponding map of actual exterior algebras. -/
def baseMap : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R (ExtendedModule R M) :=
  ExteriorAlgebra.map inclusion

/-- The two literal central coordinate functionals. -/
def centralCoordinate (i : Fin 2) : Module.Dual R (ExtendedModule R M) :=
  (LinearMap.proj i).comp (LinearMap.snd R M (Fin 2 → R))

/-- The two extra exterior generators. -/
def epsilon (i : Fin 2) : ExteriorAlgebra R (ExtendedModule R M) :=
  ExteriorAlgebra.ι R ((0 : M), Pi.single i 1)

/-- The original exterior degree is preserved by adjoining the generators. -/
theorem baseMap_mem_exteriorPower {q : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^q M) : baseMap x ∈ ⋀[R]^q (ExtendedModule R M) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  refine Submodule.span_induction
    (p := fun y _ ↦ baseMap y ∈ ⋀[R]^q (ExtendedModule R M)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨v, rfl⟩
    rw [baseMap, ExteriorAlgebra.map_apply_ιMulti]
    exact ExteriorAlgebra.ιMulti_range R q ⟨inclusion ∘ v, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb iha ihb
    rw [map_add]
    exact Submodule.add_mem _ iha ihb
  · intro r a ha iha
    rw [map_smul]
    exact Submodule.smul_mem _ r iha

/-- Each coefficient is the original form mapped into the enlarged algebra. -/
def liftedForm (f : ⋀[R]^2 M) : ⋀[R]^2 (ExtendedModule R M) :=
  ⟨baseMap (f : ExteriorAlgebra R M), baseMap_mem_exteriorPower f.property⟩

/-- Both central contractions vanish on the whole original exterior algebra. -/
theorem central_contraction_baseMap (i : Fin 2) (x : ExteriorAlgebra R M) :
    contraction (centralCoordinate (R := R) (M := M) i) (baseMap x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp [baseMap, contraction]
  | ι m =>
      simp [baseMap, ExteriorAlgebra.map_apply_ι, contraction,
        CliffordAlgebra.contractLeft_ι, centralCoordinate, inclusion]
  | mul x y hx hy =>
      rw [map_mul, contraction, CliffordAlgebra.contractLeft_mul, hx, hy]
      simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- The concrete differential is constructed from the original two forms. -/
def d (f g : ⋀[R]^2 M) : Module.End R (ExteriorAlgebra R (ExtendedModule R M)) :=
  differential (liftedForm f) (liftedForm g) (centralCoordinate 0) (centralCoordinate 1)

theorem d_isOddDerivation (f g : ⋀[R]^2 M) : IsOddDerivation (d f g) :=
  differential_isOddDerivation _ _ _ _
    (AlternatingForms.twoForm_commute (liftedForm f))
    (AlternatingForms.twoForm_commute (liftedForm g))

theorem d_square_zero (f g : ⋀[R]^2 M)
    (x : ExteriorAlgebra R (ExtendedModule R M)) : d f g (d f g x) = 0 := by
  apply differential_square_zero
  · exact AlternatingForms.twoForm_commute (liftedForm f) _
  · simpa using TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
      (liftedForm f).property
  · simpa using TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
      (liftedForm g).property
  · exact central_contraction_baseMap 0 (f : ExteriorAlgebra R M)
  · exact central_contraction_baseMap 0 (g : ExteriorAlgebra R M)
  · exact central_contraction_baseMap 1 (f : ExteriorAlgebra R M)
  · exact central_contraction_baseMap 1 (g : ExteriorAlgebra R M)

/-- Every original generator is closed. -/
theorem d_original_generator (f g : ⋀[R]^2 M) (m : M) :
    d f g (ExteriorAlgebra.ι R (inclusion m)) = 0 := by
  rw [d, differential_generator]
  simp [centralCoordinate, inclusion]

/-- The first central generator has the prescribed differential `f`. -/
theorem d_epsilon_zero (f g : ⋀[R]^2 M) :
    d f g (epsilon 0) = baseMap (f : ExteriorAlgebra R M) := by
  rw [epsilon, d, differential_generator]
  simp [centralCoordinate, liftedForm]

/-- The second central generator has the prescribed differential `g`. -/
theorem d_epsilon_one (f g : ⋀[R]^2 M) :
    d f g (epsilon 1) = baseMap (g : ExteriorAlgebra R M) := by
  rw [epsilon, d, differential_generator]
  simp [centralCoordinate, liftedForm]

/-- The differential raises the actual exterior degree by one. -/
theorem d_mem_exteriorPower (f g : ⋀[R]^2 M) {q : ℕ}
    {x : ExteriorAlgebra R (ExtendedModule R M)} (hx : x ∈ ⋀[R]^q (ExtendedModule R M)) :
    d f g x ∈ ⋀[R]^(q + 1) (ExtendedModule R M) := by
  cases q with
  | zero =>
      have h₀ := TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
        (centralCoordinate (R := R) (M := M) 0) hx
      have h₁ := TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
        (centralCoordinate (R := R) (M := M) 1) hx
      simp only [d, differential_apply, contraction, h₀, h₁, mul_zero, add_zero]
      exact Submodule.zero_mem _
  | succ q =>
      change (liftedForm f : ExteriorAlgebra R (ExtendedModule R M)) *
          contraction (centralCoordinate 0) x +
        (liftedForm g : ExteriorAlgebra R (ExtendedModule R M)) *
          contraction (centralCoordinate 1) x ∈ _
      apply Submodule.add_mem
      · convert SetLike.mul_mem_graded (liftedForm f).property
          (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
            (centralCoordinate 0) hx) using 1 <;> congr 1 <;> omega
      · convert SetLike.mul_mem_graded (liftedForm g).property
          (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
            (centralCoordinate 1) hx) using 1 <;> congr 1 <;> omega

/-- The degree-by-degree linear differential on the genuine exterior powers. -/
def degreeDifferential (f g : ⋀[R]^2 M) (q : ℕ) :
    (⋀[R]^q (ExtendedModule R M)) →ₗ[R] ⋀[R]^(q + 1) (ExtendedModule R M) where
  toFun x := ⟨d f g x, d_mem_exteriorPower f g x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (d f g) (x : ExteriorAlgebra R (ExtendedModule R M))
      (y : ExteriorAlgebra R (ExtendedModule R M))
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (d f g) r (x : ExteriorAlgebra R (ExtendedModule R M))

/-- The resulting ordinary cochain complex, with actual exterior-power terms. -/
def complex (f g : ⋀[R]^2 M) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (⋀[R]^q (ExtendedModule R M)))
    (fun q ↦ ModuleCat.ofHom (degreeDifferential f g q)) (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact d_square_zero f g (x : ExteriorAlgebra R (ExtendedModule R M)))

end PaperVerification.TwoStepExteriorComplex
