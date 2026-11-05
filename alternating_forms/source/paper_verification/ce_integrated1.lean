module

public import paper_verification.literal003
import all paper_verification.literal003
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Tactic.Abel
public import paper_verification.literal000
import all paper_verification.literal000
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi
import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.Ring
public import paper_verification.literal007
import all paper_verification.literal007
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import paper_verification.literal001
import all paper_verification.literal001
public import paper_verification.literal011
import all paper_verification.literal011
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import paper_verification.literal012
import all paper_verification.literal012
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.ExteriorQuadraticDifferential -/


/-!
# Exterior differentials for a central two-step bracket

The operators here act on Mathlib's actual exterior algebra.  The main
calculation proves that two quadratic creation operators followed by
contraction give a square-zero odd derivation when their coefficients
are closed and even.  The hypotheses are explicit algebraic identities;
this file does not assert a Lie-cohomology comparison on their own.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorQuadraticDifferential

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev parity : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.involute (Q := (0 : QuadraticForm R M))

abbrev contraction (c : Module.Dual R M) : Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) c

/-- The usual odd Leibniz rule for the genuine exterior algebra. -/
def IsOddDerivation (D : Module.End R (ExteriorAlgebra R M)) : Prop :=
  D 1 = 0 ∧ ∀ x y, D (x * y) = D x * y + parity x * D y

/-- An odd derivation is uniquely determined on the original degree-one
generators.  In particular, specifying the bracket dual determines the
Chevalley--Eilenberg exterior differential uniquely. -/
theorem oddDerivation_ext {D E : Module.End R (ExteriorAlgebra R M)}
    (hD : IsOddDerivation D) (hE : IsOddDerivation E)
    (hgen : ∀ m, D (ExteriorAlgebra.ι R m) = E (ExteriorAlgebra.ι R m)) : D = E := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, hD.1, hE.1]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul m x hx => rw [hD.2, hE.2, hgen, hx]

/-- The concrete sum of quadratic multiplication followed by contraction. -/
def differential (a b : ExteriorAlgebra R M) (c₀ c₁ : Module.Dual R M) :
    Module.End R (ExteriorAlgebra R M) :=
  (LinearMap.mulLeft R a).comp (contraction c₀) +
    (LinearMap.mulLeft R b).comp (contraction c₁)

@[simp] theorem differential_apply (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (x : ExteriorAlgebra R M) :
    differential a b c₀ c₁ x = a * contraction c₀ x + b * contraction c₁ x := rfl

/-- The value on a degree-one generator retains exactly the prescribed
coefficients of the two contracting functionals. -/
theorem differential_generator (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (m : M) :
    differential a b c₀ c₁ (ExteriorAlgebra.ι R m) = c₀ m • a + c₁ m • b := by
  rw [differential_apply, contraction, CliffordAlgebra.contractLeft_ι,
    CliffordAlgebra.contractLeft_ι]
  simp only [Algebra.smul_def]
  exact congrArg₂ (· + ·) (Algebra.commutes (c₀ m) a).symm
    (Algebra.commutes (c₁ m) b).symm

/-- Central quadratic coefficients give the required odd Leibniz rule. -/
theorem differential_isOddDerivation (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M)
    (ha : ∀ x, Commute a x) (hb : ∀ x, Commute b x) :
    IsOddDerivation (differential a b c₀ c₁) := by
  constructor
  · simp [differential_apply, contraction]
  · intro x y
    simp only [differential_apply, contraction, CliffordAlgebra.contractLeft_mul,
      mul_add, add_mul, ← mul_assoc]
    rw [(ha (parity x)).eq, (hb (parity x)).eq]
    abel

/-- The actual exterior operator squares to zero.  Its proof uses the
anticommutation of the two genuine contraction operators. -/
theorem differential_square_zero (a b : ExteriorAlgebra R M)
    (c₀ c₁ : Module.Dual R M) (hab : Commute a b)
    (ha : parity a = a) (hb : parity b = b)
    (h₀a : contraction c₀ a = 0) (h₀b : contraction c₀ b = 0)
    (h₁a : contraction c₁ a = 0) (h₁b : contraction c₁ b = 0)
    (x : ExteriorAlgebra R M) :
    differential a b c₀ c₁ (differential a b c₀ c₁ x) = 0 := by
  simp only [differential_apply, map_add, contraction,
    CliffordAlgebra.contractLeft_mul, h₀a, h₀b, h₁a, h₁b, ha, hb,
    CliffordAlgebra.contractLeft_contractLeft, zero_mul, mul_zero,
    zero_add, add_zero]
  rw [CliffordAlgebra.contractLeft_comm c₀ c₁ x]
  simp only [mul_neg, ← mul_assoc]
  simp only [hab.eq, neg_add_cancel, add_neg_cancel]

end PaperVerification.ExteriorQuadraticDifferential
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExteriorQuadraticDifferential"

section ComponentSource_1
/- Original module: PaperVerification.TwoStepExteriorComplex -/


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
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepExteriorComplex"

section ComponentSource_2
/- Original module: PaperVerification.ExteriorCoordinateProjection -/


/-!
# Removing one coordinate in the actual exterior algebra

The algebra map induced by `v ↦ v - c(v)e` equals `x ↦ x - e ∧ (c ⌋ x)`.
This identity is valid over every commutative ring, without freeness or
nondegeneracy assumptions.  It supplies the explicit decomposition needed
to compare a central Lie exterior complex with its Koszul complex.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorCoordinateProjection

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The literal rank-one modification of the identity. -/
def removeCoordinate (e : M) (c : Module.Dual R M) : M →ₗ[R] M :=
  LinearMap.id - (LinearMap.toSpanSingleton R M e).comp c

@[simp] theorem removeCoordinate_apply (e : M) (c : Module.Dual R M) (v : M) :
    removeCoordinate e c v = v - c v • e := rfl

/-- An actual exterior map written using contraction. -/
theorem map_removeCoordinate (e : M) (c : Module.Dual R M)
    (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (removeCoordinate e c) x =
      x - ExteriorAlgebra.ι R e *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) c x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
      simp only [map_add, hx, hy, mul_add]
      abel
  | ι_mul x v hx =>
      change ExteriorAlgebra.map (removeCoordinate e c) (ExteriorAlgebra.ι R v * x) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι, removeCoordinate_apply, map_sub,
        map_smul, hx, CliffordAlgebra.contractLeft_ι_mul]
      have hswap : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R e =
          -(ExteriorAlgebra.ι R e * ExteriorAlgebra.ι R v) := by
        exact eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap v e)
      simp only [sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
        hswap, ExteriorAlgebra.ι_sq_zero, zero_mul, smul_zero, sub_zero, neg_mul,
        sub_neg_eq_add]
      abel

end PaperVerification.ExteriorCoordinateProjection
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExteriorCoordinateProjection"

section ComponentSource_3
/- Original module: PaperVerification.TwoCentralExteriorDecomposition -/


/-!
# Splitting the exterior algebra along two central coordinates

For `N = M ⊕ R²`, the actual exterior algebra is the direct sum of four
copies of `Λ M`, distinguished by the presence of the two extra generators.
The projection maps are explicit contractions.  All identities hold over
an arbitrary commutative ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoCentralExteriorDecomposition

open ExteriorCoordinateProjection

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev N (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] := M × (Fin 2 → R)
abbrev E (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] := ExteriorAlgebra R M

/-- Inclusion and projection on the literal original summand. -/
def inc : M →ₗ[R] N R M := LinearMap.inl R M (Fin 2 → R)
def pr : N R M →ₗ[R] M := LinearMap.fst R M (Fin 2 → R)
def lift : E R M →ₐ[R] E R (N R M) := ExteriorAlgebra.map inc
def project : E R (N R M) →ₐ[R] E R M := ExteriorAlgebra.map pr

/-- The two central coordinate vectors and their dual functionals. -/
def vector (i : Fin 2) : N R M := (0, Pi.single i 1)
def coordinate (i : Fin 2) : Module.Dual R (N R M) :=
  (LinearMap.proj i).comp (LinearMap.snd R M (Fin 2 → R))
def e (i : Fin 2) : E R (N R M) := ExteriorAlgebra.ι R (vector i)
abbrev c (i : Fin 2) : Module.End R (E R (N R M)) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (N R M))) (coordinate i)

@[simp] theorem coordinate_vector (i j : Fin 2) :
    coordinate (R := R) (M := M) i (vector j) = if j = i then 1 else 0 := by
  simp [coordinate, vector, Pi.single_apply, eq_comm]

@[simp] theorem project_lift (x : E R M) : project (lift x) = x := by
  change ((ExteriorAlgebra.map pr).comp (ExteriorAlgebra.map inc)) x = x
  rw [ExteriorAlgebra.map_comp_map]
  change ExteriorAlgebra.map (LinearMap.id : M →ₗ[R] M) x = x
  simp only [ExteriorAlgebra.map_id, AlgHom.id_apply]

@[simp] theorem project_e (i : Fin 2) : project (e (R := R) (M := M) i) = 0 := by
  simp [project, e, pr, vector]

@[simp] theorem c_lift (i : Fin 2) (x : E R M) : c i (lift x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [lift, c, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | ι_mul x v hx =>
      change c i (lift (ExteriorAlgebra.ι R v * x)) = 0
      rw [map_mul, lift, ExteriorAlgebra.map_apply_ι, c, CliffordAlgebra.contractLeft_ι_mul]
      change (0 : R) • ExteriorAlgebra.map inc x -
        ExteriorAlgebra.ι R (inc v) * c i (lift x) = 0
      rw [hx]
      simp

@[simp] theorem c_e_mul (i j : Fin 2) (x : E R (N R M)) :
    c i (e j * x) = (if j = i then (1 : R) else 0) • x - e j * c i x := by
  rw [e, c, CliffordAlgebra.contractLeft_ι_mul, coordinate_vector]

@[simp] theorem c_c (i : Fin 2) (x : E R (N R M)) : c i (c i x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem c_swap (i j : Fin 2) (x : E R (N R M)) : c i (c j x) = -c j (c i x) :=
  CliffordAlgebra.contractLeft_comm _ _ _

@[simp] theorem e_sq (i : Fin 2) : e (R := R) (M := M) i * e i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem e_swap : e (R := R) (M := M) 1 * e 0 = -(e 0 * e 1) :=
  eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap _ _)

/-- Removing both coordinates is the original-summand projection. -/
theorem removeCoordinate_comp :
    (removeCoordinate (vector (R := R) (M := M) 0) (coordinate 0)).comp
      (removeCoordinate (vector 1) (coordinate 1)) = inc.comp pr := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · simp [removeCoordinate, vector, coordinate, inc, pr]
  · funext i
    fin_cases i <;> simp [removeCoordinate, vector, coordinate, inc, pr, Pi.single_apply]

/-- The explicit projection to the original exterior summand. -/
theorem lift_project (x : E R (N R M)) :
    lift (project x) = x - e 0 * c 0 x - e 1 * c 1 x + e 0 * e 1 * c 1 (c 0 x) := by
  have hp : lift (project x) =
      ExteriorAlgebra.map (removeCoordinate (vector 0) (coordinate 0))
        (ExteriorAlgebra.map (removeCoordinate (vector 1) (coordinate 1)) x) := by
    change ((ExteriorAlgebra.map inc).comp (ExteriorAlgebra.map pr)) x =
      ((ExteriorAlgebra.map (removeCoordinate (vector 0) (coordinate 0))).comp
        (ExteriorAlgebra.map (removeCoordinate (vector 1) (coordinate 1)))) x
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, removeCoordinate_comp]
  rw [hp, map_removeCoordinate, map_removeCoordinate]
  change (x - e 1 * c 1 x) - e 0 * c 0 (x - e 1 * c 1 x) = _
  rw [map_sub, c_e_mul]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, zero_smul,
    zero_sub, sub_neg_eq_add, mul_add]
  rw [c_swap 0 1 x]
  simp only [mul_neg, ← mul_assoc]
  abel

private theorem c_zero_one_zero (x : E R (N R M)) : c 0 (c 1 (c 0 x)) = 0 := by
  rw [c_swap, c_c, map_zero, neg_zero]

private theorem c_one_zero_one (x : E R (N R M)) : c 1 (c 0 (c 1 x)) = 0 := by
  rw [c_swap, c_c, map_zero, neg_zero]

/-- The full reconstruction from the four contracted coefficients. -/
theorem reconstruct (x : E R (N R M)) :
    lift (project x) + e 0 * lift (project (c 0 x)) + e 1 * lift (project (c 1 x)) +
      e 0 * e 1 * lift (project (c 1 (c 0 x))) = x := by
  rw [lift_project, lift_project (c 0 x), lift_project (c 1 x),
    lift_project (c 1 (c 0 x))]
  simp only [c_c, c_zero_one_zero, c_one_zero_one, map_zero, mul_zero,
    sub_zero, add_zero, mul_sub, mul_add, ← mul_assoc]
  rw [e_swap, c_swap 0 1 x]
  simp only [mul_neg, neg_mul, neg_neg]
  abel

/-- Four literal coefficients: no center, first, second, and both. -/
def coefficients : E R (N R M) →ₗ[R] E R M × (E R M × (E R M × E R M)) :=
  project.toLinearMap.prod
    ((project.toLinearMap.comp (c 0)).prod
      ((project.toLinearMap.comp (c 1)).prod (project.toLinearMap.comp ((c 1).comp (c 0)))))

/-- Reassemble the four summands in fixed exterior order. -/
def assemble : (E R M × (E R M × (E R M × E R M))) →ₗ[R] E R (N R M) where
  toFun z := lift z.1 + e 0 * lift z.2.1 + e 1 * lift z.2.2.1 + e 0 * e 1 * lift z.2.2.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add]; abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, mul_smul_comm, smul_add, RingHom.id_apply]

/-- The four coefficients recover every exterior element. -/
theorem assemble_coefficients (x : E R (N R M)) : assemble (coefficients x) = x :=
  reconstruct x

/-- Coefficient extraction recovers every tuple, proving independence. -/
theorem coefficients_assemble (z : E R M × (E R M × (E R M × E R M))) :
    coefficients (assemble z) = z := by
  rcases z with ⟨a,b,c',d⟩
  ext <;> simp [coefficients, assemble, map_add, map_mul, c_e_mul, mul_assoc]

/-- The genuine exterior-algebra decomposition as a linear equivalence. -/
def decomposition : E R (N R M) ≃ₗ[R] E R M × (E R M × (E R M × E R M)) :=
  { coefficients with
    invFun := assemble
    left_inv := assemble_coefficients
    right_inv := coefficients_assemble }

end PaperVerification.TwoCentralExteriorDecomposition
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoCentralExteriorDecomposition"

section ComponentSource_4
/- Original module: PaperVerification.TwoCentralKoszulOperator -/


/-!
# The central exterior differential in Koszul coordinates

The four-term exterior decomposition sends the literal operator
`f · contraction₀ + g · contraction₁` to the length-two Koszul differential.
The two coefficients are the original exterior two-forms, with their
original multiplication maps.  This is an equality of actual linear maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoCentralKoszulOperator

open TwoCentralExteriorDecomposition

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The original forms, included in the actual enlarged exterior algebra. -/
def operator (f g : ⋀[R]^2 M) : Module.End R (E R (N R M)) :=
  ExteriorQuadraticDifferential.differential
    (lift (f : E R M)) (lift (g : E R M)) (coordinate 0) (coordinate 1)

/-- The original first Koszul differential. -/
def first (f g : ⋀[R]^2 M) : (E R M × E R M) →ₗ[R] E R M :=
  (LinearMap.mulLeft R (f : E R M)).coprod (LinearMap.mulLeft R (g : E R M))

/-- The original second Koszul differential, with its usual sign. -/
def second (f g : ⋀[R]^2 M) : E R M →ₗ[R] (E R M × E R M) :=
  (-(LinearMap.mulLeft R (g : E R M))).prod (LinearMap.mulLeft R (f : E R M))

/-- Inclusion preserves the genuine quadratic degree and hence centrality. -/
theorem lift_twoForm_commute (f : ⋀[R]^2 M) (x : E R (N R M)) :
    Commute (lift (f : E R M)) x := by
  simpa only [exteriorPower.coe_map, lift] using
    AlternatingForms.twoForm_commute (exteriorPower.map 2 inc f) x

@[simp] theorem contract_zero_assemble (z : E R M × (E R M × (E R M × E R M))) :
    c 0 (assemble z) = lift z.2.1 + e 1 * lift z.2.2.2 := by
  simp [assemble, mul_assoc]

@[simp] theorem contract_one_assemble (z : E R M × (E R M × (E R M × E R M))) :
    c 1 (assemble z) = lift z.2.2.1 - e 0 * lift z.2.2.2 := by
  simp [assemble, mul_assoc]
  abel

/-- The actual exterior differential is precisely the two-form Koszul map
in the four explicit summands. -/
theorem operator_assemble (f g : ⋀[R]^2 M)
    (z : E R M × (E R M × (E R M × E R M))) :
    operator f g (assemble z) =
      assemble ((f : E R M) * z.2.1 + (g : E R M) * z.2.2.1,
        -((g : E R M) * z.2.2.2), (f : E R M) * z.2.2.2, 0) := by
  change lift (f : E R M) * c 0 (assemble z) + lift (g : E R M) * c 1 (assemble z) = _
  rw [contract_zero_assemble, contract_one_assemble]
  simp only [assemble, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_mul, map_neg, map_zero, mul_zero, add_zero,
    mul_add, mul_sub, mul_neg, ← mul_assoc]
  rw [(lift_twoForm_commute f (e 1)).eq, (lift_twoForm_commute g (e 0)).eq]
  abel

/-- The inverse-coordinate form of the same equality. -/
theorem coefficients_operator (f g : ⋀[R]^2 M) (x : E R (N R M)) :
    coefficients (operator f g x) =
      ((f : E R M) * (coefficients x).2.1 + (g : E R M) * (coefficients x).2.2.1,
        -((g : E R M) * (coefficients x).2.2.2),
          (f : E R M) * (coefficients x).2.2.2, 0) := by
  have h := congrArg coefficients (operator_assemble f g (coefficients x))
  simpa only [assemble_coefficients, coefficients_assemble] using h

/-- Group the two middle exterior summands into Koszul position one. -/
def regroup : (E R M × (E R M × (E R M × E R M))) ≃ₗ[R]
    E R M × ((E R M × E R M) × E R M) :=
  (LinearEquiv.refl R (E R M)).prodCongr
    (LinearEquiv.prodAssoc R (E R M) (E R M) (E R M)).symm

/-- The actual linear equivalence with the three Koszul positions. -/
def koszulCoordinates : E R (N R M) ≃ₗ[R] E R M × ((E R M × E R M) × E R M) :=
  decomposition.trans regroup

/-- Conjugation gives the literal folded Koszul differential. -/
theorem koszulCoordinates_operator (f g : ⋀[R]^2 M) (x : E R (N R M)) :
    koszulCoordinates (operator f g x) =
      (first f g (koszulCoordinates x).2.1,
        second f g (koszulCoordinates x).2.2, 0) := by
  change regroup (coefficients (operator f g x)) = _
  rw [coefficients_operator]
  rfl

end PaperVerification.TwoCentralKoszulOperator
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoCentralKoszulOperator"

section ComponentSource_5
/- Original module: PaperVerification.ExteriorTwoFormEvaluation -/


/-!
# Evaluation of exterior two-forms

These definitions use the determinant pairing in Mathlib.  They identify an
actual exterior two-form with its alternating evaluation on dual vectors;
the separation result proves that this evaluation loses no information in
finite dimension.  The transpose identity fixes the sign convention when
passing between exterior forms and Chevalley--Eilenberg cochains.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorTwoFormEvaluation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluate a genuine exterior two-form on two dual vectors. -/
def evaluate (f : ⋀[R]^2 M) : AlternatingMap R (Module.Dual R M) R (Fin 2) :=
  (Module.Dual.eval R (⋀[R]^2 M) f).compAlternatingMap
    (exteriorPower.alternatingMapToDual R M 2)

@[simp] theorem evaluate_apply (f : ⋀[R]^2 M) (v : Fin 2 → Module.Dual R M) :
    evaluate f v = exteriorPower.alternatingMapToDual R M 2 v f := rfl

/-- The two-by-two determinant formula, including its orientation. -/
theorem evaluate_word (m : Fin 2 → M) (v w : Module.Dual R M) :
    evaluate (exteriorPower.ιMulti R 2 m) ![v,w] =
      v (m 0) * w (m 1) - w (m 0) * v (m 1) := by
  simp only [evaluate_apply, exteriorPower.alternatingMapToDual_apply_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Repackage an alternating two-variable map as the ordinary bilinear map. -/
def bilinearOfAlternating (A : AlternatingMap R M R (Fin 2)) : M →ₗ[R] M →ₗ[R] R :=
  LinearMap.mk₂ R (fun v w ↦ A ![v,w])
    (fun v v' w ↦ A.map_vecCons_add ![w] v v')
    (fun r v w ↦ A.map_vecCons_smul ![w] r v)
    (fun v w w' ↦ (A.curryLeft v).map_vecCons_add ![] w w')
    (fun r v w ↦ (A.curryLeft v).map_vecCons_smul ![] r w)

@[simp] theorem bilinearOfAlternating_apply (A : AlternatingMap R M R (Fin 2)) (v w : M) :
    bilinearOfAlternating A v w = A ![v,w] := rfl

@[simp] theorem bilinearOfAlternating_self (A : AlternatingMap R M R (Fin 2)) (v : M) :
    bilinearOfAlternating A v v = 0 :=
  A.map_eq_zero_of_eq ![v,v] (i := 0) (j := 1) rfl (by decide)

/-- The bracket coefficient determined by the original exterior form. -/
def bilinear (f : ⋀[R]^2 M) : Module.Dual R M →ₗ[R] Module.Dual R M →ₗ[R] R :=
  bilinearOfAlternating (evaluate f)

@[simp] theorem bilinear_self (f : ⋀[R]^2 M) (v : Module.Dual R M) : bilinear f v v = 0 :=
  bilinearOfAlternating_self _ _

/-- Transposing the determinant converts the dual exterior pairing into
ordinary alternating evaluation on the two evaluation functionals. -/
theorem pairingDual_eq_evaluate (f : ⋀[R]^2 (Module.Dual R M)) (v w : M) :
    exteriorPower.pairingDual R M 2 f (exteriorPower.ιMulti R 2 ![v,w]) =
      evaluate f ![Module.Dual.eval R M v, Module.Dual.eval R M w] := by
  have h :
      (Module.Dual.eval R (⋀[R]^2 M) (exteriorPower.ιMulti R 2 ![v,w])).comp
          (exteriorPower.pairingDual R M 2) =
        exteriorPower.alternatingMapToDual R (Module.Dual R M) 2
          ![Module.Dual.eval R M v, Module.Dual.eval R M w] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  exact LinearMap.congr_fun h f

section Separation

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every two-form coefficient is detected by alternating evaluation. -/
theorem evaluate_injective : Function.Injective (evaluate (R := K) (M := V)) := by
  classical
  let b := Module.finBasis K V
  intro f g hfg
  apply (b.exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have hd : exteriorPower.ιMultiDual K 2 b s =
      exteriorPower.alternatingMapToDual K V 2 ![b.coord (a 0), b.coord (a 1)] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simp only [LinearMap.compAlternatingMap_apply, exteriorPower.ιMultiDual_apply_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Module.Basis.coord_apply, a]
  rw [hd]
  exact congrArg (fun A : AlternatingMap K (Module.Dual K V) K (Fin 2) ↦
    A ![b.coord (a 0), b.coord (a 1)]) hfg

/-- In finite dimension, equality on all pairs of vectors is equality of
actual exterior two-cochains. -/
theorem pairingDual_injective_on_pairs (f g : ⋀[K]^2 (Module.Dual K V))
    (h : ∀ v w, exteriorPower.pairingDual K V 2 f (exteriorPower.ιMulti K 2 ![v,w]) =
      exteriorPower.pairingDual K V 2 g (exteriorPower.ιMulti K 2 ![v,w])) : f = g := by
  apply evaluate_injective
  apply AlternatingMap.ext
  intro a
  obtain ⟨v, hv⟩ := (Module.evalEquiv K V).surjective (a 0)
  obtain ⟨w, hw⟩ := (Module.evalEquiv K V).surjective (a 1)
  have ha : a = ![Module.Dual.eval K V v, Module.Dual.eval K V w] := by
    ext i
    fin_cases i <;> simp_all
  rw [ha, ← pairingDual_eq_evaluate, ← pairingDual_eq_evaluate]
  exact h v w

end Separation
end PaperVerification.ExteriorTwoFormEvaluation
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExteriorTwoFormEvaluation"

section ComponentSource_6
/- Original module: PaperVerification.CentralLieCochainCoordinates -/


/-!
# Original forms, the actual central Lie bracket, and cochains

The two original exterior forms define an ordinary two-step Lie algebra
on `M* ⊕ R²`.  Its cochain generators are identified with `M ⊕ R²` using
the evaluation isomorphism on `M` and the negatives of the two central
dual coordinates.  This fixes the conventional equation
`d α (x,y) = -α [x,y]` while retaining `d ε₀ = f`, `d ε₁ = g`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.CentralLieCochainCoordinates

open ExteriorTwoFormEvaluation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The literal bracket coefficients of the original two forms. -/
def bracketData (f g : ⋀[R]^2 M) :
    TwoStepCentralLie.Data (K := R) (V := Module.Dual R M) (Z := Fin 2 → R) where
  bilinear := LinearMap.mk₂ R (fun v w ↦ ![bilinear f v w, bilinear g v w])
    (by intro v v' w; ext i; fin_cases i <;> simp)
    (by intro r v w; ext i; fin_cases i <;> simp)
    (by intro v w w'; ext i; fin_cases i <;> simp)
    (by intro r v w; ext i; fin_cases i <;> simp)
  alternating v := by ext i; fin_cases i <;> simp

/-- Mathlib's ordinary Lie algebra, with the actual constructed bracket. -/
abbrev L (f g : ⋀[R]^2 M) := TwoStepCentralLie.LieSpace (bracketData f g)

@[simp] theorem bracket_apply (f g : ⋀[R]^2 M) (x y : L f g) :
    ⁅x,y⁆ = ((0 : Module.Dual R M), ![bilinear f x.1 y.1, bilinear g x.1 y.1]) := rfl

/-- The canonical dual pairing for the two central coordinates. -/
theorem twoCoordinate_dual (r z : Fin 2 → R) :
    (Pi.basisFun R (Fin 2)).toDual r z = r 0 * z 0 + r 1 * z 1 := by
  let b := Pi.basisFun R (Fin 2)
  have hr : r = r 0 • b 0 + r 1 • b 1 := by
    ext i
    fin_cases i <;> simp [b, Pi.basisFun_apply]
  rw [hr, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply,
    b.toDual_apply_right, b.toDual_apply_right]
  simp [b, Pi.basisFun_repr]

section Reflexive

variable [Module.IsReflexive R M]

/-- Original generators and negative central dual generators give all
actual one-cochains.  Finite-dimensional vector spaces satisfy reflexivity. -/
def oneCochainEquiv (f g : ⋀[R]^2 M) :
    (M × (Fin 2 → R)) ≃ₗ[R] Module.Dual R (L f g) :=
  ((Module.evalEquiv R M).prodCongr
    ((Pi.basisFun R (Fin 2)).toDualEquiv.trans (LinearEquiv.neg R))).trans
      (Module.dualProdDualEquivDual R (Module.Dual R M) (Fin 2 → R))

theorem oneCochainEquiv_apply (f g : ⋀[R]^2 M) (v : M × (Fin 2 → R)) (x : L f g) :
    oneCochainEquiv f g v x = x.1 v.1 - (Pi.basisFun R (Fin 2)).toDual v.2 x.2 := by
  change x.1 v.1 + (-((Pi.basisFun R (Fin 2)).toDualEquiv v.2)) x.2 = _
  rw [LinearMap.neg_apply, Module.Basis.toDualEquiv_apply, sub_eq_add_neg]

@[simp] theorem oneCochainEquiv_original (f g : ⋀[R]^2 M) (m : M) (x : L f g) :
    oneCochainEquiv f g (m,0) x = x.1 m := by
  simp [oneCochainEquiv_apply]

@[simp] theorem oneCochainEquiv_central (f g : ⋀[R]^2 M) (i : Fin 2) (x : L f g) :
    oneCochainEquiv f g ((0 : M),Pi.single i 1) x = -x.2 i := by
  rw [oneCochainEquiv_apply]
  change x.1 (0 : M) - (Pi.basisFun R (Fin 2)).toDual (Pi.single i 1) x.2 = _
  rw [map_zero, ← Pi.basisFun_apply R (Fin 2) i, Module.Basis.toDual_apply_right]
  simp [Pi.basisFun_repr]

/-- The negative bracket dual in the original cochain coordinates. -/
theorem negative_bracket_dual (f g : ⋀[R]^2 M) (v : M × (Fin 2 → R)) (x y : L f g) :
    -(oneCochainEquiv f g v ⁅x,y⁆) =
      v.2 0 * bilinear f x.1 y.1 + v.2 1 * bilinear g x.1 y.1 := by
  rw [oneCochainEquiv_apply, bracket_apply, twoCoordinate_dual]
  simp

/-- The original two-form as an actual exterior two-cochain of the Lie algebra. -/
def originalTwoCochain (f g h : ⋀[R]^2 M) : ⋀[R]^2 (Module.Dual R (L f g)) :=
  exteriorPower.map 2
    ((oneCochainEquiv f g).toLinearMap.comp (LinearMap.inl R M (Fin 2 → R))) h

/-- Evaluation of the actual pulled-back two-cochain is the original
bracket coefficient, with no sign or scalar normalization omitted. -/
theorem originalTwoCochain_pairing (f g h : ⋀[R]^2 M) (x y : L f g) :
    exteriorPower.pairingDual R (L f g) 2 (originalTwoCochain f g h)
      (exteriorPower.ιMulti R 2 ![x,y]) = bilinear h x.1 y.1 := by
  have he :
      (Module.Dual.eval R (⋀[R]^2 (L f g)) (exteriorPower.ιMulti R 2 ![x,y])).comp
          ((exteriorPower.pairingDual R (L f g) 2).comp
            (exteriorPower.map 2
              ((oneCochainEquiv f g).toLinearMap.comp (LinearMap.inl R M (Fin 2 → R))))) =
        exteriorPower.alternatingMapToDual R M 2 ![x.1,y.1] := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti,
      exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply,
      oneCochainEquiv_original]
    ring
  exact LinearMap.congr_fun he h

end Reflexive
end PaperVerification.CentralLieCochainCoordinates
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.CentralLieCochainCoordinates"

section ComponentSource_7
/- Original module: PaperVerification.ExteriorDerivationTransport -/


/-!
# Transport of actual exterior differentials

A linear equivalence induces an algebra equivalence of the actual exterior
algebras. Conjugation by this equivalence preserves the odd Leibniz rule,
square-zero identity, and each genuine exterior degree.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ExteriorDerivationTransport

open ExteriorQuadraticDifferential

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Functoriality of the actual exterior algebra, as an algebra equivalence. -/
def mapEquiv (e : M ≃ₗ[R] N) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  { ExteriorAlgebra.map e.toLinearMap with
    invFun := ExteriorAlgebra.map e.symm.toLinearMap
    left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.left_inv
    right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.right_inv }

@[simp] theorem mapEquiv_apply (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    mapEquiv e x = ExteriorAlgebra.map e.toLinearMap x := rfl

@[simp] theorem mapEquiv_symm_apply (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R N) :
    (mapEquiv e).symm x = ExteriorAlgebra.map e.symm.toLinearMap x := rfl

@[simp] theorem mapEquiv_ι (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv e (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (e m) :=
  ExteriorAlgebra.map_apply_ι _ _

@[simp] theorem mapEquiv_symm_ι (e : M ≃ₗ[R] N) (n : N) :
    (mapEquiv e).symm (ExteriorAlgebra.ι R n) = ExteriorAlgebra.ι R (e.symm n) :=
  ExteriorAlgebra.map_apply_ι _ _

/-- The exterior grading involution is natural under every linear map. -/
theorem parity_map (e : M ≃ₗ[R] N) (x : ExteriorAlgebra R M) :
    parity (mapEquiv e x) = mapEquiv e (parity x) := by
  have h : parity.comp (mapEquiv e).toAlgHom =
      (mapEquiv e).toAlgHom.comp parity := by
    apply ExteriorAlgebra.hom_ext
    apply LinearMap.ext
    intro m
    simp [parity, CliffordAlgebra.involute_ι]
  exact DFunLike.congr_fun h x

/-- Conjugation of the genuine linear differential. -/
def conjugate (e : M ≃ₗ[R] N) (D : Module.End R (ExteriorAlgebra R M)) :
    Module.End R (ExteriorAlgebra R N) :=
  (mapEquiv e).toLinearMap.comp (D.comp (mapEquiv e).symm.toLinearMap)

@[simp] theorem conjugate_apply (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (x : ExteriorAlgebra R N) :
    conjugate e D x = mapEquiv e (D ((mapEquiv e).symm x)) := rfl

/-- Odd derivations remain odd derivations under the actual algebra map. -/
theorem conjugate_isOddDerivation (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (hD : IsOddDerivation D) :
    IsOddDerivation (conjugate e D) := by
  constructor
  · simp [conjugate_apply, hD.1]
  · intro x y
    change mapEquiv e (D ((mapEquiv e).symm (x*y))) = _
    rw [map_mul, hD.2, map_add, map_mul, map_mul]
    rw [← parity_map]
    simp only [AlgEquiv.apply_symm_apply, conjugate_apply]

/-- No square-zero assumption is lost when changing cochain coordinates. -/
theorem conjugate_square_zero (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M)) (hD : ∀ x, D (D x) = 0)
    (x : ExteriorAlgebra R N) : conjugate e D (conjugate e D x) = 0 := by
  simp only [conjugate_apply, AlgEquiv.symm_apply_apply, hD, map_zero]

/-- Exterior algebra maps preserve the actual homogeneous submodules. -/
theorem map_mem_exteriorPower (f : M →ₗ[R] N) {q : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^q M) :
    ExteriorAlgebra.map f x ∈ ⋀[R]^q N := by
  simpa only [exteriorPower.coe_map] using (exteriorPower.map q f ⟨x,hx⟩).property

/-- Conjugation also preserves the precise degree-one shift. -/
theorem conjugate_degree (e : M ≃ₗ[R] N)
    (D : Module.End R (ExteriorAlgebra R M))
    (hD : ∀ q x, x ∈ ⋀[R]^q M → D x ∈ ⋀[R]^(q+1) M)
    (q : ℕ) (x : ExteriorAlgebra R N) (hx : x ∈ ⋀[R]^q N) :
    conjugate e D x ∈ ⋀[R]^(q+1) N :=
  map_mem_exteriorPower e.toLinearMap
    (hD q _ (map_mem_exteriorPower e.symm.toLinearMap hx))

end PaperVerification.ExteriorDerivationTransport
end
end
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExteriorDerivationTransport"

section ComponentSource_8
/- Original module: PaperVerification.ChevalleyEilenbergExterior -/


/-!
# The intrinsic Chevalley--Eilenberg exterior differential

For a finite-dimensional Lie algebra, the Chevalley--Eilenberg differential
is the odd derivation of the exterior algebra on its dual whose value on a
one-cochain is the negative bracket dual.  The predicate below spells out
that definition using the actual exterior pairing.  The uniqueness theorem
is proved from nondegeneracy of that pairing, not assumed.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.ChevalleyEilenbergExterior

open ExteriorQuadraticDifferential

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L]

/-- The intrinsic defining property of the ordinary CE exterior differential.
The quadratic value is an actual second exterior power of the dual. -/
def IsDifferential (D : Module.End K (ExteriorAlgebra K (Module.Dual K L))) : Prop :=
  IsOddDerivation D ∧ ∀ α : Module.Dual K L,
    ∃ ω : ⋀[K]^2 (Module.Dual K L),
      D (ExteriorAlgebra.ι K α) = (ω : ExteriorAlgebra K (Module.Dual K L)) ∧
      ∀ x y : L, exteriorPower.pairingDual K L 2 ω
        (exteriorPower.ιMulti K 2 ![x,y]) = -α ⁅x,y⁆

/-- The intrinsic defining equations specify a unique actual operator. -/
theorem differential_unique
    {D E : Module.End K (ExteriorAlgebra K (Module.Dual K L))}
    (hD : IsDifferential D) (hE : IsDifferential E) : D = E := by
  apply oddDerivation_ext hD.1 hE.1
  intro α
  obtain ⟨ω,hω,hωeval⟩ := hD.2 α
  obtain ⟨η,hη,hηeval⟩ := hE.2 α
  have heq : ω = η := ExteriorTwoFormEvaluation.pairingDual_injective_on_pairs ω η
    (fun x y ↦ (hωeval x y).trans (hηeval x y).symm)
  rw [hω,hη,heq]

end PaperVerification.ChevalleyEilenbergExterior
end
end
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ChevalleyEilenbergExterior"

section ComponentSource_9
/- Original module: PaperVerification.TwoStepChevalleyEilenberg -/


/-!
# The actual Chevalley--Eilenberg differential of the two-step Lie algebra

Every original pair of exterior two-forms is allowed. The constructed
operator acts on the genuine exterior algebra of the dual of the actual
ordinary Lie algebra. It satisfies the intrinsic CE equations, is their
unique solution, squares to zero, and has cohomological degree one.
The same operator is identified with the already constructed exterior and
Koszul models by explicit linear and algebra equivalences.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoStepChevalleyEilenberg

open ExteriorQuadraticDifferential ExteriorDerivationTransport
open CentralLieCochainCoordinates

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

instance (f g : ⋀[K]^2 M) : FiniteDimensional K (L f g) :=
  inferInstanceAs (FiniteDimensional K (Module.Dual K M × (Fin 2 → K)))

/-- All actual cochains, with their ordinary exterior multiplication. -/
def cochainEquiv (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K (TwoStepExteriorComplex.ExtendedModule K M) ≃ₐ[K]
      ExteriorAlgebra K (Module.Dual K (L f g)) :=
  mapEquiv (oneCochainEquiv f g)

/-- The differential on the actual exterior algebra of Lie one-cochains. -/
def differential (f g : ⋀[K]^2 M) :
    Module.End K (ExteriorAlgebra K (Module.Dual K (L f g))) :=
  conjugate (oneCochainEquiv f g) (TwoStepExteriorComplex.d f g)

/-- The prescribed negative bracket dual as an actual quadratic cochain. -/
def bracketDualTwoForm (f g : ⋀[K]^2 M) (α : Module.Dual K (L f g)) :
    ⋀[K]^2 (Module.Dual K (L f g)) :=
  ((oneCochainEquiv f g).symm α).2 0 • originalTwoCochain f g f +
    ((oneCochainEquiv f g).symm α).2 1 • originalTwoCochain f g g

/-- The included original form is literally its exterior cochain image. -/
theorem originalTwoCochain_coe (f g h : ⋀[K]^2 M) :
    (originalTwoCochain f g h : ExteriorAlgebra K (Module.Dual K (L f g))) =
      cochainEquiv f g (TwoStepExteriorComplex.baseMap (h : ExteriorAlgebra K M)) := by
  simp only [originalTwoCochain, exteriorPower.coe_map, cochainEquiv, mapEquiv_apply,
    TwoStepExteriorComplex.baseMap, TwoStepExteriorComplex.inclusion]
  exact (DFunLike.congr_fun
    (ExteriorAlgebra.map_comp_map (LinearMap.inl K M (Fin 2 → K))
      (oneCochainEquiv f g).toLinearMap) (h : ExteriorAlgebra K M)).symm

/-- The differential has the genuine bracket-dual value on every one-cochain. -/
theorem differential_generator (f g : ⋀[K]^2 M) (α : Module.Dual K (L f g)) :
    differential f g (ExteriorAlgebra.ι K α) =
      (bracketDualTwoForm f g α : ExteriorAlgebra K (Module.Dual K (L f g))) := by
  rw [differential, conjugate_apply, mapEquiv_symm_ι]
  change mapEquiv (oneCochainEquiv f g)
    (ExteriorQuadraticDifferential.differential _ _ _ _
      (ExteriorAlgebra.ι K ((oneCochainEquiv f g).symm α))) = _
  rw [ExteriorQuadraticDifferential.differential_generator]
  change cochainEquiv f g
      (((oneCochainEquiv f g).symm α).2 0 • TwoStepExteriorComplex.baseMap (f : ExteriorAlgebra K M) +
        ((oneCochainEquiv f g).symm α).2 1 • TwoStepExteriorComplex.baseMap (g : ExteriorAlgebra K M)) =
    ((oneCochainEquiv f g).symm α).2 0 •
        (originalTwoCochain f g f : ExteriorAlgebra K (Module.Dual K (L f g))) +
      ((oneCochainEquiv f g).symm α).2 1 •
        (originalTwoCochain f g g : ExteriorAlgebra K (Module.Dual K (L f g)))
  rw [map_add, map_smul, map_smul, originalTwoCochain_coe, originalTwoCochain_coe]

/-- The constructed map satisfies the usual odd Leibniz rule. -/
theorem differential_isOddDerivation (f g : ⋀[K]^2 M) : IsOddDerivation (differential f g) :=
  conjugate_isOddDerivation _ _ (TwoStepExteriorComplex.d_isOddDerivation f g)

/-- Intrinsic identification with the ordinary CE differential, including
its sign convention and all one-cochains. -/
theorem differential_isChevalleyEilenberg (f g : ⋀[K]^2 M) :
    ChevalleyEilenbergExterior.IsDifferential (differential f g) := by
  refine ⟨differential_isOddDerivation f g, ?_⟩
  intro α
  refine ⟨bracketDualTwoForm f g α, differential_generator f g α, ?_⟩
  intro x y
  simp only [bracketDualTwoForm, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, originalTwoCochain_pairing, smul_eq_mul]
  simpa only [LinearEquiv.apply_symm_apply] using
    (negative_bracket_dual f g ((oneCochainEquiv f g).symm α) x y).symm

/-- These defining equations admit no different exterior operator. -/
theorem differential_unique (f g : ⋀[K]^2 M)
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K (L f g))))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) : D = differential f g :=
  ChevalleyEilenbergExterior.differential_unique hD (differential_isChevalleyEilenberg f g)

/-- The ordinary CE differential squares to zero for every pair of forms. -/
theorem differential_square_zero (f g : ⋀[K]^2 M)
    (x : ExteriorAlgebra K (Module.Dual K (L f g))) :
    differential f g (differential f g x) = 0 :=
  conjugate_square_zero _ _ (TwoStepExteriorComplex.d_square_zero f g) x

/-- The ordinary CE differential raises the actual exterior degree by one. -/
theorem differential_mem_exteriorPower (f g : ⋀[K]^2 M) {q : ℕ}
    {x : ExteriorAlgebra K (Module.Dual K (L f g))}
    (hx : x ∈ ⋀[K]^q (Module.Dual K (L f g))) :
    differential f g x ∈ ⋀[K]^(q+1) (Module.Dual K (L f g)) :=
  conjugate_degree _ _ (fun _ _ hx ↦ TwoStepExteriorComplex.d_mem_exteriorPower f g hx) q x hx

/-- The original exterior model and the explicit Koszul operator are the
same linear map by their definitions, not merely equal in dimension. -/
theorem exterior_d_eq_koszul_operator (f g : ⋀[K]^2 M) :
    TwoStepExteriorComplex.d f g = TwoCentralKoszulOperator.operator f g := rfl

/-- The cochain coordinate equivalence intertwines the actual differentials. -/
theorem cochainEquiv_d (f g : ⋀[K]^2 M)
    (x : ExteriorAlgebra K (TwoStepExteriorComplex.ExtendedModule K M)) :
    differential f g (cochainEquiv f g x) = cochainEquiv f g (TwoStepExteriorComplex.d f g x) := by
  simp only [differential, cochainEquiv, conjugate_apply, AlgEquiv.symm_apply_apply]

end PaperVerification.TwoStepChevalleyEilenberg
end
end
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepChevalleyEilenberg"

section ComponentSource_10
/- Original module: PaperVerification.FoldedComplexHomology -/


/-!
# Homology of a folded three-term complex

For a genuine complex `A₂ → A₁ → A₀`, place its three terms in one module
`A₀ × (A₁ × A₂)` and retain the original differential. The homology of this
square-zero endomorphism is canonically the product of the cokernel at `A₀`,
the usual middle homology, and the kernel at `A₂`.

All homology groups below are actual kernel/image quotients. The final
comparison also identifies this quotient with Mathlib's categorical homology.
-/

@[expose] public section
noncomputable section

universe u v

namespace PaperVerification.FoldedComplexHomology

open CategoryTheory

variable {R : Type u} [Ring R]
  {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  (d₁ : A₁ →ₗ[R] A₀) (d₂ : A₂ →ₗ[R] A₁)

/-- The original two differentials, folded into one square-zero map. -/
def differential : (A₀ × (A₁ × A₂)) →ₗ[R] A₀ × (A₁ × A₂) where
  toFun x := (d₁ x.2.1, (d₂ x.2.2, 0))
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem differential_apply (x : A₀ × (A₁ × A₂)) :
    differential d₁ d₂ x = (d₁ x.2.1, (d₂ x.2.2, 0)) := rfl

/-- Squaring the folded map is exactly the original complex relation. -/
theorem differential_sq (h : d₁.comp d₂ = 0) :
    (differential d₁ d₂).comp (differential d₁ d₂) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun h x.2.2
  · apply Prod.ext
    · exact d₂.map_zero
    · rfl

variable (h : d₁.comp d₂ = 0)

/-- The original second differential with codomain restricted to cycles. -/
def middleToCycles : A₂ →ₗ[R] LinearMap.ker d₁ :=
  d₂.codRestrict _ (fun x ↦ LinearMap.congr_fun h x)

/-- The folded differential with codomain restricted to its actual kernel. -/
def toCycles : (A₀ × (A₁ × A₂)) →ₗ[R] LinearMap.ker (differential d₁ d₂) :=
  (differential d₁ d₂).codRestrict _
    (fun x ↦ LinearMap.congr_fun (differential_sq d₁ d₂ h) x)

/-- The middle component of a folded cycle is an original middle cycle. -/
def middleCycle : LinearMap.ker (differential d₁ d₂) →ₗ[R] LinearMap.ker d₁ :=
  (((LinearMap.fst R A₁ A₂).comp (LinearMap.snd R A₀ (A₁ × A₂))).comp
    (LinearMap.ker (differential d₁ d₂)).subtype).codRestrict _ (fun x ↦ by
      have hx := x.property
      change differential d₁ d₂ x.val = 0 at hx
      exact congrArg Prod.fst hx)

/-- The last component of a folded cycle belongs to the original last kernel. -/
def lastCycle : LinearMap.ker (differential d₁ d₂) →ₗ[R] LinearMap.ker d₂ :=
  (((LinearMap.snd R A₁ A₂).comp (LinearMap.snd R A₀ (A₁ × A₂))).comp
    (LinearMap.ker (differential d₁ d₂)).subtype).codRestrict _ (fun x ↦ by
      have hx := x.property
      change differential d₁ d₂ x.val = 0 at hx
      exact congrArg (fun y : A₀ × (A₁ × A₂) ↦ y.2.1) hx)

/-- The canonical comparison on cycles, using the original quotient maps. -/
def comparison : LinearMap.ker (differential d₁ d₂) →ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  ((LinearMap.range d₁).mkQ.comp
    ((LinearMap.fst R A₀ (A₁ × A₂)).comp
      (LinearMap.ker (differential d₁ d₂)).subtype)).prod
    (((LinearMap.range (middleToCycles d₁ d₂ h)).mkQ.comp
      (middleCycle d₁ d₂)).prod (lastCycle d₁ d₂))

/-- Every triple of original homology classes has a folded cycle representative. -/
theorem comparison_surjective : Function.Surjective (comparison d₁ d₂ h) := by
  rintro ⟨a, b, c⟩
  obtain ⟨a, rfl⟩ := (LinearMap.range d₁).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (LinearMap.range (middleToCycles d₁ d₂ h)).mkQ_surjective b
  refine ⟨⟨(a, (b.val, c.val)), ?_⟩, ?_⟩
  · change (d₁ b.val, (d₂ c.val, 0)) = (0, (0, 0))
    exact Prod.ext b.property (Prod.ext c.property rfl)
  · rfl

/-- A folded cycle maps to zero precisely when it is a folded boundary. -/
theorem comparison_ker :
    LinearMap.ker (comparison d₁ d₂ h) = LinearMap.range (toCycles d₁ d₂ h) := by
  ext x
  constructor
  · intro hx
    change comparison d₁ d₂ h x = 0 at hx
    have h₀ : (LinearMap.range d₁).mkQ x.val.1 = 0 := congrArg Prod.fst hx
    have h₁ : (LinearMap.range (middleToCycles d₁ d₂ h)).mkQ
        (middleCycle d₁ d₂ x) = 0 :=
      congrArg (fun y ↦ y.2.1) hx
    have h₂ : lastCycle d₁ d₂ x = 0 := congrArg (fun y ↦ y.2.2) hx
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp h₀
    obtain ⟨c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).mp h₁
    refine ⟨(0, (b, c)), ?_⟩
    apply Subtype.ext
    exact Prod.ext hb (Prod.ext (congrArg Subtype.val hc) (congrArg Subtype.val h₂).symm)
  · rintro ⟨y, rfl⟩
    change comparison d₁ d₂ h (toCycles d₁ d₂ h y) = 0
    apply Prod.ext
    · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y.2.1, rfl⟩
    · apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y.2.2, rfl⟩
      · apply Subtype.ext
        rfl

/-- The actual kernel/image quotient of the folded differential. -/
abbrev Homology :=
  LinearMap.ker (differential d₁ d₂) ⧸ LinearMap.range (toCycles d₁ d₂ h)

/-- The canonical linear equivalence between folded and original homology. -/
def homologyEquiv : Homology d₁ d₂ h ≃ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  (Submodule.quotEquivOfEq _ _ (comparison_ker d₁ d₂ h).symm).trans
    ((comparison d₁ d₂ h).quotKerEquivOfSurjective (comparison_surjective d₁ d₂ h))

/-- The equivalence sends the class of a cycle to its three original classes. -/
@[simp] theorem homologyEquiv_mk (x : LinearMap.ker (differential d₁ d₂)) :
    homologyEquiv d₁ d₂ h (Submodule.Quotient.mk x) = comparison d₁ d₂ h x := by
  simp [homologyEquiv]

/-- The same folded differential as an actual short complex of modules. -/
def shortComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (differential d₁ d₂) (differential d₁ d₂)
    (differential_sq d₁ d₂ h)

/-- Mathlib's categorical homology has the same canonical decomposition. -/
def categoricalHomologyEquiv : (shortComplex d₁ d₂ h).homology ≃ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  (shortComplex d₁ d₂ h).moduleCatHomologyIso.toLinearEquiv.trans
    (homologyEquiv d₁ d₂ h)

section Dimension

variable {K : Type u} [DivisionRing K]
  {V₀ V₁ V₂ : Type v}
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module K V₀] [Module K V₁] [Module K V₂]
  [Module.Finite K V₀] [Module.Finite K V₁] [Module.Finite K V₂]
  (f₁ : V₁ →ₗ[K] V₀) (f₂ : V₂ →ₗ[K] V₁) (hf : f₁.comp f₂ = 0)

/-- Dimensions add because the actual homology groups are linearly equivalent. -/
theorem finrank_homology :
    Module.finrank K (Homology f₁ f₂ hf) =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        (Module.finrank K
          (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
          Module.finrank K (LinearMap.ker f₂)) := by
  rw [(homologyEquiv f₁ f₂ hf).finrank_eq]
  simp only [Module.finrank_prod]

/-- The same dimension equality for Mathlib's categorical homology object. -/
theorem finrank_categoricalHomology :
    Module.finrank K (shortComplex f₁ f₂ hf).homology =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        (Module.finrank K
          (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
          Module.finrank K (LinearMap.ker f₂)) := by
  rw [(categoricalHomologyEquiv f₁ f₂ hf).finrank_eq]
  simp only [Module.finrank_prod]

/-- The Euler identity for the three actual homology quotients. -/
theorem middle_finrank_euler :
    Module.finrank K (V₀ ⧸ LinearMap.range f₁) + Module.finrank K (LinearMap.ker f₂) +
        Module.finrank K V₁ =
      Module.finrank K
        (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
        (Module.finrank K V₀ + Module.finrank K V₂) := by
  have h₀ := (LinearMap.range f₁).finrank_quotient_add_finrank
  have h₁ := (LinearMap.range (middleToCycles f₁ f₂ hf)).finrank_quotient_add_finrank
  have h₂ := f₁.finrank_range_add_finrank_ker
  have h₃ := (middleToCycles f₁ f₂ hf).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (middleToCycles f₁ f₂ hf) = LinearMap.ker f₂ :=
    LinearMap.ker_codRestrict _ _ _
  rw [hk] at h₃
  omega

/-- For a complex with zero Euler characteristic, total folded homology has
twice the sum of the dimensions of its two end homology groups. -/
theorem finrank_homology_of_euler_zero
    (hdim : Module.finrank K V₁ = Module.finrank K V₀ + Module.finrank K V₂) :
    Module.finrank K (Homology f₁ f₂ hf) =
      2 * (Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        Module.finrank K (LinearMap.ker f₂)) := by
  have he := middle_finrank_euler f₁ f₂ hf
  rw [finrank_homology]
  omega

/-- When the two end homology groups have equal dimension, the total is four
times the dimension of the original cokernel. The equal dimension is the
separate duality input in the paper's two-generator exterior complex. -/
theorem finrank_homology_four_cokernel
    (hdim : Module.finrank K V₁ = Module.finrank K V₀ + Module.finrank K V₂)
    (hdual : Module.finrank K (LinearMap.ker f₂) =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁)) :
    Module.finrank K (Homology f₁ f₂ hf) =
      4 * Module.finrank K (V₀ ⧸ LinearMap.range f₁) := by
  rw [finrank_homology_of_euler_zero f₁ f₂ hf hdim, hdual]
  omega

end Dimension

end PaperVerification.FoldedComplexHomology
end
end
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.FoldedComplexHomology"

section ComponentSource_11
/- Original module: PaperVerification.SquareZeroHomologyConjugacy -/


/-!
# Actual homology is invariant under linear conjugacy

A linear equivalence intertwining two square-zero endomorphisms maps cycles
to cycles and boundaries to boundaries. Its induced quotient equivalence is
then transported through Mathlib's canonical `moduleCatHomologyIso`, giving
an equivalence of the actual categorical homology objects.
-/

@[expose] public section
noncomputable section

universe u v

namespace PaperVerification.SquareZeroHomologyConjugacy

open CategoryTheory

variable {R : Type u} [Ring R]
  {A B : Type v} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
  (D : A →ₗ[R] A) (E : B →ₗ[R] B)

/-- A square-zero endomorphism regarded as an ordinary short complex. -/
def complex (hD : D.comp D = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk D D hD

variable (e : A ≃ₗ[R] B) (he : ∀ x, e (D x) = E (e x))

/-- The original linear equivalence restricts to an equivalence of kernels. -/
def cyclesEquiv : LinearMap.ker D ≃ₗ[R] LinearMap.ker E where
  toFun x := ⟨e x.val, by
    change E (e x.val) = 0
    exact (he x.val).symm.trans ((congrArg e x.property).trans e.map_zero)⟩
  invFun y := ⟨e.symm y.val, by
    apply e.injective
    calc
      e (D (e.symm y.val)) = E (e (e.symm y.val)) := he _
      _ = E y.val := congrArg E (e.apply_symm_apply y.val)
      _ = 0 := y.property
      _ = e 0 := e.map_zero.symm⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' r x := Subtype.ext (e.map_smul r x.val)

@[simp] theorem cyclesEquiv_apply_val (x : LinearMap.ker D) :
    (cyclesEquiv D E e he x).val = e x.val := rfl

variable (hD : D.comp D = 0) (hE : E.comp E = 0)

/-- This kernel equivalence maps the actual boundary submodule onto the
actual boundary submodule. -/
theorem map_boundaries :
    (LinearMap.range (complex D hD).moduleCatToCycles).map
      (cyclesEquiv D E e he).toLinearMap =
      LinearMap.range (complex E hE).moduleCatToCycles := by
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨e a, Subtype.ext (he a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(complex D hD).moduleCatToCycles (e.symm b), ⟨e.symm b, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (he (e.symm b)).trans (congrArg E (e.apply_symm_apply b))

/-- The induced equivalence of the literal kernel/image quotients. -/
def quotientHomologyEquiv :
    (LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) ≃ₗ[R]
      (LinearMap.ker E ⧸ LinearMap.range (complex E hE).moduleCatToCycles) :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv D E e he) (map_boundaries D E e he hD hE)

/-- The induced map sends the class of a cycle to the class of its original
image under `e`. -/
@[simp] theorem quotientHomologyEquiv_mk (x : LinearMap.ker D) :
    quotientHomologyEquiv D E e he hD hE (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cyclesEquiv D E e he x) := rfl

/-- Conjugacy preserves Mathlib's actual short-complex homology. -/
def categoricalHomologyEquiv : (complex D hD).homology ≃ₗ[R] (complex E hE).homology :=
  (complex D hD).moduleCatHomologyIso.toLinearEquiv.trans
    ((quotientHomologyEquiv D E e he hD hE).trans
      (complex E hE).moduleCatHomologyIso.symm.toLinearEquiv)

/-- Under Mathlib's canonical quotient identifications, categorical homology
conjugacy is exactly the explicit map on classes of cycles. -/
@[simp] theorem categoricalHomologyEquiv_quotient (x : LinearMap.ker D) :
    (complex E hE).moduleCatHomologyIso.toLinearEquiv
      (categoricalHomologyEquiv D E e he hD hE
        ((complex D hD).moduleCatHomologyIso.toLinearEquiv.symm (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk (cyclesEquiv D E e he x) := by
  change (complex E hE).moduleCatHomologyIso.toLinearEquiv
    ((complex E hE).moduleCatHomologyIso.toLinearEquiv.symm
      (quotientHomologyEquiv D E e he hD hE
        ((complex D hD).moduleCatHomologyIso.toLinearEquiv
          ((complex D hD).moduleCatHomologyIso.toLinearEquiv.symm
            (Submodule.Quotient.mk x))))) = _
  exact ((complex E hE).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply _).trans
    ((congrArg (quotientHomologyEquiv D E e he hD hE)
      ((complex D hD).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply _)).trans
        (quotientHomologyEquiv_mk D E e he hD hE x))

end PaperVerification.SquareZeroHomologyConjugacy
end
end
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SquareZeroHomologyConjugacy"

section ComponentSource_12
/- Original module: PaperVerification.SquareZeroHomologyGrading -/


/-!
# The inherited grading on actual square-zero homology

The homology grading is the subquotient grading of `ker D / im D` inherited
from the original graded module. A homogeneous conjugacy preserves this
grading, with the explicit map on cycle classes constructed in
`SquareZeroHomologyConjugacy`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.SquareZeroHomologyGrading

open SquareZeroHomologyConjugacy

variable {R : Type u} [Ring R]
  {A B : Type v} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- A degree-zero homogeneous linear equivalence transports the entire
internal grading, not merely the dimensions of its pieces. -/
theorem map_eq_of_homogeneous
    (G : TauCeti.InternalGrading R A) (H : TauCeti.InternalGrading R B)
    (e : A ≃ₗ[R] B)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    G.map e = H := by
  apply TauCeti.InternalGrading.ext
  intro p
  ext y
  rw [G.mem_map_piece_iff]
  constructor
  · intro hy
    simpa using he hy
  · intro hy
    simpa using he.linearEquiv_symm hy

variable (G : TauCeti.InternalGrading R A) (D : A →ₗ[R] A)
  (hD : D.comp D = 0) {δ : ℤ}
  (hdeg : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece δ)

/-- Restricting the codomain of a homogeneous differential to its kernel
retains its original degree. -/
theorem toCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (complex D hD).moduleCatToCycles
      G.piece (G.ker hdeg).piece δ := by
  intro p x hx
  apply (G.mem_ker_piece hdeg).2
  exact hdeg hx

/-- The actual quotient of homogeneous cycles by homogeneous boundaries. -/
def homologyGrading :
    TauCeti.InternalGrading R
      (LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) :=
  (G.ker hdeg).quotient (LinearMap.range (complex D hD).moduleCatToCycles)
    (toCycles_homogeneous G D hD hdeg).isHomogeneous_range

/-- A homogeneous homology class has a cycle representative of the same
degree in the original module. -/
theorem mem_homologyGrading_iff {p : ℤ}
    {z : LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles} :
    z ∈ (homologyGrading G D hD hdeg).piece p ↔
      ∃ x : LinearMap.ker D, x.val ∈ G.piece p ∧ Submodule.Quotient.mk x = z := by
  rw [homologyGrading, TauCeti.InternalGrading.mem_quotient_piece_iff]
  simp only [TauCeti.InternalGrading.mem_ker_piece]

/-- The class of a homogeneous cycle has that cycle's original degree. -/
theorem mk_mem_homologyGrading {p : ℤ} {x : LinearMap.ker D}
    (hx : x.val ∈ G.piece p) :
    (Submodule.Quotient.mk x :
      LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) ∈
      (homologyGrading G D hD hdeg).piece p :=
  (mem_homologyGrading_iff G D hD hdeg).2 ⟨x, hx, rfl⟩

variable (H : TauCeti.InternalGrading R B) (E : B →ₗ[R] B)
  (hE : E.comp E = 0)
  (hdegE : TauCeti.LinearMap.IsHomogeneous E H.piece H.piece δ)
  (e : A ≃ₗ[R] B) (he : ∀ x, e (D x) = E (e x))
  (hgrade : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)

include hgrade in
/-- The original homogeneous conjugacy restricts to homogeneous cycles. -/
theorem cyclesEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (cyclesEquiv D E e he).toLinearMap
      (G.ker hdeg).piece (H.ker hdegE).piece 0 := by
  intro p x hx
  apply (H.mem_ker_piece hdegE).2
  exact hgrade ((G.mem_ker_piece hdeg).1 hx)

include hgrade in
/-- The induced map on actual kernel/image quotients is homogeneous. -/
theorem quotientHomologyEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (quotientHomologyEquiv D E e he hD hE).toLinearMap
      (homologyGrading G D hD hdeg).piece (homologyGrading H E hE hdegE).piece 0 := by
  intro p z hz
  obtain ⟨x, hx, rfl⟩ := (mem_homologyGrading_iff G D hD hdeg).1 hz
  rw [LinearEquiv.coe_coe, quotientHomologyEquiv_mk]
  apply mk_mem_homologyGrading H E hE hdegE
  exact hgrade hx

include hgrade in
/-- Conjugacy identifies the inherited quotient gradings exactly. -/
theorem map_homologyGrading :
    (homologyGrading G D hD hdeg).map (quotientHomologyEquiv D E e he hD hE) =
      homologyGrading H E hE hdegE :=
  map_eq_of_homogeneous _ _ _
    (quotientHomologyEquiv_homogeneous G D hD hdeg H E hE hdegE e he hgrade)

/-- The induced equivalence restricts to each actual cohomology degree. -/
def homogeneousPieceEquiv (p : ℤ) :
    (homologyGrading G D hD hdeg).piece p ≃ₗ[R]
      (homologyGrading H E hE hdegE).piece p :=
  (quotientHomologyEquiv D E e he hD hE).ofSubmodules _ _ (by
    have hp := congrArg (fun J : TauCeti.InternalGrading R _ ↦ J.piece p)
      (map_homologyGrading G D hD hdeg H E hE hdegE e he hgrade)
    simpa only [TauCeti.InternalGrading.map_piece] using hp)

/-- A degree absent from the original module is absent from its actual
homology subquotient. -/
theorem homologyGrading_piece_eq_bot {p : ℤ} (hp : G.piece p = ⊥) :
    (homologyGrading G D hD hdeg).piece p = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := (mem_homologyGrading_iff G D hD hdeg).1 hz
  have hx0 : x.val = 0 := by simpa only [hp, Submodule.mem_bot] using hx
  have hx' : x = 0 := Subtype.ext hx0
  rw [hx']
  exact Submodule.zero_mem _

end PaperVerification.SquareZeroHomologyGrading
end
end
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SquareZeroHomologyGrading"

section ComponentSource_13
/- Original module: PaperVerification.FoldedComplexHomologyGrading -/


/-!
# The genuine graded homology of a folded three-term complex

Suppose `A₂ → A₁ → A₀` has differentials of internal degree zero. On
`A₀ × (A₁ × A₂)`, shift the last two gradings by one and two respectively.
The folded differential then has cohomological degree one. Its inherited
kernel/image quotient grading is identified with the original three
homology gradings, with exactly these shifts.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.FoldedComplexHomologyGrading

open FoldedComplexHomology

variable {R : Type u} [Ring R]
  {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  (G₀ : TauCeti.InternalGrading R A₀)
  (G₁ : TauCeti.InternalGrading R A₁)
  (G₂ : TauCeti.InternalGrading R A₂)

/-- Total cohomological grading: the original internal degree minus the
position in the length-two complex. -/
def totalGrading : TauCeti.InternalGrading R (A₀ × (A₁ × A₂)) :=
  G₀.prod ((G₁.shift 1).prod (G₂.shift 2))

@[simp] theorem mem_totalGrading {p : ℤ} {x : A₀ × (A₁ × A₂)} :
    x ∈ (totalGrading G₀ G₁ G₂).piece p ↔
      x.1 ∈ G₀.piece p ∧ x.2.1 ∈ G₁.piece (p + 1) ∧
        x.2.2 ∈ G₂.piece (p + 2) := by
  simp only [totalGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod]

variable (d₁ : A₁ →ₗ[R] A₀) (d₂ : A₂ →ₗ[R] A₁)
  (h : d₁.comp d₂ = 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)

include hd₁ hd₂ in
/-- Folding the internal degree-zero maps gives a differential of total
cohomological degree one. -/
theorem differential_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (differential d₁ d₂)
      (totalGrading G₀ G₁ G₂).piece (totalGrading G₀ G₁ G₂).piece 1 := by
  intro p x hx
  obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_totalGrading G₀ G₁ G₂).1 hx
  apply (mem_totalGrading G₀ G₁ G₂).2
  refine ⟨?_, ?_, (G₂.piece _).zero_mem⟩
  · simpa only [differential_apply, add_zero] using hd₁ hx₁
  · simpa [add_assoc] using hd₂ hx₂

/-- The actual folded homology, graded by its homogeneous cycles and
boundaries in the original total module. -/
def homologyGrading : TauCeti.InternalGrading R (Homology d₁ d₂ h) :=
  SquareZeroHomologyGrading.homologyGrading (totalGrading G₀ G₁ G₂)
    (differential d₁ d₂) (differential_sq d₁ d₂ h)
    (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)

include hd₂ in
/-- The middle boundary map has internal degree zero after restricting its
codomain to the actual kernel of the first differential. -/
theorem middleToCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (middleToCycles d₁ d₂ h)
      G₂.piece (G₁.ker hd₁).piece 0 := by
  intro p x hx
  apply (G₁.mem_ker_piece hd₁).2
  exact hd₂ hx

/-- The original zeroth homology with its quotient grading. -/
def zerothGrading : TauCeti.InternalGrading R (A₀ ⧸ LinearMap.range d₁) :=
  G₀.quotient (LinearMap.range d₁) hd₁.isHomogeneous_range

/-- The original middle homology with its inherited subquotient grading. -/
def firstGrading :
    TauCeti.InternalGrading R
      (LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) :=
  (G₁.ker hd₁).quotient (LinearMap.range (middleToCycles d₁ d₂ h))
    (middleToCycles_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).isHomogeneous_range

/-- The original last homology with its kernel grading. -/
def secondGrading : TauCeti.InternalGrading R (LinearMap.ker d₂) :=
  G₂.ker hd₂

/-- The product of the original homology gradings, shifted by their complex
positions. Its factors are the actual three homology subquotients. -/
def factorsGrading : TauCeti.InternalGrading R
    ((A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂)) :=
  (zerothGrading G₀ G₁ d₁ hd₁).prod
    (((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).shift 1).prod
      ((secondGrading G₁ G₂ d₂ hd₂).shift 2))

@[simp] theorem mem_factorsGrading {p : ℤ}
    {x : (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂)} :
    x ∈ (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ↔
      x.1 ∈ (zerothGrading G₀ G₁ d₁ hd₁).piece p ∧
        x.2.1 ∈ (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ∧
        x.2.2 ∈ (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2) := by
  simp only [factorsGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod]

/-- The canonical comparison of actual homology classes preserves every
total cohomological degree. -/
theorem homologyEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (homologyEquiv d₁ d₂ h).toLinearMap
      (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece
      (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece 0 := by
  intro p z hz
  obtain ⟨x, hx, rfl⟩ :=
    (SquareZeroHomologyGrading.mem_homologyGrading_iff
      (totalGrading G₀ G₁ G₂) (differential d₁ d₂)
      (differential_sq d₁ d₂ h)
      (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)).1 hz
  obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_totalGrading G₀ G₁ G₂).1 hx
  rw [LinearEquiv.coe_coe, homologyEquiv_mk]
  simp only [factorsGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · exact G₀.mk_mem_quotient_piece (LinearMap.range d₁) hd₁.isHomogeneous_range hx₀
  · apply (G₁.ker hd₁).mk_mem_quotient_piece
      (LinearMap.range (middleToCycles d₁ d₂ h))
      (middleToCycles_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).isHomogeneous_range
    exact (G₁.mem_ker_piece hd₁).2 hx₁
  · exact (G₂.mem_ker_piece hd₂).2 hx₂

/-- The inherited grading on folded homology is exactly the product of the
three original homology gradings with their required shifts. -/
theorem map_homologyGrading :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).map (homologyEquiv d₁ d₂ h) =
      factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ :=
  SquareZeroHomologyGrading.map_eq_of_homogeneous _ _ _
    (homologyEquiv_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)

/-- The canonical equivalence in each actual cohomological degree. -/
def homogeneousPieceEquiv (p : ℤ) :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p :=
  (homologyEquiv d₁ d₂ h).ofSubmodules _ _ (by
    have hp := congrArg (fun J : TauCeti.InternalGrading R _ ↦ J.piece p)
      (map_homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)
    simpa only [TauCeti.InternalGrading.map_piece] using hp)

/-- A degree in the product grading consists of the three indicated
original homology degrees. -/
def factorsPieceEquiv (p : ℤ) :
    (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (zerothGrading G₀ G₁ d₁ hd₁).piece p ×
        ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ×
          (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2)) where
  toFun x :=
    let hx := (mem_factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).1 x.property
    (⟨x.val.1, hx.1⟩, (⟨x.val.2.1, hx.2.1⟩, ⟨x.val.2.2, hx.2.2⟩))
  invFun x := ⟨(x.1.val, (x.2.1.val, x.2.2.val)),
    (mem_factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).2
      ⟨x.1.property, x.2.1.property, x.2.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complete degreewise homology decomposition, expressed as an
equivalence of the original kernel/image subquotients in each degree. -/
def homogeneousHomologyEquiv (p : ℤ) :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (zerothGrading G₀ G₁ d₁ hd₁).piece p ×
        ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ×
          (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2)) :=
  (homogeneousPieceEquiv G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ p).trans
    (factorsPieceEquiv G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ p)

section Dimension

variable {K : Type u} [DivisionRing K]
  {V₀ V₁ V₂ : Type v}
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module K V₀] [Module K V₁] [Module K V₂]
  [Module.Finite K V₀] [Module.Finite K V₁] [Module.Finite K V₂]
  (J₀ : TauCeti.InternalGrading K V₀)
  (J₁ : TauCeti.InternalGrading K V₁)
  (J₂ : TauCeti.InternalGrading K V₂)
  (f₁ : V₁ →ₗ[K] V₀) (f₂ : V₂ →ₗ[K] V₁) (hf : f₁.comp f₂ = 0)
  (hf₁ : TauCeti.LinearMap.IsHomogeneous f₁ J₁.piece J₀.piece 0)
  (hf₂ : TauCeti.LinearMap.IsHomogeneous f₂ J₂.piece J₁.piece 0)

/-- Dimensions of genuine homogeneous cohomology add, with precisely the
degree shifts appearing in the paper's Lie-cohomology formula. -/
theorem finrank_homology_piece (p : ℤ) :
    Module.finrank K ((homologyGrading J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂).piece p) =
      Module.finrank K ((zerothGrading J₀ J₁ f₁ hf₁).piece p) +
        (Module.finrank K ((firstGrading J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂).piece (p + 1)) +
          Module.finrank K ((secondGrading J₁ J₂ f₂ hf₂).piece (p + 2))) := by
  rw [(homogeneousHomologyEquiv J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂ p).finrank_eq]
  simp only [Module.finrank_prod]

end Dimension

end PaperVerification.FoldedComplexHomologyGrading
end
end
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.FoldedComplexHomologyGrading"

section ComponentSource_14
/- Original module: PaperVerification.GradedDifferentialCochainComplex -/


/-!
# Actual cochain cohomology of a graded square-zero differential

A homogeneous differential of degree one defines an ordinary integer-indexed
cochain complex with term `G.piece q` in degree `q`. Its categorical homology
is canonically equivalent to the degree-`q` piece of the inherited global
kernel/image quotient. The boundary comparison uses homogeneous projection
of a genuine boundary preimage, so no degreewise exactness is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.GradedDifferentialCochainComplex

open CategoryTheory
open SquareZeroHomologyConjugacy SquareZeroHomologyGrading

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
  (G : TauCeti.InternalGrading R A) (D : A →ₗ[R] A)
  (hD : D.comp D = 0)
  (hd : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece 1)

/-- The original differential restricted to two consecutive pieces. -/
def pieceMap (p q : ℤ) (hpq : p + 1 = q) : G.piece p →ₗ[R] G.piece q :=
  (D.comp (G.piece p).subtype).codRestrict _ (fun x ↦ by
    change D x.val ∈ G.piece q
    simpa only [hpq] using hd x.property)

@[simp] theorem pieceMap_apply_val (p q : ℤ) (hpq : p + 1 = q) (x : G.piece p) :
    (pieceMap G D hd p q hpq x).val = D x.val := rfl

include hD in
/-- Consecutive restrictions retain the original square-zero identity. -/
theorem pieceMap_comp (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) :
    (pieceMap G D hd q r hqr).comp (pieceMap G D hd p q hpq) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun hD x.val

/-- The honest integer-indexed cochain complex of original homogeneous
pieces and the original restricted differential. -/
def cochainComplex : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (G.piece q))
    (fun q ↦ ModuleCat.ofHom (pieceMap G D hd q (q + 1) rfl))
    (fun q ↦ ModuleCat.hom_ext (pieceMap_comp G D hD hd q (q + 1) (q + 1 + 1) rfl rfl))

/-- The three original homogeneous pieces around one cohomological degree. -/
def degreeShortComplex (q : ℤ) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (pieceMap G D hd (q - 1) q (sub_add_cancel q 1))
    (pieceMap G D hd q (q + 1) rfl)
    (pieceMap_comp G D hD hd (q - 1) q (q + 1) (sub_add_cancel q 1) rfl)

/-- A degreewise cycle is an actual global cycle with the same underlying
element of the original module. -/
def cycleEmbedding (q : ℤ) :
    LinearMap.ker (pieceMap G D hd q (q + 1) rfl) →ₗ[R] LinearMap.ker D where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Sending a homogeneous cycle to its original global homology class. -/
def cycleComparison (q : ℤ) :
    LinearMap.ker (pieceMap G D hd q (q + 1) rfl) →ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (((LinearMap.range (complex D hD).moduleCatToCycles).mkQ).comp
    (cycleEmbedding G D hd q)).codRestrict _ (fun x ↦
      mk_mem_homologyGrading G D hD hd x.val.property)

/-- Every homogeneous global homology class has a homogeneous cycle
representative, and therefore comes from the degreewise complex. -/
theorem cycleComparison_surjective (q : ℤ) :
    Function.Surjective (cycleComparison G D hD hd q) := by
  intro z
  obtain ⟨x, hx, hclass⟩ := (mem_homologyGrading_iff G D hD hd).1 z.property
  refine ⟨⟨⟨x.val, hx⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    exact x.property
  · apply Subtype.ext
    exact hclass

/-- Global and degreewise boundaries agree. In the forward implication,
project a global boundary preimage to degree `q - 1`. -/
theorem cycleComparison_ker (q : ℤ) :
    LinearMap.ker (cycleComparison G D hD hd q) =
      LinearMap.range (degreeShortComplex G D hD hd q).moduleCatToCycles := by
  ext x
  constructor
  · intro hx
    change cycleComparison G D hD hd q x = 0 at hx
    have hz := congrArg Subtype.val hx
    change (Submodule.Quotient.mk (cycleEmbedding G D hd q x) :
      LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) = 0 at hz
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz
    have ha' : D a = x.val.val := congrArg Subtype.val ha
    refine ⟨DirectSum.decompose G.piece a (q - 1), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hp := hd.map_decompose (q - 1) a
    rw [sub_add_cancel, ha', DirectSum.decompose_of_mem_same G.piece x.val.property] at hp
    exact hp
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a.val, rfl⟩

/-- The explicit kernel/image quotient of the degreewise complex is the
actual homogeneous component of the global kernel/image quotient. -/
def quotientHomologyEquiv (q : ℤ) :
    (LinearMap.ker (pieceMap G D hd q (q + 1) rfl) ⧸
      LinearMap.range (degreeShortComplex G D hD hd q).moduleCatToCycles) ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (Submodule.quotEquivOfEq _ _ (cycleComparison_ker G D hD hd q).symm).trans
    ((cycleComparison G D hD hd q).quotKerEquivOfSurjective
      (cycleComparison_surjective G D hD hd q))

/-- The degreewise quotient comparison sends each cycle to its original
homology class. -/
@[simp] theorem quotientHomologyEquiv_mk (q : ℤ)
    (x : LinearMap.ker (pieceMap G D hd q (q + 1) rfl)) :
    quotientHomologyEquiv G D hD hd q (Submodule.Quotient.mk x) =
      cycleComparison G D hD hd q x := by
  rfl

/-- The actual categorical homology of the degreewise short complex. -/
def shortComplexHomologyEquiv (q : ℤ) :
    (degreeShortComplex G D hD hd q).homology ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  (degreeShortComplex G D hD hd q).moduleCatHomologyIso.toLinearEquiv.trans
    (quotientHomologyEquiv G D hD hd q)

/-- Reindexing a homogeneous submodule changes no underlying element. -/
theorem eqToHom_piece_val {p q : ℤ} (hpq : p = q) (x : G.piece p) :
    ((eqToHom (congrArg (fun r ↦ ModuleCat.of R (G.piece r)) hpq)) x : G.piece q).val =
      x.val := by
  subst q
  rfl

/-- The restricted three-term complex is the corresponding part of the
actual integer-indexed cochain complex. -/
def cochainShortComplexIso (q : ℤ) :
    (cochainComplex G D hD hd).sc' (q - 1) q (q + 1) ≅
      degreeShortComplex G D hD hd q := by
  dsimp only [cochainComplex, degreeShortComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    ShortComplex.moduleCatMk]
  refine ShortComplex.isoMk
    (Iso.refl (ModuleCat.of R (G.piece (q - 1))))
    (Iso.refl (ModuleCat.of R (G.piece q)))
    (Iso.refl (ModuleCat.of R (G.piece (q + 1)))) ?_ ?_
  · simp only [Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [CochainComplex.of.d, pieceMap]
    exact (eqToHom_piece_val G (sub_add_cancel q 1)
      (pieceMap G D hd (q - 1) (q - 1 + 1) rfl x)).symm
  · simp [CochainComplex.of_d]

/-- Actual cochain cohomology in every integer degree is the corresponding
piece of the inherited global kernel/image quotient. -/
def cochainHomologyEquiv (q : ℤ) :
    (cochainComplex G D hD hd).homology q ≃ₗ[R]
      (homologyGrading G D hD hd).piece q :=
  ((cochainComplex G D hD hd).homologyIsoSc' (q - 1) q (q + 1)
    ((ComplexShape.up ℤ).prev_eq' (by exact sub_add_cancel q 1))
    ((ComplexShape.up ℤ).next_eq' rfl)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (cochainShortComplexIso G D hD hd q)).toLinearEquiv.trans
      (shortComplexHomologyEquiv G D hD hd q))

end PaperVerification.GradedDifferentialCochainComplex
end
end
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.GradedDifferentialCochainComplex"

section ComponentSource_15
/- Original module: PaperVerification.TwoCentralExteriorGrading -/


/-!
# Cohomological degrees in the central exterior decomposition

The grading is the actual exterior degree. Under the explicit four-summand
decomposition, the original, one-central-generator, and two-central-generator
terms have degree shifts zero, one, and two. In terms of the internal Koszul
weights (zero, two, four), this is precisely the rule `cohomological = internal
minus Koszul position` used after Proposition 5.4.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoCentralExteriorGrading

open AlternatingForms TwoCentralExteriorDecomposition TwoCentralKoszulOperator

variable {K M N' : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N'] [Module K N']

/-- Exterior algebra functoriality preserves the genuine integer grading. -/
theorem exteriorMap_homogeneous (f : M →ₗ[K] N') :
    TauCeti.LinearMap.IsHomogeneous (ExteriorAlgebra.map f).toLinearMap
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  rw [add_zero]
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx ⊢
    exact ExteriorDerivationTransport.map_mem_exteriorPower f hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- Multiplication by an actual degree-r form has that integer degree. -/
theorem exteriorMultiplication_homogeneous {r : ℕ} (a : ⋀[K]^r M) :
    TauCeti.LinearMap.IsHomogeneous (LinearMap.mulLeft K (a : ExteriorAlgebra K M))
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece (r : ℤ) := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q + (r : ℤ))]
    have hdeg : (q + (r : ℤ)).toNat = r + q.toNat := by omega
    rw [hdeg]
    exact SetLike.mul_mem_graded a.property hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- A degree-one map on every actual exterior power gives the corresponding
homogeneous map on the integer extension, including negative degrees. -/
theorem homogeneous_of_exterior_degree_one
    (D : Module.End K (ExteriorAlgebra K M))
    (hD : ∀ q x, x ∈ ⋀[K]^q M → D x ∈ ⋀[K]^(q+1) M) :
    TauCeti.LinearMap.IsHomogeneous D exteriorIntegerGrading.piece
      exteriorIntegerGrading.piece 1 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q+1)]
    have hdeg : (q+1).toNat = q.toNat+1 := by omega
    rw [hdeg]
    exact hD _ _ hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- The original internal Koszul gradings, with positions subtracted to
obtain the actual cohomological grading. -/
def foldedExteriorGrading : TauCeti.InternalGrading K
    (E K M × ((E K M × E K M) × E K M)) :=
  exteriorIntegerGrading.prod
    ((((exteriorIntegerGrading.prod exteriorIntegerGrading).shift (-2)).shift 1).prod
      ((exteriorIntegerGrading.shift (-4)).shift 2))

/-- Inverse Koszul coordinates preserve the genuine exterior degree. -/
theorem koszulCoordinates_symm_homogeneous :
    TauCeti.LinearMap.IsHomogeneous
      (koszulCoordinates (R := K) (M := M)).symm.toLinearMap
      foldedExteriorGrading.piece exteriorIntegerGrading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q z hz
  rw [add_zero]
  simp only [foldedExteriorGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece] at hz
  change z.1 ∈ (exteriorIntegerGrading (K := K) (M := M)).piece q ∧
    ((z.2.1.1 ∈ exteriorIntegerGrading.piece (q+1 + -2) ∧
      z.2.1.2 ∈ exteriorIntegerGrading.piece (q+1 + -2)) ∧
      z.2.2 ∈ exteriorIntegerGrading.piece (q+2 + -4)) at hz
  have hlift := exteriorMap_homogeneous (inc (R := K) (M := M))
  have ha : lift z.1 ∈ (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    simpa only [add_zero, lift, AlgHom.toLinearMap_apply] using hlift.map_mem hz.1
  have he₀ : e (R := K) (M := M) 0 ∈ ⋀[K]^1 (N K M) :=
    TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  have he₁ : e (R := K) (M := M) 1 ∈ ⋀[K]^1 (N K M) :=
    TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  have hb : e 0 * lift z.2.1.1 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 0,he₀⟩).map_mem
      (hlift.map_mem hz.2.1.1)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_one, Nat.cast_ofNat, show q+1 + -2+0+(1 : ℤ) = q by omega] using hh
  have hc : e 1 * lift z.2.1.2 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 1,he₁⟩).map_mem
      (hlift.map_mem hz.2.1.2)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_one, Nat.cast_ofNat, show q+1 + -2+0+(1 : ℤ) = q by omega] using hh
  have he₂ : e (R := K) (M := M) 0 * e 1 ∈ ⋀[K]^2 (N K M) :=
    SetLike.mul_mem_graded he₀ he₁
  have hd : e 0 * e 1 * lift z.2.2 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 0 * e 1,he₂⟩).map_mem
      (hlift.map_mem hz.2.2)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_ofNat, show q+2 + -4+0+(2 : ℤ) = q by omega] using hh
  change lift z.1 + e 0 * lift z.2.1.1 + e 1 * lift z.2.1.2 +
    e 0 * e 1 * lift z.2.2 ∈ _
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ha hb) hc) hd

/-- The forward coordinate map also preserves actual cohomological degree. -/
theorem koszulCoordinates_homogeneous :
    TauCeti.LinearMap.IsHomogeneous
      (koszulCoordinates (R := K) (M := M)).toLinearMap
      exteriorIntegerGrading.piece foldedExteriorGrading.piece 0 :=
  TauCeti.LinearMap.IsHomogeneous.linearEquiv_symm koszulCoordinates_symm_homogeneous

end PaperVerification.TwoCentralExteriorGrading
end
end
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoCentralExteriorGrading"

section ComponentSource_16
/- Original module: PaperVerification.FoldedComplexHomologyHilbert -/


/-!
# Hilbert series of genuine folded cohomology

These identities take dimensions only after constructing the degreewise
linear equivalences of actual homology. In particular, the graded quotient
and the ordinary cochain complex are both defined independently of the
Hilbert formulas they satisfy.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.FoldedComplexHomologyHilbert

open AlternatingForms

variable {K : Type u} [Field K]

section Conjugacy

variable {A B : Type v} [AddCommGroup A] [AddCommGroup B]
  [Module K A] [Module K B] [FiniteDimensional K A] [FiniteDimensional K B]
  (G : TauCeti.InternalGrading K A) (H : TauCeti.InternalGrading K B)
  (D : A →ₗ[K] A) (E : B →ₗ[K] B)
  (hD : D.comp D = 0) (hE : E.comp E = 0) {δ : ℤ}
  (hd : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece δ)
  (he : TauCeti.LinearMap.IsHomogeneous E H.piece H.piece δ)
  (e : A ≃ₗ[K] B) (hcomm : ∀ x, e (D x) = E (e x))
  (hgrade : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)

include hcomm hgrade in
/-- Homogeneous conjugacy preserves the genuine Hilbert series of the
inherited kernel/image quotient. -/
theorem hilbert_conjugacy :
    finiteHilbertLaurent (SquareZeroHomologyGrading.homologyGrading G D hD hd) =
      finiteHilbertLaurent (SquareZeroHomologyGrading.homologyGrading H E hE he) := by
  ext q
  simp only [finiteHilbertLaurent_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    (SquareZeroHomologyGrading.homogeneousPieceEquiv G D hD hd H E hE he e hcomm hgrade q).finrank_eq

end Conjugacy

section Folded

open FoldedComplexHomologyGrading

variable {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module K A₀] [Module K A₁] [Module K A₂]
  [FiniteDimensional K A₀] [FiniteDimensional K A₁] [FiniteDimensional K A₂]
  (G₀ : TauCeti.InternalGrading K A₀)
  (G₁ : TauCeti.InternalGrading K A₁)
  (G₂ : TauCeti.InternalGrading K A₂)
  (d₁ : A₁ →ₗ[K] A₀) (d₂ : A₂ →ₗ[K] A₁) (h : d₁.comp d₂ = 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)

/-- The full Laurent-polynomial identity for actual folded homology. -/
theorem hilbert_folded :
    finiteHilbertLaurent (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂) =
      finiteHilbertLaurent (zerothGrading G₀ G₁ d₁ hd₁) +
        (LaurentPolynomial.T (-1) *
            finiteHilbertLaurent (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂) +
          LaurentPolynomial.T (-2) *
            finiteHilbertLaurent (secondGrading G₁ G₂ d₂ hd₂)) := by
  ext q
  change (Module.finrank K ((homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece q) : ℤ) =
    (finiteHilbertLaurent (zerothGrading G₀ G₁ d₁ hd₁)).coeff q +
      ((LaurentPolynomial.T (-1) *
          finiteHilbertLaurent (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)).coeff q +
        (LaurentPolynomial.T (-2) *
          finiteHilbertLaurent (secondGrading G₁ G₂ d₂ hd₂)).coeff q)
  simp only [finiteHilbertLaurent_coeff, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_neg]
  rw [finrank_homology_piece]
  simp only [Nat.cast_add]
  rw [add_comm (1 : ℤ) q, add_comm (2 : ℤ) q]

/-- In each integer degree, the actual categorical cochain cohomology has
the sum of the three original homology dimensions, with their exact shifts. -/
theorem finrank_cochain_homology (q : ℤ) :
    Module.finrank K
      ((GradedDifferentialCochainComplex.cochainComplex (totalGrading G₀ G₁ G₂)
        (FoldedComplexHomology.differential d₁ d₂)
        (FoldedComplexHomology.differential_sq d₁ d₂ h)
        (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)).homology q) =
      Module.finrank K ((zerothGrading G₀ G₁ d₁ hd₁).piece q) +
        (Module.finrank K ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (q + 1)) +
          Module.finrank K ((secondGrading G₁ G₂ d₂ hd₂).piece (q + 2))) := by
  rw [(GradedDifferentialCochainComplex.cochainHomologyEquiv
    (totalGrading G₀ G₁ G₂) (FoldedComplexHomology.differential d₁ d₂)
    (FoldedComplexHomology.differential_sq d₁ d₂ h)
    (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂) q).finrank_eq]
  exact finrank_homology_piece G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ q

end Folded

end PaperVerification.FoldedComplexHomologyHilbert
end
end
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.FoldedComplexHomologyHilbert"

section ComponentSource_17
/- Original module: PaperVerification.TwoStepLieCohomology -/


/-!
# Actual Chevalley--Eilenberg cohomology after Proposition 5.4

The cochain complex below uses the actual exterior powers of the dual of
the original two-step Lie algebra and its uniquely characterized CE
differential. Its cohomology is Mathlib's categorical homology. The Hilbert
formula is derived through actual homogeneous equivalences of kernels and
images, followed by the independently proved exterior Koszul formulas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepLieCohomology

open AlternatingForms

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The paper's original two-step Lie algebra, with its actual bracket. -/
abbrev LieAlgebra (f g : ⋀[K]^2 M) := CentralLieCochainCoordinates.L f g

/-- All actual exterior cochains of that Lie algebra. -/
abbrev Cochains (f g : ⋀[K]^2 M) := ExteriorAlgebra K (Module.Dual K (LieAlgebra f g))

instance cochains_finite (f g : ⋀[K]^2 M) : FiniteDimensional K (Cochains f g) := by
  change FiniteDimensional K
    (ExteriorAlgebra K (Module.Dual K (CentralLieCochainCoordinates.L f g)))
  infer_instance

/-- Its ordinary exterior grading, extended by zero to negative integers. -/
def cochainGrading (f g : ⋀[K]^2 M) : TauCeti.InternalGrading K (Cochains f g) :=
  exteriorIntegerGrading

theorem differential_square (f g : ⋀[K]^2 M) :
    (TwoStepChevalleyEilenberg.differential f g).comp
      (TwoStepChevalleyEilenberg.differential f g) = 0 := by
  apply LinearMap.ext
  exact TwoStepChevalleyEilenberg.differential_square_zero f g

theorem differential_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (TwoStepChevalleyEilenberg.differential f g)
      (cochainGrading f g).piece (cochainGrading f g).piece 1 :=
  TwoCentralExteriorGrading.homogeneous_of_exterior_degree_one _
    (fun _ _ hx ↦ TwoStepChevalleyEilenberg.differential_mem_exteriorPower f g hx)

/-- The genuine integer-indexed Chevalley--Eilenberg cochain complex. -/
def cochainComplex (f g : ⋀[K]^2 M) : CochainComplex (ModuleCat K) ℤ :=
  GradedDifferentialCochainComplex.cochainComplex (cochainGrading f g)
    (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)
    (differential_homogeneous f g)

/-- Ordinary categorical cohomology of the actual CE cochain complex. -/
def cohomology (f g : ⋀[K]^2 M) (q : ℤ) : ModuleCat K :=
  (cochainComplex f g).homology q

/-- The literal total CE kernel/image quotient. -/
abbrev TotalCohomology (f g : ⋀[K]^2 M) :=
  LinearMap.ker (TwoStepChevalleyEilenberg.differential f g) ⧸
    LinearMap.range (SquareZeroHomologyConjugacy.complex
      (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)).moduleCatToCycles

instance totalCohomology_finite (f g : ⋀[K]^2 M) :
    FiniteDimensional K (TotalCohomology f g) :=
  inferInstanceAs (FiniteDimensional K
    (LinearMap.ker (TwoStepChevalleyEilenberg.differential f g) ⧸
      LinearMap.range ((TwoStepChevalleyEilenberg.differential f g).codRestrict
        (LinearMap.ker (TwoStepChevalleyEilenberg.differential f g))
        (fun x ↦ LinearMap.congr_fun (differential_square f g) x))))

/-- The inherited grading of the original total CE kernel/image quotient. -/
def cohomologyGrading (f g : ⋀[K]^2 M) :
    TauCeti.InternalGrading K (TotalCohomology f g) :=
  SquareZeroHomologyGrading.homologyGrading (cochainGrading f g)
    (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)
    (differential_homogeneous f g)

/-- Its degree-`q` piece is the actual categorical CE cohomology in degree
`q`, through the explicit homogeneous-cycle comparison. -/
def cohomologyEquiv (f g : ⋀[K]^2 M) (q : ℤ) :
    cohomology f g q ≃ₗ[K] (cohomologyGrading f g).piece q :=
  GradedDifferentialCochainComplex.cochainHomologyEquiv _ _ _ _ q

/-- Finiteness follows from the actual homogeneous subquotient of the
finite-dimensional exterior algebra. -/
instance cohomology_finite (f g : ⋀[K]^2 M) (q : ℤ) :
    FiniteDimensional K (cohomology f g q) :=
  Module.Finite.equiv (cohomologyEquiv f g q).symm

/-- The actual finite Poincare series, with coefficients justified below
as dimensions of categorical CE cohomology. -/
def poincarePolynomial (f g : ⋀[K]^2 M) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (cohomologyGrading f g)

theorem poincarePolynomial_coeff (f g : ⋀[K]^2 M) (q : ℤ) :
    (poincarePolynomial f g).coeff q = (Module.finrank K (cohomology f g q) : ℤ) :=
  congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq.symm

/-- Actual CE cochains in Koszul coordinates; the two middle factors are
the original first Koszul term. -/
def coordinates (f g : ⋀[K]^2 M) :
    Cochains f g ≃ₗ[K]
      ExteriorAlgebra K M × ((ExteriorAlgebra K M × ExteriorAlgebra K M) × ExteriorAlgebra K M) :=
  (TwoStepChevalleyEilenberg.cochainEquiv f g).toLinearEquiv.symm.trans
    TwoCentralKoszulOperator.koszulCoordinates

/-- The actual CE operator is conjugate to the original folded Koszul
differential, on every cochain. -/
theorem coordinates_differential (f g : ⋀[K]^2 M) (x : Cochains f g) :
    coordinates f g (TwoStepChevalleyEilenberg.differential f g x) =
      FoldedComplexHomology.differential (exteriorKoszulFirst f g) (exteriorKoszulSecond f g)
        (coordinates f g x) := by
  change TwoCentralKoszulOperator.koszulCoordinates
    ((TwoStepChevalleyEilenberg.cochainEquiv f g).symm
      (TwoStepChevalleyEilenberg.cochainEquiv f g
        (TwoStepExteriorComplex.d f g ((TwoStepChevalleyEilenberg.cochainEquiv f g).symm x)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact TwoCentralKoszulOperator.koszulCoordinates_operator f g _

/-- The coordinate equivalence preserves the genuine cohomological degree,
namely the original internal Koszul degree minus its position. -/
theorem coordinates_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (coordinates f g).toLinearMap
      (cochainGrading f g).piece
      (FoldedComplexHomologyGrading.totalGrading exteriorKoszulTerm₀Grading
        exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading).piece 0 := by
  intro q x hx
  have hx' := (TwoCentralExteriorGrading.exteriorMap_homogeneous
    (CentralLieCochainCoordinates.oneCochainEquiv f g).symm.toLinearMap).map_mem hx
  have hh := TwoCentralExteriorGrading.koszulCoordinates_homogeneous.map_mem hx'
  change TwoCentralKoszulOperator.koszulCoordinates
    (ExteriorAlgebra.map (CentralLieCochainCoordinates.oneCochainEquiv f g).symm.toLinearMap x) ∈
      TwoCentralExteriorGrading.foldedExteriorGrading.piece (q + 0)
  simpa only [add_zero, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using hh

/-- The CE Poincare series is the Hilbert series of the actual folded
Koszul homology with its inherited grading. -/
theorem poincare_eq_folded (f g : ⋀[K]^2 M) :
    poincarePolynomial f g =
      finiteHilbertLaurent
        (FoldedComplexHomologyGrading.homologyGrading exteriorKoszulTerm₀Grading
          exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading
          (exteriorKoszulFirst f g) (exteriorKoszulSecond f g) (exteriorKoszul_comp f g)
          (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g)) :=
  FoldedComplexHomologyHilbert.hilbert_conjugacy
    (cochainGrading f g)
    (FoldedComplexHomologyGrading.totalGrading exteriorKoszulTerm₀Grading
      exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading)
    (TwoStepChevalleyEilenberg.differential f g)
    (FoldedComplexHomology.differential (exteriorKoszulFirst f g) (exteriorKoszulSecond f g))
    (differential_square f g)
    (FoldedComplexHomology.differential_sq _ _ (exteriorKoszul_comp f g))
    (differential_homogeneous f g)
    (FoldedComplexHomologyGrading.differential_homogeneous _ _ _ _ _
      (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g))
    (coordinates f g) (coordinates_differential f g) (coordinates_homogeneous f g)

/-- Codomain restriction of the second Koszul differential changes neither
its kernel nor any of its homogeneous elements. -/
def topDegreeEquiv (f g : ⋀[K]^2 M) (q : ℤ) :
    (FoldedComplexHomologyGrading.secondGrading exteriorKoszulTerm₁Grading
      exteriorKoszulTerm₂Grading (exteriorKoszulSecond f g)
      (exteriorKoszulSecond_homogeneous f g)).piece q ≃ₗ[K]
      (exteriorKoszulH₂Grading f g).piece q where
  toFun a := ⟨⟨a.val.val, Subtype.ext a.val.property⟩, by
    apply (mem_exteriorKoszulH₂_piece f g q _).2
    have ha := (exteriorKoszulTerm₂Grading.mem_ker_piece
      (exteriorKoszulSecond_homogeneous f g)).1 a.property
    simpa only [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece] using ha⟩
  invFun a := ⟨⟨a.val.val, congrArg Subtype.val a.val.property⟩, by
    apply (exteriorKoszulTerm₂Grading.mem_ker_piece
      (exteriorKoszulSecond_homogeneous f g)).2
    simpa only [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece] using
      (mem_exteriorKoszulH₂_piece f g q a.val).1 a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem top_hilbert_eq (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent
      (FoldedComplexHomologyGrading.secondGrading exteriorKoszulTerm₁Grading
        exteriorKoszulTerm₂Grading (exteriorKoszulSecond f g)
        (exteriorKoszulSecond_homogeneous f g)) =
      finiteHilbertLaurent (exteriorKoszulH₂Grading f g) := by
  ext q
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (topDegreeEquiv f g q).finrank_eq

/-- The actual three Koszul homology polynomials give the full categorical
CE cohomology series, with the two required cohomological shifts. -/
theorem poincare_eq_koszul (f g : ⋀[K]^2 M) :
    poincarePolynomial f g =
      finiteHilbertLaurent (exteriorKoszulH₀Grading f g) +
        (LaurentPolynomial.T (-1) * finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
          LaurentPolynomial.T (-2) * finiteHilbertLaurent (exteriorKoszulH₂Grading f g)) := by
  rw [poincare_eq_folded]
  simpa only [top_hilbert_eq, FoldedComplexHomologyGrading.zerothGrading,
    FoldedComplexHomologyGrading.firstGrading, exteriorKoszulH₀Grading,
    exteriorKoszulH₁Grading, shortComplexH₀Grading, shortComplexH₁Grading,
    FoldedComplexHomology.middleToCycles, shortComplexToCycles] using
    FoldedComplexHomologyHilbert.hilbert_folded exteriorKoszulTerm₀Grading
      exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading
      (exteriorKoszulFirst f g) (exteriorKoszulSecond f g) (exteriorKoszul_comp f g)
      (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g)

/-- The Poincare formula following Proposition 5.4, before the separate
identification of the middle Koszul polynomial with ordinary Tor. -/
theorem poincare_formula (f g : ⋀[K]^2 M) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  rw [poincare_eq_koszul, exteriorKoszulH₂_hilbert, ← mul_assoc, ← LaurentPolynomial.T_add]
  congr 3
  ring

/-- No negative cohomological degrees are introduced by the Laurent
notation: the original exterior grading vanishes there. -/
theorem cohomologyGrading_piece_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (cohomologyGrading f g).piece q = ⊥ :=
  SquareZeroHomologyGrading.homologyGrading_piece_eq_bot
    (cochainGrading f g) (TwoStepChevalleyEilenberg.differential f g)
    (differential_square f g) (differential_homogeneous f g)
    (exteriorIntegerGrading_piece_negative hq)

theorem poincarePolynomial_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (poincarePolynomial f g).coeff q = 0 := by
  change (Module.finrank K ((cohomologyGrading f g).piece q) : ℤ) = 0
  rw [cohomologyGrading_piece_negative f g hq, finrank_bot, Nat.cast_zero]

/-- The actual categorical cohomology itself vanishes in negative degrees. -/
theorem cohomology_subsingleton_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    Subsingleton (cohomology f g q) := by
  haveI : Subsingleton ((cohomologyGrading f g).piece q) := by
    rw [cohomologyGrading_piece_negative f g hq]
    infer_instance
  constructor
  intro x y
  apply (cohomologyEquiv f g q).injective
  exact Subsingleton.elim _ _

/-- Evaluation at one is defined on Laurent polynomials since one is a
unit. -/
def evalAtOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

@[simp] theorem evalAtOne_T (q : ℤ) : evalAtOne (LaurentPolynomial.T q) = 1 := by
  simp [evalAtOne]

@[simp] theorem evalAtOne_invert (P : LaurentPolynomial ℤ) :
    evalAtOne (LaurentPolynomial.invert P) = evalAtOne P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T q a => simp [evalAtOne]

/-- At one, evaluation is exactly the finite sum of all coefficients. -/
theorem evalAtOne_eq_sum (P : LaurentPolynomial ℤ) :
    evalAtOne P = P.coeff.sum (fun _ a ↦ a) := by
  have h : evalAtOne P = P.smeval (1 : ℤˣ) := by
    induction P using LaurentPolynomial.induction_on' with
    | add P Q hP hQ => simp only [map_add, LaurentPolynomial.smeval_add, hP, hQ]
    | C_mul_T q a =>
      rw [map_mul, LaurentPolynomial.smeval_C_mul_T_n]
      simp [evalAtOne, smul_eq_mul]
  rw [h]
  simp only [LaurentPolynomial.smeval, one_zpow, Units.val_one, smul_eq_mul, mul_one]

/-- The total dimension is the sum of the dimensions of the actual
categorical cohomology groups over their finite support. -/
def totalCohomologyDimension (f g : ⋀[K]^2 M) : ℤ :=
  ∑ q ∈ (poincarePolynomial f g).coeff.support, (Module.finrank K (cohomology f g q) : ℤ)

/-- Degrees outside this finite support contribute zero actual
cohomology dimension. -/
theorem cohomology_finrank_zero_of_not_support (f g : ⋀[K]^2 M) {q : ℤ}
    (hq : q ∉ (poincarePolynomial f g).coeff.support) :
    Module.finrank K (cohomology f g q) = 0 := by
  have hz := Finsupp.notMem_support_iff.1 hq
  rw [poincarePolynomial_coeff] at hz
  exact_mod_cast hz

theorem totalDimension_eq_eval (f g : ⋀[K]^2 M) :
    totalCohomologyDimension f g = evalAtOne (poincarePolynomial f g) := by
  rw [evalAtOne_eq_sum]
  change (∑ q ∈ (poincarePolynomial f g).coeff.support,
    (Module.finrank K (cohomology f g q) : ℤ)) =
      ∑ q ∈ (poincarePolynomial f g).coeff.support, (poincarePolynomial f g).coeff q
  exact Finset.sum_congr rfl (fun q _ ↦ (poincarePolynomial_coeff f g q).symm)

/-- The complete Poincare series evaluates to four times the actual
exterior quotient Hilbert series at one. -/
theorem poincare_at_one (f g : ⋀[K]^2 M) :
    evalAtOne (poincarePolynomial f g) = 4 * evalAtOne (exteriorQuotientHilbert f g) := by
  rw [poincare_eq_koszul, (exteriorKoszul_all_hilbert_formulas f g).2.2,
    exteriorKoszulH₂_hilbert]
  change evalAtOne
    (exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) *
        (exteriorQuotientHilbert f g +
          LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
          (1 - LaurentPolynomial.T 2) ^ 2 *
            (1 + LaurentPolynomial.T 1) ^ Module.finrank K M) +
        LaurentPolynomial.T (-2) *
          (LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g)))) = _
  simp only [map_add, map_mul, map_sub, map_pow, map_one, evalAtOne_T, evalAtOne_invert]
  ring

/-- The paper's total Lie-cohomology dimension formula, with every summand
the actual categorical cohomology of the original CE complex. -/
theorem total_dimension_four (f g : ⋀[K]^2 M) :
    totalCohomologyDimension f g = 4 * evalAtOne (exteriorQuotientHilbert f g) := by
  rw [totalDimension_eq_eval, poincare_at_one]

end PaperVerification.TwoStepLieCohomology
end
end
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepLieCohomology"

section ComponentSource_18
/- Original module: PaperVerification.TwoStepLieCohomologyBetti -/


/-!
# The paper's Lie-cohomology formula with the actual ordinary Tor polynomial

This final comparison substitutes the independently established ordinary
Tor identification from Proposition 5.4 into the actual CE Poincare formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepLieCohomology

open AlternatingForms

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The full graded Lie-cohomology formula following Proposition 5.4,
with `B₁` defined by ordinary Mathlib Tor over the actual polynomial ring
and its coefficient field at the origin. -/
theorem paper_lie_cohomology_poincare (f g : ⋀[K]^2 M) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  rw [exteriorOriginBettiPolynomial_eq, exteriorBettiPolynomial_one]
  exact poincare_formula f g

/-- The same formula explicitly identifies each genuine categorical
cohomology dimension, in every integer degree. -/
theorem paper_lie_cohomology_degree (f g : ⋀[K]^2 M) (q : ℤ) :
    (Module.finrank K (cohomology f g q) : ℤ) =
      (exteriorQuotientHilbert f g +
        (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
          LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g))).coeff q := by
  rw [← poincarePolynomial_coeff, paper_lie_cohomology_poincare]

/-- The Poincare series is an ordinary polynomial. Its use of Laurent
notation in the formula does not add negative cohomological degrees. -/
theorem poincarePolynomial_is_ordinary (f g : ⋀[K]^2 M) :
    ∃! P : Polynomial ℤ, P.toLaurent = poincarePolynomial f g := by
  refine ⟨LaurentPolynomial.trunc (poincarePolynomial f g),
    toLaurent_trunc_of_nonnegative _ (fun q hq ↦ poincarePolynomial_negative f g hq), ?_⟩
  intro P hP
  apply Polynomial.toLaurent_injective
  rw [hP, toLaurent_trunc_of_nonnegative _ (fun q hq ↦ poincarePolynomial_negative f g hq)]

end PaperVerification.TwoStepLieCohomology
end
end
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepLieCohomologyBetti"

section ComponentSource_19
/- Original module: PaperVerification.ExteriorAlternatingCochains -/


/-!
# Exterior cochains and alternating multilinear cochains

For a finite free module, the determinant pairing identifies the exterior
power of its dual with the actual module of alternating multilinear forms.
The comparison below uses Mathlib's independently defined exterior powers,
alternating maps and perfect dual pairing.  Its evaluation formulas record
the normalization in every degree, including degree zero.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.ExteriorAlternatingCochains

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The determinant pairing followed by the universal property of the
exterior power, in the direction from exterior cochains to alternating forms. -/
def cochainEquiv (q : ℕ) :
    (⋀[R]^q (Module.Dual R M)) ≃ₗ[R] AlternatingMap R M R (Fin q) :=
  (LinearEquiv.ofBijective (exteriorPower.pairingDual R M q)
    (exteriorPower.bijective_pairingDual R M q)).trans
      exteriorPower.alternatingMapLinearEquiv.symm

/-- The comparison is the original exterior pairing on every tuple. -/
theorem cochainEquiv_apply (q : ℕ) (ω : ⋀[R]^q (Module.Dual R M))
    (v : Fin q → M) :
    cochainEquiv R M q ω v = exteriorPower.pairingDual R M q ω
      (exteriorPower.ιMulti R q v) := by
  change exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual R M q ω) v = _
  exact exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

/-- A wedge of one-cochains evaluates by the usual determinant, with no
factorial normalization or sign left implicit. -/
theorem cochainEquiv_wedge (q : ℕ) (α : Fin q → Module.Dual R M)
    (v : Fin q → M) :
    cochainEquiv R M q (exteriorPower.ιMulti R q α) v =
      Matrix.det (Matrix.of (fun i j ↦ α j (v i))) := by
  rw [cochainEquiv_apply, exteriorPower.pairingDual_ιMulti_ιMulti]

/-- Every alternating cochain comes from exactly one exterior cochain. -/
theorem existsUnique_exterior_cochain (q : ℕ) (F : AlternatingMap R M R (Fin q)) :
    ∃! ω : ⋀[R]^q (Module.Dual R M),
      ∀ v, exteriorPower.pairingDual R M q ω (exteriorPower.ιMulti R q v) = F v := by
  refine ⟨(cochainEquiv R M q).symm F, ?_, ?_⟩
  · intro v
    rw [← cochainEquiv_apply, LinearEquiv.apply_symm_apply]
  · intro ω hω
    apply (cochainEquiv R M q).injective
    ext v
    rw [cochainEquiv_apply, hω]
    exact congrArg (fun F : AlternatingMap R M R (Fin q) ↦ F v)
      ((cochainEquiv R M q).apply_symm_apply F).symm

/-- Equality of exterior cochains can be checked on actual tuples of vectors. -/
theorem cochain_ext (q : ℕ) (ω η : ⋀[R]^q (Module.Dual R M))
    (h : ∀ v, exteriorPower.pairingDual R M q ω (exteriorPower.ιMulti R q v) =
      exteriorPower.pairingDual R M q η (exteriorPower.ιMulti R q v)) : ω = η := by
  apply (cochainEquiv R M q).injective
  ext v
  simpa only [cochainEquiv_apply] using h v

end PaperVerification.ExteriorAlternatingCochains
end
end
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ExteriorAlternatingCochains"

section ComponentSource_20
/- Original module: PaperVerification.TwoStepOriginalLie -/


/-!
# The original vector-space presentation of the two-step Lie algebra

When the original exterior algebra is `Λ(V*)`, the dual-coordinate
construction uses `V**` as its noncentral vector space. This file defines
the ordinary bracket directly on `V × K²`, by the original exterior
pairing, and proves that the canonical evaluation map is a Lie equivalence.
Both central directions are preserved literally. No independence or
nonvanishing hypothesis on the two original forms is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoStepOriginalLie

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The original alternating form on `V`, obtained from its actual exterior
cochain by the universal exterior pairing. -/
def alternatingForm (f : ⋀[K]^2 (Module.Dual K V)) :
    AlternatingMap K V K (Fin 2) :=
  exteriorPower.alternatingMapLinearEquiv.symm (exteriorPower.pairingDual K V 2 f)

theorem alternatingForm_apply (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    alternatingForm f ![x,y] = exteriorPower.pairingDual K V 2 f
      (exteriorPower.ιMulti K 2 ![x,y]) :=
  exteriorPower.alternatingMapLinearEquiv_symm_apply _ _

/-- The literal bilinear coefficient of the original central bracket. -/
def bilinearForm (f : ⋀[K]^2 (Module.Dual K V)) : V →ₗ[K] V →ₗ[K] K :=
  ExteriorTwoFormEvaluation.bilinearOfAlternating (alternatingForm f)

theorem bilinearForm_apply (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    bilinearForm f x y = exteriorPower.pairingDual K V 2 f
      (exteriorPower.ιMulti K 2 ![x,y]) :=
  alternatingForm_apply f x y

/-- Evaluation in the double dual preserves the original form, including
its determinant normalization and sign. -/
theorem bilinearForm_eval (f : ⋀[K]^2 (Module.Dual K V)) (x y : V) :
    bilinearForm f x y = ExteriorTwoFormEvaluation.bilinear f
      (Module.evalEquiv K V x) (Module.evalEquiv K V y) := by
  rw [bilinearForm_apply, ExteriorTwoFormEvaluation.pairingDual_eq_evaluate]
  rfl

/-- The two-step bracket on the original vector space, before any passage
to its double dual. -/
def bracketData (f g : ⋀[K]^2 (Module.Dual K V)) :
    TwoStepCentralLie.Data (K := K) (V := V) (Z := Fin 2 → K) where
  bilinear := LinearMap.mk₂ K (fun x y ↦ ![bilinearForm f x y, bilinearForm g x y])
    (by intro x x' y; ext i; fin_cases i <;> simp)
    (by intro r x y; ext i; fin_cases i <;> simp)
    (by intro x y y'; ext i; fin_cases i <;> simp)
    (by intro r x y; ext i; fin_cases i <;> simp)
  alternating x := by
    ext i
    fin_cases i
    · change bilinearForm f x x = 0
      exact ExteriorTwoFormEvaluation.bilinearOfAlternating_self (alternatingForm f) x
    · change bilinearForm g x x = 0
      exact ExteriorTwoFormEvaluation.bilinearOfAlternating_self (alternatingForm g) x

/-- The ordinary Lie algebra on `V × K²` with the original form coefficients. -/
abbrev L (f g : ⋀[K]^2 (Module.Dual K V)) :=
  TwoStepCentralLie.LieSpace (bracketData f g)

/-- The bracket is exactly the one printed in the paper, expressed through
the independently defined exterior pairing on the original vectors. -/
theorem bracket_apply (f g : ⋀[K]^2 (Module.Dual K V)) (x y : L f g) :
    ⁅x,y⁆ = ((0 : V),
      ![exteriorPower.pairingDual K V 2 f (exteriorPower.ιMulti K 2 ![x.1,y.1]),
        exteriorPower.pairingDual K V 2 g (exteriorPower.ιMulti K 2 ![x.1,y.1])]) := by
  change ((0 : V), ![bilinearForm f x.1 y.1, bilinearForm g x.1 y.1]) = _
  rw [bilinearForm_apply, bilinearForm_apply]

/-- Canonical evaluation gives an actual Lie equivalence from the original
presentation to the dual-coordinate presentation used in the CE calculation. -/
def evalLieEquiv (f g : ⋀[K]^2 (Module.Dual K V)) :
    L f g ≃ₗ⁅K⁆ CentralLieCochainCoordinates.L f g :=
  { (Module.evalEquiv K V).prodCongr (LinearEquiv.refl K (Fin 2 → K)) with
    map_lie' := by
      intro x y
      apply Prod.ext
      · change Module.evalEquiv K V (0 : V) = 0
        exact map_zero _
      · change ![bilinearForm f x.1 y.1, bilinearForm g x.1 y.1] =
          ![ExteriorTwoFormEvaluation.bilinear f
              (Module.evalEquiv K V x.1) (Module.evalEquiv K V y.1),
            ExteriorTwoFormEvaluation.bilinear g
              (Module.evalEquiv K V x.1) (Module.evalEquiv K V y.1)]
        ext i
        fin_cases i
        · exact bilinearForm_eval f x.1 y.1
        · exact bilinearForm_eval g x.1 y.1 }

/-- The equivalence is the canonical evaluation map on the original
vectors and the literal identity on the central coordinates. -/
theorem evalLieEquiv_apply (f g : ⋀[K]^2 (Module.Dual K V)) (x : L f g) :
    evalLieEquiv f g x = (Module.evalEquiv K V x.1, x.2) := rfl

@[simp] theorem evalLieEquiv_central (f g : ⋀[K]^2 (Module.Dual K V)) (z : Fin 2 → K) :
    evalLieEquiv f g ((0 : V), z) = (0, z) := by
  change (Module.evalEquiv K V (0 : V), z) = (0, z)
  rw [map_zero]

end PaperVerification.TwoStepOriginalLie
end
end
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepOriginalLie"

section ComponentSource_21
/- Original module: PaperVerification.ChevalleyEilenbergTransport -/


/-!
# Pullback of the actual Chevalley--Eilenberg exterior differential

The determinant pairing is natural in every degree. Consequently the
pullback on one-cochains induced by an actual Lie equivalence transports
the intrinsic CE differential, including its negative bracket-dual sign.
Conjugation preserves square-zero and the original exterior degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ChevalleyEilenbergTransport

open ExteriorDerivationTransport

section Pairing

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The original determinant pairing commutes with linear pullback in
all exterior degrees, including degree zero. -/
theorem pairingDual_pullback (F : A →ₗ[R] B) (q : ℕ)
    (ω : ⋀[R]^q (Module.Dual R B)) (v : Fin q → A) :
    exteriorPower.pairingDual R A q (exteriorPower.map q F.dualMap ω)
        (exteriorPower.ιMulti R q v) =
      exteriorPower.pairingDual R B q ω
        (exteriorPower.ιMulti R q (F ∘ v)) := by
  have h :
      (Module.Dual.eval R (⋀[R]^q A) (exteriorPower.ιMulti R q v)).comp
        ((exteriorPower.pairingDual R A q).comp (exteriorPower.map q F.dualMap)) =
      (Module.Dual.eval R (⋀[R]^q B) (exteriorPower.ιMulti R q (F ∘ v))).comp
        (exteriorPower.pairingDual R B q) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro α
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply,
      LinearMap.dualMap_apply]
  exact LinearMap.congr_fun h ω

end Pairing

section Lie

variable {K L L' : Type*} [Field K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L']

/-- Pullback of the genuine exterior differential along an actual Lie
equivalence, using its contravariant map on dual one-cochains. -/
def pullback (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L'))) :
    Module.End K (ExteriorAlgebra K (Module.Dual K L)) :=
  conjugate e.toLinearEquiv.dualMap D

/-- Pullback preserves the intrinsic CE defining equations on every
one-cochain, with the actual Lie brackets on the two original spaces. -/
theorem pullback_isDifferential (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) :
    ChevalleyEilenbergExterior.IsDifferential (pullback e D) := by
  refine ⟨conjugate_isOddDerivation _ _ hD.1, ?_⟩
  intro α
  obtain ⟨ω, hω, hωeval⟩ := hD.2 (e.toLinearEquiv.dualMap.symm α)
  refine ⟨exteriorPower.map 2 e.toLinearEquiv.toLinearMap.dualMap ω, ?_, ?_⟩
  · rw [pullback, conjugate_apply, mapEquiv_symm_ι, hω, mapEquiv_apply]
    rw [exteriorPower.coe_map]
    apply congrArg (fun F : Module.Dual K L' →ₗ[K] Module.Dual K L =>
      ExteriorAlgebra.map F (ω : ExteriorAlgebra K (Module.Dual K L')))
    ext β z
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply, LinearMap.dualMap_apply]
  · intro x y
    rw [pairingDual_pullback]
    have hv : e.toLinearEquiv.toLinearMap ∘ ![x,y] = ![e x,e y] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, hωeval, ← e.map_lie]
    change -((e.toLinearEquiv.dualMap (e.toLinearEquiv.dualMap.symm α)) ⁅x,y⁆) = -α ⁅x,y⁆
    rw [LinearEquiv.apply_symm_apply]

/-- Actual cochain pullback intertwines the two linear differentials. -/
theorem pullback_map (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (x : ExteriorAlgebra K (Module.Dual K L')) :
    pullback e D (mapEquiv e.toLinearEquiv.dualMap x) =
      mapEquiv e.toLinearEquiv.dualMap (D x) := by
  simp only [pullback, conjugate_apply, AlgEquiv.symm_apply_apply]

/-- Square-zero is retained on the original cochains. -/
theorem pullback_square_zero (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ∀ x, D (D x) = 0) (x : ExteriorAlgebra K (Module.Dual K L)) :
    pullback e D (pullback e D x) = 0 :=
  conjugate_square_zero _ _ hD x

/-- The ordinary cohomological degree is retained, in every natural
exterior degree and for the original homogeneous submodules. -/
theorem pullback_degree (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ∀ q x, x ∈ ⋀[K]^q (Module.Dual K L') →
      D x ∈ ⋀[K]^(q+1) (Module.Dual K L'))
    (q : ℕ) (x : ExteriorAlgebra K (Module.Dual K L))
    (hx : x ∈ ⋀[K]^q (Module.Dual K L)) :
    pullback e D x ∈ ⋀[K]^(q+1) (Module.Dual K L) :=
  conjugate_degree _ _ hD q x hx

end Lie
end PaperVerification.ChevalleyEilenbergTransport
end
end
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ChevalleyEilenbergTransport"

section ComponentSource_22
/- Original module: PaperVerification.TwoStepOriginalLieCohomology -/


/-!
# Cohomology of the paper's literal Lie algebra on `V × K²`

The two original forms belong to `Λ²(V*)`.  The bracket is defined directly
on `V × K²`, and the differential below is the uniquely characterized
Chevalley--Eilenberg differential on its actual exterior cochains.  The
canonical evaluation Lie equivalence transports the already computed
cohomology, with the comparison proved on actual homogeneous cycle classes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepOriginalLieCohomology

open AlternatingForms

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

instance lie_finite (f g : ⋀[K]^2 (Module.Dual K V)) :
    FiniteDimensional K (TwoStepOriginalLie.L f g) :=
  inferInstanceAs (FiniteDimensional K (V × (Fin 2 → K)))

/-- The cochains are exterior powers of the dual of the original `V × K²`. -/
abbrev Cochains (f g : ⋀[K]^2 (Module.Dual K V)) :=
  ExteriorAlgebra K (Module.Dual K (TwoStepOriginalLie.L f g))

instance cochains_finite (f g : ⋀[K]^2 (Module.Dual K V)) :
    FiniteDimensional K (Cochains f g) := by
  change FiniteDimensional K
    (ExteriorAlgebra K (Module.Dual K (TwoStepOriginalLie.L f g)))
  infer_instance

/-- Pullback is the actual exterior-algebra map induced by the dual of
the canonical evaluation Lie equivalence. -/
def cochainPullback (f g : ⋀[K]^2 (Module.Dual K V)) :
    TwoStepLieCohomology.Cochains f g ≃ₐ[K] Cochains f g :=
  ExteriorDerivationTransport.mapEquiv
    (TwoStepOriginalLie.evalLieEquiv f g).toLinearEquiv.dualMap

/-- The actual CE differential on the original Lie algebra. -/
def differential (f g : ⋀[K]^2 (Module.Dual K V)) : Module.End K (Cochains f g) :=
  ChevalleyEilenbergTransport.pullback (TwoStepOriginalLie.evalLieEquiv f g)
    (TwoStepChevalleyEilenberg.differential f g)

/-- Its intrinsic characterization uses the original bracket and the
usual negative bracket-dual sign. -/
theorem differential_isChevalleyEilenberg (f g : ⋀[K]^2 (Module.Dual K V)) :
    ChevalleyEilenbergExterior.IsDifferential (differential f g) :=
  ChevalleyEilenbergTransport.pullback_isDifferential _ _
    (TwoStepChevalleyEilenberg.differential_isChevalleyEilenberg f g)

theorem differential_unique (f g : ⋀[K]^2 (Module.Dual K V))
    (D : Module.End K (Cochains f g))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) : D = differential f g :=
  ChevalleyEilenbergExterior.differential_unique hD (differential_isChevalleyEilenberg f g)

theorem differential_square (f g : ⋀[K]^2 (Module.Dual K V)) :
    (differential f g).comp (differential f g) = 0 := by
  apply LinearMap.ext
  exact ChevalleyEilenbergTransport.pullback_square_zero _ _
    (TwoStepChevalleyEilenberg.differential_square_zero f g)

/-- Original exterior degrees, with the negative integer pieces zero. -/
def cochainGrading (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.InternalGrading K (Cochains f g) := exteriorIntegerGrading

theorem differential_homogeneous (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.LinearMap.IsHomogeneous (differential f g)
      (cochainGrading f g).piece (cochainGrading f g).piece 1 :=
  TwoCentralExteriorGrading.homogeneous_of_exterior_degree_one _
    (ChevalleyEilenbergTransport.pullback_degree _ _
      (fun _ _ hx ↦ TwoStepChevalleyEilenberg.differential_mem_exteriorPower f g hx))

/-- Pullback commutes with the actual differentials, on every cochain. -/
theorem cochainPullback_differential (f g : ⋀[K]^2 (Module.Dual K V))
    (x : TwoStepLieCohomology.Cochains f g) :
    cochainPullback f g (TwoStepChevalleyEilenberg.differential f g x) =
      differential f g (cochainPullback f g x) :=
  (ChevalleyEilenbergTransport.pullback_map _ _ x).symm

theorem cochainPullback_homogeneous (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.LinearMap.IsHomogeneous (cochainPullback f g).toLinearMap
      (TwoStepLieCohomology.cochainGrading f g).piece (cochainGrading f g).piece 0 :=
  TwoCentralExteriorGrading.exteriorMap_homogeneous
    (TwoStepOriginalLie.evalLieEquiv f g).toLinearEquiv.dualMap.toLinearMap

/-- The genuine integer-indexed CE complex of the original Lie algebra. -/
def cochainComplex (f g : ⋀[K]^2 (Module.Dual K V)) : CochainComplex (ModuleCat K) ℤ :=
  GradedDifferentialCochainComplex.cochainComplex (cochainGrading f g)
    (differential f g) (differential_square f g) (differential_homogeneous f g)

/-- Its actual categorical cohomology in every integer degree. -/
def cohomology (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) : ModuleCat K :=
  (cochainComplex f g).homology q

/-- Canonical evaluation induces a linear equivalence on the actual
categorical cohomology groups, through explicit homogeneous cycle classes. -/
def cohomologyEquiv (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    cohomology f g q ≃ₗ[K] TwoStepLieCohomology.cohomology f g q :=
  (GradedDifferentialCochainComplex.cochainHomologyEquiv
    (cochainGrading f g) (differential f g) (differential_square f g)
    (differential_homogeneous f g) q).trans
      ((SquareZeroHomologyGrading.homogeneousPieceEquiv
        (TwoStepLieCohomology.cochainGrading f g)
        (TwoStepChevalleyEilenberg.differential f g)
        (TwoStepLieCohomology.differential_square f g)
        (TwoStepLieCohomology.differential_homogeneous f g)
        (cochainGrading f g) (differential f g) (differential_square f g)
        (differential_homogeneous f g) (cochainPullback f g).toLinearEquiv
        (cochainPullback_differential f g) (cochainPullback_homogeneous f g) q).symm.trans
          (TwoStepLieCohomology.cohomologyEquiv f g q).symm)

instance cohomology_finite (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    FiniteDimensional K (cohomology f g q) :=
  Module.Finite.equiv (cohomologyEquiv f g q).symm

/-- The Poincare polynomial transported along the proved degreewise
equivalence; the next theorem identifies its coefficients intrinsically. -/
def poincarePolynomial (f g : ⋀[K]^2 (Module.Dual K V)) : LaurentPolynomial ℤ :=
  TwoStepLieCohomology.poincarePolynomial f g

theorem poincarePolynomial_coeff (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    (poincarePolynomial f g).coeff q = (Module.finrank K (cohomology f g q) : ℤ) := by
  rw [poincarePolynomial, TwoStepLieCohomology.poincarePolynomial_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq.symm

/-- The paper's full formula on the literal original Lie space, with
ordinary Tor in `B₁` and the dimension of the original vector space `V`. -/
theorem paper_lie_cohomology_poincare (f g : ⋀[K]^2 (Module.Dual K V)) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
        LaurentPolynomial.T ((Module.finrank K V : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  simpa only [poincarePolynomial, Subspace.dual_finrank_eq] using
    TwoStepLieCohomology.paper_lie_cohomology_poincare f g

theorem paper_lie_cohomology_degree (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    (Module.finrank K (cohomology f g q) : ℤ) =
      (exteriorQuotientHilbert f g +
        (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
          LaurentPolynomial.T ((Module.finrank K V : ℤ) + 2) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g))).coeff q := by
  rw [← poincarePolynomial_coeff, paper_lie_cohomology_poincare]

/-- There is no categorical cohomology in negative degrees. -/
theorem cohomology_subsingleton_negative (f g : ⋀[K]^2 (Module.Dual K V))
    {q : ℤ} (hq : q < 0) : Subsingleton (cohomology f g q) := by
  haveI := TwoStepLieCohomology.cohomology_subsingleton_negative f g hq
  constructor
  intro x y
  apply (cohomologyEquiv f g q).injective
  exact Subsingleton.elim _ _

theorem poincarePolynomial_is_ordinary (f g : ⋀[K]^2 (Module.Dual K V)) :
    ∃! P : Polynomial ℤ, P.toLaurent = poincarePolynomial f g :=
  TwoStepLieCohomology.poincarePolynomial_is_ordinary f g

/-- The finite sum of the dimensions of the actual original cohomology. -/
def totalCohomologyDimension (f g : ⋀[K]^2 (Module.Dual K V)) : ℤ :=
  ∑ q ∈ (poincarePolynomial f g).coeff.support, (Module.finrank K (cohomology f g q) : ℤ)

theorem cohomology_finrank_zero_of_not_support (f g : ⋀[K]^2 (Module.Dual K V)) {q : ℤ}
    (hq : q ∉ (poincarePolynomial f g).coeff.support) :
    Module.finrank K (cohomology f g q) = 0 := by
  rw [(cohomologyEquiv f g q).finrank_eq]
  exact TwoStepLieCohomology.cohomology_finrank_zero_of_not_support f g hq

/-- The total dimension is four times the actual exterior-quotient
Hilbert polynomial at one, with no genericity assumption on the forms. -/
theorem total_dimension_four (f g : ⋀[K]^2 (Module.Dual K V)) :
    totalCohomologyDimension f g =
      4 * TwoStepLieCohomology.evalAtOne (exteriorQuotientHilbert f g) := by
  have h : totalCohomologyDimension f g = TwoStepLieCohomology.totalCohomologyDimension f g := by
    apply Finset.sum_congr rfl
    intro q _
    exact congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq
  rw [h, TwoStepLieCohomology.total_dimension_four]

end PaperVerification.TwoStepOriginalLieCohomology
end
end
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.TwoStepOriginalLieCohomology"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.SquareZeroHomologyGrading.map_eq_of_homogeneous, "theorem"),
    (`PaperVerification.SquareZeroHomologyGrading.toCycles_homogeneous, "theorem"),
    (`PaperVerification.SquareZeroHomologyGrading.homologyGrading, "definition"),
    (`PaperVerification.SquareZeroHomologyGrading.mem_homologyGrading_iff, "theorem"),
    (`PaperVerification.SquareZeroHomologyGrading.quotientHomologyEquiv_homogeneous, "theorem"),
    (`PaperVerification.SquareZeroHomologyGrading.map_homologyGrading, "theorem"),
    (`PaperVerification.SquareZeroHomologyGrading.homogeneousPieceEquiv, "definition"),
    (`PaperVerification.FoldedComplexHomologyGrading.differential_homogeneous, "theorem"),
    (`PaperVerification.FoldedComplexHomologyGrading.homologyGrading, "definition"),
    (`PaperVerification.FoldedComplexHomologyGrading.homologyEquiv_homogeneous, "theorem"),
    (`PaperVerification.FoldedComplexHomologyGrading.map_homologyGrading, "theorem"),
    (`PaperVerification.FoldedComplexHomologyGrading.homogeneousHomologyEquiv, "definition"),
    (`PaperVerification.FoldedComplexHomologyGrading.finrank_homology_piece, "theorem"),
    (`PaperVerification.GradedDifferentialCochainComplex.pieceMap_comp, "theorem"),
    (`PaperVerification.GradedDifferentialCochainComplex.cochainComplex, "definition"),
    (`PaperVerification.GradedDifferentialCochainComplex.cycleComparison_surjective, "theorem"),
    (`PaperVerification.GradedDifferentialCochainComplex.cycleComparison_ker, "theorem"),
    (`PaperVerification.GradedDifferentialCochainComplex.quotientHomologyEquiv, "definition"),
    (`PaperVerification.GradedDifferentialCochainComplex.quotientHomologyEquiv_mk, "theorem"),
    (`PaperVerification.GradedDifferentialCochainComplex.shortComplexHomologyEquiv, "definition"),
    (`PaperVerification.GradedDifferentialCochainComplex.cochainShortComplexIso, "definition"),
    (`PaperVerification.GradedDifferentialCochainComplex.cochainHomologyEquiv, "definition"),
    (`PaperVerification.FoldedComplexHomologyHilbert.hilbert_conjugacy, "theorem"),
    (`PaperVerification.FoldedComplexHomologyHilbert.hilbert_folded, "theorem"),
    (`PaperVerification.FoldedComplexHomologyHilbert.finrank_cochain_homology, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.cochainComplex, "definition"),
    (`PaperVerification.TwoStepLieCohomology.cohomology, "definition"),
    (`PaperVerification.TwoStepLieCohomology.cohomologyEquiv, "definition"),
    (`PaperVerification.TwoStepLieCohomology.poincarePolynomial_coeff, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.coordinates_differential, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.coordinates_homogeneous, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.poincare_eq_folded, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.topDegreeEquiv, "definition"),
    (`PaperVerification.TwoStepLieCohomology.poincare_eq_koszul, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.poincare_formula, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.poincarePolynomial_negative, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.totalDimension_eq_eval, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.total_dimension_four, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.paper_lie_cohomology_poincare, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.paper_lie_cohomology_degree, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.poincarePolynomial_is_ordinary, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.cohomology_finite, "theorem"),
    (`PaperVerification.TwoStepLieCohomology.cohomology_subsingleton_negative, "theorem"),
    (`PaperVerification.TwoCentralExteriorGrading.exteriorMap_homogeneous, "theorem"),
    (`PaperVerification.TwoCentralExteriorGrading.exteriorMultiplication_homogeneous, "theorem"),
    (`PaperVerification.TwoCentralExteriorGrading.homogeneous_of_exterior_degree_one, "theorem"),
    (`PaperVerification.TwoCentralExteriorGrading.koszulCoordinates_symm_homogeneous, "theorem"),
    (`PaperVerification.TwoCentralExteriorGrading.koszulCoordinates_homogeneous, "theorem"),
    (`PaperVerification.ExteriorAlternatingCochains.cochainEquiv, "definition"),
    (`PaperVerification.ExteriorAlternatingCochains.cochainEquiv_apply, "theorem"),
    (`PaperVerification.ExteriorAlternatingCochains.cochainEquiv_wedge, "theorem"),
    (`PaperVerification.ExteriorAlternatingCochains.existsUnique_exterior_cochain, "theorem"),
    (`PaperVerification.ExteriorAlternatingCochains.cochain_ext, "theorem"),
    (`PaperVerification.TwoStepExteriorComplex.complex, "definition"),
    (`PaperVerification.TwoCentralExteriorDecomposition.decomposition, "definition"),
    (`PaperVerification.TwoCentralKoszulOperator.koszulCoordinates_operator, "theorem"),
    (`PaperVerification.ChevalleyEilenbergExterior.differential_unique, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.cochainEquiv, "definition"),
    (`PaperVerification.TwoStepChevalleyEilenberg.originalTwoCochain_coe, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.differential_generator, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.differential_isChevalleyEilenberg, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.differential_unique, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.differential_square_zero, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.differential_mem_exteriorPower, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.exterior_d_eq_koszul_operator, "theorem"),
    (`PaperVerification.TwoStepChevalleyEilenberg.cochainEquiv_d, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.Cochains, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochains_finite, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochainPullback, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.differential, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.differential_isChevalleyEilenberg, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.differential_unique, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.differential_square, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochainGrading, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.differential_homogeneous, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochainPullback_differential, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochainPullback_homogeneous, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cochainComplex, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cohomology, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cohomologyEquiv, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cohomology_finite, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.poincarePolynomial, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.poincarePolynomial_coeff, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.paper_lie_cohomology_poincare, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.paper_lie_cohomology_degree, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cohomology_subsingleton_negative, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.poincarePolynomial_is_ordinary, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.totalCohomologyDimension, "definition"),
    (`PaperVerification.TwoStepOriginalLieCohomology.cohomology_finrank_zero_of_not_support, "theorem"),
    (`PaperVerification.TwoStepOriginalLieCohomology.total_dimension_four, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.alternatingForm, "definition"),
    (`PaperVerification.TwoStepOriginalLie.alternatingForm_apply, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.bilinearForm, "definition"),
    (`PaperVerification.TwoStepOriginalLie.bilinearForm_apply, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.bilinearForm_eval, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.bracketData, "definition"),
    (`PaperVerification.TwoStepOriginalLie.L, "definition"),
    (`PaperVerification.TwoStepOriginalLie.bracket_apply, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.evalLieEquiv, "definition"),
    (`PaperVerification.TwoStepOriginalLie.evalLieEquiv_apply, "theorem"),
    (`PaperVerification.TwoStepOriginalLie.evalLieEquiv_central, "theorem"),
    (`PaperVerification.ChevalleyEilenbergTransport.pairingDual_pullback, "theorem"),
    (`PaperVerification.ChevalleyEilenbergTransport.pullback, "definition"),
    (`PaperVerification.ChevalleyEilenbergTransport.pullback_isDifferential, "theorem"),
    (`PaperVerification.ChevalleyEilenbergTransport.pullback_map, "theorem"),
    (`PaperVerification.ChevalleyEilenbergTransport.pullback_square_zero, "theorem"),
    (`PaperVerification.ChevalleyEilenbergTransport.pullback_degree, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "fa71ed08561f70cae57f02fae4e8c473"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:fa71ed08561f70cae57f02fae4e8c473"
