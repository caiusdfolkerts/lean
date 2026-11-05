import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The exact sequence for adjoining one ideal generator

For every commutative ring, this constructs the literal short exact sequence
`0 → J → J + (m) → R/(J:m) → 0`. No regularity assumption on `m` is needed.
-/

noncomputable section

namespace CommAlg

open Classical CategoryTheory

variable {R : Type*} [CommRing R]

def generatorExtension (J : Ideal R) (m : R) : Ideal R := J ⊔ Ideal.span {m}

def generatorSubmodule (J : Ideal R) (m : R) : Submodule R (generatorExtension J m) :=
  Submodule.comap (generatorExtension J m).subtype (J : Submodule R R)

abbrev generatorQuotient (J : Ideal R) (m : R) :=
  generatorExtension J m ⧸ generatorSubmodule J m

def mulToGeneratorExtension (J : Ideal R) (m : R) : R →ₗ[R] generatorExtension J m where
  toFun r := ⟨r * m, (show Ideal.span {m} ≤ generatorExtension J m from le_sup_right)
    (Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩)⟩
  map_add' r s := Subtype.ext (add_mul r s m)
  map_smul' r s := Subtype.ext (by simp [mul_assoc])

def generatorQuotientMap (J : Ideal R) (m : R) : R →ₗ[R] generatorQuotient J m :=
  (generatorSubmodule J m).mkQ.comp (mulToGeneratorExtension J m)

theorem generatorQuotientMap_ker (J : Ideal R) (m : R) :
    LinearMap.ker (generatorQuotientMap J m) = J.colon {m} := by
  ext r
  simp only [LinearMap.mem_ker, generatorQuotientMap, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton,
    smul_eq_mul]
  rfl

theorem generatorQuotientMap_surjective (J : Ideal R) (m : R) :
    Function.Surjective (generatorQuotientMap J m) := by
  intro q
  obtain ⟨x, rfl⟩ := (generatorSubmodule J m).mkQ_surjective q
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp x.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change r * m - x.val ∈ J
  rw [← he, ← hr]
  simpa using J.neg_mem hy

/-- The actual quotient by the previously generated ideal is the quotient by
the ordinary colon ideal. -/
def generatorQuotientEquiv (J : Ideal R) (m : R) :
    generatorQuotient J m ≃ₗ[R] R ⧸ J.colon {m} :=
  (LinearMap.quotKerEquivOfSurjective (generatorQuotientMap J m)
    (generatorQuotientMap_surjective J m)).symm.trans
      (Submodule.quotEquivOfEq _ _ (generatorQuotientMap_ker J m))

def generatorInclusion (J : Ideal R) (m : R) : J →ₗ[R] generatorExtension J m :=
  Submodule.inclusion le_sup_left

def generatorProjection (J : Ideal R) (m : R) :
    generatorExtension J m →ₗ[R] R ⧸ J.colon {m} :=
  (generatorQuotientEquiv J m).toLinearMap.comp (generatorSubmodule J m).mkQ

@[simp] theorem generatorProjection_eq_zero_iff (J : Ideal R) (m : R)
    (x : generatorExtension J m) : generatorProjection J m x = 0 ↔ x.val ∈ J := by
  change (generatorQuotientEquiv J m) ((generatorSubmodule J m).mkQ x) = 0 ↔ _
  rw [(generatorQuotientEquiv J m).map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem generatorProjection_comp_inclusion (J : Ideal R) (m : R) :
    (generatorProjection J m).comp (generatorInclusion J m) = 0 := by
  ext x
  apply (generatorProjection_eq_zero_iff J m _).mpr
  exact x.property

/-- The genuine categorical exact sequence used for induction along a linear
quotient ordering. -/
def generatorExact (J : Ideal R) (m : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (generatorInclusion J m) (generatorProjection J m)
    (generatorProjection_comp_inclusion J m)

theorem generatorExact_shortExact (J : Ideal R) (m : R) :
    (generatorExact J m).ShortExact := by
  unfold generatorExact
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (generatorInclusion J m) (generatorProjection J m)
    intro x
    rw [generatorProjection_eq_zero_iff]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · change Function.Injective (generatorInclusion J m)
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : generatorExtension J m => z.val) hxy)
  · exact (generatorQuotientEquiv J m).surjective.comp
      (generatorSubmodule J m).mkQ_surjective

/-- The projective-dimension bound has exactly the two terms needed in the
linear-quotient induction. -/
theorem generatorExtension_projectiveDimension_le (J : Ideal R) (m : R) :
    projectiveDimension (ModuleCat.of R (generatorExtension J m)) ≤
      projectiveDimension (ModuleCat.of R J) ⊔
        projectiveDimension (ModuleCat.of R (R ⧸ J.colon {m})) :=
  (generatorExact_shortExact J m).projectiveDimension_X₂_le_sup

end CommAlg
