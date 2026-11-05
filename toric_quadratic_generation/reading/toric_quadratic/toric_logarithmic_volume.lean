module

public import PaperVerification.ToricCoordinateDifferentials
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

@[expose] public section

/-!
# The logarithmic character volume form

Logarithmic differentials are defined using the universal Kähler
derivation, and additivity is proved by the Leibniz rule. An integral basis
gives their genuine Laurent-module basis. The actual top exterior power
then changes by the determinant of an integral basis change. In a smooth
polynomial chart its regular volume is the product of the coordinates
times this logarithmic volume.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical

section Exterior

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ}

theorem alternating_eq_basis_determinant (b : Module.Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) : f = b.det.smulRight (f b) := by
  apply b.ext_alternating
  intro v hv
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change f (b ∘ σ) = b.det (b ∘ σ) • f b
  simp only [AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def,
    Int.smul_one_eq_cast, Int.cast_smul_eq_zsmul]

/-- The actual top exterior power of a finite free module is a rank-one
module, with coefficient given by the determinant in the chosen basis. -/
def basisTopExteriorEquiv (b : Module.Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R := by
  let f : (⋀[R]^n M) →ₗ[R] R := exteriorPower.alternatingMapLinearEquiv b.det
  let w := exteriorPower.ιMulti R n b
  refine { f with invFun := fun r => r • w, left_inv := ?_, right_inv := ?_ }
  · intro x
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨v, rfl⟩
      change f (exteriorPower.ιMulti R n v) • w = exteriorPower.ιMulti R n v
      rw [show f (exteriorPower.ιMulti R n v) = b.det v from
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v]
      exact (congrArg (fun F => F v)
        (alternating_eq_basis_determinant b (exteriorPower.ιMulti R n))).symm
    · change f 0 • w = 0
      rw [map_zero, zero_smul]
    · intro x y hx hy ihx ihy
      change f (x + y) • w = x + y
      change f x • w = x at ihx
      change f y • w = y at ihy
      rw [map_add, add_smul, ihx, ihy]
    · intro r x hx ihx
      change f (r • x) • w = r • x
      change f x • w = x at ihx
      rw [map_smul, smul_eq_mul, mul_smul, ihx]
  · intro r
    change f (r • exteriorPower.ιMulti R n b) = r
    rw [map_smul, show f (exteriorPower.ιMulti R n b) = b.det b from
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det b,
      Module.Basis.det_self, smul_eq_mul, mul_one]

@[simp] theorem basisTopExteriorEquiv_wedge (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp] theorem basisTopExteriorEquiv_basis (b : Module.Basis (Fin n) R M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n b) = 1 := by
  rw [basisTopExteriorEquiv_wedge, Module.Basis.det_self]

end Exterior

variable (k : Type*) [CommRing k] {E : Type*} [AddCommGroup E] [Module ℤ E]

def logDifferential (m : E) : Ω[AddMonoidAlgebra k E⁄k] :=
  single (-m) (1 : k) • D k (AddMonoidAlgebra k E) (single m 1)

@[simp] theorem logDifferential_zero : logDifferential k (0 : E) = 0 := by
  simp [logDifferential, ← AddMonoidAlgebra.one_def]

theorem logDifferential_add (m p : E) :
    logDifferential k (m + p) = logDifferential k m + logDifferential k p := by
  have hprod : (single (m + p) (1 : k)) = single m 1 * single p 1 := by simp
  have hm : -(m + p) + m = -p := by abel
  have hp : -(m + p) + p = -m := by abel
  unfold logDifferential
  rw [hprod, Derivation.leibniz, smul_add, smul_smul, smul_smul]
  simp only [single_mul_single, one_mul, hm, hp]
  exact add_comm _ _

def logDifferentialAddHom : E →+ Ω[AddMonoidAlgebra k E⁄k] where
  toFun := logDifferential k
  map_zero' := logDifferential_zero k
  map_add' := logDifferential_add k

@[simp] theorem logDifferential_zsmul (m : E) (z : ℤ) :
    logDifferential k (z • m) = z • logDifferential k m :=
  (logDifferentialAddHom k).map_zsmul z m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem logDifferentialBasis_eq (b : Module.Basis ι ℤ E) (i : ι) :
    logDifferentialBasis k b i = logDifferential k (b i) :=
  logDifferentialBasis_apply k b i

theorem logDifferential_expansion (b : Module.Basis ι ℤ E) (m : E) :
    logDifferential k m =
      ∑ i, (b.repr m i : AddMonoidAlgebra k E) • logDifferential k (b i) := by
  calc
    logDifferential k m = logDifferential k (∑ i, b.repr m i • b i) := by
      apply congrArg (logDifferential k)
      calc
        m = ∑ i, (inferInstance : Module ℤ E).smul (b.repr m i) (b i) :=
          (b.sum_repr m).symm
        _ = _ := Finset.sum_congr rfl (fun i _ =>
          int_smul_eq_zsmul (inferInstance : Module ℤ E) (b.repr m i) (b i))
    _ = ∑ i, (b.repr m i : ℤ) • logDifferential k (b i) := by
      exact (map_sum (logDifferentialAddHom k (E := E)) _ _).trans (by
        congr 1
        funext i
        exact logDifferential_zsmul k (b i) (b.repr m i))
    _ = _ := by simp only [Int.cast_smul_eq_zsmul]

theorem logDifferentialBasis_repr (b : Module.Basis ι ℤ E) (m : E) (i : ι) :
    (logDifferentialBasis k b).repr (logDifferential k m) i = (b.repr m i : AddMonoidAlgebra k E) := by
  have hrepr (j : ι) : (logDifferentialBasis k b).repr (logDifferential k (b j)) =
      Finsupp.single j 1 := by
    rw [← logDifferentialBasis_eq, Module.Basis.repr_self]
  rw [logDifferential_expansion k b m]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, hrepr]
  simp [Finsupp.single_apply]

theorem character_differential_eq_smul_log (m : E) :
    D k (AddMonoidAlgebra k E) (single m 1) = single m (1 : k) • logDifferential k m := by
  rw [logDifferential, smul_smul]
  simp [← AddMonoidAlgebra.one_def]

section TopVolume

variable {n : ℕ}

def logVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n (logDifferentialBasis k b)

def regularCoordinateVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n
    (fun i => D k (AddMonoidAlgebra k E) (single (b i) 1))

theorem logDifferentialBasis_det (b c : Module.Basis (Fin n) ℤ E) :
    (logDifferentialBasis k b).det (logDifferentialBasis k c) =
      (b.det c : AddMonoidAlgebra k E) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix : (logDifferentialBasis k b).toMatrix (logDifferentialBasis k c) =
      (Int.castRingHom (AddMonoidAlgebra k E)).mapMatrix (b.toMatrix c) := by
    funext i j
    change (logDifferentialBasis k b).repr (logDifferentialBasis k c j) i =
      (b.repr (c j) i : AddMonoidAlgebra k E)
    rw [logDifferentialBasis_eq, logDifferentialBasis_repr]
  rw [hmatrix, ← RingHom.map_det]
  rfl

/-- The transition factor is the genuine determinant of the unimodular
integral character change of basis. -/
theorem logVolume_change_basis (b c : Module.Basis (Fin n) ℤ E) :
    logVolume k c = (b.det c : AddMonoidAlgebra k E) • logVolume k b := by
  have h := congrArg (fun f => f (logDifferentialBasis k c))
    (alternating_eq_basis_determinant (logDifferentialBasis k b)
      (exteriorPower.ιMulti (AddMonoidAlgebra k E) n))
  change logVolume k c = (logDifferentialBasis k b).det (logDifferentialBasis k c) •
    logVolume k b at h
  rw [logDifferentialBasis_det] at h
  exact h

theorem logVolume_transition_isUnit (b c : Module.Basis (Fin n) ℤ E) :
    IsUnit (b.det c : AddMonoidAlgebra k E) :=
  (b.isUnit_det c).map (Int.castRingHom (AddMonoidAlgebra k E))

/-- In a smooth full chart the regular differential volume has precisely
one copy of every coordinate character relative to the logarithmic volume. -/
theorem regularCoordinateVolume_eq_character_logVolume (b : Module.Basis (Fin n) ℤ E) :
    regularCoordinateVolume k b = single (∑ i, b i) (1 : k) • logVolume k b := by
  unfold regularCoordinateVolume
  simp_rw [character_differential_eq_smul_log]
  rw [AlternatingMap.map_smul_univ]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  exact congrArg (exteriorPower.ιMulti (AddMonoidAlgebra k E) n)
    (funext (fun i => (logDifferentialBasis_eq k b i).symm))

end TopVolume

end PaperVerification.ToricCharacters
