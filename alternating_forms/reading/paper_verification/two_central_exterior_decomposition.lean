module

public import PaperVerification.ExteriorCoordinateProjection
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FinCases

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
