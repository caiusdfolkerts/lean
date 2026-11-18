module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The saturated integral trace of a real subspace

These are the exact lattice declarations formerly embedded in `SchemeCore`.
Separating them avoids importing derived categories to state elementary
lattice facts. The definitions and proof bodies are unchanged; their current
verification status is still development source awaiting compilation.
-/

/-! ## The actual saturated lattice of a rational subspace -/
@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  (i : N →+ V)

/-- Literal integral trace `N ∩ W`, as an integral submodule of `N`. -/
def latticeTrace (W : Submodule ℝ V) : Submodule ℤ N :=
  (W.restrictScalars ℤ).comap i.toIntLinearMap

@[simp] theorem mem_latticeTrace (W : Submodule ℝ V) (n : N) :
    n ∈ latticeTrace i W ↔ i n ∈ W := Iff.rfl

/-- The integral trace maps into the subspace itself, without an extraneous
ambient torus factor. -/
def latticeTraceMap (W : Submodule ℝ V) : latticeTrace i W →+ W where
  toFun n := ⟨i n, n.property⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] theorem latticeTraceMap_coe (W : Submodule ℝ V) (n : latticeTrace i W) :
    ((latticeTraceMap i W n : W) : V) = i n := rfl

/-- Rationality of a real subspace means precisely that its integral points
span it over the reals. -/
def IsRationalSubspace (W : Submodule ℝ V) : Prop :=
  Submodule.span ℝ (Set.range (fun n : latticeTrace i W => i n)) = W

/-- The literal trace is saturated: division by a positive integer cannot
leave the real subspace. -/
theorem latticeTrace_saturated (W : Submodule ℝ V) (k : ℕ) (hk : 0 < k) (n : N) :
    k • n ∈ latticeTrace i W ↔ n ∈ latticeTrace i W := by
  simp only [mem_latticeTrace, map_nsmul]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact Submodule.smul_mem_iff _ (by exact_mod_cast hk.ne')

/-- A rational subspace with its actual saturated integral trace is an integral
lattice in the strong scalar-extension sense used by the toric scheme library.
The full-rank condition is proved from a basis, not replaced by mere injectivity. -/
theorem latticeTrace_isIntegralLattice (hi : IsIntegralLattice i)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    IsIntegralLattice (latticeTraceMap i W) := by
  letI := hi.free
  letI := hi.finite
  let L := latticeTrace i W
  letI : Module.Finite ℤ L := inferInstance
  letI : Module.Free ℤ L := inferInstance
  let b := Module.finBasis ℤ L
  let j : L →ₗ[ℤ] V := i.toIntLinearMap.comp L.subtype
  have hz : LinearIndependent ℤ (fun a => ((b a : L) : N)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hr : LinearIndependent ℝ (fun a => j (b a)) := by
    exact (linearIndependent_comp_iff_of_liftBaseChange_injective
      hi.isBaseChange.liftBaseChange_injective).mpr hz
  have hsZ : Submodule.span ℤ (Set.range (fun a => j (b a))) = LinearMap.range j := by
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hs : Submodule.span ℝ (Set.range (fun a => j (b a))) = W := by
    calc
      Submodule.span ℝ (Set.range (fun a => j (b a))) =
          Submodule.span ℝ (Submodule.span ℤ (Set.range (fun a => j (b a))) : Set V) :=
        (Submodule.span_span_of_tower ℤ ℝ _).symm
      _ = Submodule.span ℝ (LinearMap.range j : Set V) := by rw [hsZ]
      _ = W := hW
  let c : Module.Basis (Fin (Module.finrank ℤ L)) ℝ W :=
    (Module.Basis.span hr).map (LinearEquiv.ofEq _ _ hs)
  apply isIntegralLattice_of_basis b c
  intro a
  apply Subtype.ext
  simp only [c, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply, latticeTraceMap_coe]
  rfl

end ToricPower
end

