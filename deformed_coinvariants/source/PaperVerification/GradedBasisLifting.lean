module

public import PaperVerification.PolynomialBasisLifting
public import TauCeti.Algebra.Module.GradedModule.Polynomial
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.NormNum

/-!
# Homogeneous basis lifting over a polynomial parameter

A parameter strictly shifting a bounded grading, regular on the module, lifts
any homogeneous basis of the quotient to a polynomial-module basis. Both
spanning and independence are proved. A finite input basis gives finite generation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Polynomial DirectSum Module
open scoped BigOperators

namespace PaperVerification.GradedBasisLifting

variable {K M V I : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [Module K[X] M] [IsScalarTower K K[X] M]
  [AddCommGroup V] [Module K V]

/-- The scalar `X` regarded as a coefficient-ring linear endomorphism. -/
def parameterMap : M →ₗ[K] M := Algebra.lsmul K K M (X : K[X])

@[simp] theorem parameterMap_apply (x : M) : parameterMap (K := K) x = (X : K[X]) • x := rfl

/-- Homogeneous lifts of a spanning family modulo a strictly shifting parameter span. -/
theorem span_lifts_eq_top
    (G : TauCeti.InternalGrading K M) (d : ℕ) (hd : d ≠ 0)
    (hbdd : BddAbove {p | G.piece p ≠ ⊥})
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : K[X]) • x ∈ G.piece (p - d))
    (q : M →ₗ[K] V) (hker : LinearMap.ker q = LinearMap.range (parameterMap (K := K)))
    (b : I → M) (hbhom : ∀ i, ∃ p, b i ∈ G.piece p)
    (hbspan : Submodule.span K (Set.range (fun i => q (b i))) = ⊤) :
    Submodule.span K[X] (Set.range b) = ⊤ := by
  let C : Submodule K M := Submodule.span K (Set.range b)
  let N : Submodule K[X] M := Submodule.span K[X] (Set.range b)
  have hCN : C ≤ N.restrictScalars K := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span hx
  have hChom : DirectSum.SetLike.IsHomogeneous G.piece C :=
    G.isHomogeneous_span _ (by rintro _ ⟨i, rfl⟩; exact hbhom i)
  have hCmap : C.map q = ⊤ := by
    change (Submodule.span K (Set.range b)).map q = ⊤
    rw [Submodule.map_span, ← Set.range_comp']
    exact hbspan
  have hstep : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → x ∈ (⊤ : Submodule K[X] M) →
      ∃ y ∈ G.piece (p + d), y ∈ (⊤ : Submodule K[X] M) ∧ x - (X : K[X]) • y ∈ N := by
    intro p x hx _
    have hqx : q x ∈ C.map q := hCmap.symm ▸ Submodule.mem_top
    obtain ⟨z, hz, hqz⟩ := hqx
    have hxz : x - z ∈ LinearMap.range (parameterMap (K := K)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, hqz, sub_self]
    obtain ⟨y, hy⟩ := hxz
    let y' : M := DirectSum.decompose G.piece y (p + d)
    refine ⟨y', (DirectSum.decompose G.piece y (p + d)).property, Submodule.mem_top, ?_⟩
    have hproj : (DirectSum.decompose G.piece ((X : K[X]) • y) p : M) =
        (X : K[X]) • y' := by
      have hi : p + ((1 : ℕ) : ℤ) * (d : ℤ) = p + d := by norm_num
      calc
        (DirectSum.decompose G.piece ((X : K[X]) • y) p : M) =
            (X : K[X]) • (DirectSum.decompose G.piece y
              (p + ((1 : ℕ) : ℤ) * (d : ℤ)) : M) := by
          simpa only [pow_one] using
            (TauCeti.InternalGrading.coe_decompose_X_pow_smul hX 1 p y)
        _ = (X : K[X]) • y' :=
          congrArg (fun q : ℤ => (X : K[X]) • (DirectSum.decompose G.piece y q : M)) hi
    have heq := congrArg (fun u : M => (DirectSum.decompose G.piece u p : M)) hy
    change (DirectSum.decompose G.piece ((X : K[X]) • y) p : M) =
      (DirectSum.decompose G.piece (x - z) p : M) at heq
    rw [hproj, DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      DirectSum.decompose_of_mem_same G.piece hx] at heq
    have hfinal : x - (X : K[X]) • y' = (DirectSum.decompose G.piece z p : M) := by
      rw [heq]
      abel
    rw [hfinal]
    exact hCN (hChom p hz)
  apply top_unique
  exact TauCeti.InternalGrading.le_of_forall_mem_piece_exists_sub_X_smul_mem
    hd hbdd (L := (⊤ : Submodule K[X] M)) (N := N)
    (by intro p x hx; exact Submodule.mem_top) hstep

/-- A regular positive-degree parameter lifts every homogeneous quotient basis
without changing the chosen representatives. -/
theorem basis_lifts
    (G : TauCeti.InternalGrading K M) (d : ℕ) (hd : d ≠ 0)
    (hbdd : BddAbove {p | G.piece p ≠ ⊥})
    (hXhom : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : K[X]) • x ∈ G.piece (p - d))
    (hXreg : IsSMulRegular M (X : K[X]))
    (q : M →ₗ[K] V) (hker : LinearMap.ker q = LinearMap.range (parameterMap (K := K)))
    (b : I → M) (hbhom : ∀ i, ∃ p, b i ∈ G.piece p)
    (hb : Basis I K V) (hqb : ∀ i, q (b i) = hb i) :
    ∃ B : Basis I K[X] M, ∀ i, B i = b i := by
  have hqX : ∀ x, q ((X : K[X]) • x) = 0 := by
    intro x
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact ⟨x, rfl⟩
  have hli : LinearIndependent K (fun i => q (b i)) := by
    simpa only [hqb] using hb.linearIndependent
  have hsp : Submodule.span K (Set.range (fun i => q (b i))) = ⊤ := by
    simpa only [hqb] using hb.span_eq
  have hliP := PolynomialBasisLifting.linearIndependent_lifts q hqX hXreg b hli
  have hspP := span_lifts_eq_top G d hd hbdd hXhom q hker b hbhom hsp
  exact ⟨Basis.mk hliP hspP.ge, fun i => Basis.mk_apply _ _ i⟩

end PaperVerification.GradedBasisLifting
