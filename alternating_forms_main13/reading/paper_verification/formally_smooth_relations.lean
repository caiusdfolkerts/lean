module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.Tactic

/-!
# A differential criterion for a smooth zero scheme

This is the multi-equation version of the elementary cotangent splitting
argument. All modules and differentials are Mathlib's actual cotangent
modules. The hypotheses say that derivations dual to the defining equations
exist; they are precisely what a right inverse of the Jacobian supplies.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential TensorProduct Algebra

namespace PaperVerification.GenericSectionDifferentials

/-- A finite family of defining equations with dual derivations gives a
formally smooth quotient of a formally smooth algebra. -/
theorem formallySmooth_of_dual_derivations
    {K S κ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    [Fintype κ] [DecidableEq κ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f) = P.ker)
    (δ : κ → Derivation K P.Ring S)
    (hδ : ∀ i j, δ i (f j) = if i=j then 1 else 0) :
    Algebra.FormallySmooth K S := by
  let g : κ → P.Cotangent := fun i => Extension.Cotangent.mk
    ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  let l : P.CotangentSpace →ₗ[S] P.Cotangent := ∑ i,
    (LinearMap.toSpanSingleton S P.Cotangent (g i)).comp
      (LinearMap.liftBaseChange S (δ i).liftKaehlerDifferential)
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨l, ?_⟩
  have hspan : Submodule.span S (Set.range g) = ⊤ :=
    Extension.Cotangent.span_eq_top_of_span_eq_ker f hf
  apply LinearMap.ext_on_range hspan
  intro j
  simp [l, g, hδ]


/-- A right inverse of the actual Jacobian produces the dual derivations.
The ambient differential module is given a basis, as on an affine-space chart. -/
theorem formallySmooth_of_jacobian_rightInverse
    {K S κ τ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    [Fintype κ] [DecidableEq κ] [Fintype τ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (b : Module.Basis τ P.Ring Ω[P.Ring⁄K])
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f)=P.ker)
    (u : Matrix τ κ S)
    (hu : (show Matrix κ τ S from
      fun j t => algebraMap P.Ring S (b.repr (D K P.Ring (f j)) t)) * u=1) :
    Algebra.FormallySmooth K S := by
  let δ : κ → Derivation K P.Ring S := fun j =>
    (∑ t, u t j • ((Algebra.linearMap P.Ring S).comp (b.coord t))).compDer
      (D K P.Ring)
  apply formallySmooth_of_dual_derivations P f hf δ
  intro i j
  have h := congrFun (congrFun hu j) i
  change (∑ t, algebraMap P.Ring S (b.repr (D K P.Ring (f j)) t) * u t i) =
    if j=i then 1 else 0 at h
  simpa [δ, Module.Basis.coord_apply, mul_comm, eq_comm] using h

end PaperVerification.GenericSectionDifferentials
