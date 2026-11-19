module

public import higher_specht.verified.remaining03_fiber

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct Polynomial Classical

namespace HigherSpecht

section SplitFiber
variable {n m : ℕ} {ι : Type*} [Fintype ι]

theorem theorem_7_1_parameter_fiber_exists
    (K : Type*) [Field K] (lam : YoungDiagram) (a : Fin m → K)
    (hsize : lam.card + m = n) (r0 : ℕ)
    (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    Nonempty (ParameterFiber K n lam m a ≃ₐ[K]
      ∀ _f : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r),
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j)))) :=
  ⟨theorem_7_1_parameter_fiber K lam a hsize r0 c hc hcz r hr hfactor⟩

end SplitFiber

theorem theorem_7_1_algebraicClosure_exists
    (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    Nonempty (L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
      ∀ _f : PrescribedRootAssignments n
          (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q)),
        ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j)))) :=
  ⟨theorem_7_1_algebraicClosure K lam a hsize⟩

end HigherSpecht
