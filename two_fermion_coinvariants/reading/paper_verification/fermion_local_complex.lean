module

public import PaperVerification.FermionSeparatedFactorBridge
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The literal complex statements in Section 7.2

Mathlib's proved fundamental theorem of algebra supplies `IsAlgClosed ℂ`.
These statements have no algebraic-closedness or characteristic premise:
they concern precisely the complex algebras in the paper.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

/-- Theorem 7.2 over the paper's actual coefficient field. -/
theorem theorem_7_2_complex {n : ℕ} (d : SeparatedPairedData ℂ n) :
    Finite d.O.SupportPoint ∧
    (∀ rho : d.O.SupportPoint,∃ e :
        d.LocalSuper rho ≃ₐ[ℂ] (d.localClusterFamily rho).tensor.Carrier,
      ∀ g x,e x∈(d.localClusterFamily rho).tensorBigrading.part g ↔
        x∈d.localSuperBigradedPart rho g) ∧
    Nonempty (d.SuperQuotient ≃ₐ[ℂ]
      ∀ rho : d.O.SupportPoint,(d.localClusterFamily rho).tensor.Carrier) ∧
    (∀ rho : d.O.SupportPoint,Nontrivial (d.LocalSuper rho)) ∧
    (∀ (rho : d.O.SupportPoint) (c : Fin (Fintype.card (d.O.PointCluster rho))),
      ∃ e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[ℂ]
        PairedQuotient (d.localFactorPairedData rho c).beta
          (d.localFactorPairedData rho c).phi
          (d.localFactorPairedData rho c).a
          (d.localFactorPairedData rho c).b,
        ∀ g x,e x∈d.localFactorPairedBigradedPart rho c g ↔
          x∈((d.localClusterFamily rho).factorBigrading c).part g) :=
  theorem_7_2 d

theorem localSuper_finrank_complex {n : ℕ} (d : SeparatedPairedData ℂ n)
    (rho : d.O.SupportPoint) :
    Module.finrank ℂ (d.LocalSuper rho)=
      2^n*(∏ i,d.O.ramificationOrder rho i)*
        ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)) :=
  d.localSuper_finrank rho

theorem localSuper_exterior_hilbert_coefficient_complex {n : ℕ}
    (d : SeparatedPairedData ℂ n) (rho : d.O.SupportPoint) (k : ℕ) :
    Module.finrank ℂ (d.localSuperExteriorTotalPart rho k)=
      (Polynomial.C ((∏ i,d.O.ramificationOrder rho i)*
          ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
            ((d.localClusterFamily rho).s c).ascFactorial
              (Fintype.card (d.LocalFactorIndex rho c)))*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k :=
  d.localSuper_exterior_hilbert_coefficient rho k

theorem globalSuper_finrank_closed_complex {n : ℕ}
    (d : SeparatedPairedData ℂ n) (hn : 0<n) :
    Module.finrank ℂ d.SuperQuotient=
      2^n*(∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n :=
  d.globalSuper_finrank_closed hn

theorem globalSuper_exterior_hilbert_coefficient_complex {n : ℕ}
    (d : SeparatedPairedData ℂ n) (hn : 0<n) (k : ℕ) :
    Module.finrank ℂ (d.globalSuperExteriorTotalPart k)=
      (Polynomial.C ((∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n)*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k :=
  d.globalSuper_exterior_hilbert_coefficient hn k

/-- The original presentation is retained even if the factors were first
given as coupled multivariate polynomials. -/
def originalSuperTensorProductEquiv_complex {n : ℕ}
    {d : PairedData (K := ℂ) (n := n)} (c : SeparatedCoverOfPairedData d) :
    PairedQuotient d.beta d.phi d.a d.b ≃ₐ[ℂ]
      ∀ rho : c.toSeparatedData.O.SupportPoint,
        (c.toSeparatedData.localClusterFamily rho).tensor.Carrier :=
  c.originalSuperTensorProductEquiv

end PaperVerification.Fermion
