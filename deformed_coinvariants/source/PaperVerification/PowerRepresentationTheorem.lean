module

public import PaperVerification.PowerGradedRepresentation
public import PaperVerification.GradedRepresentationAssembly

/-!
# The graded representation assertion of Theorem 2.2

The endpoint is a single equivalence of the actual quotient representations
over the original field. Its forward and inverse maps preserve every genuine
homogeneous quotient piece. The comparison quotient is the literal ideal
quotient by `h_m, …, h_(m+n-1)`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Module

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

def completeHomogeneousAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    Representation K G (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) :=
  ordinaryQuotientAction G (completeHomogeneousFamily K n m)
    (completeHomogeneousFamily_invariant G m)

def completeHomogeneousActualGrading (K : Type*) [Field K] (n m : ℕ) :
    TauCeti.InternalGrading K
      (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) ℕ where
  piece := ordinaryQuotientDegree (completeHomogeneousFamily K n m)
  isInternal := by
    have h := (completeHomogeneousGrading K n m).isInternal
    have he : (completeHomogeneousGrading K n m).piece =
        ordinaryQuotientDegree (completeHomogeneousFamily K n m) :=
      funext fun d => completeHomogeneousGrading_piece m d
    rwa [he] at h

def tailQuotientActualGrading (c : Fin n → K) (lam : K) (m : ℕ) :
    TauCeti.InternalGrading K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) ℕ where
  piece := tailQuotientDegree c lam m
  isInternal := by
    have h := (tailQuotientGrading c lam m).isInternal
    have he : (tailQuotientGrading c lam m).piece = tailQuotientDegree c lam m :=
      funext fun d => tailQuotientGrading_piece c lam m d
    rwa [he] at h

/-- The full graded `G`-module comparison, with the field, coefficient tuple,
deformation slope, tail index, subgroup, and all degrees left unrestricted
except for the paper's stated nonresonance and positive tail hypotheses. -/
theorem paper_theorem_2_2_graded_representation
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    ∃ e : (tailQuotientAction G c lam m hfix).Equiv (completeHomogeneousAction G m),
      (∀ d x, x ∈ tailQuotientDegree c lam m d →
        e x ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) ∧
      (∀ d y, y ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d →
        e.symm y ∈ tailQuotientDegree c lam m d) := by
  let GV := completeHomogeneousActualGrading K n m
  let GW := tailQuotientActualGrading c lam m
  let ed : ∀ d, (completeHomogeneousDegreeRepresentation G m d).Equiv
      (tailQuotientDegreeRepresentation G c lam m hfix d) :=
    fun d => Classical.choice (paper_theorem_2_2_degree_representation c lam m d hm hnr G hfix)
  let e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d := fun d => (ed d).toLinearEquiv
  have hV : ∀ g d x, x ∈ GV.piece d → completeHomogeneousAction G m g x ∈ GV.piece d := by
    intro g d x hx
    exact ordinaryQuotientAction_preserves_degree G (completeHomogeneousFamily K n m)
      (completeHomogeneousFamily_invariant G m) g d hx
  have he : ∀ g d (x : GV.piece d),
      (e d ⟨completeHomogeneousAction G m g x,hV g d x x.property⟩ :
        MvPolynomial (Fin n) K ⧸ tailHit c lam m) =
      tailQuotientAction G c lam m hfix g (e d x) := by
    intro g d x
    exact congrArg Subtype.val
      (LinearMap.congr_fun ((ed d).toIntertwiningMap.isIntertwining' g) x)
  let E := GradedRepresentationAssembly.representationEquiv GV GW
    (completeHomogeneousAction G m) (tailQuotientAction G c lam m hfix) hV e he
  refine ⟨E.symm,?_,?_⟩
  · intro d x hx
    exact GradedRepresentationAssembly.representationEquiv_symm_preserves_piece GV GW
      (completeHomogeneousAction G m) (tailQuotientAction G c lam m hfix) hV e he d hx
  · intro d y hy
    exact GradedRepresentationAssembly.representationEquiv_preserves_piece GV GW
      (completeHomogeneousAction G m) (tailQuotientAction G c lam m hfix) hV e he d hy

/-- The reversed-family basis and representation assertions of Theorem 2.2:
the literal
Artin monomials form a basis, and the entire quotient has the stated graded
representation type for every coefficient-fixing subgroup. -/
theorem paper_theorem_2_2_reversed_basis_and_representation
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m) :
    (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m),
      ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1)) ∧
    ∀ (G : Subgroup (Equiv.Perm (Fin n)))
      (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i),
      ∃ e : (tailQuotientAction G c lam m hfix).Equiv (completeHomogeneousAction G m),
        (∀ d x, x ∈ tailQuotientDegree c lam m d →
          e x ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) ∧
        (∀ d y, y ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d →
          e.symm y ∈ tailQuotientDegree c lam m d) := by
  refine ⟨paper_theorem_2_2_monomial_basis c lam m hm hnr,?_⟩
  intro G hfix
  exact paper_theorem_2_2_graded_representation c lam m hm hnr G hfix

end PaperVerification.PowerOperators
