module

public import PaperVerification.PowerOriginalDegreePresentation
public import PaperVerification.PowerStandardDual
public import PaperVerification.SelfDualSubrepresentation

/-!
# A standard subrepresentation at every resonant degree

The degree-`q+1` Fischer functionals are genuine functionals on the original
joint-image quotient. Their explicit permutation law and injectivity, followed
by self-duality and an averaged section, give an injective intertwiner into
that exact homogeneous quotient piece.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation

namespace PaperVerification.PowerStandardHarmonics

open PowerOperators

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def standardSubgroupRepresentation (G : Subgroup (Equiv.Perm (Fin n))) :
    Representation K G (standardSpace (K := K) (ι := Fin n)) :=
  (standardRepresentation (K := K) (ι := Fin n)).comp G.subtype

theorem standardDegreeDualMap_intertwines [Nonempty (Fin n)]
    (α : K) (q : ℕ)
    (hres : (Fintype.card (Fin n) : K) + α*(q+1 : ℕ) = 0)
    (G : Subgroup (Equiv.Perm (Fin n))) (g : G)
    (v : standardSpace (K := K) (ι := Fin n))
    (x : originalTailQuotientDegree (fun _ : Fin n => (1 : K)) α 1 (q+1)) :
    standardDegreeDualMap α q hres (standardSubgroupRepresentation G g v) x =
      standardDegreeDualMap α q hres v
        (originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
          α 1 (fun _ _ => rfl) (q+1) g⁻¹ x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨p, hp, rfl⟩ := hx
  change standardQuotientDualMap α q hres (permuteStandard (g : Equiv.Perm (Fin n)) v)
      ((originalTailHit (fun _ => (1 : K)) α 1).mkQ p) =
    standardQuotientDualMap α q hres v
      ((originalTailHit (fun _ => (1 : K)) α 1).mkQ
        (rename (g : Equiv.Perm (Fin n)).symm p))
  exact standardQuotientDualMap_permutation α q hres g v p

theorem exists_resonant_standard_subrepresentation [Nonempty (Fin n)]
    (α : K) (q : ℕ)
    (hres : (Fintype.card (Fin n) : K) + α*(q+1 : ℕ) = 0)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    ∃ f : IntertwiningMap (standardSubgroupRepresentation (K := K) G)
      (originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
        α 1 (fun _ _ => rfl) (q+1)), Function.Injective f := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine SelfDualSubrepresentation.exists_injective_intertwiner
    (originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
      α 1 (fun _ _ => rfl) (q+1)) (standardSubgroupRepresentation G)
    (standardDualEquiv (K := K) (ι := Fin n)) ?_
    (standardDegreeDualMap α q hres) ?_ (standardDegreeDualMap_injective α q hres)
  · intro g v w
    exact standardDualEquiv_contragredient (g : Equiv.Perm (Fin n)) v w
  · exact standardDegreeDualMap_intertwines α q hres G

end PaperVerification.PowerStandardHarmonics
