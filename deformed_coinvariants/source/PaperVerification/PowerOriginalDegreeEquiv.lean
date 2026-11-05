module

public import PaperVerification.PowerOriginalRepresentation
public import PaperVerification.PowerOriginalDegreePresentation

/-! Degree restrictions of the actual original-family representation equivalence. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation

namespace PaperVerification.RepresentationHomComparison

variable {K G : Type*} [Field K] [Group G]
variable {L V W : Type*} [AddCommGroup L] [Module K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def intertwinerTargetEquiv (τ : Representation K G L)
    {ρ : Representation K G V} {σ : Representation K G W} (e : ρ.Equiv σ) :
    IntertwiningMap τ ρ ≃ₗ[K] IntertwiningMap τ σ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by
    ext x
    exact e.symm_apply_apply (f x)
  right_inv f := by
    ext x
    exact e.apply_symm_apply (f x)
  map_add' f g := by
    ext x
    exact e.map_add (f x) (g x)
  map_smul' a f := by
    ext x
    exact e.map_smul a (f x)

end PaperVerification.RepresentationHomComparison

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem paper_theorem_2_2_original_degree_representation
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Nonempty ((originalTailQuotientDegreeRepresentation G c lam m hfix d).Equiv
      (completeHomogeneousDegreeRepresentation G m d)) := by
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_original_graded_representation c lam m hm hnr hlow G hfix
  let ed : originalTailQuotientDegree c lam m d ≃ₗ[K]
      ordinaryQuotientDegree (completeHomogeneousFamily K n m) d :=
    { toFun x := ⟨e x,he d x x.property⟩
      invFun y := ⟨e.symm y,he' d y y.property⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x)
      right_inv y := Subtype.ext (e.apply_symm_apply y)
      map_add' x y := Subtype.ext (e.map_add x y)
      map_smul' a x := Subtype.ext (e.map_smul a x) }
  refine ⟨Representation.Equiv.mk ed ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change e (originalTailQuotientAction G c lam m hfix g x.val) =
    completeHomogeneousAction G m g (e x.val)
  simpa only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
    Representation.Equiv.coe_toIntertwiningMap] using
    LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x

end PaperVerification.PowerOperators
