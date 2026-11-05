module

public import PaperVerification.PowerCoinvariantStandard
public import PaperVerification.PowerOriginalArtinSpanning

/-! The standard-absence result on the literal elementary quotient interface. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation

namespace PaperVerification.PowerCoinvariantStabilizer

open PowerOperators PowerStandardHarmonics

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "G" => (⊤ : Subgroup (Equiv.Perm (Fin (n+1))))
local notation "Q" => MvPolynomial (Fin (n+1)) K ⧸ ordinaryCoinvariantIdeal K (n+1)

theorem coinvariantGrading_piece_eq_elementary_degree (d : ℕ) :
    (coinvariantGrading (K := K) (n := n)).piece d =
      ordinaryQuotientDegree (elementaryCoinvariantFamily K (n+1)) d := by
  rw [coinvariantGrading_piece]
  rfl

theorem elementary_top_action_eq_coinvariant (σ : Equiv.Perm (Fin (n+1))) (x : Q) :
    ordinaryQuotientAction G (elementaryCoinvariantFamily K (n+1))
      (elementaryCoinvariantFamily_invariant G) ⟨σ,trivial⟩ x = coinvariantAction σ x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem standard_elementary_degree_intertwiner_eq_zero (d : ℕ) (hd : n+1 ≤ d)
    (f : IntertwiningMap
      ((standardRepresentation (K := K) (ι := Fin (n+1))).comp (G).subtype)
      (ordinaryQuotientDegreeRepresentation G (elementaryCoinvariantFamily K (n+1))
        (elementaryCoinvariantFamily_invariant G) d)) : f = 0 := by
  let e : ordinaryQuotientDegree (elementaryCoinvariantFamily K (n+1)) d ≃ₗ[K]
      (coinvariantGrading (K := K) (n := n)).piece d :=
    LinearEquiv.ofEq _ _ (coinvariantGrading_piece_eq_elementary_degree (K := K) (n := n) d).symm
  let f' : IntertwiningMap (standardRepresentation (K := K) (ι := Fin (n+1)))
      (coinvariantDegreeRepresentation (K := K) (n := n) d) :=
    { toLinearMap := e.toLinearMap.comp f.toLinearMap
      isIntertwining' σ := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        have hi := LinearMap.congr_fun (f.isIntertwining' ⟨σ,trivial⟩) v
        simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at hi
        have h := congrArg Subtype.val hi
        change (f (standardRepresentation σ v)).val =
          ordinaryQuotientAction G (elementaryCoinvariantFamily K (n+1))
            (elementaryCoinvariantFamily_invariant G) ⟨σ,trivial⟩ (f v).val at h
        have ha := elementary_top_action_eq_coinvariant (K := K) (n := n) σ (f v).val
        change (f (standardRepresentation σ v)).val = coinvariantAction σ (f v).val
        exact h.trans ha }
  have hz := standard_intertwiner_eq_zero d hd f'
  ext v
  change (f v).val = 0
  have h := congrArg (fun a : IntertwiningMap (standardRepresentation (K := K) (ι := Fin (n+1)))
      (coinvariantDegreeRepresentation (K := K) (n := n) d) => (a v).val) hz
  change (f v).val = 0 at h
  exact h

end PaperVerification.PowerCoinvariantStabilizer
