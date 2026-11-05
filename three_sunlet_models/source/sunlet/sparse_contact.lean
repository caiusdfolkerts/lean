module

public import sunlet.contact_completion
public import sunlet.toric_differential

/-! The complete sparse radial-contact calculation under its explicit
combinatorial support hypotheses. The theorem concerns the actual second
differential proved in `ToricDifferential`, not an assumed contact criterion. -/

@[expose] public section
noncomputable section

namespace Sunlet.SparseContact

open Contact ToricDifferential

variable {ι Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
  [Field K] [CharZero K]

/-- Proposition 4.5's sparse calculation, including all unused colors. -/
theorem radial
    (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hdis : Disjoint A B) (hm : 5 ≤ Fintype.card Ω)
    (hder : ∀ a, ∀ x, π a x ≠ x) (hAnonempty : A.Nonempty)
    (hBtwo : ∃ a ∈ B, ∃ b ∈ B, π a ≠ π b)
    (hBtrans : TransitiveFamily π B)
    (hredtwo : ∀ b ∈ B, ∃ a ∈ B \ {b}, ∃ c ∈ B \ {b}, π a ≠ π c)
    (hredtrans : ∀ b ∈ B, TransitiveFamily π (B \ {b}))
    (hthree : ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
      π a ≠ π b ∧ π a ≠ π c ∧ π b ≠ π c)
    (hconn : ∀ x y, Relation.EqvGen (PuncturedBothEndpoints.OrdinaryEdge o π B) x y)
    (hout : Function.Injective (fun a => π a o))
    (hin : Function.Injective (fun a => (π a).symm o))
    (v : ToricDifferential.Variation K ι Ω) (hbase : v.2 o = 0)
    (hcontact : ∀ w : ToricDifferential.Variation K ι Ω,
      hessian π (sparseCoefficients A) (fun _ => 1) v w ∈ tangentSpan π o A B) :
    ∃ lam : K, v = lam • (sparseCoefficients A, (0 : Ω → K)) := by
  classical
  have hcoeff : ∀ a, colorVector a (fun x => v.2 x - v.2 (π a x)) ∈ tangentSpan π o A B := by
    intro a
    have hh := hcontact ((fun b => if b = a then 1 else 0), 0)
    convert hh using 1
    funext bx
    rcases bx with ⟨b, x⟩
    simp only [colorVector, hessian, ratio, div_self one_ne_zero, one_mul,
      Pi.zero_apply, sub_self, mul_zero, add_zero]
    split_ifs with hab <;> simp [hab]
  have hK := torus_velocity_zero π o A B hdis (fun a => hder a o)
    hBtwo hBtrans hredtwo hredtrans v.2 hbase hcoeff
  have hp : TorusContact π o A B v.1 := by
    intro H
    have hh := hcontact (0, H)
    convert hh using 1
    funext ax
    rcases ax with ⟨a, x⟩
    simp [hessian, ratio, hK]
  have hpA := coefficient_constant_on_first π o A B hdis hm hder v.1 hp
  have hpB := coefficient_constant_on_second π o A B hdis hm hder v.1 hp
  have hBzero : ∀ b ∈ B, v.1 b = 0 := by
    intro b hb
    exact common_second_coefficient_zero π o A B hdis hm hder hthree hconn hout hin v.1 hp
      (v.1 b) (fun a ha => hpB a ha b hb)
  have hOff := coefficient_zero_off_supports π o A B hm hder v.1 hp
  obtain ⟨a₀, ha₀⟩ := hAnonempty
  refine ⟨v.1 a₀, ?_⟩
  apply Prod.ext
  · funext a
    by_cases ha : a ∈ A
    · simpa [sparseCoefficients, ha] using hpA a ha a₀ ha₀
    · by_cases hb : a ∈ B
      · simpa [sparseCoefficients, ha] using hBzero a hb
      · simpa [sparseCoefficients, ha] using hOff a ha hb
  · funext x
    simpa using hK x

end Sunlet.SparseContact
