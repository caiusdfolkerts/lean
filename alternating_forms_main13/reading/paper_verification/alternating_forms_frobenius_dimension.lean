module

public import PaperVerification.AlternatingFormsExcessDimension
public import PaperVerification.AlternatingFormsSparseProjection

/-!
# The full integer exterior dimension bound from Frobenius cycles

All terms are actual homogeneous exterior powers. The two sparse algebra
maps prove independence of the extra cycles modulo the Koszul image; the
only injectivity input is subsequently supplied by the matching theorem.
The quotient is the homogeneous component of the actual generated ideal.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The rank-nullity mechanism for two nilpotent quadratic forms, with
explicit algebra maps detecting their extra syzygies separately. -/
theorem exterior_quotient_excess_of_frobenius_certificates
    (f g : ⋀[K]^2 M) (r : ℕ) (hr : 1 ≤ r)
    (hf : (f : ExteriorAlgebra K M)^(r+1) = 0)
    (hg : (g : ExteriorAlgebra K M)^(r+1) = 0)
    (hinj : ∀ h : ⋀[K]^(2*r-2) M,
      (f : ExteriorAlgebra K M)*h = 0 → h = 0)
    (π₁ π₂ : ExteriorAlgebra K M →ₐ[K] ExteriorAlgebra K M)
    (hπ₁ : π₁ (g : ExteriorAlgebra K M) = 0)
    (hπ₁pow : π₁ ((f : ExteriorAlgebra K M)^r) ≠ 0)
    (hπ₂ : π₂ (f : ExteriorAlgebra K M) = 0)
    (hπ₂pow : π₂ ((g : ExteriorAlgebra K M)^r) ≠ 0) :
    ((Module.finrank K M).choose (2*r+2) : ℤ) -
      2*((Module.finrank K M).choose (2*r) : ℤ) +
      ((Module.finrank K M).choose (2*r-2) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree f g (2*r+2)) : ℤ) := by
  let q := 2*r-2
  have hq₂ : q+2 = 2*r := by dsimp [q]; omega
  have hq₄ : q+4 = 2*r+2 := by dsimp [q]; omega
  let fp : ⋀[K]^(q+2) M := ⟨(f : ExteriorAlgebra K M)^r, by
    rw [hq₂]
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (A := fun d : ℕ => ⋀[K]^d M) r f.property⟩
  let gp : ⋀[K]^(q+2) M := ⟨(g : ExteriorAlgebra K M)^r, by
    rw [hq₂]
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (A := fun d : ℕ => ⋀[K]^d M) r g.property⟩
  let z₁ : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M := (fp, 0)
  let z₂ : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M := (0, gp)
  have hz₁ : exteriorRelationMapDegree f g q z₁ = 0 := by
    apply Subtype.ext
    change (f : ExteriorAlgebra K M)*(f : ExteriorAlgebra K M)^r +
      (g : ExteriorAlgebra K M)*0 = 0
    rw [mul_zero, add_zero, ← pow_succ', hf]
  have hz₂ : exteriorRelationMapDegree f g q z₂ = 0 := by
    apply Subtype.ext
    change (f : ExteriorAlgebra K M)*0 +
      (g : ExteriorAlgebra K M)*(g : ExteriorAlgebra K M)^r = 0
    rw [mul_zero, zero_add, ← pow_succ', hg]
  have hrel : ∀ (h : ⋀[K]^q M) (α β : K),
      exteriorKoszulMapDegree f g q h + α • z₁ + β • z₂ = 0 →
        α = 0 ∧ β = 0 := by
    intro h α β heq
    have hleft := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
      (x.1 : ExteriorAlgebra K M)) heq
    have hright := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
      (x.2 : ExteriorAlgebra K M)) heq
    change (g : ExteriorAlgebra K M)*h + α • (f : ExteriorAlgebra K M)^r + β • 0 = 0 at hleft
    change -((f : ExteriorAlgebra K M)*h) + α • 0 + β • (g : ExteriorAlgebra K M)^r = 0 at hright
    have hα := congrArg π₁ hleft
    have hβ := congrArg π₂ hright
    simp only [map_add, map_mul, map_smul, map_zero, hπ₁, zero_mul,
      smul_zero, zero_add, add_zero] at hα
    simp only [map_add, map_neg, map_mul, map_smul, map_zero, hπ₂, zero_mul,
      neg_zero, smul_zero, zero_add, add_zero] at hβ
    exact ⟨(smul_eq_zero.mp hα).resolve_right hπ₁pow,
      (smul_eq_zero.mp hβ).resolve_right hπ₂pow⟩
  have hd := cokernel_finrank_lower_of_two_extra_cycles
    (exteriorRelationMapDegree f g q) (exteriorKoszulMapDegree f g q)
    (exteriorRelationMapDegree_comp f g q)
    (exteriorKoszulMapDegree_injective f g q hinj) z₁ z₂ hz₁ hz₂ hrel
  rw [exteriorRelationMapDegree_range] at hd
  change (Module.finrank K (⋀[K]^(q+4) M) : ℤ) -
    (Module.finrank K (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) : ℤ) +
    (Module.finrank K (⋀[K]^q M) : ℤ) + 2 ≤
    (Module.finrank K (ExteriorQuotientDegree f g (q+4)) : ℤ) at hd
  rw [Module.finrank_prod, hq₂, hq₄] at hd
  simp only [exteriorPower.finrank_eq, Nat.cast_add, q] at hd
  linarith

section OddPath

variable {k : ℕ}

theorem oddPath_first_pow_char (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^p = 0 := by
  rw [oddPathFirstQuadratic, matchingQuadratic_coe]
  exact exterior_matching_pow_char
    (fun i => b (oddPathFirstLeft i)) (fun i => b (oddPathMiddle i)) p

theorem oddPath_second_pow_char (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^p = 0 := by
  rw [oddPathSecondQuadratic, matchingQuadratic_coe]
  exact exterior_matching_pow_char
    (fun i => b (oddPathMiddle i)) (fun i => b (oddPathSecondRight i)) p

/-- The complete numerical lower bound once genuine matching injectivity
is supplied. The next theorem discharges this specific remaining input. -/
theorem oddPath_quotient_excess_of_injective
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k)
    (hinj : ∀ h : ⋀[K]^(2*p-4) M,
      (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)*h = 0 → h = 0) :
    ((2*k+1).choose (2*p) : ℤ) - 2*((2*k+1).choose (2*p-2) : ℤ) +
      ((2*k+1).choose (2*p-4) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) : ℤ) := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨π₁, π₂, hπ₁, hπ₁pow, hπ₂, hπ₂pow⟩ :=
    oddPath_frobenius_projection_certificates b p (by omega : 2*(p-1) ≤ k)
  have hf : (oddPathFirstQuadratic (K := K) b : ExteriorAlgebra K M)^((p-1)+1) = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using oddPath_first_pow_char b p
  have hg : (oddPathSecondQuadratic (K := K) b : ExteriorAlgebra K M)^((p-1)+1) = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using oddPath_second_pow_char b p
  have h₀ : 2*(p-1)-2 = 2*p-4 := by omega
  have h₁ : 2*(p-1) = 2*p-2 := by omega
  have h₂ : 2*(p-1)+2 = 2*p := by omega
  have hrank : Module.finrank K M = 2*k+1 := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  have h := exterior_quotient_excess_of_frobenius_certificates
    (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (p-1) (by omega)
    hf hg (by rw [h₀]; exact hinj) π₁ π₂ hπ₁ hπ₁pow hπ₂ hπ₂pow
  rw [h₂, h₀, h₁, hrank] at h
  exact h

end OddPath

end PaperVerification.AlternatingForms
