module

public import ToricPower.DiagonalCellFrames
public import ToricPower.DualDiagonalWeightComplex

/-!
# The genuine dual Cartier frame and every Laurent weight

The finite free module in each dual diagonal degree has a basis of
normalized cells with polynomial coefficients in the two affine charts.
Expanding these coefficients gives exactly the unrestricted total-character
sum of the actual dual-strip coefficient bases. The two Cartier frame
equations, including their signs, prove this bijection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))

abbrev DualDiagonalAllWeightIndex (q : ℕ) :=
  Σ u : Fin n → ℤ, DualDiagonalWeightIndex A S T u q

@[ext]
theorem dualDiagonalAllWeightIndex_ext {q : ℕ}
    {x y : DualDiagonalAllWeightIndex A S T q}
    (weight : x.1 = y.1) (cell : x.2.1 = y.2.1)
    (character : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨u, c, a, ha⟩
  rcases y with ⟨v, d, b, hb⟩
  dsimp at weight cell character
  subst v
  subst d
  subst b
  rfl

namespace DiagonalCellFrames

variable {A S T} {d : ℕ} (F : DiagonalCellFrames A S T d)

/-- The actual total character in the two dual Cartier frames. -/
def dualWeight (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) : Fin n → ℤ :=
  (F.left j + p.1.val) + (F.right j + p.2.val)

theorem dualAllowed (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    dualDiagonalWeightAllowed A S T (F.dualWeight j p)
      ⟨d, j⟩ (F.left j + p.1.val) := by
  constructor
  · intro ρ hρ
    change 0 ≤ rayPairing A (F.left j + p.1.val) ρ + reflectedCeiling A j.val ρ
    rw [rayPairing_add, F.left_eq j ρ hρ]
    have hp := p.1.property ρ hρ
    omega
  · intro ρ hρ
    have difference : F.dualWeight j p - (F.left j + p.1.val) =
        F.right j + p.2.val := by unfold dualWeight; abel
    change 0 ≤ rayPairing A (F.dualWeight j p - (F.left j + p.1.val)) ρ +
      j.val.val.1 (.inl ρ)
    rw [difference, rayPairing_add, F.right_eq j ρ hρ]
    have hp := p.2.property ρ hρ
    omega

/-- A regular polynomial monomial in the actual dual frame is the
specified total weight and actual first-factor Laurent character. -/
def dualCell (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    DualDiagonalAllWeightIndex A S T d :=
  ⟨F.dualWeight j p, j, ⟨F.left j + p.1.val, F.dualAllowed j p⟩⟩

def dualLeftCoordinate (x : DualDiagonalAllWeightIndex A S T d) :
    rayCharacterMonoid A S :=
  ⟨x.2.2.val - F.left x.2.1, by
    intro ρ hρ
    rw [rayPairing_sub, F.left_eq _ ρ hρ]
    have h := x.2.2.property.1 ρ hρ
    change 0 ≤ rayPairing A x.2.2.val ρ + reflectedCeiling A x.2.1.val ρ at h
    omega⟩

def dualRightCoordinate (x : DualDiagonalAllWeightIndex A S T d) :
    rayCharacterMonoid A T :=
  ⟨x.1 - x.2.2.val - F.right x.2.1, by
    intro ρ hρ
    rw [rayPairing_sub, F.right_eq _ ρ hρ]
    have h := x.2.2.property.2 ρ hρ
    change 0 ≤ rayPairing A (x.1 - x.2.2.val) ρ + x.2.1.val.val.1 (.inl ρ) at h
    omega⟩

/-- The complete basis equivalence. It retains every integral weight
and uses precisely the two ordinary Cartier equations. -/
def dualCellEquiv :
    (NormalizedCell A d × (rayCharacterMonoid A S × rayCharacterMonoid A T)) ≃
      DualDiagonalAllWeightIndex A S T d where
  toFun p := F.dualCell p.1 p.2
  invFun x := (x.2.1, F.dualLeftCoordinate x, F.dualRightCoordinate x)
  left_inv p := by
    rcases p with ⟨j, p⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext
      · change F.left j + p.1.val - F.left j = p.1.val
        abel
      · change F.dualWeight j p - (F.left j + p.1.val) - F.right j = p.2.val
        unfold dualWeight
        abel
  right_inv x := by
    apply dualDiagonalAllWeightIndex_ext
    · change (F.left x.2.1 + (x.2.2.val - F.left x.2.1)) +
        (F.right x.2.1 + (x.1 - x.2.2.val - F.right x.2.1)) = x.1
      abel
    · rfl
    · change F.left x.2.1 + (x.2.2.val - F.left x.2.1) = x.2.2.val
      abel

variable (k : Type) [CommRing k]

/-- Expansion of the actual polynomial coefficients into the complete
Laurent-weight basis, as an isomorphism over the coefficient ring. -/
def dualCoefficientEquiv :
    (NormalizedCell A d →₀ DiagonalChartRing k A S T) ≃ₗ[k]
      (DualDiagonalAllWeightIndex A S T d →₀ k) :=
  ((Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv k)).trans
    (Finsupp.curryLinearEquiv k).symm).trans
      (Finsupp.domLCongr F.dualCellEquiv)

@[simp]
theorem dualCoefficientEquiv_single (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    F.dualCoefficientEquiv k (Finsupp.single j (AddMonoidAlgebra.single p r)) =
      Finsupp.single (F.dualCell j p) r := by
  change Finsupp.equivMapDomain F.dualCellEquiv
    (Finsupp.uncurry (Finsupp.mapRange (fun x => (AddMonoidAlgebra.coeffLinearEquiv k) x)
      (by rfl) (Finsupp.single j (AddMonoidAlgebra.single p r)))) = _
  rw [Finsupp.mapRange_single]
  change Finsupp.equivMapDomain F.dualCellEquiv
    (Finsupp.uncurry (Finsupp.single j (Finsupp.single p r))) = _
  rw [Finsupp.uncurry_single, Finsupp.equivMapDomain_single]
  rfl

end DiagonalCellFrames
end ToricPower.IntegralArrangement
