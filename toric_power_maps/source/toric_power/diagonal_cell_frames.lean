module

public import ToricPower.DiagonalChartComplex
public import ToricPower.ArrangementEquivariant
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Actual free bases for the cellular modules on Cartier charts

A Cartier equation on each factor gives a distinguished cell in each
normalized orbit. Every actual allowed strip cell is uniquely its translate
by a pair of regular chart characters. This explicit bijection gives an
isomorphism between the genuine cellular chart module and the free module
on normalized cells. Its compatibility with the complete chart-ring action
is proved on monomials and then on arbitrary finite sums.

The frame data contains only the ordinary Cartier character equations;
it contains no exactness, generation, differential, or comparison premise.
The actual fan frames are supplied separately by the proved Cartier API.
Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))

/-- The ordinary Cartier equation characters for the two labelled
line bundles, one pair for every normalized cell in a degree. -/
structure DiagonalCellFrames (d : ℕ) where
  left : NormalizedCell A d → (Fin n → ℤ)
  right : NormalizedCell A d → (Fin n → ℤ)
  left_eq : ∀ j ρ, ρ ∈ S →
    rayPairing A (left j) ρ = -reflectedCeiling A j.val ρ
  right_eq : ∀ j ρ, ρ ∈ T →
    rayPairing A (right j) ρ = -j.val.val.1 (.inl ρ)

@[simp]
theorem normalizeCell_normalized {d : ℕ} (j : NormalizedCell A d) :
    normalizeCell A j.val = j := by
  apply Subtype.ext
  change translateCell A (-coordinateCeilings A j.val) j.val = j.val
  rw [j.property,neg_zero,translateCell_zero]

namespace DiagonalCellFrames

variable {A S T} {d : ℕ} (F : DiagonalCellFrames A S T d)

def weight (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) : Fin n → ℤ :=
  (p.1.val-F.left j)+(p.2.val-F.right j)

theorem allowed (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    stripCellAllowed A S T (F.weight j p)
      (translateCell A (p.1.val-F.left j) j.val) := by
  rw [stripCellAllowed_translate_iff]
  constructor
  · intro ρ hρ
    rw [rayPairing_sub,F.left_eq j ρ hρ]
    have hp := p.1.property ρ hρ
    omega
  · intro ρ hρ
    have hw : F.weight j p-(p.1.val-F.left j) = p.2.val-F.right j := by
      unfold weight
      abel
    rw [hw,rayPairing_sub,F.right_eq j ρ hρ]
    have hp := p.2.property ρ hρ
    omega

/-- The literal actual cell corresponding to a regular monomial in
the selected Cartier frame. -/
def cell (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    DiagonalChartCell A S T d :=
  ⟨F.weight j p,translateCell A (p.1.val-F.left j) j.val,F.allowed j p⟩

theorem normalized_allowed (x : DiagonalChartCell A S T d) :
    diagonalMonomialAllowed A S T x.1
      (normalizeCell A x.2.val,coordinateCeilings A x.2.val) := by
  apply (stripCellAllowed_translate_iff A S T x.1
    (coordinateCeilings A x.2.val) (normalizeCell A x.2.val).val).mp
  rw [translate_normalizeCell]
  exact x.2.property

def leftCoordinate (x : DiagonalChartCell A S T d) : rayCharacterMonoid A S :=
  ⟨coordinateCeilings A x.2.val+F.left (normalizeCell A x.2.val),by
    intro ρ hρ
    rw [rayPairing_add,F.left_eq _ ρ hρ]
    have h := (normalized_allowed (A := A) (S := S) (T := T) x).1 ρ hρ
    change reflectedCeiling A (normalizeCell A x.2.val).val ρ ≤
      rayPairing A (coordinateCeilings A x.2.val) ρ at h
    omega⟩

def rightCoordinate (x : DiagonalChartCell A S T d) : rayCharacterMonoid A T :=
  ⟨x.1-coordinateCeilings A x.2.val+F.right (normalizeCell A x.2.val),by
    intro ρ hρ
    rw [rayPairing_add,F.right_eq _ ρ hρ]
    have h := (normalized_allowed (A := A) (S := S) (T := T) x).2 ρ hρ
    change (normalizeCell A x.2.val).val.val.1 (.inl ρ) ≤
      rayPairing A (x.1 - coordinateCeilings A x.2.val) ρ at h
    omega⟩

/-- The free-orbit basis equivalence includes all and only the literal
allowed strip cells. -/
def cellEquiv :
    (NormalizedCell A d ×
      (rayCharacterMonoid A S × rayCharacterMonoid A T)) ≃
        DiagonalChartCell A S T d where
  toFun p := F.cell p.1 p.2
  invFun x := (normalizeCell A x.2.val,F.leftCoordinate x,F.rightCoordinate x)
  left_inv p := by
    rcases p with ⟨j,p⟩
    apply Prod.ext
    · simp [cell,normalizeCell_translate]
    · apply Prod.ext <;> apply Subtype.ext
      · simp [leftCoordinate,cell,normalizeCell_translate,j.property]
      · simp only [rightCoordinate,cell,normalizeCell_translate,
          normalizeCell_normalized,coordinateCeilings_translateCell,j.property,zero_add]
        change F.weight j p - (p.1.val-F.left j) + F.right j = p.2.val
        unfold weight
        abel
  right_inv x := by
    have hw : F.weight (normalizeCell A x.2.val)
        (F.leftCoordinate x,F.rightCoordinate x) = x.1 := by
      change ((coordinateCeilings A x.2.val+F.left (normalizeCell A x.2.val))-
        F.left (normalizeCell A x.2.val))+
        ((x.1-coordinateCeilings A x.2.val+F.right (normalizeCell A x.2.val))-
          F.right (normalizeCell A x.2.val)) = x.1
      abel
    apply diagonalChartCell_ext A hw
    change translateCell A
      ((coordinateCeilings A x.2.val+F.left (normalizeCell A x.2.val))-
        F.left (normalizeCell A x.2.val)) (normalizeCell A x.2.val).val = x.2.val
    rw [add_sub_cancel_right,translate_normalizeCell]

/-- The basis equivalence intertwines the actual chart translation
with addition in its regular character monoid. -/
theorem cell_add (j : NormalizedCell A d)
    (p q : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    F.cell j (p+q) = diagonalChartTranslate A S T p (F.cell j q) := by
  have hw : F.weight j (p+q) = F.weight j q+p.1.val+p.2.val := by
    change ((p.1.val+q.1.val)-F.left j)+((p.2.val+q.2.val)-F.right j) =
      (q.1.val-F.left j)+(q.2.val-F.right j)+p.1.val+p.2.val
    abel
  apply diagonalChartCell_ext A hw
  change translateCell A ((p.1.val+q.1.val)-F.left j) j.val =
    translateCell A p.1.val (translateCell A (q.1.val-F.left j) j.val)
  rw [translateCell_add]
  congr 1
  abel

variable (k : Type) [CommRing k]

/-- On the underlying coefficient modules, uncurry the actual polynomial
coefficients and apply the proved cell equivalence. -/
def coefficientEquiv :
    (NormalizedCell A d →₀ DiagonalChartRing k A S T) ≃ₗ[k]
      DiagonalChartChains k A S T d :=
  ((Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv k)).trans
    (Finsupp.curryLinearEquiv k).symm).trans
      (Finsupp.domLCongr F.cellEquiv)

@[simp]
theorem coefficientEquiv_single (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    F.coefficientEquiv k (Finsupp.single j (AddMonoidAlgebra.single p r)) =
      Finsupp.single (F.cell j p) r := by
  change Finsupp.equivMapDomain F.cellEquiv
    (Finsupp.uncurry (Finsupp.mapRange (fun x => (AddMonoidAlgebra.coeffLinearEquiv k) x)
      (by rfl) (Finsupp.single j (AddMonoidAlgebra.single p r)))) = _
  rw [Finsupp.mapRange_single]
  change Finsupp.equivMapDomain F.cellEquiv
    (Finsupp.uncurry (Finsupp.single j (Finsupp.single p r))) = _
  rw [Finsupp.uncurry_single, Finsupp.equivMapDomain_single]
  rfl

theorem coefficientEquiv_monomial_single (j : NormalizedCell A d)
    (p q : rayCharacterMonoid A S × rayCharacterMonoid A T) (a b : k) :
    F.coefficientEquiv k
        (AddMonoidAlgebra.single p a •
          (Finsupp.single j (AddMonoidAlgebra.single q b) :
            NormalizedCell A d →₀ DiagonalChartRing k A S T)) =
      AddMonoidAlgebra.single p a •
        F.coefficientEquiv k (Finsupp.single j (AddMonoidAlgebra.single q b)) := by
  rw [Finsupp.smul_single,smul_eq_mul,AddMonoidAlgebra.single_mul_single,
    F.coefficientEquiv_single,F.coefficientEquiv_single]
  exact (congrArg (fun x => Finsupp.single x (a * b)) (F.cell_add j p q)).trans
    (diagonalChartChains_single_smul_single k A S T d p a b (F.cell j q)).symm

theorem coefficientEquiv_monomial (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (a : k) (v : NormalizedCell A d →₀ DiagonalChartRing k A S T) :
    F.coefficientEquiv k (AddMonoidAlgebra.single p a • v) =
      AddMonoidAlgebra.single p a • F.coefficientEquiv k v := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add j r v hj hr ih =>
      rw [smul_add,map_add,map_add,smul_add,ih]
      congr 1
      clear hj hr
      induction r using AddMonoidAlgebra.induction with
      | zero => simp
      | single_add q b r _ _ ihr =>
          rw [Finsupp.single_add,smul_add,map_add,map_add,smul_add,ihr,
            F.coefficientEquiv_monomial_single]

theorem coefficientEquiv_smul (r : DiagonalChartRing k A S T)
    (v : NormalizedCell A d →₀ DiagonalChartRing k A S T) :
    F.coefficientEquiv k (r • v) = r • F.coefficientEquiv k v := by
  induction r using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p a r _ _ ih =>
      rw [add_smul,map_add,add_smul,ih,F.coefficientEquiv_monomial]

/-- The genuine cellular chart module is finite free on the normalized
cells, with the actual scalar action, rather than only as a vector space. -/
def linearEquiv :
    (NormalizedCell A d →₀ DiagonalChartRing k A S T) ≃ₗ[DiagonalChartRing k A S T]
      DiagonalChartChains k A S T d where
  toAddEquiv := (F.coefficientEquiv k).toAddEquiv
  map_smul' := F.coefficientEquiv_smul k

@[simp]
theorem linearEquiv_single (j : NormalizedCell A d)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    F.linearEquiv k (Finsupp.single j (AddMonoidAlgebra.single p r)) =
      Finsupp.single (F.cell j p) r :=
  F.coefficientEquiv_single k j p r

end DiagonalCellFrames

end ToricPower.IntegralArrangement
