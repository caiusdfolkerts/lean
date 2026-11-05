import cubical.cube_face_code
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic

/-! # Exact enumeration and prism structure of cube face codes -/

open Classical
open scoped BigOperators

noncomputable section

namespace Cubical.Cube

/-- A face is specified by its free coordinates and one Boolean value
on every remaining coordinate. -/
def faceCodeOnComplement {d : ℕ} (A : Finset (Fin d)) (s : (↑Aᶜ) → Bool) : FaceCode d :=
  fun i => if hi : i ∈ A then .free else .fixed (s ⟨i, Finset.mem_compl.mpr hi⟩)

@[simp] theorem freeCoords_faceCodeOnComplement {d : ℕ} (A : Finset (Fin d))
    (s : (↑Aᶜ) → Bool) : freeCoords (faceCodeOnComplement A s) = A := by
  ext i
  by_cases hi : i ∈ A <;> simp [faceCodeOnComplement, hi]

def freeCoordsFiberEquiv {d : ℕ} (A : Finset (Fin d)) :
    {p : FaceCode d // freeCoords p = A} ≃ ((↑Aᶜ) → Bool) where
  toFun p := fun i => baseCode p.val i.val
  invFun s := ⟨faceCodeOnComplement A s, freeCoords_faceCodeOnComplement A s⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A
    · have hp : p.val i = .free := (mem_freeCoords p.val i).mp (p.property.symm ▸ hi)
      simp [faceCodeOnComplement, hi, hp]
    · have hp : p.val i ≠ .free := by
        intro hp
        exact hi (p.property ▸ (mem_freeCoords p.val i).mpr hp)
      cases heq : p.val i with
      | free => exact (hp heq).elim
      | fixed b => simp [faceCodeOnComplement, hi, baseCode, heq]
  right_inv s := by
    funext i
    have hi : i.val ∉ A := Finset.mem_compl.mp i.property
    simp [faceCodeOnComplement, hi, baseCode]

/-- There are exactly `2^(d-i) choose(d,i)` nonempty i-dimensional cube
faces, including the whole cube at i=d. The formula also handles i>d. -/
theorem card_faceCodes_rank (d i : ℕ) :
    Fintype.card {p : FaceCode d // (freeCoords p).card = i} =
      2 ^ (d - i) * d.choose i := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (freeCoords (d := d))
    (p := fun p => (freeCoords p).card = i) (q := fun A => A.card = i) (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  have hcard (A : {A : Finset (Fin d) // A.card = i}) :
      Fintype.card {p : FaceCode d // freeCoords p = A.val} = 2 ^ (d - i) := by
    rw [Fintype.card_congr (freeCoordsFiberEquiv A.val), Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe, Finset.card_compl, Fintype.card_fin, A.property]
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Fintype.card_finset_len,
    Fintype.card_fin, Nat.mul_comm]

/-- Splitting the last coordinate identifies a cube with a prism on a
lower-dimensional cube at the level of the ordinary face posets. -/
def faceCodePrismIso (d : ℕ) : FaceCode d × FaceCoordinate ≃o FaceCode (d + 1) where
  toFun p := Fin.snoc p.1 p.2
  invFun p := (Fin.init p, p (Fin.last d))
  left_inv p := by simp
  right_inv p := by simp
  map_rel_iff' := by
    intro p q
    change (∀ i : Fin (d + 1), (Fin.snoc p.1 p.2 : FaceCode (d + 1)) i ≤
      (Fin.snoc q.1 q.2 : FaceCode (d + 1)) i) ↔ p ≤ q
    constructor
    · intro h
      exact ⟨fun i => by simpa only [Fin.snoc_castSucc] using h i.castSucc,
        by simpa only [Fin.snoc_last] using h (Fin.last d)⟩
    · rintro ⟨h1, h2⟩ i
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using h2
      | cast i => simpa only [Fin.snoc_castSucc] using h1 i

end Cubical.Cube
