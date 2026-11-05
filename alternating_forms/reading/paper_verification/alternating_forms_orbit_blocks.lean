module

public import PaperVerification.AlternatingFormsOrbitChart
public import PaperVerification.AlternatingFormsOrbitCross

/-!
# Explicit blocks solving the odd pencil orbit differential

The AA and BB blocks are solved by the rectangular chart isomorphisms in adjacent
sizes. The mixed block is solved by the previously established diagonal difference map.
No normal-form or generic-rank hypothesis is assumed.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms

open Matrix

variable {K : Type*} [Field K]

abbrev OddOrbitBlockInput (K : Type*) (t : ℕ) :=
  (Matrix (Fin (t + 1)) (Fin (t + 1)) K ×
    Matrix (Fin (t + 2)) (Fin (t + 2)) K) ×
  (Matrix (Fin (t + 1)) (Fin (t + 2)) K ×
    Matrix (Fin (t + 2)) (Fin (t + 1)) K)

abbrev OddOrbitBlockOutput (K : Type*) (t : ℕ) :=
  ((Orbit.StrictPair (t + 1) ⊕ Orbit.StrictPair (t + 1)) → K) ×
  (((Orbit.StrictPair (t + 2) ⊕ Orbit.StrictPair (t + 2)) → K) ×
    (Matrix (Fin (t + 1)) (Fin (t + 2)) K ×
      Matrix (Fin (t + 1)) (Fin (t + 2)) K))

/-- Blocks of the derivative at the canonical pair, ordered AA, BB, AB. -/
def oddOrbitBlockMap (t : ℕ) (H : OddOrbitBlockInput K t) :
    OddOrbitBlockOutput K t :=
  (Sum.elim
    (fun p ↦ H.2.2 p.val.1.succ p.val.2 - H.2.2 p.val.2.succ p.val.1)
    (fun p ↦ H.2.2 p.val.1.castSucc p.val.2 -
      H.2.2 p.val.2.castSucc p.val.1),
   (-Orbit.rectangleChart (K := K) (t + 1) H.2.1,
    orbitCrossMap (K := K) t H.1))

/-- The full canonical odd pencil differential is onto in block coordinates. -/
theorem oddOrbitBlockMap_surjective (t : ℕ) :
    Function.Surjective (oddOrbitBlockMap (K := K) t) := by
  rintro ⟨AA, BB, AB⟩
  obtain ⟨T, hT⟩ := Orbit.rectangleChart_surjective (K := K) t
    (fun z ↦ AA z.swap)
  obtain ⟨Q, hQ⟩ := Orbit.rectangleChart_surjective (K := K) (t + 1) (-BB)
  obtain ⟨PS, hPS⟩ := orbitCrossMap_surjective (K := K) t AB
  let R : Matrix (Fin (t + 2)) (Fin (t + 1)) K :=
    Matrix.of fun i j ↦ Orbit.rectPad T i.val j
  refine ⟨(PS, (Q, R)), ?_⟩
  apply Prod.ext
  · funext z
    rcases z with p | p
    · have h := congrFun hT (Sum.inr p)
      simpa only [oddOrbitBlockMap, R, Matrix.of_apply, Fin.val_succ,
        Orbit.rectangleChart, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Sum.swap_inr] using h
    · have h := congrFun hT (Sum.inl p)
      simpa only [oddOrbitBlockMap, R, Matrix.of_apply, Fin.val_castSucc,
        Orbit.rectangleChart, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Sum.swap_inl] using h
  · apply Prod.ext
    · change -Orbit.rectangleChart (K := K) (t + 1) Q = BB
      rw [hQ, neg_neg]
    · exact hPS

/-- Assemble the four solved blocks into the actual infinitesimal change of basis. -/
def oddOrbitBlockMatrix (t : ℕ) (H : OddOrbitBlockInput K t) :
    Matrix (Fin (t + 1) ⊕ Fin (t + 2)) (Fin (t + 1) ⊕ Fin (t + 2)) K :=
  Matrix.fromBlocks H.1.1 H.2.1 H.2.2 H.1.2

end PaperVerification.AlternatingForms
