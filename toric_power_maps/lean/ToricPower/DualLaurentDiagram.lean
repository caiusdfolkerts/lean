module

public import ToricPower.ClosedDualLaurentLabels

/-! # The unrestricted contravariant inverse-label Laurent diagram

An incidence acts by addition of its original lattice character. This
coefficient diagram imposes no closed-support or finite-weight cutoff.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (b : Fin s → ℤ) (k : Type) [CommRing k]

def dualLaurentDiagram : (IncidenceObject A)ᵒᵖ ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (DualLaurentWeight A S b c.unop →₀ k)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain k k (dualLaurentWeightMap A S b f.unop))
  map_id c := by
    have same : dualLaurentWeightMap A S b (𝟙 c.unop) = id := by
      funext m
      apply Subtype.ext
      exact add_zero _
    rw [unop_id,same,Finsupp.lmapDomain_id]
    rfl
  map_comp {c d e} f g := by
    have same : dualLaurentWeightMap A S b (g.unop ≫ f.unop) =
        dualLaurentWeightMap A S b g.unop ∘ dualLaurentWeightMap A S b f.unop := by
      funext m
      apply Subtype.ext
      change m.val+(g.unop.val+f.unop.val)=(m.val+f.unop.val)+g.unop.val
      abel
    rw [unop_comp,same,Finsupp.lmapDomain_comp]
    rfl

@[simp]
theorem dualLaurentDiagram_map_single {c d : IncidenceObject A} (f : c ⟶ d)
    (m : DualLaurentWeight A S b d) (r : k) :
    (dualLaurentDiagram A S b k).map f.op (Finsupp.single m r) =
      Finsupp.single (dualLaurentWeightMap A S b f m) r :=
  Finsupp.mapDomain_single

end ToricPower.IntegralArrangement

end
