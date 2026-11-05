import Characterizations.Projection
import Characterizations.Transport

/-! # Retained-variable and ambient descriptions of monomial localization agree -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem embeddedFamily_polymatroidal {B : Family W} (hp : IsPolymatroidal B) (e : W ↪ V) :
    IsPolymatroidal (embeddedFamily e B) := by
  obtain ⟨d, hd⟩ := hp.1
  apply (polymatroidal_iff_universal_revlex (k := ℚ) (embeddedFamily_equigenerated hd e)).mpr
  intro o
  exact (embeddedFamily_linearQuotients_iff hd e o).mpr
    (polymatroidal_variable_linearQuotients hp.2 (restrictedOrder o e))

theorem localize_eq_embeddedFamily (B : Family V) (U : Finset V) :
    localize B U = embeddedFamily (Function.Embedding.subtype (· ∈ U)) (localFamily B U) := by
  rw [localize_eq_extend_localFamily]
  unfold embeddedFamily
  congr 1
  funext a
  exact Finsupp.extendDomain_eq_embDomain_subtype a

theorem localize_polymatroidal_of_localFamily {B : Family V} (U : Finset V)
    (h : IsPolymatroidal (localFamily B U)) : IsPolymatroidal (localize B U) := by
  rw [localize_eq_embeddedFamily]
  exact embeddedFamily_polymatroidal h _

theorem localize_polymatroidal {B : Family V} (hp : IsPolymatroidal B) (U : Finset V) :
    IsPolymatroidal (localize B U) :=
  localize_polymatroidal_of_localFamily U (localFamily_polymatroidal hp U)

theorem localFamily_polymatroidal_iff (B : Family V) (U : Finset V) :
    IsPolymatroidal (localFamily B U) ↔ IsPolymatroidal (localize B U) := by
  refine ⟨localize_polymatroidal_of_localFamily U, ?_⟩
  intro h
  obtain ⟨d, hd⟩ := h.1
  have heq : Equigenerated (localFamily B U) d := by
    intro a ha
    have hh : extendExponent U a ∈ localize B U := by
      rw [localize_eq_extend_localFamily]
      exact mem_image.mpr ⟨a, ha, rfl⟩
    simpa only [extendExponent_degree] using hd _ hh
  rw [localize_eq_embeddedFamily] at h
  exact embeddedFamily_polymatroidal_implies heq _ h

end Characterizations
