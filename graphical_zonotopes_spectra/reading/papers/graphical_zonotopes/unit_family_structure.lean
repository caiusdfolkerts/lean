module

public import Papers.GraphicalZonotopes.BooleanFourPartStructure
public import Papers.GraphicalZonotopes.FourPartCompletion

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.UnitFamilyStructure
open Finset Function FourPartCompletion BooleanFourPartStructure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {y : SetFunction V} {C : Finset (Finset V)}

theorem update_injective (v : Fin 4 → V) (hv : Injective v)
    (i : Fin 4) (x : V) (hx : x∉vertices v) : Injective (update v i x) := by
  intro a b he
  by_cases hai : a=i
  · subst a
    by_cases hbi : b=i
    · exact hbi.symm
    · have hxb : x=v b := by simpa [update_of_ne hbi] using he
      exact False.elim (hx (hxb.symm ▸ self_mem_vertices v b))
  · by_cases hbi : b=i
    · subst b
      have hax : v a=x := by simpa [update_of_ne hai] using he
      exact False.elim (hx (hax ▸ self_mem_vertices v a))
    · apply hv
      simpa [update_of_ne hai,update_of_ne hbi] using he

theorem thin_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C := by
  intro v hv hf i x z hx hz hX hZ
  by_contra hxz
  have hvi := self_mem_vertices v i
  have hD := vertices_card v hv
  have hT : ((vertices v).erase (v i)).card=3 := by rw [card_erase_of_mem hvi,hD]
  have hbase : y (insert (v i) ((vertices v).erase (v i)))≠0 := by
    rw [insert_erase hvi]
    exact ((hC _).mp hf).2
  have hx' : x∉(vertices v).erase (v i) := fun h => hx (mem_of_mem_erase h)
  have hz' : z∉(vertices v).erase (v i) := fun h => hz (mem_of_mem_erase h)
  have hix : v i≠x := fun he => hx (he ▸ hvi)
  have hiz : v i≠z := fun he => hz (he ▸ hvi)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv i z] at h
  exact three_extensions_impossible hG hy hb hT (by simp) hx' hz' hix hiz hxz hbase hX' hZ'

theorem squareClosed_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : SquareClosed C := by
  intro v hv hf i j hij x z hx hz hX hZ
  have hvi := self_mem_vertices v i
  have hvj := self_mem_vertices v j
  have hvij : v i≠v j := fun he => hij (hv he)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v j)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv j z] at h
  obtain ⟨hxz,hnew⟩ := replacement_square hG hy hb (vertices_card v hv)
    ((hC _).mp hf).2 hvi hvj hvij hx hz hX' hZ'
  refine ⟨hxz,?_⟩
  have hvx : Injective (update v i x) := update_injective v hv i x hx
  have hznew : z∉vertices (update v i x) := by
    rw [vertices_update v hv i x]
    intro h
    rcases mem_insert.mp h with he | he
    · exact hxz he.symm
    · exact hz (mem_of_mem_erase he)
  apply (hC _).mpr
  refine ⟨vertices_card _ (update_injective _ hvx j z hznew),?_⟩
  have hvjx : v j≠x := fun he => hx (he ▸ hvj)
  have he : vertices (update (update v i x) j z)=
      insert z (insert x (((vertices v).erase (v i)).erase (v j))) := by
    rw [vertices_update _ hvx j z,vertices_update v hv i x]
    simp only [update_of_ne (Ne.symm hij),erase_insert_of_ne (Ne.symm hvjx)]
  rwa [he]

/-- Exactly the two local structural properties required by the global
Cartesian completion theorem, for the actual nonzero coefficient family. -/
theorem structure_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C ∧ SquareClosed C :=
  ⟨thin_of_boolean hG hy hb hC,squareClosed_of_boolean hG hy hb hC⟩

end GraphicalZonotopes.UnitFamilyStructure
