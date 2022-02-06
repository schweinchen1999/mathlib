/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Pointed
import data.pfun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
classically stems from the difference between `part` and `option`. Both can model partial functions,
but the latter forces a decidable domain.

## References

* [nLab, *The category of sets and partial functions]
[http://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/partial+function]
-/

open category_theory option

universes u
variables {α β : Type*}

@[simp] lemma subtype.coe_inj {p : α → Prop} {a b : subtype p} : (a : α) = b ↔ a = b :=
subtype.coe_injective.eq_iff

/-- The category of types equipped with partial functions. -/
def PartialFun : Type* := Type*

namespace PartialFun

instance : has_coe_to_sort PartialFun Type* := ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
@[nolint has_inhabited_instance] def of : Type* → PartialFun := id

instance : inhabited PartialFun := ⟨Type*⟩

instance large_category : large_category.{u} PartialFun :=
{ hom := pfun,
  id := pfun.id,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := @pfun.comp_id,
  comp_id' := @pfun.id_comp,
  assoc' := λ W X Y Z _ _ _, (pfun.comp_assoc _ _ _).symm }

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def Type_to_PartialFun : Type ⥤ PartialFun :=
{ obj := id,
  map := @pfun.lift,
  map_comp' := λ _ _ _ _ _, pfun.coe_comp _ _ }

instance : faithful Type_to_PartialFun := ⟨λ X Y, pfun.coe_injective⟩

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
def Pointed_to_PartialFun : Pointed.{u} ⥤ PartialFun :=
{ obj := λ X, {x : X // x ≠ X.point},
  map := λ X Y f, pfun.to_subtype _ f.to_fun ∘ subtype.val,
  map_id' := λ X, pfun.ext $ λ a b,
    pfun.mem_to_subtype_iff.trans (subtype.coe_inj.trans part.mem_some_iff.symm),
  map_comp' := λ X Y Z f g, pfun.ext $ λ a c, begin
    refine (pfun.mem_to_subtype_iff.trans _).trans part.mem_bind_iff.symm,
    simp_rw [pfun.mem_to_subtype_iff, subtype.exists],
    refine ⟨λ h, ⟨f.to_fun a, λ ha, c.2 $ h.trans
      ((congr_arg g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩, _⟩,
    rintro ⟨b, _, (rfl : b = _), h⟩,
    exact h,
  end }

/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't
be computable because `= option.none` is decidable while the domain of a general `part` isn't. -/
noncomputable def PartialFun_to_Pointed : PartialFun ⥤ Pointed :=
by classical; exact
{ obj := λ X, ⟨option X, none⟩,
  map := λ X Y f, ⟨λ o, o.elim none (λ a, (f a).to_option), rfl⟩,
  map_id' := λ X, Pointed.hom.ext _ _ $ funext $ λ o, rec_on o rfl (λ a, part.some_to_option _),
  map_comp' := λ X Y Z f g, Pointed.hom.ext _ _ $ funext $ λ o, rec_on o rfl $ λ a,
    part.bind_to_option _ _ }

/-- The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.
`part.equiv_option` with extra steps. -/
@[simps] noncomputable def PartialFun_equiv_Pointed : PartialFun.{u} ≌ Pointed :=
by classical; exact
equivalence.mk PartialFun_to_Pointed Pointed_to_PartialFun
  (nat_iso.of_components (λ X,
    { hom := λ a, part.some ⟨some a, some_ne_none _⟩,
      inv := λ a, part.some (get $ ne_none_iff_is_some.1 a.2),
      hom_inv_id' := pfun.ext $ λ a b, begin
        unfold_projs,
        refine (part.mem_bind_iff.trans _).trans part.mem_some_iff.symm,
        simp_rw [part.mem_some_iff, exists_prop, exists_eq_left, get_some],
      end,
      inv_hom_id' := pfun.ext $ λ a b, begin
        unfold_projs,
        refine (part.mem_bind_iff.trans _).trans part.mem_some_iff.symm,
        dsimp,
        simp_rw [part.mem_some_iff, exists_prop, exists_eq_left, some_get, subtype.coe_eta],
      end }) $ λ X Y f, pfun.ext $ λ a b, begin
      unfold_projs,
      dsimp,
      rw part.bind_some,
      refine (part.mem_bind_iff.trans _).trans pfun.mem_to_subtype_iff.symm,
      obtain ⟨b | b, hb⟩ := b,
      { exact (hb rfl).elim },
      simp_rw [part.mem_some_iff, subtype.mk_eq_mk, exists_prop, subtype.coe_mk, some_inj,
        exists_eq_right'],
      refine part.mem_to_option.symm.trans _,
      convert eq_comm,
      convert rfl,
    end)
  (nat_iso.of_components (λ X,
    { hom := ⟨λ a, a.elim X.point subtype.val, rfl⟩,
      inv := ⟨λ a, if h : a = X.point then none else some ⟨_, h⟩, dif_pos rfl⟩,
      hom_inv_id' := Pointed.hom.ext _ _ $ funext $ λ a, rec_on a (dif_pos rfl) $ λ a,
        (dif_neg a.2).trans by { simp only [elim, subtype.val_eq_coe, subtype.coe_eta], refl },
      inv_hom_id' := Pointed.hom.ext _ _ $ funext $ λ a, begin
          change elim (dite _ _ _) _ _ = _,
          split_ifs,
          { rw h, refl },
          { refl }
        end }) $ λ X Y f, Pointed.hom.ext _ _ $ funext $ λ a, rec_on a f.map_point.symm $ λ a,
    begin
      unfold_projs,
      change elim (elim _ _ _) _ _ = _,
      rw [elim, part.elim_to_option],
      split_ifs,
      { refl },
      { exact eq.symm (of_not_not h) }
    end)

/-- Forgetting that maps are total and make them total again by adding a point is the same as just
adding a point. -/
@[simps] noncomputable def Type_to_PartialFun_iso_PartialFun_to_Pointed :
  Type_to_PartialFun ⋙ PartialFun_to_Pointed ≅ Type_to_Pointed :=
nat_iso.of_components (λ X, { hom := ⟨id, rfl⟩,
                              inv := ⟨id, rfl⟩,
                              hom_inv_id' := rfl,
                              inv_hom_id' := rfl }) $ λ X Y f,
  Pointed.hom.ext _ _ $ funext $ λ a, rec_on a rfl $ λ a, by convert part.some_to_option _
