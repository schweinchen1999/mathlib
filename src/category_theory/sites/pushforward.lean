import category_theory.sites.sheaf
import category_theory.limits.has_limits
import category_theory.functor_category
import category_theory.sites.grothendieck
import category_theory.full_subcategory
import category_theory.equivalence
import category_theory.sites.spaces
import category_theory.limits.kan_extension

universes v u
noncomputable theory

open topological_space
open category_theory
open opposite


section
variables {C : Type u} [category.{v} C] {D : Type u} [category.{v} D]
variables {P Q Q' : Dᵒᵖ ⥤ Type v} (F : C ⥤ D)
open category_theory.presieve

namespace category_theory
namespace presieve
def functor_pullback {X : C} (R : presieve (F.obj X)) : presieve X := λ Y f, R (F.map f)

end presieve

namespace sieve
def functor_pullback {X : C} (R : sieve (F.obj X)) : sieve X := {
  arrows := presieve.functor_pullback F R,
  downward_closed' := λ _ _ f hf g, by {
    unfold presieve.functor_pullback,
    rw F.map_comp,
    exact R.downward_closed hf (F.map g),
  }
}
end sieve

namespace presieve
namespace family_of_elements
section functor_pullback
variables {X : C} {R : presieve (F.obj X)} {x : family_of_elements P R}

def functor_pullback (x : family_of_elements P R) :
  family_of_elements (F.op ⋙ P) (R.functor_pullback F) := λ Y f hf, x (F.map f) hf

lemma compatible.functor_pullback (h : x.compatible) : (x.functor_pullback F).compatible :=
begin
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])
end

end functor_pullback

section pullback
def pullback {X Y: D} (f : Y ⟶ X) {R : sieve X} (x : family_of_elements P R) :
  family_of_elements P (R.pullback f) := λ _ g hg, x (g ≫ f) hg

lemma compatible.pullback {X Y: D} (f : Y ⟶ X) {R : sieve X}
  {x : family_of_elements P R} (h : x.compatible) : (x.pullback f).compatible :=
begin
  simp only [compatible_iff_sieve_compatible] at h ⊢,
  intros W Z f₁ f₂ hf,
  refine eq.trans _ (h (f₁ ≫ f) f₂ hf),
  unfold pullback,
  simp only [category.assoc],
end

end pullback


def comp_presheaf_map {X : D} {R : presieve X} (f : P ⟶ Q) (x : family_of_elements P R) :
  family_of_elements Q R := λ Y g hg, f.app (op Y) (x g hg)

lemma compatible.comp_presheaf_map {X : D} {R : presieve X} (f : P ⟶ Q) {x : family_of_elements P R}
  (h : x.compatible) : (x.comp_presheaf_map f).compatible :=
begin
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,
  change (f.app _ ≫ Q.map _) _ = (f.app _ ≫ Q.map _) _,
  simp only [← f.naturality],
  exact congr_arg (f.app (op W)) (h g₁ g₂ h₁ h₂ eq)
end

end family_of_elements
end presieve
end category_theory
end

variables {C D E A : Type u} [category.{u} C] [category.{u} D] [category.{u} E] [category.{u} A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables (F : C ⥤ D) [limits.has_limits A]
open category_theory.limits

variable (ℱ : Sheaf J A)

/- Can't find these stuff anywhere. -/
lemma lem1 {α : Sort*} {P : α → Prop} (Q : α → Prop) (H : ∀ x, P x → Q x) (h : ∃ x, P x) : Q (classical.some h)
:= by {
  apply H, apply classical.some_spec,
}

lemma lem2 {α : Sort*} {P : α → Prop} {h : ∃! x, P x} {y : α} (H : P y) : y = classical.some h
:= by {
  apply lem1,
  intros x hx,
  exact hx.2 y H,
}

/--
Given a structured arrow `X ⟶ F(U)`, and an arrow `U ⟶ Y`, we can construct a structured
arrow given by `X ⟶ F(U) ⟶ F(Y)`.
-/
def structured_arrow.mk_hom {F : C ⥤ D} {X : D} {Y : C} (U : structured_arrow X F) (f : U.right ⟶ Y) :
U ⟶ structured_arrow.mk (U.hom ≫ F.map f) := { right := f }


section sheaf
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.sieve
noncomputable theory
/-
Suppose there is a compatible family `x` of elements on `U`, we ought to glue them together
to form a unique section on `S`. We will achieve this by restricting `x` onto objects of the form
`F(Y)` with `Y : C`, and glueing them via the sheaf property.
The uniqueness also follows from the uniqueness provided by the sheaf property.
-/
variables {X : A} {U : D} {S : sieve U} (hS : S ∈ K U)
variable (x : S.arrows.family_of_elements ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X)))
variable (hx : x.compatible)

/-- An explicit definition for the counit of the adjunction `F ⋙ _ ⊣ Ran F` -/
def Ran_counit : F.op ⋙ (Ran F.op).obj ℱ.val ⟶ ℱ.val := {
  app := λ U, limit.π _ (structured_arrow.mk (𝟙 _)),
  naturality' := λ X Y f, by {
    erw limit.pre_π,
    symmetry,
    convert limit.w
      (Ran.diagram F.op ℱ.val (F.op.obj X))
      (structured_arrow.mk_hom (structured_arrow.mk (𝟙 (F.op.obj X))) f),
    simp,
  }
}

private def hom_sh (X : A) :=
  whisker_right (Ran_counit F ℱ : _ ⟶ _) (coyoneda.obj (op X))


/-- Probably not very useful... -/
lemma is_amalg_iff_on_cover (ℱ : Cᵒᵖ ⥤ A)
  {x : S.arrows.family_of_elements ((Ran F.op).obj ℱ ⋙ coyoneda.obj (op X))} (hx : x.compatible)
  (t) : x.is_amalgamation t ↔ ∀ (Y : structured_arrow (op U) F.op) (hY : S Y.hom.unop),
    (((Ran F.op).obj ℱ ⋙ coyoneda.obj (op X)).map Y.hom t) = x Y.hom.unop hY :=
begin
  split,
  {
    intros hx Y hY,
    rw ← hx _ hY,
    simp,
    congr,
    },
  { intros H B fB hB,
    ext Y,
    simp only [category_theory.functor.comp_map, coyoneda_obj_map, category.assoc, Ran_obj_map],
    erw limit.pre_π,
    have eq := H (structured_arrow.mk (fB.op ≫ Y.hom)) (by simpa using S.downward_closed hB Y.hom.unop),
    simp only [quiver.hom.unop_op, functor.comp_map, coyoneda_obj_map, unop_comp, op_id_unop,
      structured_arrow.mk_hom_eq_self, category.assoc, Ran_obj_map, types_id_apply] at eq,
    have := hx (Y.hom.unop) (𝟙 _) hB (by simpa using S.downward_closed hB Y.hom.unop) (by simp),

    erw category_theory.functor.map_id at this,
    erw ← eq at this,
    simp only [category_theory.functor.comp_map, coyoneda_obj_map, Ran_obj_map,
      quiver.hom.op_unop, types_id_apply] at this,
    have := congr_arg (λ f, f ≫ limit.π _ (structured_arrow.mk (𝟙 _))) this,
    simp only [category_theory.category.assoc] at this,
    symmetry,
    erw limit.pre_π at this,
    erw limit.pre_π at this,
    convert this using 3,
    { cases Y, dsimp only [structured_arrow.map, comma.map_left],
      congr, { cases Y_left, refl }, {simp, erw category.comp_id, } },
    { cases Y, cases Y_left, dsimp only [structured_arrow.map, comma.map_left],
      congr' 1,
      simp only [functor.const.map_app, nat_trans.comp_app, category.assoc, functor.map_comp],
      erw category.comp_id, } }
end

/-
This is equivalent to the definition found in https://stacks.math.columbia.edu/tag/00XI
via `category_theory.grothendieck_topology.superset_covering`.
-/
structure precontinuous (J : grothendieck_topology C) (K : grothendieck_topology D) (F : C ⥤ D) :=
(cover_lift : ∀ {U : C} {S : sieve (F.obj U)} (hS : S ∈ K (F.obj U)), S.functor_pullback F ∈ J U)

variables (HF : precontinuous J K F)


variables {F} {x}
include HF hS hx

/-- Given a `F(Y) ⟶ U`, we can find a unique section on `ℱ(Y)` that agrees with `x` in `Y`. -/
private def get_section (Y : structured_arrow (op U) F.op) :
 ∃! (t : (ℱ.val ⋙ coyoneda.obj (op X)).obj (op (unop Y.right))),
  presieve.family_of_elements.is_amalgamation
    (((x.pullback Y.3.unop).functor_pullback F).comp_presheaf_map (hom_sh F ℱ X)) t :=
begin
  have S' := (K.pullback_stable Y.hom.unop hS),
  let s' := ((x.pullback Y.3.unop).functor_pullback F).comp_presheaf_map (hom_sh F ℱ X : _ ⟶ _),
  have hs' := ((hx.pullback Y.3.unop).functor_pullback F).comp_presheaf_map (hom_sh F ℱ X : _ ⟶ _),
  have prop := ℱ.2 X _ (HF.cover_lift S') s' hs',
  exact prop
end

/-- get section recovers the restriction when `F(Y) ⟶ U` is in the sieve. -/
private lemma get_section_of_cover (Y : structured_arrow (op U) F.op) (hY : S Y.hom.unop) :
  classical.some (get_section ℱ hS hx HF Y) = (hom_sh F ℱ X).app Y.right (x Y.hom.unop hY) :=
begin
  symmetry, apply lem2,
  intros B fB hB,
  unfold family_of_elements.comp_presheaf_map family_of_elements.functor_pullback family_of_elements.pullback,
  symmetry,
  convert congr_fun ((hom_sh F ℱ X).naturality fB.op) (x Y.hom.unop hY),
  convert hx (𝟙 _) (F.map fB) hB hY (by tidy) using 2,
  simp,
end

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
private def glued_limit_cone : limits.cone ((structured_arrow.proj (op U) (F.op)) ⋙ ℱ.val) := by {
  let get_section := get_section ℱ hS hx HF,
  let F_iso : _ ⟶ ℱ.val ⋙ _ := hom_sh F ℱ X,
  exact {
    X := X,
    π := {
      app := λ Y, classical.some (get_section Y),
      naturality' := λ Y Z f, by {
    simp only [functor.comp_map,
 structured_arrow.proj_map,
 functor.const.obj_map],
    change 𝟙 X ≫ classical.some (get_section Z) = classical.some (get_section Y) ≫ ℱ.val.map f.right,
    erw category.id_comp,
    apply lem1 (λ x, classical.some (get_section Z) = x ≫ ℱ.val.map f.right),
    rintros t₁ ⟨Pt₁, _⟩,
    symmetry,
    apply lem2,
    intros W fw hw,
    have eq := congr_arg quiver.hom.unop f.w,
    erw category.id_comp at eq,
    have := Pt₁ (fw ≫ f.right.unop) (by {
      change S (F.map _ ≫ Y.hom.unop),
      rw eq at hw,
      simpa using hw,
    }),
    convert this using 1,
    { tidy },
    {
      dsimp only [comp_presheaf_map,
        family_of_elements.functor_pullback, family_of_elements.pullback],
      congr' 2,
      rw eq,
      simp
    }
      }
    }
  }
}

/-- The obtained section is indeed the amalgamation. -/
private lemma glued_section_is_amalgamation :
  x.is_amalgamation (limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone ℱ hS hx HF)) :=
begin
  rw is_amalg_iff_on_cover F ℱ.val hx,
  intros Y hY,
  ext Z,
  simp, erw limit.pre_π, erw limit.lift_π,
  dsimp[glued_limit_cone],
  rw get_section_of_cover,
  swap, exact S.downward_closed hY Z.hom.unop,
  dsimp[structured_arrow.map, hom_sh, Ran.adjunction], delta Ran.diagram,
  have := hx Z.hom.unop (𝟙 _) hY (S.downward_closed hY Z.hom.unop) (by tidy),
  symmetry,
  have := congr_arg (λ f, f ≫ limit.π (structured_arrow.proj (op (F.obj (unop Z.right))) F.op ⋙ ℱ.val)
    (structured_arrow.mk (𝟙 _))) this,
  simp only [category_theory.functor.comp_map, coyoneda_obj_map, category.assoc, Ran_obj_map,
    quiver.hom.op_unop, op_id_unop] at this,
  erw limit.pre_π at this,
  erw limit.pre_π at this,
  unfold Ran_counit,
  convert this using 2,
  { cases Z, cases Z_left, congr, erw category.comp_id, refl },
  { dsimp only, congr, erw category.comp_id, refl }
end


/-- The amalgamation is indeed unique. -/
lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) :
  y = limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone ℱ hS hx HF) :=
begin
  unfold limit.lift,
  refine limits.is_limit.uniq _ (glued_limit_cone ℱ hS hx HF) y _,
  intro W,
  apply lem2,
  intros B fB hB,
  simp,
  dsimp [comp_presheaf_map],
  conv_rhs{ change (hom_sh F ℱ X).app (op B) (x (F.map fB ≫ W.hom.unop) _) },
  rw ←  hy (F.map fB ≫ W.hom.unop) hB,
  dsimp only [hom_sh],
  simp only [functor.comp_map, op_comp, coyoneda_obj_map, category.assoc, Ran_obj_map,
    quiver.hom.op_unop, whisker_right_app,
    iso_whisker_right_hom, nat_iso.of_components.hom_app, coyoneda_obj_map,
    category.assoc, as_iso_hom],
  congr' 1,
  convert limit.w (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (structured_arrow.mk_hom W fB.op),
  unfold Ran_counit,
  erw limit.pre_π,
  congr,
  simp only [quiver.hom.unop_op, structured_arrow.map_comp, functor.op_map,
 category_theory.structured_arrow.map_mk],
  erw category.comp_id,
end

omit hS hx
/--
If `F` is precontinuous, then `Ran F.op` pushes sheaves to sheaves.
Basically https://stacks.math.columbia.edu/tag/00XK but without the condition that C or D
has pullbacks
-/
lemma lem (HF : precontinuous J K F) (ℱ : Sheaf J A) :
  presheaf.is_sheaf K ((Ran F.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap, exact limits.limit.lift _ (glued_limit_cone ℱ hS hx HF),
  split,
  {
    apply glued_section_is_amalgamation,
  },
  {
    apply glued_section_is_unique
  }
end

end sheaf
