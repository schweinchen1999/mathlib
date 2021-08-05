/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import order.conditionally_complete_lattice
import algebra.pointwise

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bdd_above_neg`).
-/

open set

section inv_neg

variables {G : Type*} [group G] [preorder G] [covariant_class G G (*) (≤)]
  [covariant_class G G (function.swap (*)) (≤)] {s : set G} {a : G}

@[simp, to_additive]
lemma bdd_above_inv : bdd_above s⁻¹ ↔ bdd_below s := (order_iso.inv G).bdd_above_preimage

@[simp, to_additive]
lemma bdd_below_inv : bdd_below s⁻¹ ↔ bdd_above s := (order_iso.inv G).bdd_below_preimage

@[to_additive]
lemma bdd_above.inv (h : bdd_above s) : bdd_below s⁻¹ := bdd_below_inv.2 h

@[to_additive]
lemma bdd_below.inv (h : bdd_below s) : bdd_above s⁻¹ := bdd_above_inv.2 h

@[simp, to_additive]
lemma is_lub_inv : is_lub s⁻¹ a ↔ is_glb s a⁻¹ := (order_iso.inv G).is_lub_preimage

@[to_additive]
lemma is_lub_inv' : is_lub s⁻¹ a⁻¹ ↔ is_glb s a := (order_iso.inv G).is_lub_preimage'

@[to_additive]
lemma is_glb.inv (h : is_glb s a) : is_lub s⁻¹ a⁻¹ := is_lub_inv'.2 h

@[simp, to_additive]
lemma is_glb_inv : is_glb s⁻¹ a ↔ is_lub s a⁻¹ := (order_iso.inv G).is_glb_preimage

@[to_additive]
lemma is_glb_inv' : is_glb s⁻¹ a⁻¹ ↔ is_lub s a := (order_iso.inv G).is_glb_preimage'

@[to_additive]
lemma is_lub.inv (h : is_lub s a) : is_glb s⁻¹ a⁻¹ := is_glb_inv'.2 h

end inv_neg

section mul_add

variables {M : Type*} [has_mul M] [preorder M] [covariant_class M M (*) (≤)]
  [covariant_class M M (function.swap (*)) (≤)]

@[to_additive] lemma mul_mem_upper_bounds_mul {s t : set M} {a b : M} (ha : a ∈ upper_bounds s)
  (hb : b ∈ upper_bounds t) :
  a * b ∈ upper_bounds (s * t) :=
forall_image2_iff.2 $ λ x hx y hy, mul_le_mul' (ha hx) (hb hy)

@[to_additive] lemma subset_upper_bounds_mul (s t : set M) :
  upper_bounds s * upper_bounds t ⊆ upper_bounds (s * t) :=
image2_subset_iff.2 $ λ x hx y hy, mul_mem_upper_bounds_mul hx hy

@[to_additive] lemma mul_mem_lower_bounds_mul {s t : set M} {a b : M} (ha : a ∈ lower_bounds s)
  (hb : b ∈ lower_bounds t) : a * b ∈ lower_bounds (s * t) :=
@mul_mem_upper_bounds_mul (order_dual M) _ _ _ _ _ _ _ _ ha hb

@[to_additive] lemma subset_lower_bounds_mul (s t : set M) :
  lower_bounds s * lower_bounds t ⊆ lower_bounds (s * t) :=
@subset_upper_bounds_mul (order_dual M) _ _ _ _ _ _

@[to_additive] lemma bdd_above.mul {s t : set M} (hs : bdd_above s) (ht : bdd_above t) :
  bdd_above (s * t) :=
(hs.mul ht).mono (subset_upper_bounds_mul s t)

@[to_additive] lemma bdd_below.mul {s t : set M} (hs : bdd_below s) (ht : bdd_below t) :
  bdd_below (s * t) :=
(hs.mul ht).mono (subset_lower_bounds_mul s t)

end mul_add

section conditionally_complete_lattice

variables {G : Type*} [linear_ordered_add_comm_group G]
  {H : ∀ s : set G, s.nonempty → bdd_below s → ∃ a, is_glb s a}

@[simp] lemma cInf_neg [no_bot_order G] (s : set G) :
  @Inf G (@conditionally_complete_lattice.to_has_Inf G $
    conditionally_complete_lattice_of_exists_is_glb H 0) (-s) =
    -@Sup G (@conditionally_complete_lattice.to_has_Sup G $
    conditionally_complete_lattice_of_exists_is_glb H 0) s :=
begin
  letI : conditionally_complete_linear_order G :=
    { .. ‹linear_ordered_add_comm_group G›, .. lattice_of_linear_order,
      .. conditionally_complete_lattice_of_exists_is_glb H 0 },
  rcases s.eq_empty_or_nonempty with rfl|hne, { simp },
  by_cases hbdd : bdd_above s,
  { exact (is_lub_cSup hne hbdd).neg.cInf_eq hne.neg },
  { rw [cInf_of_not_bdd_below, cSup_of_not_bdd_above hbdd, neg_zero],
    exact mt bdd_below_neg.1 hbdd }
end

@[simp] lemma cSup_neg [no_bot_order G] (s : set G) :
  @Sup G (@conditionally_complete_lattice.to_has_Sup G $
    conditionally_complete_lattice_of_exists_is_glb H 0) (-s) =
    -@Inf G (@conditionally_complete_lattice.to_has_Inf G $
    conditionally_complete_lattice_of_exists_is_glb H 0) s :=
by rw [← neg_neg (Sup _), ← cInf_neg, set.neg_neg]

end conditionally_complete_lattice
