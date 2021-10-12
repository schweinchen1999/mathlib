/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Witnesses of non uniformity
-/

open_locale classical

variables {α : Type*}

namespace simple_graph
variables (G : simple_graph α)

/-- Extracts a witness of the non-uniformity of `(U, V)`. Witnesses for `(U, V)` and `(V, U)` don't
necessarily match. Hence the motivation to define `witness`. -/
noncomputable def witness_aux (ε : ℝ) (U V : finset α) : finset α × finset α :=
dite (U = V ∨ G.is_uniform ε U V) (λ _, (U, V)) (λ h, begin
    unfold is_uniform at h,
    push_neg at h,
    exact (h.2.some, h.2.some_spec.2.some),
  end)

/-- Extracts a witness of the non-uniformity of `(U, V)`. It uses an arbitrary ordering of
`finset α` (`well_ordering_rel`) to ensure that the witnesses of `(U, V)` and `(V, U)` are related
(the existentials don't ensure we would take the same from `¬G.is_uniform ε U V` and
`¬G.is_uniform ε V U`). -/
noncomputable def witness (ε : ℝ) (U V : finset α) : finset α × finset α :=
ite (well_ordering_rel U V) (G.witness_aux ε U V) (G.witness_aux ε V U).swap

variables {ε : ℝ} {U V : finset α}

lemma left_witness_aux_subs : (G.witness_aux ε U V).1 ⊆ U :=
begin
  rw [witness_aux],
  split_ifs,
  { refl },
  unfold is_uniform at h,
  push_neg at h,
  apply h.2.some_spec.1,
end

lemma right_witness_aux_subs : (G.witness_aux ε U V).2 ⊆ V :=
begin
  rw [witness_aux],
  split_ifs,
  { refl },
  unfold is_uniform at h,
  push_neg at h,
  apply h.2.some_spec.2.some_spec.1,
end

lemma left_witness_subs : (G.witness ε U V).1 ⊆ U :=
begin
  dsimp [witness],
  split_ifs,
  { apply left_witness_aux_subs },
  { apply right_witness_aux_subs },
end

lemma witness_comm (ε : ℝ) (U V : finset α) :
  G.witness ε U V = (G.witness ε V U).swap :=
begin
  unfold witness,
  obtain h | rfl | h := trichotomous_of well_ordering_rel U V,
  { rw [if_pos h, if_neg (asymm h), prod.swap_swap] },
  { rw [witness_aux, if_neg, dif_pos (or.intro_left _ rfl), prod.swap],
    exact _root_.irrefl _ },
  rw [if_pos h, if_neg (asymm h)],
end

lemma right_witness_subs : (G.witness ε U V).2 ⊆ V :=
begin
  rw witness_comm,
  apply left_witness_subs
end

end simple_graph
