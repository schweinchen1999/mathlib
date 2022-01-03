/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import topology.order.lattice
import analysis.normed.group.basic
import algebra.lattice_ordered_group

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

local notation `|`a`|` := abs a

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `∥a∥ ≤ ∥b∥`. Then `α` is
said to be a normed lattice ordered group.
-/
class normed_lattice_add_comm_group (α : Type*)
  extends lattice_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(solid : ∀ a b : α, |a| ≤ |b| → ∥a∥ ≤ ∥b∥)

lemma solid {α : Type*} [normed_lattice_add_comm_group α] {a b : α} (h : |a| ≤ |b|) : ∥a∥ ≤ ∥b∥ :=
normed_lattice_add_comm_group.solid a b h

@[priority 100] -- see Note [lower instance priority]
instance to_normed_group (α : Type*) [h : normed_lattice_add_comm_group α] : normed_group α :=
{ dist_eq := h.dist_eq, }

noncomputable instance : lattice_add_comm_group ℝ :=
{ add_le_add_left := λ a b, add_le_add_left,
  ..real.lattice,
  ..real.add_comm_group }

noncomputable instance : normed_lattice_add_comm_group ℝ :=
{ dist_eq := λ x y, rfl,
  solid := λ _ _, id, }

/--
A normed lattice ordered group is an ordered additive commutative group
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_to_ordered_add_comm_group {α : Type*}
  [h : normed_lattice_add_comm_group α] : ordered_add_comm_group α := { ..h }

/--
Let `α` be a normed group with a partial order. Then the order dual is also a normed group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} : Π [normed_group α], normed_group (order_dual α) := id

variables {α : Type*} [normed_lattice_add_comm_group α]
open lattice_ordered_group

lemma dual_solid (a b : α) (h: b⊓-b ≤ a⊓-a) : ∥a∥ ≤ ∥b∥ :=
begin
  have h₂ := _root_.neg_le_neg h,
  rw [neg_inf_eq_sup_neg, neg_inf_eq_sup_neg, neg_neg, neg_neg, @sup_comm _ _ _ a,
    @sup_comm _ _ _ b] at h₂,
  exact solid h₂,
end

/--
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} [h : normed_lattice_add_comm_group α] :
  normed_lattice_add_comm_group (order_dual α) :=
{ dist_eq := h.dist_eq,
  solid := λ a b h₂, dual_solid _ _ h₂,
  ..order_dual.lattice_add_comm_group α }

lemma norm_abs_eq_norm (a : α) : ∥|a|∥ = ∥a∥ :=
(solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

lemma norm_inf_sub_inf_le_add_norm (a b c d : α) : ∥a ⊓ b - c ⊓ d∥ ≤ ∥a - c∥ + ∥b - d∥ :=
begin
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)],
  refine le_trans (solid _) (norm_add_le (|a - c|) (|b - d|)),
  rw abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d))),
  calc |a ⊓ b - c ⊓ d| =
    |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| : by rw sub_add_sub_cancel
  ... ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| : abs_add_le _ _
  ... ≤ |a -c| + |b - d| : by
    { apply add_le_add,
      { exact abs_inf_sub_inf_le_abs _ _ _, },
      { rw [@inf_comm _ _ c, @inf_comm _ _ c],
        exact abs_inf_sub_inf_le_abs _ _ _, } },
end

lemma norm_sup_sub_sup_le_add_norm (a b c d : α) : ∥a ⊔ b - (c ⊔ d)∥ ≤ ∥a - c∥ + ∥b - d∥ :=
begin
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)],
  refine le_trans (solid _) (norm_add_le (|a - c|) (|b - d|)),
  rw abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d))),
  calc |a ⊔ b - (c ⊔ d)| =
    |a ⊔ b - (c ⊔ b) + (c ⊔ b - (c ⊔ d))| : by rw sub_add_sub_cancel
  ... ≤ |a ⊔ b - (c ⊔ b)| + |c ⊔ b - (c ⊔ d)| : abs_add_le _ _
  ... ≤ |a -c| + |b - d| : by
    { apply add_le_add,
      { exact abs_sup_sub_sup_le_abs _ _ _, },
      { rw [@sup_comm _ _ c, @sup_comm _ _ c],
        exact abs_sup_sub_sup_le_abs _ _ _, } },
end

/--
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_has_continuous_inf : has_continuous_inf α :=
begin
  refine ⟨continuous_iff_continuous_at.2 $ λ q, tendsto_iff_norm_tendsto_zero.2 $ _⟩,
  have : ∀ p : α × α, ∥p.1 ⊓ p.2 - q.1 ⊓ q.2∥ ≤ ∥p.1 - q.1∥ + ∥p.2 - q.2∥,
    from λ _, norm_inf_sub_inf_le_add_norm _ _ _ _,
  refine squeeze_zero (λ e, norm_nonneg _) this _,
  convert (((continuous_fst.tendsto q).sub tendsto_const_nhds).norm).add
        (((continuous_snd.tendsto q).sub tendsto_const_nhds).norm),
  simp,
end

/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_topological_lattice : topological_lattice α :=
topological_lattice.mk

lemma norm_abs_sub_abs (a b : α) :
  ∥ |a| - |b| ∥ ≤ ∥a-b∥ :=
solid (abs_abs_sub_abs_le _ _)
