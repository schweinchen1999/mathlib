/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import order.lattice
import algebra.abs

variables {α : Type*} [lattice α]

/-- `abs a` is the absolute value of `a`. -/
@[to_additive, priority 100] -- see Note [lower instance priority]
instance has_inv_lattice_has_abs [has_inv α] : has_abs (α) := ⟨λ a, a ⊔ a⁻¹⟩

@[to_additive, priority 100] -- see Note [lower instance priority]
instance has_one_lattice_has_pos_part [has_one α] : has_pos_part (α) := ⟨λ a, a ⊔ 1⟩

@[to_additive, priority 100] -- see Note [lower instance priority]
instance has_one_lattice_has_neg_part [has_inv α] [has_one α] :
  has_neg_part (α) := ⟨λ a, a⁻¹ ⊔ 1⟩

@[to_additive]
lemma abs_eq_sup_inv [has_inv α] (a : α) : |a| = a ⊔ a⁻¹ := rfl

section pos_part

variables [has_one α]

@[to_additive]
lemma pos_part_eq_sup_one (a : α) : a⁺ = a ⊔ 1 := rfl

@[to_additive, simp]
lemma pos_part_one : (1 : α)⁺ = 1 := sup_idem

@[to_additive pos_part_nonneg]
lemma one_le_pos_part (a : α) : 1 ≤ a⁺ := le_sup_right

end pos_part


section has_inv

variables [has_inv α] {a b: α}

@[to_additive abs_le']
lemma mabs_le' : |a| ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff

@[to_additive la_abs_self]
lemma le_mabs_self (a : α) : a ≤ |a| := le_sup_left

@[to_additive neg_le_abs_self]
lemma inv_le_mabs_self (a : α) : a⁻¹ ≤ |a| := le_sup_right

@[to_additive abs_le_abs]
theorem mabs_le_mabs (h₀ : a ≤ b) (h₁ : a⁻¹ ≤ b) : |a| ≤ |b| :=
(mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)

section neg_part

variables [has_one α]

@[to_additive]
lemma neg_part_eq_inv_sup_one (a : α) : a⁻ = a⁻¹ ⊔ 1 := rfl

@[to_additive neg_part_nonneg]
lemma one_le_neg_part (a : α) : 1 ≤ a⁻ := le_sup_right

end neg_part

end has_inv
