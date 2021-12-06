/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import order.lattice
import algebra.abs
import algebra.group.basic

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

@[simp, to_additive]
lemma pos_part_one : (1 : α)⁺ = 1 := sup_idem

@[to_additive pos_part_nonneg]
lemma one_le_pos_part (a : α) : 1 ≤ a⁺ := le_sup_right

@[to_additive] -- pos_part_of_nonneg
lemma pos_part_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a :=
by { rw pos_part_eq_sup_one, exact sup_of_le_left h, }

@[to_additive] -- pos_part_nonpos_iff
lemma pos_part_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 :=
by { rw [pos_part_eq_sup_one, sup_le_iff], simp, }

@[to_additive]
lemma pos_part_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 :=
by { rw le_antisymm_iff, simp only [one_le_pos_part, and_true], exact pos_part_le_one_iff, }

@[to_additive] -- pos_part_of_nonpos
lemma pos_part_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
pos_part_eq_one_iff.mpr h

@[to_additive le_pos_part]
lemma m_le_pos_part (a : α) : a ≤ a⁺ := le_sup_left

end pos_part

section has_inv

variables [has_inv α] {a b: α}

@[to_additive abs_le']
lemma mabs_le' : |a| ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff

@[to_additive le_abs_self]
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

@[to_additive] -- neg_nonpos_iff
lemma neg_part_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 :=
by { rw [neg_part_eq_inv_sup_one, sup_le_iff], simp, }

@[to_additive]
lemma neg_part_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 :=
by { rw le_antisymm_iff, simp only [one_le_neg_part, and_true], rw neg_part_le_one_iff, }

@[to_additive]
lemma inv_le_neg_part (a : α) : a⁻¹ ≤ a⁻ := le_sup_left

@[to_additive]
lemma neg_part_eq_pos_part_inv (a : α) : a⁻ = (a⁻¹)⁺ := rfl

@[to_additive neg_part_of_neg_nonneg]
lemma neg_part_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ :=
by { rw neg_part_eq_pos_part_inv, exact pos_part_of_one_le _ h, }

@[to_additive] -- neg_part_of_neg_nonpos
lemma neg_part_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
neg_part_eq_one_iff'.mpr h

end neg_part

end has_inv

section group

variables [group α]

@[simp, to_additive]
lemma abs_one : |(1 : α)| = 1 :=
by rw [abs_eq_sup_inv, one_inv, sup_idem]

@[simp, to_additive]
lemma neg_part_one : (1 : α)⁻ = 1 :=
by rw [neg_part_eq_inv_sup_one, one_inv, sup_idem]

@[simp, to_additive] lemma abs_inv (a : α) : |a⁻¹| = |a| :=
by rw [abs_eq_sup_inv, sup_comm, inv_inv, abs_eq_sup_inv]

@[to_additive abs_sub_comm]
lemma abs_inv_comm (a b : α) : |a / b| = |b / a| :=
calc  |a / b| = |(b / a)⁻¹| : congr_arg _ (inv_div' b a).symm
          ... = |b / a|      : abs_inv (b / a)

end group
