/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.group_power.basic -- Needed for squares
import algebra.order.group
import tactic.nth_rewrite

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
* `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[lattice α]`
* `[comm_group α]`
* `[covariant_class α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/

universe u

variables {α : Type u} [lattice_comm_group α]

-- Special case of Bourbaki A.VI.9 (2)
-- -(a ⊔ b)=(-a) ⊓ (-b)
@[to_additive]
lemma inv_sup_eq_inv_inf_inv [covariant_class α α (*) (≤)] (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ :=
begin
  apply le_antisymm,
  { refine le_inf _ _,
    { rw inv_le_inv_iff, exact le_sup_left, },
    { rw inv_le_inv_iff, exact le_sup_right, } },
  { rw [← inv_le_inv_iff, inv_inv],
    refine sup_le _ _,
    { rw ← inv_le_inv_iff, simp, },
    { rw ← inv_le_inv_iff, simp, } }
end

-- -(a ⊓ b) = -a ⊔ -b
@[to_additive]
lemma inv_inf_eq_sup_inv [covariant_class α α (*) (≤)] (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ :=
by rw [← inv_inv (a⁻¹ ⊔ b⁻¹), inv_sup_eq_inv_inf_inv a⁻¹ b⁻¹, inv_inv, inv_inv]

-- Bourbaki A.VI.10 Prop 7
-- a ⊓ b + (a ⊔ b) = a + b
@[to_additive]
lemma inf_mul_sup (a b : α) : a ⊓ b * (a ⊔ b) = a * b :=
calc a ⊓ b * (a ⊔ b) = a ⊓ b * ((a * b) * (b⁻¹ ⊔ a⁻¹)) :
  by { rw ← mul_sup_mul_left b⁻¹ a⁻¹ (a * b), simp, }
... = a ⊓ b * ((a * b) * (a ⊓ b)⁻¹) : by rw [inv_inf_eq_sup_inv, sup_comm]
... = a * b                       : by rw [mul_comm, inv_mul_cancel_right]

namespace lattice_ordered_comm_group

-- a⁻ = -(a ⊓ 0)
@[to_additive]
lemma neg_eq_inv_inf_one [covariant_class α α (*) (≤)] (a : α) : a⁻ = (a ⊓ 1)⁻¹ :=
by rw [neg_part_eq_inv_sup_one, ← inv_inj, inv_sup_eq_inv_inf_inv, inv_inv, inv_inv, one_inv]

@[to_additive]
lemma neg_eq_one_iff [covariant_class α α has_mul.mul has_le.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a :=
begin
  rw le_antisymm_iff,
  simp only [one_le_neg_part, and_true],
  rw [neg_part_le_one_iff, inv_le_one'],
end

-- a⁺ = (-a)⁻
@[to_additive]
lemma pos_eq_neg_inv (a : α) : a⁺ = (a⁻¹)⁻ := by simp [neg_part_eq_pos_part_inv]

-- We use this in Bourbaki A.VI.12  Prop 9 a)
-- c + (a ⊓ b) = (c + a) ⊓ (c + b)
@[to_additive]
lemma mul_inf_eq_mul_inf_mul
  (a b c : α) : c * (a ⊓ b) = (c * a) ⊓ (c * b) :=
begin
  refine le_antisymm (by simp) _,
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul, le_inf_iff],
  simp,
end

-- Bourbaki A.VI.12  Prop 9 a)
-- a = a⁺ - a⁻
@[to_additive, simp]
lemma pos_div_neg (a : α) : a⁺ / a⁻ = a :=
begin
  symmetry,
  rw div_eq_mul_inv,
  apply eq_mul_inv_of_mul_eq,
  rw [neg_part_eq_inv_sup_one, ← mul_sup_mul_left, mul_one, mul_right_inv, sup_comm,
    pos_part_eq_sup_one],
end

-- Bourbaki A.VI.12  Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
lemma pos_inf_neg_eq_one [covariant_class α α (*) (≤)] (a : α) : a⁺ ⊓ a⁻ = 1 :=
by rw [←mul_right_inj (a⁻)⁻¹, mul_inf_eq_mul_inf_mul, mul_one, mul_left_inv, mul_comm,
  ← div_eq_mul_inv, pos_div_neg, neg_eq_inv_inf_one, inv_inv]

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊔b = b + (a - b)⁺
@[to_additive]
lemma sup_eq_mul_pos_div [covariant_class α α (*) (≤)] (a b : α) : a ⊔ b = b * (a / b)⁺ :=
calc a ⊔ b = (b * (a / b)) ⊔ (b * 1) : by rw [mul_one b, div_eq_mul_inv, mul_comm a,
  mul_inv_cancel_left]
... = b * ((a / b) ⊔ 1) : by rw mul_sup_mul_left (a / b) 1 b

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
lemma inf_eq_div_pos_div [covariant_class α α (*) (≤)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
calc a ⊓ b = (a * 1) ⊓ (a * (b / a)) : by { rw [mul_one a, div_eq_mul_inv, mul_comm b,
  mul_inv_cancel_left], }
... = a * (1 ⊓ (b / a))     : by rw ← mul_inf_eq_mul_inf_mul 1 (b / a) a
... = a * ((b / a) ⊓ 1)     : by rw inf_comm
... = a * ((a / b)⁻¹ ⊓ 1)   : by { rw div_eq_mul_inv, nth_rewrite 0 ← inv_inv b,
  rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv], }
... = a * ((a / b)⁻¹ ⊓ 1⁻¹) : by rw one_inv
... = a / ((a / b) ⊔ 1)     : by rw [← inv_sup_eq_inv_inf_inv, ← div_eq_mul_inv]

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive le_iff_pos_le_neg_ge]
lemma m_le_iff_pos_le_neg_ge [covariant_class α α (*) (≤)] (a b : α) : a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ :=
begin
  split; intro h,
  { split,
    { exact sup_le (h.trans (m_le_pos_part b)) (one_le_pos_part b), },
    { rw ← inv_le_inv_iff at h,
      exact sup_le (h.trans (inv_le_neg_part a)) (one_le_neg_part a), } },
  { rw [← pos_div_neg a, ← pos_div_neg b],
    exact div_le_div'' h.1 h.2, }
end

@[to_additive neg_abs]
lemma m_neg_abs [covariant_class α α (*) (≤)] (a : α) : |a|⁻ = 1 :=
begin
  refine le_antisymm _ _,
  { rw ← pos_inf_neg_eq_one a,
    apply le_inf,
    { rw pos_eq_neg_inv,
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_mabs_self a)).right, },
    { exact and.right (iff.elim_left (m_le_iff_pos_le_neg_ge _ _) (le_mabs_self a)), } },
  { exact one_le_neg_part _, }
end

@[to_additive pos_abs]
lemma m_pos_abs [covariant_class α α (*) (≤)] (a : α) : |a|⁺ = |a| :=
begin
  nth_rewrite 1 ← pos_div_neg (|a|),
  rw div_eq_mul_inv,
  symmetry,
  rw [mul_right_eq_self, inv_eq_one],
  exact m_neg_abs a,
end

@[to_additive abs_nonneg]
lemma one_le_abs [covariant_class α α (*) (≤)] (a : α) : 1 ≤ |a| :=
by { rw ← m_pos_abs, exact one_le_pos_part _, }

-- The proof from Bourbaki A.VI.12 Prop 9 d)
-- |a| = a⁺ - a⁻
@[to_additive]
lemma pos_mul_neg [covariant_class α α (*) (≤)] (a : α) : |a| = a⁺ * a⁻ :=
begin
  refine le_antisymm _ _,
  { refine sup_le _ _,
    { nth_rewrite 0 ← mul_one a,
      exact mul_le_mul' (m_le_pos_part a) (one_le_neg_part a) },
    { nth_rewrite 0 ← one_mul (a⁻¹),
      exact mul_le_mul' (one_le_pos_part a) (inv_le_neg_part a) } },
  { rw [← inf_mul_sup, pos_inf_neg_eq_one, one_mul, ← m_pos_abs a],
    apply sup_le,
    { exact ((m_le_iff_pos_le_neg_ge _ _).mp (le_mabs_self a)).left, },
    { rw neg_part_eq_pos_part_inv,
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_mabs_self a)).left, }, }
end

-- a ⊔ b - (a ⊓ b) = |b - a|
@[to_additive]
lemma sup_div_inf_eq_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊔ b) / (a ⊓ b) = |b / a| :=
begin
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv],
  nth_rewrite 1 div_eq_mul_inv,
  rw [mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b)],
  nth_rewrite 1 div_eq_mul_inv,
  rw [mul_inv_rev, ← div_eq_mul_inv, inv_inv, ← pos_mul_neg],
end

-- 2•(a ⊔ b) = a + b + |b - a|
@[to_additive two_sup_eq_add_add_abs_sub]
lemma sup_sq_eq_mul_mul_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊔ b)^2 = a * b * |b / a| :=
by rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, ← mul_assoc, mul_comm,
    mul_assoc, ← pow_two, inv_mul_cancel_left]

-- 2•(a ⊓ b) = a + b - |b - a|
@[to_additive two_inf_eq_add_sub_abs_sub]
lemma inf_sq_eq_mul_div_abs_div [covariant_class α α (*) (≤)] (a b : α) :
  (a ⊓ b)^2 = a * b / |b / a| :=
by rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv,
    mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]

/--
Every lattice ordered commutative group is a distributive lattice
-/
@[to_additive
  "Every lattice ordered commutative additive group is a distributive lattice"
]
def lattice_ordered_comm_group_to_distrib_lattice (α : Type u)
  [s: lattice_comm_group α] : distrib_lattice α :=
{ le_sup_inf :=
  begin
    intros,
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z),
      ← inv_mul_le_iff_le_mul, le_inf_iff],
    split,
    { rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y],
      apply mul_le_mul',
      { apply inf_le_inf_left, apply inf_le_left, },
      { apply inf_le_left, } },
    { rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z],
      apply mul_le_mul',
      { apply inf_le_inf_left, apply inf_le_right, },
      { apply inf_le_right, }, }
  end,
  ..s }

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
-- |a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|
@[to_additive]
theorem abs_div_sup_mul_abs_div_inf [covariant_class α α (*) (≤)] (a b c : α) :
  |(a ⊔ c) / (b ⊔ c)| * |(a ⊓ c) / (b ⊓ c)| = |a / b| :=
begin
  letI : distrib_lattice α := lattice_ordered_comm_group_to_distrib_lattice α,
  calc |(a ⊔ c) / (b ⊔ c)| * |a ⊓ c / (b ⊓ c)| =
    ((b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c))) * |a ⊓ c / (b ⊓ c)| : by rw sup_div_inf_eq_abs_div
  ... = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * (((b ⊓ c) ⊔ (a ⊓ c)) / ((b ⊓ c) ⊓ (a ⊓ c))) :
    by rw sup_div_inf_eq_abs_div (b ⊓ c) (a ⊓ c)
  ... = (b ⊔ a ⊔ c) / ((b ⊓ a) ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) : by
  { rw [← sup_inf_right, ← inf_sup_right, sup_assoc],
    nth_rewrite 1 sup_comm,
    rw [sup_right_idem, sup_assoc, inf_assoc],
    nth_rewrite 3 inf_comm,
    rw [inf_right_idem, inf_assoc], }
  ... = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) /(((b ⊓ a) ⊔ c) * (b ⊓ a ⊓ c)) : by rw div_mul_comm
  ... = (b ⊔ a) * c / (b ⊓ a * c) :
    by rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
  ... = (b ⊔ a) / (b ⊓ a) : by rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
      ← div_eq_mul_inv]
  ... = |a / b|           : by rw sup_div_inf_eq_abs_div
end

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its positive component `a⁺`.
-/
@[to_additive] -- pos_of_nonneg
lemma pos_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a :=
by { rw pos_part_eq_sup_one, exact sup_of_le_left h, }

-- 0 ≤ a implies a⁺ = a
@[to_additive] -- pos_of_nonpos
lemma pos_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
pos_part_eq_one_iff.mpr h

@[to_additive neg_of_inv_nonneg]
lemma neg_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ :=
by { rw neg_part_eq_pos_part_inv, exact pos_of_one_le _ h, }

@[to_additive] -- neg_of_neg_nonpos
lemma neg_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
neg_part_eq_one_iff'.mpr h

@[to_additive] -- neg_of_nonpos
lemma neg_of_le_one [covariant_class α α (*) (≤)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ :=
by { refine neg_of_one_le_inv _ _, rw one_le_inv', exact h, }

@[to_additive] -- neg_of_nonneg'
lemma neg_of_one_le [covariant_class α α (*) (≤)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
neg_eq_one_iff.mpr h

-- 0 ≤ a implies |a| = a
@[to_additive abs_of_nonneg]
lemma mabs_of_one_le [covariant_class α α (*) (≤)] (a : α) (h : 1 ≤ a) : |a| = a :=
begin
  unfold has_abs.abs,
  rw [sup_eq_mul_pos_div, div_eq_mul_inv, inv_inv, ← pow_two, inv_mul_eq_iff_eq_mul,
    ← pow_two, pos_of_one_le],
  rw pow_two,
  apply one_le_mul h h,
end

/--
The unary operation of taking the absolute value is idempotent.
-/
@[to_additive abs_abs, simp]
lemma m_abs_abs [covariant_class α α (*) (≤)] (a : α) : | |a| | = |a| :=
mabs_of_one_le _ (one_le_abs _)

@[to_additive abs_sup_sub_sup_le_abs]
lemma mabs_sup_div_sup_le_mabs [covariant_class α α (*) (≤)] (a b c : α) :
  |(a ⊔ c) / (b ⊔ c)| ≤ |a / b| :=
begin
  apply le_of_mul_le_of_one_le_left,
  { rw abs_div_sup_mul_abs_div_inf, },
  { exact one_le_abs _, },
end

@[to_additive abs_inf_sub_inf_le_abs]
lemma mabs_inf_div_inf_le_mabs [covariant_class α α (*) (≤)] (a b c : α) :
  |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
begin
  apply le_of_mul_le_of_one_le_right,
  { rw abs_div_sup_mul_abs_div_inf, },
  { exact one_le_abs _, },
end

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
-- |(a ⊔ c) - (b ⊔ c)| ⊔ |(a ⊓ c) - (b ⊓ c)| ≤ |a - b|
@[to_additive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [covariant_class α α (*) (≤)] (a b c : α) :
|(a ⊔ c) / (b ⊔ c)| ⊔ |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/--
The absolute value satisfies the triangle inequality.
-/
@[to_additive abs_add_le]
lemma mabs_mul_le [covariant_class α α (*) (≤)] (a b : α) : |a * b| ≤ |a| * |b| :=
begin
  apply sup_le,
  { exact mul_le_mul' (le_mabs_self a) (le_mabs_self b), },
  { rw mul_inv,
    exact mul_le_mul' (inv_le_mabs_self _) (inv_le_mabs_self _), }
end

-- |a - b| = |b - a|
@[to_additive]
lemma abs_inv_comm (a b : α) : |a/b| = |b/a| :=
begin
  unfold has_abs.abs,
  rw [inv_div' a b, ← inv_inv (a / b), inv_div', sup_comm],
end

-- | |a| - |b| | ≤ |a - b|
@[to_additive]
lemma abs_abs_div_abs_le [covariant_class α α (*) (≤)] (a b : α) : | |a| / |b| | ≤ |a / b| :=
begin
  unfold has_abs.abs,
  rw sup_le_iff,
  split,
  { apply div_le_iff_le_mul.2,
    convert mabs_mul_le (a/b) b,
    { rw div_mul_cancel', },
    { rw div_mul_cancel', },
    { exact covariant_swap_mul_le_of_covariant_mul_le α, } },
  { rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, ← mabs_eq_sup_inv (a / b),
      abs_inv_comm],
    convert  mabs_mul_le (b/a) a,
    { rw div_mul_cancel', },
    {rw div_mul_cancel', } },
end

end lattice_ordered_comm_group
