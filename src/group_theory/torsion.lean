/-
Copyright (c) 2021 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/

import group_theory.quotient_group

/-!
# Torsion groups

This file defines torsion groups, or more generally torsion monoids. A torsion group `G` is one
where all elements have finite order.

## Main definitions

* `monoid.is_torsion` is a predicate asserting a monoid `G` is a torsion monoid, i.e. that for
  each `g : G` there is some positive `n` such that `g ^ n = 1`. Torsion groups are also known as
  periodic groups.
* `add_monoid.is_torsion` the additive version of `monoid.is_torsion`.

## Main results

-/

universe u

variable {G : Type u}

open_locale classical

namespace monoid

variables (G) [monoid G]

/--A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive "A predicate on an additive monoid saying that for each `g` there is a positive
  integer `n` such that `n • g = 0` for all `g`."]
def is_torsion := ∀ g : G, ∃ n, 0 < n ∧ g ^ n = 1

end monoid

open monoid (is_torsion)

/--Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
lemma subgroup.is_torsion [group G] {tG : is_torsion G} (H : subgroup G) : is_torsion H := begin
  intro g,
  obtain ⟨n, ⟨npos, hn⟩⟩ := tG g,
  refine ⟨n, npos, subtype.coe_injective _⟩,
  rw [subgroup.coe_pow, subgroup.coe_one, hn],
end

/--Quotient groups of torsion groups are torsion groups. -/
lemma is_torsion.quotient_group [group G] {N : subgroup G} [nN : N.normal] (tG : is_torsion G) : is_torsion (G ⧸ N) := begin
  intro g,
  refine quotient.induction_on' g _,
  intro a,
  obtain ⟨n, ⟨npos, hn⟩⟩ := tG a,
  exact ⟨n, npos, (quotient_group.con N).eq.mpr $ hn ▸ (quotient_group.con N).eq.mp rfl⟩,
end
