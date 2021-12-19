/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise

/-!
# Change of variables under diffeomorphisms

The goal of this file is to prove the change of variables formula for local diffeomorphisms in
higher dimension. For now, there is only the preliminary fact that, locally, the volume of balls
is rescaled according to the jacobian of the map, in
`tendsto_add_haar_preimage_closed_ball_div_add_haar_closed_ball`
-/

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open metric set asymptotics filter measure_theory measure_theory.measure finite_dimensional
open_locale pointwise topological_space ennreal

/-- Consider a map `f` with a derivative `f'` at a point `x`. For small enough `r`, the image under
`f` of the ball `closed_ball x r` resembles its under image `f'`. Here, we show that it is
eventually contained in the `ε r` thickening of `f' '' (closed_ball 0 r)`, for any fixed
positive `ε`. -/
lemma eventually_image_closed_ball_subset_image_closed_ball_fderiv
  {f : E → F} {x : E} {f' : E →L[ℝ] F} (hf : has_fderiv_at f f' x) {ε : ℝ} (εpos : 0 < ε) :
  ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
    f '' (closed_ball x r) ⊆ closed_ball (f x) (ε * r) + f' '' (closed_ball 0 r) :=
begin
  obtain ⟨R, Rpos, hR⟩ : ∃ (R : ℝ) (H : R > 0),
    closed_ball x R ⊆ {z : E | ∥f z - f x - f' (z - x)∥ ≤ ε * ∥z - x∥} :=
      nhds_basis_closed_ball.mem_iff.1 (is_o.def hf εpos),
  have : Ioo (0 : ℝ) R ∈ 𝓝[Ioi (0 : ℝ)] (0 : ℝ) := Ioo_mem_nhds_within_Ioi ⟨le_rfl, Rpos⟩,
  filter_upwards [this],
  rintros r hr y ⟨z, hz, rfl⟩,
  refine set.mem_add.2 ⟨f z - f' (z - x), f' (z - x), _, _, by abel⟩,
  { simp only [dist_eq_norm, mem_closed_ball],
    calc ∥f z - f' (z - x) - f x∥
    = ∥f z - f x - f' (z - x)∥ : by { congr' 1, abel }
    ... ≤ ε * ∥z - x∥ : hR (closed_ball_subset_closed_ball hr.2.le hz)
    ... ≤ ε * r : mul_le_mul_of_nonneg_left (mem_closed_ball_iff_norm.1 hz) εpos.le },
  { apply mem_image_of_mem,
    simpa only [mem_closed_ball_iff_norm, sub_zero] using hz }
end


/-- Consider a map `f` with a derivative `f'` at a point `x`. For small enough `r`, the image under
`f` of the ball `closed_ball x r` resembles its under image `f'`. Here, we show that its rescaling
by `r⁻¹` is eventually contained in the `ε` thickening of `f' '' (closed_ball 0 1)`, for any fixed
positive `ε`. This form is handy for measure computations as the set on the right hand side does
not depend on `r`. -/
lemma eventually_smul_image_closed_ball_subset_image_closed_ball_fderiv
  {f : E → F} {x : E} {f' : E →L[ℝ] F} (hf : has_fderiv_at f f' x) {ε : ℝ} (εpos : 0 < ε) :
  ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
    r⁻¹ • ({-f x} + f '' (closed_ball x r)) ⊆ closed_ball 0 ε + f' '' (closed_ball 0 1) :=
begin
  filter_upwards [eventually_image_closed_ball_subset_image_closed_ball_fderiv hf εpos,
    self_mem_nhds_within],
  assume r hr rpos,
  replace rpos : 0 < r := rpos,
  have A : r⁻¹ ≠ 0, by simp only [rpos.ne', inv_eq_zero, ne.def, not_false_iff],
  have B : r⁻¹ * (ε * r) = ε, by field_simp [rpos.ne'],
  calc r⁻¹ • ({-f x} + f '' closed_ball x r)
  ⊆ r⁻¹ • ({-f x} + (closed_ball (f x) (ε * r) + f' '' (closed_ball 0 r))) :
    smul_set_mono (add_subset_add subset.rfl hr)
  ... = closed_ball 0 ε + f' '' closed_ball 0 1 : begin
    rw [← add_assoc, singleton_add_closed_ball, add_left_neg, smul_add_set, ← f'.image_smul_set,
      smul_closed_ball' A, smul_closed_ball' A],
    simp only [real.norm_eq_abs, smul_zero, abs_of_nonneg (inv_nonneg.2 rpos.le),
      inv_mul_cancel rpos.ne', B],
  end
end


/-- Consider a map `f` with an invertible derivative `f'` at a point `x`. Then the preimage under
`f` of a small ball `closed_ball (f x) r` around `f x` resembles its preimage under `f'`.
Here we prove that the rescaling of the latter by a fixed factor `t < 1` is contained in the former,
for small enough `r`. -/
lemma eventually_preimage_fderiv_closed_ball_subset_preimage_closed_ball
  {f : E → F} {x : E} {f' : E ≃L[ℝ] F} (hf : has_fderiv_at f (f' : E →L[ℝ] F) x)
  {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
  ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
    {x} + f' ⁻¹' (closed_ball 0 (t * r)) ⊆ f ⁻¹' (closed_ball (f x) r) :=
begin
  let C : ℝ := max (∥↑(f'.symm)∥₊) 1,
  have Cpos : 0 < C := zero_lt_one.trans_le (le_max_right _ _),
  let ε : ℝ := (1 - t) / C,
  have εpos : 0 < ε := div_pos (by linarith [ht.2]) Cpos,
  obtain ⟨δ, δpos, hδ⟩ :
    ∃ (δ : ℝ) (H : 0 < δ), closed_ball 0 δ ⊆ {z : E | ∥f (x + z) - f x - f' z∥ ≤ ε * ∥z∥} :=
      nhds_basis_closed_ball.mem_iff.1 ((has_fderiv_at_iff_is_o_nhds_zero.1 hf).def εpos),
  have : Ioc (0 : ℝ) (δ / C) ∈ 𝓝[Ioi (0 : ℝ)] 0,
    by { apply Ioc_mem_nhds_within_Ioi, simp only [div_pos δpos Cpos, left_mem_Ico] },
  filter_upwards [this],
  rintros r ⟨rpos, rle⟩ y hy,
  let z := y - x,
  have B : ∥f' z∥ ≤ t * r, by simpa only [continuous_linear_equiv.map_add,
    continuous_linear_equiv.map_neg, continuous_linear_equiv.map_sub, image_add_left, mem_preimage,
    singleton_add, mem_closed_ball_zero_iff, neg_add_eq_sub] using hy,
  have Iz : ∥z∥ ≤ C * r := calc
    ∥z∥ = dist z 0 : (dist_zero_right _).symm
    ... ≤ ∥↑(f'.symm)∥₊ * dist (f' z) (f' 0) : f'.antilipschitz.le_mul_dist _ _
    ... ≤ C * dist (f' z) (f' 0) : mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    ... ≤ C * (t * r) :
      by { rw [dist_eq_norm, f'.map_zero, sub_zero], exact mul_le_mul_of_nonneg_left B Cpos.le }
    ... ≤ C * r : mul_le_mul_of_nonneg_left (mul_le_of_le_one_left rpos.le ht.2.le) Cpos.le,
  have A : ∥f (x + z) - f x - f' z∥ ≤ (1 - t) * r, from calc
    ∥f (x + z) - f x - f' z∥ ≤ ε * ∥z∥ :
      hδ (mem_closed_ball_zero_iff.2 (Iz.trans ((le_div_iff' Cpos).1 rle)))
    ... ≤ ε * (C * r) : mul_le_mul_of_nonneg_left Iz εpos.le
    ... = (1 - t) * r : by { field_simp [ε, Cpos.ne'], ring },
  simp only [dist_eq_norm, mem_closed_ball, mem_preimage],
  calc ∥f y - f x∥
      = ∥(f (x + z) - f x - f' z) + f' z∥ : by simp only [add_sub_cancel'_right, sub_add_cancel]
  ... ≤ ∥f (x + z) - f x - f' z∥ + ∥f' z∥ : norm_add_le _ _
  ... ≤ (1 - t) * r + t * r : add_le_add A B
  ... = r : by ring
end

/-- Consider a map `f` with an invertible derivative `f'` at a point `x`. Then the preimage under
`f` of a small ball `closed_ball (f x) r` around `f x` resembles its preimage under `f'`.
Here we prove that the rescaling of the latter by a fixed factor `t < 1` is contained in
the intersection of any neighborhood of `x` with the former, for small enough `r`. -/
lemma eventually_preimage_fderiv_closed_ball_subset_inter_preimage_closed_ball
  {f : E → F} {x : E} {f' : E ≃L[ℝ] F} (hf : has_fderiv_at f (f' : E →L[ℝ] F) x)
  {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {u : set E} (hu : u ∈ 𝓝 x) :
  ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
    {x} + f' ⁻¹' (closed_ball 0 (t * r)) ⊆ u ∩ f ⁻¹' (closed_ball (f x) r) :=
begin
  have A : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
    {x} + f' ⁻¹' (closed_ball 0 (t * r)) ⊆ f ⁻¹' (closed_ball (f x) r) :=
      eventually_preimage_fderiv_closed_ball_subset_preimage_closed_ball hf ht,
  have B : ∀ᶠ r in 𝓝 (0 : ℝ), {x} + r • f' ⁻¹' (closed_ball 0 t) ⊆ u :=
    eventually_singleton_add_smul_subset (f'.antilipschitz.bounded_preimage bounded_closed_ball) hu,
  filter_upwards [A, nhds_within_le_nhds B, self_mem_nhds_within],
  assume r hr h'r rpos,
  change 0 < r at rpos,
  apply subset_inter _ hr,
  convert h'r,
  rw [← f'.preimage_smul_set, smul_closed_ball _ _ ht.1, real.norm_eq_abs,
    abs_of_nonneg rpos.le, smul_zero, mul_comm],
end

variables [measurable_space E] [finite_dimensional ℝ E] [borel_space E]
  (μ : measure E) [is_add_haar_measure μ]

/-- Consider a local homeomorphism `f`. Assume that `f.symm` has a derivative `g` at a point `y`.
Then `f` locally rescales volume according to the determinant of the derivative `g` of `f.symm`.
More precisely, the ratio of the Lebesgue measures of `f ⁻¹' (closed_ball y r)` and
of `closed_ball y r` converges to the absolute value of the determinant of `g` as `r` tends
to zero. -/
theorem tendsto_add_haar_preimage_closed_ball_div_add_haar_closed_ball
  (f : local_homeomorph E E) (g : E →L[ℝ] E) (y : E) (y_mem : y ∈ f.target)
  (h : has_fderiv_at f.symm g y) :
  tendsto (λ r, μ (f.source ∩ f ⁻¹' (closed_ball y r)) / μ (closed_ball y r)) (𝓝[Ioi (0 : ℝ)] 0)
    (𝓝 (ennreal.of_real (abs (g : E →ₗ[ℝ] E).det))) :=
begin
  let d := ennreal.of_real (abs (g : E →ₗ[ℝ] E).det),
  let x := f.symm y,
  have x_mem : x ∈ f.source := f.map_target y_mem,
  /- First show that the ratio of measures is asymptotically bounded above by the determinant.
  For this, we have to show that the measure of the preimage of a ball under `f` is small.
  We rewrite this preimage as a direct image under `f.symm`, and use
  `eventually_smul_image_closed_ball_subset_image_closed_ball_fderiv` to say that is contained
  in a small thickening of `g '' (closed_ball 0 1)`, whose measure is controlled by that of
  `g '' (closed_ball 0 1)` if the neighborhood is small enough, which in turn is controlled by the
  determinant of `g`. -/
  have A : ∀ m, d < m → ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      μ (f.source ∩ f ⁻¹' (closed_ball y r)) / μ (closed_ball y r) < m,
  { assume m hm,
    -- construct a small neighborhood of `g '' (closed_ball 0 1)` with measure comparable to
    -- the determinant of `g`.
    obtain ⟨ε, hε, εpos⟩ : ∃ (ε : ℝ),
      μ (closed_ball 0 ε + g '' (closed_ball 0 1)) < m * μ (closed_ball 0 1) ∧ 0 < ε,
    { have HC : is_compact (g '' closed_ball 0 1) :=
        (proper_space.is_compact_closed_ball _ _).image g.continuous,
      have L0 : tendsto (λ ε, μ (cthickening ε (g '' (closed_ball 0 1))))
        (𝓝[Ioi 0] 0) (𝓝 (μ (g '' (closed_ball 0 1)))),
      { apply tendsto.mono_left _ nhds_within_le_nhds,
        exact tendsto_measure_cthickening_of_is_compact HC },
      have L1 : tendsto (λ ε, μ (closed_ball 0 ε + g '' (closed_ball 0 1)))
        (𝓝[Ioi 0] 0) (𝓝 (μ (g '' (closed_ball 0 1)))),
      { apply L0.congr' _,
        filter_upwards [self_mem_nhds_within],
        assume r hr,
        rw [HC.cthickening_eq_add_closed_ball (le_of_lt hr), add_comm] },
      have L2 : tendsto (λ ε, μ (closed_ball 0 ε + g '' (closed_ball 0 1)))
        (𝓝[Ioi 0] 0) (𝓝 (d * μ (closed_ball 0 1))),
      { convert L1,
        exact (add_haar_image_continuous_linear_map _ _ _).symm },
      have I : d * μ (closed_ball 0 1) < m * μ (closed_ball 0 1) :=
        (ennreal.mul_lt_mul_right ((add_haar_closed_ball_pos μ _ zero_lt_one).ne')
          measure_closed_ball_lt_top.ne).2 hm,
      have H : ∀ᶠ (b : ℝ) in 𝓝[Ioi 0] 0,
        μ (closed_ball 0 b + ⇑g '' closed_ball 0 1) < m * μ (closed_ball 0 1) :=
          (tendsto_order.1 L2).2 _ I,
      exact (H.and self_mem_nhds_within).exists },
    -- for small enough `r`, the image of a small ball `closed_ball y r` under `f.symm` is contained
    -- in the `ε`-thickening of `g '' (closed_ball 0 1)`, and coincides with the preimage under `f`.
    have R1 : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      r⁻¹ • ({-x} + f.symm '' (closed_ball y r)) ⊆ closed_ball 0 ε + g '' (closed_ball 0 1) :=
        eventually_smul_image_closed_ball_subset_image_closed_ball_fderiv h εpos,
    have R2 : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      f.source ∩ f ⁻¹' (closed_ball y r) = f.symm '' (closed_ball y r),
    { have : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), closed_ball y r ⊆ f.target,
      { apply nhds_within_le_nhds,
        exact eventually_closed_ball_subset (f.open_target.mem_nhds y_mem) },
      filter_upwards [this],
      assume r hr,
      have : f.is_image (f.source ∩ f ⁻¹' (closed_ball y r)) (closed_ball y r),
      { apply local_homeomorph.is_image.of_preimage_eq',
        simp only [inter_eq_right_iff_subset.mpr hr, ←inter_assoc, inter_self] },
      simpa only [inter_eq_right_iff_subset.mpr hr, ←inter_assoc, inter_self]
        using this.symm_image_eq.symm },
    -- for such an `r`, one checks that the desired upper bound on the ratio of the Lebesgue
    -- measures of `f ⁻¹' (closed_ball y r)` and of `closed_ball y r` holds.
    filter_upwards [R1, R2, self_mem_nhds_within],
    assume r hr1 hr2 rpos,
    change 0 < r at rpos,
    have I : ennreal.of_real (|(r ^ finrank ℝ E)⁻¹|) * μ (f.symm '' closed_ball y r)
    < ennreal.of_real (|(r ^ finrank ℝ E)⁻¹|) * m * μ (closed_ball y r) := calc
      ennreal.of_real (|(r ^ finrank ℝ E)⁻¹|) * μ (f.symm '' closed_ball y r)
      = μ (r⁻¹ • ({-x} + ⇑(f.symm) '' closed_ball y r)) :
        by simp only [add_haar_smul, image_add_left, inv_pow₀, add_haar_preimage_add, singleton_add]
      ... ≤ μ (closed_ball 0 ε + ⇑g '' closed_ball 0 1) :
        measure_mono hr1
      ... < m * μ (closed_ball 0 1) : hε
      ... = ennreal.of_real (|(r ^ finrank ℝ E)⁻¹|) * m * μ (closed_ball y r) :
        by rw [add_haar_closed_ball' μ y rpos.le, mul_comm _ m, mul_assoc, ← mul_assoc _ _ (μ _),
          ← ennreal.of_real_mul (abs_nonneg _), abs_of_nonneg (inv_nonneg.2 (pow_nonneg rpos.le _)),
          inv_mul_cancel (pow_pos rpos _).ne', ennreal.of_real_one, one_mul],
    have J : μ (f.symm '' closed_ball y r) < m * μ (closed_ball y r),
    { rw mul_assoc at I,
      apply (ennreal.mul_lt_mul_left _ ennreal.of_real_ne_top).1 I,
      simpa only [abs_nonpos_iff, ennreal.of_real_eq_zero, inv_eq_zero, ne.def]
        using (pow_pos rpos _).ne' },
    rwa [hr2, ennreal.div_lt_iff (or.inl (add_haar_closed_ball_pos μ y rpos).ne')
          (or.inl measure_closed_ball_lt_top.ne)] },
  /- Let us now prove that the ratio of measures is asymptotically larger than the determinant.
  For this, we have to show that the measure of the preimage of a ball under `f` is large. We rely
  on `eventually_preimage_fderiv_closed_ball_subset_inter_preimage_closed_ball`, which says that
  this preimage contains a slightly rescaled preimage of the ball under `g`. This statement requires
  `g` to be invertible, but it is not an issue since there is nothing to prove if `g` is
  not invertible. -/
  have B : ∀ l, l < d → ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      l < μ (f.source ∩ f ⁻¹' (closed_ball y r)) / μ (closed_ball y r),
  { assume l hl,
    -- we can assume that the determinant of `g` is nonzero, as otherwise there is nothing to prove.
    rcases eq_or_lt_of_le (abs_nonneg _ : 0 ≤ abs (g : E →ₗ[ℝ] E).det) with h|detpos,
    { simp only [d, ←h, ennreal.not_lt_zero, ennreal.of_real_zero] at hl, exact false.elim hl },
    have : (g : E →ₗ[ℝ] E).det ≠ 0 :=
      λ h, by simpa only [h, lt_self_iff_false, abs_zero] using detpos,
    let G : E ≃L[ℝ] E := (linear_map.equiv_of_det_ne_zero _ this).to_continuous_linear_equiv,
    let f' : E →L[ℝ] E := G.symm,
    -- then `f` is differentiable at `f.symm y`, with derivative the inverse of `g`
    have h' : has_fderiv_at f.symm (G : E →L[ℝ] E) y := h,
    have hff' : has_fderiv_at f f' x :=
      local_homeomorph.has_fderiv_at_symm' f.symm y_mem h',
    -- choose a rescaling factor `t` so close enough to `1` that it does not spoil the estimates.
    obtain ⟨t, tlim, ht⟩ : ∃ (t : ℝ), l < ennreal.of_real (t ^ finrank ℝ E) * d ∧
      t ∈ Ico (0 : ℝ) 1,
    { have L : tendsto (λ (t : ℝ), ennreal.of_real (t ^ finrank ℝ E) * d) (𝓝[Ico 0 1] 1)
        (𝓝 (ennreal.of_real (1 ^ finrank ℝ E) * d)),
      { apply ennreal.tendsto.mul_const _ (or.inr ennreal.of_real_ne_top),
        apply ennreal.tendsto_of_real (tendsto.pow _ _),
        exact nhds_within_le_nhds, },
      simp only [one_pow, one_mul, ennreal.of_real_one] at L,
      haveI : (𝓝[Ico (0 : ℝ) 1] 1).ne_bot := right_nhds_within_Ico_ne_bot zero_lt_one,
      exact (((tendsto_order.1 L).1 _ hl).and self_mem_nhds_within).exists },
    -- use `eventually_preimage_fderiv_closed_ball_subset_inter_preimage_closed_ball` to compare
    -- the measures of the preimage under `f'` of a ball of radius `t * r` and under `f` of a
    -- ball of radius `r`.
    have : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      ennreal.of_real (r ^ finrank ℝ E) * ennreal.of_real (t ^ finrank ℝ E)
        * d * μ (closed_ball 0 1) ≤ μ (f.source ∩ f ⁻¹' (closed_ball y r)),
    { have : ∀ᶠ r in 𝓝[Ioi (0 : ℝ)] (0 : ℝ), {x} + f' ⁻¹' (closed_ball 0 (t * r))
        ⊆ f.source ∩ f ⁻¹' (closed_ball (f x) r),
          by apply eventually_preimage_fderiv_closed_ball_subset_inter_preimage_closed_ball hff' ht
            (is_open.mem_nhds f.open_source x_mem),
      filter_upwards [this, self_mem_nhds_within],
      assume r hr r_pos,
      change 0 < r at r_pos,
      calc
      ennreal.of_real (r ^ finrank ℝ E) * ennreal.of_real (t ^ finrank ℝ E) * d
        * μ (closed_ball 0 1) = μ ({x} + f' ⁻¹' (closed_ball 0 (t * r))) :
        begin
          have : d = ennreal.of_real (abs (G : E →ₗ[ℝ] E).det),
          { simp only [d, coe_coe], congr, ext z, refl },
          simp only [μ.add_haar_closed_ball' 0 (mul_nonneg ht.left r_pos.le), mul_pow,
            image_add_left, add_haar_preimage_continuous_linear_equiv, this,
            continuous_linear_equiv.symm_symm, continuous_linear_equiv.coe_coe,
            add_haar_preimage_add, singleton_add, coe_coe, ennreal.of_real_mul (pow_nonneg ht.1 _)],
          simp only [mul_assoc, mul_comm],
        end
      ... ≤ μ (f.source ∩ f ⁻¹' (closed_ball (f x) r)) : measure_mono hr
      ... = μ (f.source ∩ f ⁻¹' (closed_ball y r)) : by simp only [y_mem, f.right_inv], },
    -- conclude using the previous estimate and the good choice of `t`.
    filter_upwards [this, self_mem_nhds_within],
    assume r hr rpos,
    change 0 < r at rpos,
    apply tlim.trans_le,
    rw [ennreal.le_div_iff_mul_le (or.inl (add_haar_closed_ball_pos μ _ rpos).ne')
      (or.inl measure_closed_ball_lt_top.ne), add_haar_closed_ball' μ _ rpos.le],
    convert hr using 1,
    ring },
  /- We have showed that the ratio of measures is asymptotically both smaller and larger than
  the determinant. This concludes the proof. -/
  exact tendsto_order.2 ⟨B, A⟩
end
