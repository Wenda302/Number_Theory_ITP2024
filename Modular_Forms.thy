theory Modular_Forms
  imports Modular_Fourier
begin

lemma zorder_0_eq: "zorder (\<lambda>_. 0) x = (THE n. False)"
proof -
  {
    fix h r n
    assume *: "r > 0" "h holomorphic_on cball x r" "h x \<noteq> 0"
              "\<forall>w\<in>cball x r - {x}. 0 = h w * (w - x) powi n \<and> h w \<noteq> 0"
    define y where "y = x + of_real (r / 2)"
    have "y \<in> cball x r - {x}"
      using \<open>r > 0\<close> by (auto simp: y_def dist_norm)
    with * have "0 = h y * (y - x) powi n \<and> h y \<noteq> 0"
      by blast
    hence "y = x"
      by auto
    hence False
      using \<open>r > 0\<close> by (simp add: y_def)
  } note * = this
  show ?thesis
    unfolding zorder_def by (rule arg_cong[of _ _ The] ext)+ (use * in blast)
qed    

lemma zorder_0_eq': "zorder (\<lambda>_. 0) x = zorder (\<lambda>_. 0) 0"
  unfolding zorder_0_eq ..

lemma moebius_meromorphic [meromorphic_intros]:
  assumes "f meromorphic_on A" "a meromorphic_on A" "b meromorphic_on A" 
          "c meromorphic_on A" "d meromorphic_on A"
  shows   "(\<lambda>z. moebius (a z) (b z) (c z) (d z) (f z)) meromorphic_on A"
  unfolding moebius_def
  by (intro Meromorphic1.meromorphic_intros assms )

lemma apply_modgrp_meromorphic [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>z. apply_modgrp h (f z)) meromorphic_on A"
  unfolding apply_modgrp_altdef 
  by (intro Meromorphic1.meromorphic_intros moebius_meromorphic assms)

notation const_mero_uhp ("\<langle>_\<rangle>")

locale weakly_modular_form = modgrp_subgroup_periodic G
  for f :: mero_uhp and weight :: int and G :: "modgrp set" +
  assumes invariant_compose_modgrp:
    "h \<in> G \<Longrightarrow> compose_modgrp_mero_uhp f h = modgrp_factor_mero_uhp h powi weight * f"
begin

lemma mero_uhp_rel_apply_modgrp:
  assumes "h \<in> G"
  shows "mero_uhp_rel (\<lambda>z. eval_mero_uhp f (apply_modgrp h z))
           (\<lambda>z. modgrp_factor h z powi weight * eval_mero_uhp f z)"
proof -
  have "mero_uhp_rel (\<lambda>z. eval_mero_uhp f (apply_modgrp h z)) (compose_modgrp_mero_uhp f h)"
    by mero_uhp_rel
  also have "compose_modgrp_mero_uhp f h = modgrp_factor_mero_uhp h powi weight * f"
    using assms by (rule invariant_compose_modgrp)
  also have "mero_uhp_rel \<dots> (\<lambda>z. modgrp_factor h z powi weight * eval_mero_uhp f z)"
    by mero_uhp_rel
  finally show ?thesis .
qed

lemmas [analytic_intros del] = constant_on_imp_analytic_on

lemma is_pole_apply_modgrp_iff [simp]:
  assumes h: "h \<in> G"
  shows "is_pole (eval_mero_uhp f) (apply_modgrp h z) \<longleftrightarrow> is_pole f z"
proof (cases "Im z > 0")
  case True
  have "is_pole (eval_mero_uhp f) (apply_modgrp h z) \<longleftrightarrow>
        is_pole (eval_mero_uhp f \<circ> apply_modgrp h) z"
  proof (rule is_pole_compose_iff [symmetric])
    show "filtermap (apply_modgrp h) (at z) = at (apply_modgrp h z)"
      using True by (intro filtermap_at_apply_modgrp) auto
  qed
  also have "\<dots> \<longleftrightarrow> is_pole (\<lambda>z. modgrp_factor h z powi weight * eval_mero_uhp f z) z"
  proof (rule is_pole_cong')
    show " \<forall>\<^sub>\<approx>x\<in>{z. Im z > 0}. (eval_mero_uhp f \<circ> apply_modgrp h) x =
                                 modgrp_factor h x powi weight * eval_mero_uhp f x"
      using mero_uhp_rel_apply_modgrp[of h] by (simp add: mero_uhp_rel_def assms)
  qed (use True in \<open>auto simp: open_halfspace_Im_gt\<close>)
  also have "\<dots> \<longleftrightarrow> is_pole (eval_mero_uhp f) z"
    by (rule is_pole_mult_analytic_nonzero1_iff) (use True in \<open>auto intro!: analytic_intros\<close>)
  finally show ?thesis .
next
  case False
  have "\<not>is_pole f z" "\<not>is_pole f (apply_modgrp h z)"
    by (rule not_is_pole_eval_mero_uhp_outside; use False in simp; fail)+
  thus ?thesis
    by simp
qed  

lemma invariant_apply_modgrp [simp]:
  assumes h: "h \<in> G"
  shows "eval_mero_uhp f (apply_modgrp h z) = modgrp_factor h z powi weight * eval_mero_uhp f z"
proof (cases "Im z > 0 \<and> \<not>is_pole (eval_mero_uhp f) z")
  case True
  have "mero_uhp_rel
          (eval_mero_uhp (compose_modgrp_mero_uhp f h - modgrp_factor_mero_uhp h powi weight * f))
          (\<lambda>z. eval_mero_uhp f (apply_modgrp h z) - modgrp_factor h z powi weight * eval_mero_uhp f z)"
    by mero_uhp_rel
  also have "compose_modgrp_mero_uhp f h - modgrp_factor_mero_uhp h powi weight * f = 0"
    using h by (simp add: invariant_compose_modgrp)
  finally have "eval_mero_uhp 0 z =
           eval_mero_uhp f (apply_modgrp h z) - modgrp_factor h z powi weight * eval_mero_uhp f z"
    by (rule mero_uhp_rel_imp_eval_mero_uhp_eq) (use True h in \<open>auto intro!: analytic_intros\<close>)
  thus ?thesis
    using True by auto
next
  case False
  then consider "Im z \<le> 0" | "Im z > 0" "is_pole (eval_mero_uhp f) z"
    by fastforce
  thus ?thesis
    by cases (auto simp: eval_mero_uhp_outside eval_mero_uhp_pole is_pole_apply_modgrp_iff h)
qed

lemma rel_imp_zorder_eq:
  assumes "rel z z'"
  shows   "zorder f z = zorder f z'"
proof (cases "f = 0")
  case True
  hence *: "eval_mero_uhp f = (\<lambda>_. 0)"
    by (intro ext) auto
  thus ?thesis
    by (simp add: zorder_shift')
next
  case False
  from assms obtain g where g: "g \<in> G" "z' = apply_modgrp g z" "Im z > 0" "Im z' > 0"
    by (auto simp: rel_def)
  note z = g(3)
  have ev_nz: "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
    using \<open>f \<noteq> 0\<close> z eventually_eval_mero_uhp_neq_iff[of z f 0] by auto

  have "\<forall>\<^sub>F w in at z. w \<in> {w. Im w > 0} - {z}"
    by (intro eventually_at_in_open open_halfspace_Im_gt) (use g in auto)
  hence ev_nz': "\<forall>\<^sub>F w in at z. apply_modgrp g w \<noteq> apply_modgrp g z"
  proof eventually_elim
    case (elim w)
    with g show ?case 
      by (subst apply_modgrp_eq_iff) auto
  qed

  have "zorder (\<lambda>w. modgrp_factor g w powi weight * f w) z =
        zorder f z + zorder (\<lambda>w. modgrp_factor g w powi weight) z"
  proof (subst zorder_mult)
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
      using z by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
    hence "eventually (\<lambda>z. modgrp_factor g z powi weight \<noteq> 0) (at z)"
      by eventually_elim auto
    thus "\<exists>\<^sub>F z in at z. modgrp_factor g z powi weight \<noteq> 0"
      by (intro eventually_frequently) auto
  next
    show "\<exists>\<^sub>F z in at z. eval_mero_uhp f z \<noteq> 0"
      by (intro eventually_frequently ev_nz) auto
  qed (use \<open>Im z > 0\<close> in \<open>auto intro!: Meromorphic1.meromorphic_intros\<close>)
  also have "zorder (\<lambda>w. modgrp_factor g w powi weight) z = 0"
    by (intro zorder_eq_0I analytic_intros) (use \<open>Im z > 0\<close> in auto)
  also have "zorder (\<lambda>w. modgrp_factor g w powi weight * eval_mero_uhp f w) z =
             zorder (eval_mero_uhp f \<circ> apply_modgrp g) z"
    using g by (simp add: o_def)
  also have "\<dots> = zorder_mero_uhp f (apply_modgrp g z) * zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z"
  proof (rule zorder_compose')
    show "\<forall>\<^sub>F w in at (apply_modgrp g z). eval_mero_uhp f w \<noteq> 0"
      using z eventually_eval_mero_uhp_neq_iff[of "apply_modgrp g z" f 0] \<open>f \<noteq> 0\<close> by auto
  qed (use z ev_nz' in \<open>auto intro!: meromorphic_on_isolated_singularity meromorphic_on_not_essential
                          Meromorphic1.meromorphic_intros analytic_intros\<close>)
  also have "zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z = 1"
    by (intro zorder_apply_modgrp) (use g in auto)
  finally show ?thesis
    using g by simp
qed

lemma zorder_apply_modgrp:
  assumes "h \<in> G" "Im z > 0"
  shows   "zorder f (apply_modgrp h z) = zorder f z"
  by (intro rel_imp_zorder_eq) (use assms in auto)

lemma rel_imp_is_pole_iff:
  assumes "rel z z'"
  shows   "is_pole f z \<longleftrightarrow> is_pole f z'"
  using assms unfolding rel_def by auto

abbreviation period where "period \<equiv> modgrp_subgroup_period G"

lemma shift_modgrp_in_G [intro]: "period dvd n \<Longrightarrow> shift_modgrp n \<in> G"
  by auto

lemma shift_modgrp_in_G_iff [simp]: "shift_modgrp n \<in> G \<longleftrightarrow> period dvd n"
  by (simp add: shift_modgrp_in_G_iff)

sublocale fourier_expansion f period
proof
  show "period > 0"
    by (rule modgrp_subgroup_period_pos)
next
  show "compose_modgrp_mero_uhp f (shift_modgrp (int period)) = f"
    using invariant_compose_modgrp[of "shift_modgrp (int period)"] by simp
qed

lemma weakly_modular_form_minus [intro]: "weakly_modular_form (-f) weight G"
  by standard (simp_all add: hom_distribs invariant_compose_modgrp)

lemma weakly_modular_form_power [intro]: "weakly_modular_form (f ^ n) (weight * n) G"
  by standard (simp_all add: hom_distribs invariant_compose_modgrp field_simps power_int_mult)

lemma weakly_modular_form_power_int [intro]: "weakly_modular_form (f powi n) (weight * n) G"
  by standard (simp_all add: hom_distribs invariant_compose_modgrp field_simps power_int_mult_distrib flip: power_int_mult)

lemma weakly_modular_form_inverse [intro]: "weakly_modular_form (inverse f) (-weight) G"
  by standard (cases "f = 0", simp_all add: hom_distribs invariant_compose_modgrp field_simps power_int_minus)

end

lemma (in modgrp_subgroup_periodic) weakly_modular_form_0 [intro]:
  "weakly_modular_form 0 weight G"
  by unfold_locales auto

lemma (in modgrp_subgroup_periodic) weakly_modular_form_const [intro]:
  "weakly_modular_form (const_mero_uhp c) 0 G"
  by unfold_locales auto

lemma (in modgrp_subgroup_periodic) weakly_modular_form_1 [intro]:
  "weakly_modular_form 1 0 G"
  by unfold_locales auto

locale weakly_modular_form_weight_0 = weakly_modular_form f 0 G
  for f G
begin

lemma rel_imp_eval_eq:
  assumes "rel z z'"
  shows   "eval_mero_uhp f z = eval_mero_uhp f z'"
  using assms unfolding rel_def by auto

end


locale weakly_modular_form_pair =
  f: weakly_modular_form f weight G + g: weakly_modular_form g weight' G
  for f g weight weight' G
begin

lemma weakly_modular_form_add [intro]: "weight = weight' \<Longrightarrow> weakly_modular_form (f + g) weight G"
  by standard (simp_all add: hom_distribs f.invariant_compose_modgrp g.invariant_compose_modgrp)

lemma weakly_modular_form_diff [intro]: "weight = weight' \<Longrightarrow> weakly_modular_form (f - g) weight G"
  by standard (simp_all add: hom_distribs algebra_simps f.invariant_compose_modgrp g.invariant_compose_modgrp)

lemma weakly_modular_form_mult [intro]: "weakly_modular_form (f * g) (weight + weight') G"
  by standard (auto simp: hom_distribs algebra_simps power_int_add f.invariant_compose_modgrp g.invariant_compose_modgrp)

lemma weakly_modular_form_divide [intro]: "weakly_modular_form (f / g) (weight - weight') G"
  by standard (auto simp: hom_distribs algebra_simps power_int_diff f.invariant_compose_modgrp g.invariant_compose_modgrp)

end


(* TODO Move *)
lift_definition modgrp_factor' :: "modgrp \<Rightarrow> complex \<Rightarrow> int \<Rightarrow> complex" is
  "\<lambda>(a,b,c,d) z k. (of_int c * z + of_int d) powi (2 * k)"
  by (auto simp: modgrp_rel_def fun_eq_iff power_int_mult minus_minus_power2_eq)

lemma modgrp_factor'_mult_S:
  assumes "z \<noteq> 0"
  shows   "modgrp_factor' (g * S_modgrp) z k = modgrp_factor' g (-1/z) k * z powi (2*k)"
  using assms unfolding modgrp_factor_def
proof (transfer', goal_cases)
  case (1 z g k)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have "(of_int (fst (snd (snd g))) - of_int (snd (snd (snd g))) * z)\<^sup>2 powi k =
        ((of_int (snd (snd (snd g))) - of_int (fst (snd (snd g))) / z) * z)\<^sup>2 powi k"
    using 1 by (simp add: field_simps power2_commute)
  thus ?case using 1
    by (simp add: modgrp_factor_def case_prod_unfold power_int_mult minus_minus_power2_eq field_simps
             flip: power_int_mult_distrib power_mult_distrib)
qed

lemma modgrp_factor'_mult_shift:
  "modgrp_factor' (g * shift_modgrp n) z k = modgrp_factor' g (z + of_int n) k"
  unfolding modgrp_factor_def
  by transfer' (auto simp: algebra_simps)

lemma modgrp_factor'_eq:
  "modgrp_factor' g z k = (of_int (modgrp_c g) * z + of_int (modgrp_d g)) powi (2 * k)"
  by transfer (auto simp: modgrp_rel_def power_int_mult minus_minus_power2_eq)

lemma modgrp_factor'_1 [simp]: "modgrp_factor' 1 z k = 1"
  by (simp add: modgrp_factor'_eq)

lemma modgrp_factor_powi_eq: "even k \<Longrightarrow> modgrp_factor g z powi k = modgrp_factor' g z (k div 2)"
  by (auto elim!: evenE simp: modgrp_factor'_eq modgrp_factor_def)

lemma mero_uhp_relI_weak:
  assumes "\<And>z. Im z > 0 \<Longrightarrow> f z = g z"
  shows   "mero_uhp_rel f g"
proof -
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse {z. Im z > 0})"
    by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
  thus ?thesis
    unfolding mero_uhp_rel_def by eventually_elim (use assms in auto)
qed

lemma weakly_modular_formI_generators:
  fixes f :: mero_uhp and g :: "complex \<Rightarrow> complex"
  assumes "even k"
  assumes [mero_uhp_rel_intros]: "mero_uhp_rel f g"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> g (z + 1) = g z"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> g (-(1/z)) = z powi k * g z"
  shows   "weakly_modular_form f k UNIV"
proof
  fix h :: modgrp
  define k' where "k' = k div 2"
  have [simp]: "k = 2 * k'"
    using \<open>even k\<close> by (elim evenE) (auto simp: k'_def)
  have "mero_uhp_rel (compose_modgrp_mero_uhp f h) (\<lambda>z. g (apply_modgrp h z))"
    by mero_uhp_rel
  also have "g (apply_modgrp h z) = modgrp_factor h z powi k * g z" if z: "Im z > 0" for z
  proof -
    have "g (apply_modgrp h z) = modgrp_factor' h z k' * g z" using z
    proof (induction h arbitrary: z rule: modgrp_induct')
      case (id z)
      thus ?case by auto
    next
      case (S h z)
      from \<open>Im z > 0\<close> have [simp]: "z \<noteq> 0"
        by auto
      from \<open>Im z > 0\<close> have *: "Im (-(1/z)) > 0"
        using modgrp.Im_transform_pos[of z S_modgrp] by simp
      have "g (apply_modgrp (h * S_modgrp) z) = g (apply_modgrp h (- (1 / z)))"
        using S by (subst apply_modgrp_mult) auto
      also have "\<dots> = modgrp_factor' h (- (1 / z)) k' * g (- (1 / z))"
        using S.prems * by (subst S.IH) auto
      also have "\<dots> = modgrp_factor' (h * S_modgrp) z k' * z powi (-k) * g (- (1 / z))"
        using \<open>Im z > 0\<close> \<open>even k\<close>
        by (subst modgrp_factor'_mult_S) (auto simp: power_int_minus field_simps)
      also have "g (- (1 / z)) = z powi k * g z"
        by (intro assms \<open>Im z > 0\<close>)
      finally show ?case
        by (simp add: field_simps power_int_minus)
    next
      case (T h z)
      have "g (apply_modgrp (h * T_modgrp) z) = modgrp_factor' h (z + 1) k' * g z"
        using T assms by (subst apply_modgrp_mult) (auto simp: modgrp_factor_powi_eq)
      also have "modgrp_factor' h (z + 1) k' = modgrp_factor' (h * T_modgrp) z k'"
        by (simp add: modgrp_factor'_mult_shift flip: shift_modgrp_1)
      finally show ?case
        using \<open>even k\<close> by (simp add: modgrp_factor_powi_eq)
    next
      case (inv_T h z)
      have [simp]: "inverse T_modgrp = shift_modgrp (-1)"
        by (simp add: shift_modgrp_1 shift_modgrp_minus)
      have "g (apply_modgrp (h * inverse T_modgrp) z) = modgrp_factor' h (z - 1) k' * g (z - 1)"
        using inv_T assms by (subst apply_modgrp_mult) (auto simp: modgrp_factor_powi_eq)    
      also have "g (z - 1) = g z"
        using assms(3)[of "z - 1"] inv_T by simp
      also have "modgrp_factor' h (z - 1) k' = modgrp_factor' (h * inverse T_modgrp) z k'"
        by (simp add: modgrp_factor'_mult_shift)
      finally show ?case
        using \<open>even k\<close> by (simp add: modgrp_factor_powi_eq del: modgrp_factor_shift_right)
    qed
    also have "modgrp_factor' h z k' = modgrp_factor h z powi k"
      using modgrp_factor_powi_eq[of k h z] by simp
    finally show "g (apply_modgrp h z) = modgrp_factor h z powi k * g z" .
  qed
  hence "mero_uhp_rel (\<lambda>z. g (apply_modgrp h z)) (\<lambda>z. modgrp_factor h z powi k * g z)"
    by (intro mero_uhp_relI_weak)
  also have "mero_uhp_rel \<dots> (modgrp_factor_mero_uhp h powi k * f)"
    by mero_uhp_rel
  finally show "compose_modgrp_mero_uhp f h = modgrp_factor_mero_uhp h powi k * f"
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed




locale meromorphic_form = weakly_modular_form +
  assumes meromorphic_at_cusp: "fourier meromorphic_on {0}"
begin

sublocale fourier_expansion_meromorphic f period
  by standard (rule meromorphic_at_cusp)

lemma finite_inv_image_mero_uhp:
  assumes "f \<noteq> const_mero_uhp c"
  shows   "finite (inv_image_mero_uhp f c)"
proof -
  have "eventually (\<lambda>z. f z \<noteq> c) at_cusp"
    by (rule eventually_neq_at_cusp) fact
  then obtain y where y: "\<And>z. Im z > y \<Longrightarrow> f z \<noteq> c"
    by (auto simp: eventually_at_cusp_iff)
  define R where "R = closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> y}"
  have "closed R"
    unfolding R_def by (auto intro!: closed_Int closed_halfspace_Im_le)
  moreover have "bounded R"
  proof -
    have "R \<subseteq> cbox (-1) (1 + \<i> * y)"
      by (auto simp: R_def in_closure_std_fund_region_iff in_cbox_complex_iff)
    moreover have "bounded \<dots>"
      by auto
    ultimately show "bounded R"
      using bounded_subset by blast
  qed
  ultimately have "compact R"
    using compact_eq_bounded_closed by blast

  have "\<forall>\<^sub>\<approx>z\<in>\<H>. f z \<noteq> c"
    by (rule eval_mero_uhp_avoid) fact
  hence "{z. f z = c} sparse_in \<H>"
    by (simp add: eventually_cosparse)
  hence "{z. f z = c} sparse_in R"
    by (rule sparse_in_subset) (use closure_std_fund_region_Im_pos in \<open>auto simp: R_def\<close>)
  from this and \<open>compact R\<close> have fin: "finite (R \<inter> {z. f z = c})"
    by (rule sparse_in_compact_finite)
  have "finite (\<R>\<^sub>\<Gamma>' \<inter> {z. \<not>is_pole f z \<and> f z = c})"
    by (rule finite_subset[OF _ fin]) (use std_fund_region'_subset y in \<open>force simp: R_def\<close>)
  also have "\<R>\<^sub>\<Gamma>' \<inter> {z. \<not>is_pole f z \<and> f z = c} = inv_image_mero_uhp f c"
    unfolding inv_image_mero_uhp_def by blast
  finally show ?thesis .
qed    

lemma finite_zeros_mero_uhp [intro]:
  assumes "f \<noteq> 0"
  shows   "finite (zeros_mero_uhp f)"
  using finite_inv_image_mero_uhp[of 0] assms by simp

lemma meromorphic_form_unop:
  assumes "weakly_modular_form (g f) weight' G"
  assumes "fourier_expansion_meromorphic f period \<Longrightarrow> fourier_expansion_meromorphic (g f) period"
  shows   "meromorphic_form (g f) weight' G"
proof -
  interpret A: weakly_modular_form "g f" weight' G
    by (rule assms)
  interpret A: fourier_expansion_meromorphic "g f" period
    by (rule assms) (fact fourier_expansion_meromorphic_axioms)
  show ?thesis
    by unfold_locales (fact A.fourier_meromorphic_at_0)
qed

lemma meromorphic_form_minus [intro]: "meromorphic_form (-f) weight G"
  by (rule meromorphic_form_unop weakly_modular_form_minus
           fourier_expansion_meromorphic.fourier_expansion_meromorphic_minus)+

lemma meromorphic_form_inverse [intro]: "meromorphic_form (inverse f) (-weight) G"
  by (rule meromorphic_form_unop weakly_modular_form_inverse
           fourier_expansion_meromorphic.fourier_expansion_meromorphic_inverse)+

lemma meromorphic_form_power [intro]: "meromorphic_form (f ^ n) (weight * n) G"
  by (rule meromorphic_form_unop weakly_modular_form_power
           fourier_expansion_meromorphic.fourier_expansion_meromorphic_power)+

lemma meromorphic_form_power_int [intro]: "meromorphic_form (f powi n) (weight * n) G"
  by (rule meromorphic_form_unop weakly_modular_form_power_int
           fourier_expansion_meromorphic.fourier_expansion_meromorphic_power_int)+

lemma finite_poles_mero_uhp [intro]: "finite (poles_mero_uhp f)"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  interpret inv: meromorphic_form "inverse f" "-weight" G ..
  have "finite (zeros_mero_uhp (inverse f))"
    using \<open>f \<noteq> 0\<close> by (intro inv.finite_zeros_mero_uhp) auto
  also have "zeros_mero_uhp (inverse f) = poles_mero_uhp f"
    using \<open>f \<noteq> 0\<close> by (simp add: zeros_mero_uhp_inverse)
  finally show ?thesis .  
qed auto

end

locale meromorphic_form_full = 
  fixes f :: mero_uhp and weight :: int
  assumes meromorphic_form_UNIV: "meromorphic_form f weight UNIV"
begin

sublocale meromorphic_form f weight UNIV
  rewrites "modgrp_subgroup_period UNIV = Suc 0"
  using meromorphic_form_UNIV by auto

end
  


context modgrp_subgroup_periodic
begin

lemma meromorphic_form_0 [intro]: "meromorphic_form 0 weight G"
proof -
  have [intro]: "weakly_modular_form.period G > 0"
    by (metis modgrp_subgroup_period_pos)
  interpret fourier_expansion_context "weakly_modular_form.period G"
    by unfold_locales auto
  interpret fourier_expansion_meromorphic 0 "weakly_modular_form.period G"
    unfolding zero_mero_uhp_def ..
  show ?thesis 
    by unfold_locales (auto intro!: fourier_meromorphic_at_0)
qed

lemma meromorphic_form_const [intro]: "meromorphic_form (const_mero_uhp c) 0 G"
proof -
  have [intro]: "weakly_modular_form.period G > 0"
    by (metis modgrp_subgroup_period_pos)
  interpret fourier_expansion_context "weakly_modular_form.period G"
    by unfold_locales auto
  interpret fourier_expansion_meromorphic "const_mero_uhp c" "weakly_modular_form.period G" ..
  show ?thesis 
    by unfold_locales (auto intro!: const.fourier_meromorphic_at_0)
qed

lemma meromorphic_form_1 [intro]: "meromorphic_form 1 0 G"
  using meromorphic_form_const[of 1] by simp

end


locale meromorphic_form_pair =
  f: meromorphic_form f weight G + g: meromorphic_form g weight' G 
  for f g weight weight' G
begin

sublocale weakly_modular_form_pair f g weight weight' G ..

sublocale fourier_expansion_meromorphic_pair f g "f.period" ..

lemma meromorphic_form_binop:
  assumes "weakly_modular_form (h f g) weight'' G"
  assumes "fourier_expansion_meromorphic f f.period \<Longrightarrow> fourier_expansion_meromorphic g f.period \<Longrightarrow>
           fourier_expansion_meromorphic (h f g) f.period"
  shows   "meromorphic_form (h f g) weight'' G"
proof -
  interpret A: weakly_modular_form "h f g" weight'' G
    by (rule assms)
  interpret B: fourier_expansion_meromorphic "h f g" f.period
    by (rule assms) (fact f.fourier_expansion_meromorphic_axioms g.fourier_expansion_meromorphic_axioms)+
  show ?thesis
    by unfold_locales (fact B.fourier_meromorphic_at_0)
qed

lemma meromorphic_form_add [intro]: "weight = weight' \<Longrightarrow> meromorphic_form (f + g) weight G"
  by (rule meromorphic_form_binop weakly_modular_form_add
           fourier_expansion_meromorphic_add | assumption)+

lemma meromorphic_form_diff [intro]: "weight = weight' \<Longrightarrow> meromorphic_form (f - g) weight G"
  by (rule meromorphic_form_binop weakly_modular_form_diff
           fourier_expansion_meromorphic_diff | assumption)+

lemma meromorphic_form_mult [intro]: "meromorphic_form (f * g) (weight + weight') G"
  by (rule meromorphic_form_binop weakly_modular_form_mult
           fourier_expansion_meromorphic_mult | assumption)+

lemma meromorphic_form_divide [intro]: "meromorphic_form (f / g) (weight - weight') G"
  by (rule meromorphic_form_binop weakly_modular_form_divide
           fourier_expansion_meromorphic_divide | assumption)+

end


  


definition holo_uhp :: "mero_uhp \<Rightarrow> bool" where
  "holo_uhp f \<longleftrightarrow> (\<forall>z. \<not>is_pole f z)"

lemma holo_uhp_mero_uhp_rel_transfer:
  assumes "mero_uhp_rel (eval_mero_uhp f) g"
  assumes "g analytic_on {z. Im z > 0}"
  shows   "holo_uhp f"
  unfolding holo_uhp_def
proof
  fix z :: complex
  show "\<not>is_pole f z"
  proof (cases "Im z > 0")
    case True
    have "\<not>is_pole g z"
      using True assms(2) by (metis analytic_at_imp_no_pole analytic_on_analytic_at mem_Collect_eq)
    moreover have "is_pole f z \<longleftrightarrow> is_pole g z"
      using assms(1) True
      unfolding mero_uhp_rel_def eventually_cosparse_open_eq[OF open_halfspace_Im_gt]
      by (intro is_pole_cong) (auto elim!: eventually_mono)
    ultimately show "\<not>is_pole f z"
      by blast
  qed (simp add: not_is_pole_eval_mero_uhp_outside)
qed


locale modular_form = weakly_modular_form +
  assumes holo_form: "holo_uhp f"
  assumes convergent_at_cusp: "\<exists>L. fourier \<midarrow>0\<rightarrow> L"
begin

sublocale meromorphic_form
proof
  from convergent_at_cusp have lim: "fourier \<midarrow>0\<rightarrow> fourier 0"
    using fourier_0_aux fourier_tendsto_0_iff by blast
  hence "(\<lambda>q. norm (fourier q)) \<midarrow>0\<rightarrow> norm (fourier 0)"
    by (intro tendsto_intros)
  hence "eventually (\<lambda>q. norm (fourier q) < norm (fourier 0) + 1) (at 0)"
    by (simp add: order_tendsto_iff)
  then obtain A 
    where A: "open A" "0 \<in> A" "\<And>q. q \<in> A - {0} \<Longrightarrow> norm (fourier q) < norm (fourier 0) + 1"
    unfolding eventually_at_topological by blast
  have "\<not>is_pole fourier q" if q: "q \<in> A \<inter> ball 0 1 - {0}" for q
  proof
    assume "is_pole fourier q"
    hence "eventually (\<lambda>q. norm (fourier q) > norm (fourier 0) + 1) (at q)"
      unfolding is_pole_def using filterlim_at_infinity_iff_eventually_norm_gt by blast
    moreover have "eventually (\<lambda>w. w \<in> A - {0} - {q}) (at q)"
      using q A by (intro eventually_at_in_open) auto
    ultimately have "eventually (\<lambda>_. False) (at q)"
      by eventually_elim (use A in force)
    thus False
      by simp
  qed
  hence "fourier holomorphic_on A \<inter> ball 0 1 - {0}"
    by (intro analytic_imp_holomorphic analytic_fourier) (auto simp: fourier_poles_altdef)
  hence "isolated_singularity_at fourier 0"
    by (rule isolated_singularity_at_holomorphic) (use A in auto)
  moreover from lim have "not_essential fourier 0"
    by auto
  ultimately show "fourier meromorphic_on {0}"
    by (simp add: meromorphic_at_iff)
qed

lemma no_poles [simp]: "\<not>is_pole (eval_mero_uhp f) z"
  using holo_form by (auto simp: holo_uhp_def)

lemma no_poles_fourier [simp]: "norm q < 1 \<Longrightarrow> \<not>is_pole fourier q"
  by (metis at_cusp_neq_bot convergent_at_cusp cusp_q_cusp_q_inv fourier_is_pole_0_iff
            fourier_is_pole_cusp_q_iff fourier_tendsto_0_iff no_poles 
            not_tendsto_and_filterlim_at_infinity period_pos)

lemma no_poles_fourier' [simp]: "fourier_poles = {}"
  by (auto simp: fourier_poles_altdef)

lemma analytic [analytic_intros]:
  "g analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> Im z > 0) \<Longrightarrow> eval_mero_uhp f analytic_on A"
  by (intro analytic_intros) auto

lemma fourier_analytic [analytic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. fourier (g z)) analytic_on A"
proof (rule analytic_on_compose_gen[OF assms(1), unfolded o_def])
  have "fourier analytic_on ball 0 1 - {0}"
    by (intro analytic_fourier) auto
  moreover have "fourier analytic_on {0}"
    using fourier_nicely_meromorphic nicely_meromorphic_on_imp_analytic_at by auto
  ultimately show "fourier analytic_on (ball 0 1 - {0} \<union> {0})"
    by (subst analytic_on_Un) auto
qed (use assms(2) in auto)

lemma zorder_at_cusp_ge_0 [simp, intro]: "zorder_at_cusp period f \<ge> 0"
proof (cases "f = 0")
  case False
  thus ?thesis
    by (auto simp: zorder_at_cusp_conv_fourier)
qed auto

lemma modular_form_unop:
  assumes "mero_uhp_rel (eval_mero_uhp (g f)) (\<lambda>z. g' (eval_mero_uhp f z))"
  assumes "meromorphic_form (g f) weight' G"
  assumes "g' analytic_on UNIV"
  shows   "modular_form (g f) weight' G"
proof -
  interpret A: meromorphic_form "g f" weight' G
    by (rule assms)
  show ?thesis
  proof
    note [analytic_intros] = analytic_on_compose_gen[OF _ assms(3), unfolded o_def]
    show "holo_uhp (g f)"
      by (rule holo_uhp_mero_uhp_rel_transfer[OF assms(1)]) (intro analytic_intros, auto)
    have "(\<lambda>q. g' (fourier q)) analytic_on {0}"
      by (intro analytic_intros) auto
    hence "(\<lambda>q. g' (fourier q)) \<midarrow>0\<rightarrow> g' (fourier 0)"
      by (intro isContD analytic_at_imp_isCont)
    also have "eventually (\<lambda>q::complex. q \<in> ball 0 1 - {0}) (at 0)"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. g' (fourier q) = A.fourier q) (at 0)"
    proof eventually_elim
      case q: (elim q) (* TODO: pull out as lemma? *)
      have "g' (fourier q) = g' (eval_mero_uhp f (cusp_q_inv A.period q))"
        using q by (simp add: fourier_def)
      also have "\<dots> = eval_mero_uhp (g f) (cusp_q_inv A.period q)"
        by (rule mero_uhp_rel_imp_eval_mero_uhp_eq [OF assms(1), symmetric])
           (use q in \<open>auto intro!: analytic_intros Im_cusp_q_inv_gt\<close>)
      also have "\<dots> = A.fourier q"
        using q by (simp add: A.fourier_def)
      finally show ?case .
    qed
    hence "(\<lambda>q. g' (fourier q)) \<midarrow>0\<rightarrow> g' (fourier 0) \<longleftrightarrow> A.fourier \<midarrow>0\<rightarrow> g' (fourier 0)"
      by (intro tendsto_cong) (auto elim!: eventually_mono simp: A.fourier_def)
    finally show "\<exists>L. A.fourier \<midarrow>0\<rightarrow> L" ..
  qed
qed

lemma modular_form_minus [intro]: "modular_form (-f) weight G"
  by (rule modular_form_unop[of _ "\<lambda>x. -x"], mero_uhp_rel) (auto intro!: analytic_intros)

lemma modular_form_power [intro]: "modular_form (f ^ n) (weight * n) G"
  by (rule modular_form_unop[of _ "\<lambda>x. x ^ n"], mero_uhp_rel) (auto intro!: analytic_intros)

lemma modular_form_power_int [intro]: "n \<ge> 0 \<Longrightarrow> modular_form (f powi n) (weight * n) G"
  by (rule modular_form_unop[of _ "\<lambda>x. x powi n"], mero_uhp_rel) (auto intro!: analytic_intros)

end


context modgrp_subgroup_periodic
begin

lemma modular_form_zero [intro]: "modular_form 0 weight G"
proof -
  have [intro]: "weakly_modular_form.period G > 0"
    by (metis modgrp_subgroup_period_pos)
  interpret fourier_expansion_context "weakly_modular_form.period G"
    by unfold_locales auto
  show ?thesis 
  proof
    show "holo_uhp 0"
      by (rule holo_uhp_mero_uhp_rel_transfer[of _ "\<lambda>_. 0"] mero_uhp_rel_intros)+ auto   
  next
    have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at (0 :: complex))"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. const.fourier 0 q = 0) (at 0)"
      by eventually_elim (use fourier_const[of _ 0] in \<open>auto simp del: fourier_const\<close>)
    hence "(\<lambda>_::complex. 0) \<midarrow>0\<rightarrow> (0 :: complex) \<longleftrightarrow> const.fourier 0 \<midarrow>0\<rightarrow> 0"
      by (intro tendsto_cong) auto
    thus "\<exists>L. fourier_expansion.fourier 0 (weakly_modular_form.period G) \<midarrow>0\<rightarrow> L"
      by auto
  qed auto
qed

lemma modular_form_const [intro]: "modular_form (const_mero_uhp c) 0 G"
proof -
  have [intro]: "weakly_modular_form.period G > 0"
    by (metis modgrp_subgroup_period_pos)
  interpret fourier_expansion_context "weakly_modular_form.period G"
    by unfold_locales auto
  show ?thesis 
  proof
    show "holo_uhp (const_mero_uhp c)"
      by (rule holo_uhp_mero_uhp_rel_transfer[of _ "\<lambda>_. c"] mero_uhp_rel_intros)+ auto      
  next
    have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at (0 :: complex))"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. const.fourier c q = c) (at 0)"
      by eventually_elim auto
    hence "(\<lambda>_::complex. c) \<midarrow>0\<rightarrow> c \<longleftrightarrow> const.fourier c \<midarrow>0\<rightarrow> c"
      by (intro tendsto_cong) (auto simp: eq_commute)
    thus "\<exists>L. fourier_expansion.fourier (const_mero_uhp c) (weakly_modular_form.period G) \<midarrow>0\<rightarrow> L"
      by auto
  qed auto
qed

lemma modular_form_1 [intro]: "modular_form 1 0 G"
  using modular_form_const[of 1] by simp

end


locale modular_form_pair =
  f: modular_form f weight G + g: modular_form g weight' G 
  for f g weight weight' G
begin

sublocale meromorphic_form_pair f g weight weight' G ..

sublocale fourier_expansion_meromorphic_pair f g "f.period" ..

lemma modular_form_binop:
  assumes "mero_uhp_rel (eval_mero_uhp (h f g)) (\<lambda>z. h' (eval_mero_uhp f z) (eval_mero_uhp g z))"
  assumes "meromorphic_form (h f g) weight'' G"
  assumes "\<And>f g A. f analytic_on A \<Longrightarrow> g analytic_on A \<Longrightarrow> (\<lambda>z. h' (f z) (g z)) analytic_on A"
  shows   "modular_form (h f g) weight'' G"
proof -
  interpret A: meromorphic_form "h f g" weight'' G
    by (rule assms)
  show ?thesis
  proof
    note [analytic_intros] = assms(3)
    show "holo_uhp (h f g)"
      by (rule holo_uhp_mero_uhp_rel_transfer[OF assms(1)]) (intro analytic_intros, auto)
    have "(\<lambda>q. h' (f.fourier q) (g.fourier q)) analytic_on {0}"
      by (intro analytic_intros) auto
    hence "(\<lambda>q. h' (f.fourier q) (g.fourier q)) \<midarrow>0\<rightarrow> h' (f.fourier 0) (g.fourier 0)"
      by (intro isContD analytic_at_imp_isCont)
    also have "eventually (\<lambda>q::complex. q \<in> ball 0 1 - {0}) (at 0)"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. h' (f.fourier q) (g.fourier q) = A.fourier q) (at 0)"
    proof eventually_elim
      case q: (elim q) (* TODO: pull out as lemma? *)
      have "h' (f.fourier q) (g.fourier q) =
              h' (eval_mero_uhp f (cusp_q_inv A.period q)) (eval_mero_uhp g (cusp_q_inv A.period q))"
        using q by (simp add: f.fourier_def g.fourier_def)
      also have "\<dots> = eval_mero_uhp (h f g) (cusp_q_inv A.period q)"
        by (rule mero_uhp_rel_imp_eval_mero_uhp_eq [OF assms(1), symmetric])
           (use q in \<open>auto intro!: analytic_intros Im_cusp_q_inv_gt\<close>)
      also have "\<dots> = A.fourier q"
        using q by (simp add: A.fourier_def)
      finally show ?case .
    qed
    hence "(\<lambda>q. h' (f.fourier q) (g.fourier q)) \<midarrow>0\<rightarrow> h' (f.fourier 0) (g.fourier 0) \<longleftrightarrow> 
           A.fourier \<midarrow>0\<rightarrow> h' (f.fourier 0) (g.fourier 0)"
      by (intro tendsto_cong) (auto elim!: eventually_mono simp: A.fourier_def)
    finally show "\<exists>L. A.fourier \<midarrow>0\<rightarrow> L" ..
  qed
qed

lemma modular_form_add [intro]: "weight = weight' \<Longrightarrow> modular_form (f + g) weight G"
  by (rule modular_form_binop[of _ "(+)"], mero_uhp_rel)
     (use meromorphic_form_add in \<open>auto intro!: analytic_intros\<close>)

lemma modular_form_diff [intro]: "weight = weight' \<Longrightarrow> modular_form (f - g) weight G"
  by (rule modular_form_binop[of _ "(-)"], mero_uhp_rel)
     (use meromorphic_form_diff in \<open>auto intro!: analytic_intros\<close>)

lemma modular_form_mult [intro]: "modular_form (f * g) (weight + weight') G"
  by (rule modular_form_binop[of _ "(*)"], mero_uhp_rel)
     (use meromorphic_form_mult in \<open>auto intro!: analytic_intros\<close>)

lemma modular_form_divide:
  defines "period \<equiv> modgrp_subgroup_period G"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> eval_mero_uhp g z = 0 \<Longrightarrow> zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "eval_mero_uhp_at_cusp g = 0 \<Longrightarrow> zorder_at_cusp period f \<ge> zorder_at_cusp period g"
  shows   "modular_form (f / g) (weight - weight') G"
proof (cases "f = 0 \<or> g = 0")
  case False
  hence [simp]: "f \<noteq> 0" "g \<noteq> 0"
    by auto
  interpret meromorphic_form "f / g" "weight - weight'" G
    by (rule meromorphic_form_divide)
  show ?thesis
  proof
    have freq: "\<exists>\<^sub>F w in at z. eval_mero_uhp f w \<noteq> 0" "\<exists>\<^sub>F w in at z. eval_mero_uhp g w \<noteq> 0"
      if z: "Im z > 0" for z
      using z by (intro eventually_frequently; simp add: eventually_neq_eval_mero_uhp)+
    have "\<not>is_pole (f / g) z" for z :: complex
    proof (cases "Im z > 0")
      case z: True
      have "mero_uhp_rel (eval_mero_uhp (f / g)) (\<lambda>z. eval_mero_uhp f z / eval_mero_uhp g z)"
        by mero_uhp_rel
      hence "zorder (eval_mero_uhp (f / g)) z = zorder (\<lambda>z. eval_mero_uhp f z / eval_mero_uhp g z) z"
        using z by (intro zorder_cong) (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
      also have "\<dots> = zorder f z - zorder g z"
        using freq z by (subst zorder_divide) (auto intro!: Meromorphic1.meromorphic_intros)
      also have "\<dots> \<ge> 0"
      proof (cases "eval_mero_uhp g z = 0")
        case True
        with assms(2)[of z] z show ?thesis
          by simp
      next
        case False
        have "zorder_mero_uhp f z \<ge> 0"
          using z by (subst zorder_mero_uhp_nonneg_iff) auto
        moreover have "zorder_mero_uhp g z = 0"
          using z False by (subst zorder_mero_uhp_eq_0_iff) auto
        ultimately show ?thesis by simp
      qed
      finally show "\<not>is_pole (f / g) z"
        using z by (subst (asm) zorder_mero_uhp_nonneg_iff) auto
    qed (auto simp: not_is_pole_eval_mero_uhp_outside)
    thus "holo_uhp (f / g)"
      by (auto simp: holo_uhp_def)
  next
    show "\<exists>L. divide.map.fourier \<midarrow>0\<rightarrow> L"
    proof (cases "eval_mero_uhp_at_cusp g = 0")
      case False
      from False have "(\<lambda>q. f.fourier q / g.fourier q) \<midarrow>0\<rightarrow> f.fourier 0 / g.fourier 0"
        by (intro tendsto_divide isContD analytic_at_imp_isCont analytic_intros) auto
      also have "?this \<longleftrightarrow> divide.map.fourier \<midarrow>0\<rightarrow> f.fourier 0 / g.fourier 0"
        using fourier_divide_eventually_eq
        by (intro tendsto_cong) (auto simp: eventually_cosparse_open_eq eq_commute)
      finally show ?thesis ..
    next
      case True
      have freq: "\<exists>\<^sub>F q in at 0. f.fourier q \<noteq> 0" "\<exists>\<^sub>F q in at 0. g.fourier q \<noteq> 0"
        by (intro eventually_frequently; simp add: f.eventually_neq_fourier g.eventually_neq_fourier)+
      have "zorder divide.map.fourier 0 = zorder (\<lambda>q. f.fourier q / g.fourier q) 0"
        using fourier_divide_eventually_eq
        by (intro zorder_cong) (auto simp: eventually_cosparse_open_eq eq_commute)
      also have "\<dots> = zorder f.fourier 0 - zorder g.fourier 0"
        using freq by (subst zorder_divide) (auto intro!: Meromorphic1.meromorphic_intros)
      also have "\<dots> \<ge> 0"
        using True assms(1,3) f.zorder_at_cusp_conv_fourier g.zorder_at_cusp_conv_fourier
        by (simp_all add: period_def)
      finally show ?thesis
        by (metis fls_subdegree_fls_to_fps fps_zero_to_fls has_laurent_expansion_imp_tendsto_0
                  has_laurent_expansion_zorder_0 insert_iff meromorphic_at_cusp meromorphic_onE
                  not_essential_has_laurent_expansion_0 of_nat_0_le_iff)
    qed
  qed
qed auto
        
end



locale modular_function = meromorphic_form f 0 G
  for f :: mero_uhp and G :: "modgrp set"
begin

sublocale weakly_modular_form_weight_0 ..

lemmas [simp del] = invariant_apply_modgrp

lemma invariant_apply_modgrp' [simp]:
  assumes "h \<in> G"
  shows   "eval_mero_uhp f (apply_modgrp h z) = eval_mero_uhp f z"
proof (cases "z = 0")
  case False
  thus ?thesis using assms
    by (simp add: invariant_apply_modgrp)
qed (auto simp: eval_mero_uhp_outside) 

lemma modular_function_minus [intro]: "modular_function (-f) G"
  unfolding modular_function_def using meromorphic_form_minus by simp

lemma modular_function_inverse [intro]: "modular_function (inverse f) G"
  unfolding modular_function_def using meromorphic_form_inverse by simp

lemma modular_function_power [intro]: "modular_function (f ^ n) G"
  unfolding modular_function_def using meromorphic_form_power[of n] by simp

lemma modular_function_power_int [intro]: "modular_function (f powi n) G"
  unfolding modular_function_def using meromorphic_form_power_int[of n] by simp

end


context modgrp_subgroup_periodic
begin

lemma modular_function_0 [intro]: "modular_function 0 G"
  unfolding modular_function_def ..

lemma modular_function_1 [intro]: "modular_function 1 G"
  unfolding modular_function_def ..

lemma modular_function_const [intro]: "modular_function (const_mero_uhp c) G"
  unfolding modular_function_def ..

end


locale modular_function_pair =
  f: modular_function f G + g: modular_function g G 
  for f g G
begin

sublocale meromorphic_form_pair f g 0 0 G ..

lemma modular_function_add [intro]: "modular_function (f + g) G"
  unfolding modular_function_def using meromorphic_form_add by simp

lemma modular_function_diff [intro]: "modular_function (f - g) G"
  unfolding modular_function_def using meromorphic_form_diff by simp

lemma modular_function_mult [intro]: "modular_function (f * g) G"
  unfolding modular_function_def using meromorphic_form_mult by simp

lemma modular_function_divide [intro]: "modular_function (f / g) G"
  unfolding modular_function_def using meromorphic_form_divide by simp

end




lemma eval_mero_uhp_at_cusp_const [simp]: "eval_mero_uhp_at_cusp (const_mero_uhp c) = c"
proof -
  interpret fourier_expansion_context "Suc 0"
    by standard auto
  interpret fourier_expansion_meromorphic "const_mero_uhp c" "Suc 0" ..
  show ?thesis by simp
qed

lemma eval_mero_uhp_at_cusp_0 [simp]: "eval_mero_uhp_at_cusp 0 = 0"
  and eval_mero_uhp_at_cusp_1 [simp]: "eval_mero_uhp_at_cusp 1 = 1"
  and eval_mero_uhp_at_cusp_of_nat [simp]: "eval_mero_uhp_at_cusp (of_nat n) = of_nat n"
  and eval_mero_uhp_at_cusp_of_int [simp]: "eval_mero_uhp_at_cusp (of_int k) = of_int k"
  and eval_mero_uhp_at_cusp_of_numeral [simp]: "eval_mero_uhp_at_cusp (numeral num) = numeral num"
  by (metis const_mero_uhp.hom_zero const_mero_uhp.hom_one const_mero_uhp.hom_of_nat
            eval_mero_uhp_at_cusp_const const_mero_uhp.hom_of_int const_mero_uhp.hom_numeral)+


context modgrp_subgroup_periodic
begin

sublocale const: modular_function "const_mero_uhp c" G
proof -
  interpret modular_function "\<langle>c\<rangle>" G
    by auto
  show "modular_function \<langle>c\<rangle> G" ..
qed

interpretation const': fourier_expansion_context "modgrp_subgroup_period G"
  by standard (rule modgrp_subgroup_period_pos)

lemma const_fourier [simp]:
  assumes "norm q < 1"
  shows   "const.fourier c q = c"
  using const'.fourier_const assms by simp

lemma not_is_pole_const_fourier [simp]: "\<not>is_pole (const.fourier c) q"
  using const'.not_is_pole_const_fourier by simp

lemma zorder_fourier_0_const [simp]:
  assumes "c \<noteq> 0"
  shows   "zorder (const.fourier c) 0 = 0"
  using const'.zorder_fourier_0_const assms by simp

end


named_theorems mform_intros

subsection \<open>Modular forms and cusp forms\<close>

subsubsection \<open>Weakly modular forms\<close>
definition WMForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("WMForms[_,_]") where
  "WMForms G k = {f. weakly_modular_form f k G}"

abbreviation WMForms' :: "int \<Rightarrow> mero_uhp set" ("WMForms[_]") where
  "WMForms' \<equiv> WMForms UNIV"

lemma weakly_modular_form_WMForms [dest]: "f \<in> WMForms[G, k] \<Longrightarrow> weakly_modular_form f k G"
  by (auto simp: WMForms_def)

context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

interpretation modgrp_subgroup_periodic G
  by (rule G)

lemma WMForms_0 [mform_intros, simp, intro]: "0 \<in> WMForms[G, k]"
  by (auto simp: WMForms_def)

lemma WMForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> WMForms[G, 0]"
  by (auto simp: WMForms_def)

lemma WMForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> WMForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma WMForms_1 [mform_intros, simp, intro]: "1 \<in> WMForms[G, 0]"
  and WMForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> WMForms[G, 0]"
  and WMForms_of_int [mform_intros, simp, intro]: "of_int m \<in> WMForms[G, 0]"
  and WMForms_of_real [mform_intros, simp, intro]: "of_real x \<in> WMForms[G, 0]"
  and WMForms_numeral [mform_intros, simp, intro]: "numeral num \<in> WMForms[G, 0]"
  by (rule WMForms_is_const; simp; fail)+

lemma WMForms_uminus [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> -f \<in> WMForms[G, k]"
  by (auto simp: WMForms_def intro!: weakly_modular_form.weakly_modular_form_minus
         weakly_modular_form.weakly_modular_form_inverse)

lemma WMForms_add [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, k] \<Longrightarrow> f + g \<in> WMForms[G, k]"
  by (auto simp: WMForms_def weakly_modular_form_pair_def
           intro!: weakly_modular_form_pair.weakly_modular_form_add)

lemma WMForms_diff [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, k] \<Longrightarrow> f - g \<in> WMForms[G, k]"
  by (auto simp: WMForms_def weakly_modular_form_pair_def
           intro!: weakly_modular_form_pair.weakly_modular_form_diff)

lemma WMForms_mult [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, m - k] \<Longrightarrow> f * g \<in> WMForms[G, m]"
  using weakly_modular_form_pair.weakly_modular_form_mult[of f g k "m - k"]
  by (auto simp: WMForms_def weakly_modular_form_pair_def)

lemma WMForms_inverse [mform_intros]:
  assumes "f \<in> WMForms[G, m]" "f \<noteq> 0" "m = -l"
  shows   "inverse f \<in> WMForms[G, l]"
  using weakly_modular_form.weakly_modular_form_inverse[of f m G] assms
  by (auto simp: WMForms_def)

lemma WMForms_divide [mform_intros]:
  assumes "f \<in> WMForms[G, k]" "g \<in> WMForms[G, k-m]" "g \<noteq> 0"
  shows   "f / g \<in> WMForms[G, m]"
  using weakly_modular_form_pair.weakly_modular_form_divide[of f g k "k - m"] assms
  by (auto simp: WMForms_def weakly_modular_form_pair_def)

lemma WMForms_power [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f ^ n \<in> WMForms[G, m]"
  using weakly_modular_form.weakly_modular_form_power[of f k G n] by (auto simp: WMForms_def)

lemma WMForms_power_int [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f powi n \<in> WMForms[G, m]"
  using weakly_modular_form.weakly_modular_form_power_int[of f k G n] by (auto simp: WMForms_def)
   
lemma WMForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> WMForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> WMForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros)

lemma WMForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> WMForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> WMForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros)

end


subsubsection \<open>Meromorphic forms\<close>

definition MeForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("MeForms[_,_]") where
  "MeForms G k = {f. meromorphic_form f k G}"

abbreviation MeForms' :: "int \<Rightarrow> mero_uhp set" ("MeForms[_]") where
  "MeForms' \<equiv> MeForms UNIV"

lemma meromorphic_form_MeForms [dest]: "f \<in> MeForms[G, k] \<Longrightarrow> meromorphic_form f k G"
  by (auto simp: MeForms_def)


context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

interpretation modgrp_subgroup_periodic G
  by (fact G)

lemma MeForms_0 [mform_intros, simp, intro]: "0 \<in> MeForms[G, k]"
  by (auto simp: MeForms_def)

lemma MeForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> MeForms[G, 0]"
  by (auto simp: MeForms_def)

lemma MeForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> MeForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma MeForms_1 [mform_intros, simp, intro]: "1 \<in> MeForms[G, 0]"
  and MeForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> MeForms[G, 0]"
  and MeForms_of_int [mform_intros, simp, intro]: "of_int m \<in> MeForms[G, 0]"
  and MeForms_of_real [mform_intros, simp, intro]: "of_real x \<in> MeForms[G, 0]"
  and MeForms_numeral [mform_intros, simp, intro]: "numeral num \<in> MeForms[G, 0]"
  by (rule MeForms_is_const; simp; fail)+

end

lemma MeForms_uminus [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> -f \<in> MeForms[G, k]"
  by (auto simp: MeForms_def intro!: meromorphic_form.meromorphic_form_minus
         meromorphic_form.meromorphic_form_inverse)

lemma MeForms_add [mform_intros]:
  "f \<in> MeForms[G, k] \<Longrightarrow> g \<in> MeForms[G, k] \<Longrightarrow> f + g \<in> MeForms[G, k]"
  by (auto simp: MeForms_def meromorphic_form_pair_def
           intro!: meromorphic_form_pair.meromorphic_form_add)

lemma MeForms_diff [mform_intros]:
  "f \<in> MeForms[G, k] \<Longrightarrow> g \<in> MeForms[G, k] \<Longrightarrow> f - g \<in> MeForms[G, k]"
  by (auto simp: MeForms_def meromorphic_form_pair_def
           intro!: meromorphic_form_pair.meromorphic_form_diff)

lemma MeForms_mult [mform_intros]:
  "f \<in> MeForms[G, k] \<Longrightarrow> g \<in> MeForms[G, m - k] \<Longrightarrow> f * g \<in> MeForms[G, m]"
  using meromorphic_form_pair.meromorphic_form_mult[of f g k "m - k"]
  by (auto simp: MeForms_def meromorphic_form_pair_def)

lemma MeForms_inverse [mform_intros]:
  assumes "f \<in> MeForms[G, m]" "f \<noteq> 0" "m = -l"
  shows   "inverse f \<in> MeForms[G, l]"
  using meromorphic_form.meromorphic_form_inverse[of f m G] assms
  by (auto simp: MeForms_def)

lemma MeForms_divide [mform_intros]:
  assumes "f \<in> MeForms[G, k]" "g \<in> MeForms[G, k-m]" "g \<noteq> 0"
  shows   "f / g \<in> MeForms[G, m]"
  using meromorphic_form_pair.meromorphic_form_divide[of f g k "k - m"] assms
  by (auto simp: MeForms_def meromorphic_form_pair_def)

lemma MeForms_power [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f ^ n \<in> MeForms[G, m]"
  using meromorphic_form.meromorphic_form_power[of f k G n] by (auto simp: MeForms_def)

lemma MeForms_power_int [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f powi n \<in> MeForms[G, m]"
  using meromorphic_form.meromorphic_form_power_int[of f k G n] by (auto simp: MeForms_def)


context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

lemma MeForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MeForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> MeForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros G)

lemma MeForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MeForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> MeForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros G)

end


subsubsection \<open>Modular functions\<close>

abbreviation MFuns :: "modgrp set \<Rightarrow> mero_uhp set" ("MFuns[_]") where
  "MFuns G \<equiv> MeForms G 0"

abbreviation MFuns' :: "mero_uhp set" ("MFuns") where
  "MFuns' \<equiv> MFuns[UNIV]"

lemma MFuns_altdef: "MFuns[G] = {f. modular_function f G}"
  by (simp add: MeForms_def modular_function_def)

lemma modular_function_MFuns [dest]: "f \<in> MFuns[G] \<Longrightarrow> modular_function f G"
  by (auto simp: MFuns_altdef)


subsubsection \<open>(Entire) modular forms\<close>

definition MForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("MForms[_,_]") where
  "MForms G k = {f. modular_form f k G}"

abbreviation MForms' :: "int \<Rightarrow> mero_uhp set" ("MForms[_]") where
  "MForms' \<equiv> MForms UNIV"

lemma modular_form_MForms [dest]: "f \<in> MForms[G, k] \<Longrightarrow> modular_form f k G"
  by (auto simp: MForms_def)


context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

interpretation modgrp_subgroup_periodic G
  by (fact G)

lemma MForms_0 [mform_intros, simp, intro]: "0 \<in> MForms[G, k]"
  by (auto simp: MForms_def)

lemma MForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> MForms[G, 0]"
  by (auto simp: MForms_def)

lemma MForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> MForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma MForms_1 [mform_intros, simp, intro]: "1 \<in> MForms[G, 0]"
  and MForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> MForms[G, 0]"
  and MForms_of_int [mform_intros, simp, intro]: "of_int m \<in> MForms[G, 0]"
  and MForms_of_real [mform_intros, simp, intro]: "of_real x \<in> MForms[G, 0]"
  and MForms_numeral [mform_intros, simp, intro]: "numeral num \<in> MForms[G, 0]"
  by (rule MForms_is_const; simp; fail)+

end

lemma MForms_uminus [mform_intros]: "f \<in> MForms[G, k] \<Longrightarrow> -f \<in> MForms[G, k]"
  by (auto simp: MForms_def intro!: modular_form.modular_form_minus modular_form.modular_form_minus)

lemma MForms_add [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> MForms[G, k] \<Longrightarrow> f + g \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_pair_def
           intro!: modular_form_pair.modular_form_add)

lemma MForms_diff [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> MForms[G, k] \<Longrightarrow> f - g \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_pair_def
           intro!: modular_form_pair.modular_form_diff)

lemma MForms_mult [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> MForms[G, m - k] \<Longrightarrow> f * g \<in> MForms[G, m]"
  using modular_form_pair.modular_form_mult[of f g k "m - k"]
  by (auto simp: MForms_def modular_form_pair_def)

lemma MForms_power [mform_intros]: "f \<in> MForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f ^ n \<in> MForms[G, m]"
  using modular_form.modular_form_power[of f k G n] by (auto simp: MForms_def)

lemma MForms_power_int [mform_intros]: "n \<ge> 0 \<Longrightarrow> f \<in> MForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> f powi n \<in> MForms[G, m]"
  using modular_form.modular_form_power_int[of f k G n] by (auto simp: MForms_def)

context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

lemma MForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> MForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros G)

lemma MForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> MForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros G)

end

lemma MForms_divide [mform_intros]:
  fixes G
  defines "period \<equiv> modgrp_subgroup_period G"
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k - m]" "k \<ge> l"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> eval_mero_uhp g z = 0 \<Longrightarrow> zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "eval_mero_uhp_at_cusp g = 0 \<Longrightarrow> zorder_at_cusp period f \<ge> zorder_at_cusp period g"
  shows   "f / g \<in> MForms[G, m]"
  unfolding MForms_def
proof safe
  interpret f: modular_form f k G
    using assms(2) by auto
  interpret g: modular_form g "k - m" G
    using assms(3) by auto
  interpret modular_form_pair f g  k "k - m" G ..
  have "modular_form (f / g) (k - (k - m)) G"
    by (rule modular_form_divide) (use assms in auto)
  thus "modular_form (f / g) m G"
    by simp
qed

lemma eval_mero_uhp_at_cusp_uminus [simp]:
  assumes "f \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_cusp (-f) = -eval_mero_uhp_at_cusp f"
proof -
  interpret modular_form f k G
    using assms by auto
  interpret minus: modular_form "-f" k G
    by (rule modular_form_minus)
  show ?thesis
    by (simp add: minus.eval_at_cusp_conv_fourier fourier_minus_eq)
qed

lemma eval_mero_uhp_at_cusp_add [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_cusp (f + g) = eval_mero_uhp_at_cusp f + eval_mero_uhp_at_cusp g"
proof -
  interpret f: modular_form f k G
    using assms by auto
  interpret g: modular_form g k G
    using assms by auto
  interpret fg: modular_form_pair f g k k G ..
  interpret add: modular_form "f + g" k G
    by (rule fg.modular_form_add) auto
  show ?thesis
    by (simp add: fg.add.eval_at_cusp_conv_fourier fg.fourier_add_eq)
qed

lemma eval_mero_uhp_at_cusp_diff [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_cusp (f - g) = eval_mero_uhp_at_cusp f - eval_mero_uhp_at_cusp g"
proof -
  have "eval_mero_uhp_at_cusp (f + (-g)) = eval_mero_uhp_at_cusp f - eval_mero_uhp_at_cusp g"
    using assms by (subst eval_mero_uhp_at_cusp_add) (auto intro: mform_intros)
  thus ?thesis
    by simp
qed

lemma eval_mero_uhp_at_cusp_mult [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k']"
  shows   "eval_mero_uhp_at_cusp (f * g) = eval_mero_uhp_at_cusp f * eval_mero_uhp_at_cusp g"
proof -
  interpret f: modular_form f k G
    using assms by auto
  interpret g: modular_form g k' G
    using assms by auto
  interpret fg: modular_form_pair f g k k' G ..
  interpret mult: modular_form "f * g" "k + k'" G
    by (rule fg.modular_form_mult)
  show ?thesis
    by (simp add: fg.mult.eval_at_cusp_conv_fourier fg.fourier_mult_eq)
qed

lemma eval_mero_uhp_at_cusp_power [simp]:
  assumes [mform_intros]: "f \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_cusp (f ^ n) = eval_mero_uhp_at_cusp f ^ n"
proof (induction n)
  case (Suc n)
  show ?case
    unfolding power_Suc
    by (subst eval_mero_uhp_at_cusp_mult) (auto intro!: mform_intros simp: Suc.IH)
qed auto

lemma eval_mero_uhp_at_cusp_power_int [simp]:
  assumes "f \<in> MForms[G, k]" "n \<ge> 0"
  shows   "eval_mero_uhp_at_cusp (f powi n) = eval_mero_uhp_at_cusp f powi n"
  using assms by (auto simp: power_int_def)

lemma zorder_MForms_nonneg [simp, intro]:
  assumes "f \<in> MForms[G, k]" "Im z > 0" "f \<noteq> 0"
  shows   "zorder f  z \<ge> 0"
proof -
  interpret modular_form f k G
    using assms by auto
  show ?thesis
    using assms by auto
qed

lemma zorder_at_cusp_nonneg [simp, intro]:
  assumes "f \<in> MForms[G, k]" "f \<noteq> 0"
  shows   "zorder_at_cusp (modgrp_subgroup_period G) f \<ge> 0"
proof -
  interpret modular_form f k G
    using assms by auto
  have "zorder_at_cusp (modgrp_subgroup_period G) f = zorder fourier 0"
    using assms zorder_at_cusp_conv_fourier by simp
  also have "\<dots> \<ge> 0"
    using assms by simp
  finally show ?thesis .
qed




subsubsection \<open>Cusp forms\<close>

definition CForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("CForms[_,_]") where
  "CForms G k = {f\<in>MForms G k. eval_mero_uhp_at_cusp f = 0}"

abbreviation CForms' :: "int \<Rightarrow> mero_uhp set" ("CForms[_]") where
  "CForms' \<equiv> CForms UNIV"

lemma CForms_MForms [dest]: "f \<in> CForms[G, k] \<Longrightarrow> f \<in> MForms[G, k]"
  by (auto simp: CForms_def)

lemma zorder_at_cusp_CForms:
  assumes "f \<in> CForms[G, k]" "f \<noteq> 0"
  shows "zorder_at_cusp (modgrp_subgroup_period G) f > 0"
proof -
  interpret modular_form f k G
    using assms by auto
  have "zorder_at_cusp period f = zorder fourier 0"  
    using zorder_at_cusp_conv_fourier \<open>f \<noteq> 0\<close> by simp
  also have "\<dots> > 0"
    using assms unfolding CForms_def by auto
  finally show ?thesis by simp
qed

context
  fixes G
  assumes G: "modgrp_subgroup_periodic G"
begin

interpretation modgrp_subgroup_periodic G
  by (fact G)

lemma CForms_0 [mform_intros, simp, intro]: "0 \<in> CForms[G, k]"
  using G by (auto simp: CForms_def)

end

lemma CForms_add [mform_intros]:
  assumes "f \<in> CForms[G, k]" "g \<in> CForms[G, k]"
  shows   "f + g \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: mform_intros)

lemma CForms_uminus [mform_intros]:
  assumes "f \<in> CForms[G, k]"
  shows   "-f \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: mform_intros)

lemma CForms_diff [mform_intros]:
  assumes "f \<in> CForms[G, k]" "g \<in> CForms[G, k]"
  shows   "f - g \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: mform_intros)

lemma CForms_cmult [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> CForms[G, m - k] \<Longrightarrow> f * g \<in> CForms[G, m]"
  by (auto simp: CForms_def intro: mform_intros)

lemma CForms_power [mform_intros]: "f \<in> CForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> n > 0 \<Longrightarrow> f ^ n \<in> CForms[G, m]"
  by (auto simp: CForms_def intro: mform_intros)

lemma CForms_power_int [mform_intros]: "f \<in> CForms[G, k] \<Longrightarrow> m = k * n \<Longrightarrow> n > 0 \<Longrightarrow> f powi n \<in> CForms[G, m]"
  by (auto simp: power_int_def intro!: CForms_power)

lemma CForms_sum [mform_intros]:
  "modgrp_subgroup_periodic G \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> CForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> CForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros)

lemma
  assumes "modgrp_subgroup_periodic G"
  shows subspace_WMForms: "mero_uhp.subspace (WMForms[G, k])"
    and subspace_MeForms: "mero_uhp.subspace (MeForms[G, k])"
    and subspace_MForms: "mero_uhp.subspace (MForms[G, k])"
    and subspace_CForms: "mero_uhp.subspace (CForms[G, k])"
  unfolding mero_uhp.subspace_def by (auto intro!: mform_intros assms)

(* TODO Move *)
lemma Eisenstein_G_apply_modgrp [simp]:
  "Eisenstein_G k (apply_modgrp h z) = modgrp_factor h z ^ k * Eisenstein_G k z"
proof (cases "Im z = 0")
  case z: False
  interpret std_lattice z
    using z by unfold_locales (auto simp: complex_is_Real_iff)
  interpret unimodular_transform_lattice 1 z "modgrp_a h" "modgrp_b h" "modgrp_c h" "modgrp_d h"
    rewrites "modgrp.as_modgrp = (\<lambda>x. x)" and "modgrp.\<phi> = apply_modgrp"
      by unfold_locales (use z in auto)

  have "Eisenstein_G k (apply_modgrp h z) = Eisenstein_G k (\<omega>2' / \<omega>1')"
    by (simp add: \<omega>2'_def \<omega>1'_def modgrp.\<phi>_def moebius_def)
  also have "\<dots> = modgrp_factor h z powi int k * transformed.eisenstein_series k"
    by (subst transformed.eisenstein_series_conv_Eisenstein_G)
       (auto simp: \<omega>1'_def power_int_minus field_simps modgrp_factor_def)
  also have "\<dots> = modgrp_factor h z powi int k * eisenstein_series k"
    by simp
  also have "\<dots> = modgrp_factor h z powi int k * Eisenstein_G k z"
    by (subst eisenstein_series_conv_Eisenstein_G) auto
  finally show "Eisenstein_G k (apply_modgrp h z) =
                  modgrp_factor h z ^ k * Eisenstein_G k z"
    by simp
next
  case True
  thus ?thesis
    by (cases "k > 0") (auto simp: complex_is_Real_iff)
qed

lemma Eisenstein_g2_apply_modgrp [simp]:
  "Eisenstein_g2 (apply_modgrp h z) = modgrp_factor h z ^ 4 * Eisenstein_g2 z"
  by (simp add: Eisenstein_g2_def algebra_simps)

lemma Eisenstein_g3_apply_modgrp [simp]:
  "Eisenstein_g3 (apply_modgrp h z) = modgrp_factor h z ^ 6 * Eisenstein_g3 z"
  by (simp add: Eisenstein_g3_def algebra_simps)

lemma modular_discr_apply_modgrp [simp]:
  "modular_discr (apply_modgrp h z) = modgrp_factor h z ^ 12 * modular_discr z"
  by (simp add: modular_discr_def algebra_simps)

lemma Klein_J_apply_modgrp [simp]:
  "Klein_J (apply_modgrp h z) = Klein_J z"
  by (cases "z \<in> \<real>") (simp_all add: Klein_J_def algebra_simps complex_is_Real_iff)

lemmas [analytic_intros del] = constant_on_imp_analytic_on
lemmas [meromorphic_intros del] = constant_on_imp_meromorphic_on

locale weakly_modular_form_explicit = modgrp_subgroup_periodic G for G +
  fixes f :: "complex \<Rightarrow> complex" and weight :: int
  assumes meromorphic_aux: "f meromorphic_on {z. Im z > 0}"
  assumes invariant_aux: 
    "\<And>z. Im z > 0 \<Longrightarrow> h \<in> G \<Longrightarrow> f (apply_modgrp h z) = modgrp_factor h z powi weight * f z"
begin

sublocale weakly_modular_form "mero_uhp f" weight G
proof
  fix h :: modgrp assume h: "h \<in> G"
  show "compose_modgrp_mero_uhp (mero_uhp f) h = modgrp_factor_mero_uhp h powi weight * mero_uhp f"
  proof -
    have "mero_uhp_rel (compose_modgrp_mero_uhp (mero_uhp f) h - modgrp_factor_mero_uhp h powi weight * mero_uhp f)
            (\<lambda>z. f (apply_modgrp h z) - modgrp_factor h z powi weight * f z)"
      by mero_uhp_rel (auto intro!: meromorphic_aux)
    also have "mero_uhp_rel \<dots> (\<lambda>_. 0)"
      using h by (intro mero_uhp_relI_weak) (auto simp: invariant_aux)
    finally have "compose_modgrp_mero_uhp (mero_uhp f) h - modgrp_factor_mero_uhp h powi weight * mero_uhp f = 0"
      using mero_uhp_rel_eval_mero_uhp_0 mero_uhp_rel_imp_eq_mero_uhp mero_uhp_rel_simpI by blast
    thus ?thesis
      by simp
  qed
qed

end



locale meromorphic_form_explicit = weakly_modular_form_explicit +
  fixes F :: "complex fls"
  assumes has_expansion_at_cusp: "fourier has_laurent_expansion F"
begin

sublocale meromorphic_form "mero_uhp f" weight G
proof
  show "fourier meromorphic_on {0}"
    using has_expansion_at_cusp by (auto simp: Meromorphic1.meromorphic_on_def)
qed

lemma expansion_at_cusp_eq_0_iff: "F = 0 \<longleftrightarrow> mero_uhp f = 0"
proof
  assume [simp]: "F = 0"
  hence "eventually (\<lambda>q. fourier q = 0) (at 0)"
    using has_expansion_at_cusp by (auto simp: has_laurent_expansion_def)
  hence "frequently (\<lambda>q. fourier q = 0) (at 0)"
    by (intro eventually_frequently) auto
  thus "mero_uhp f = 0"
    using eventually_neq_fourier[of 0] by (cases "mero_uhp f = 0") (auto simp: frequently_def)
next
  assume [simp]: "mero_uhp f = 0"
  have "eventually (\<lambda>q :: complex. q \<in> ball 0 1 - {0}) (at 0)"
    by (intro eventually_at_in_open) auto
  hence "eventually (\<lambda>q. fourier q = 0) (at 0)"
    unfolding fourier_def by eventually_elim (use period_pos in \<open>auto simp: Im_cusp_q_inv_gt\<close>)
  hence "fourier has_laurent_expansion 0"
    using has_laurent_expansion_def by auto
  with has_expansion_at_cusp show "F = 0"
    using has_laurent_expansion_unique by blast
qed  

lemma zorder_at_cusp_eq: "zorder_at_cusp period (mero_uhp f) = fls_subdegree F"
proof (cases "mero_uhp f = 0")
  case True
  thus ?thesis using True expansion_at_cusp_eq_0_iff by auto
next
  case False
  thus ?thesis using False has_expansion_at_cusp expansion_at_cusp_eq_0_iff
    by (simp add: has_laurent_expansion_zorder_0 zorder_at_cusp_conv_fourier)
qed

lemma eval_at_cusp_eq:
  assumes "fls_subdegree F \<ge> 0"
  shows   "eval_mero_uhp_at_cusp (mero_uhp f) = fls_nth F 0"
proof -
  have "eval_mero_uhp_at_cusp (mero_uhp f) = fourier 0"
    by (rule eval_at_cusp_conv_fourier)
  also have "fourier 0 = fls_nth F 0"
    using has_expansion_at_cusp assms zorder_at_cusp_eq
          fourier_0_aux fourier_tendsto_0_iff has_laurent_expansion_imp_tendsto_0 by blast
  finally show ?thesis .
qed

end



locale modular_form_explicit = weakly_modular_form_explicit +
  fixes F :: "complex fps"
  assumes analytic_aux: "f analytic_on {z. Im z > 0}"
  assumes has_expansion_at_cusp: "fourier has_fps_expansion F"
begin

context
begin

interpretation mero: meromorphic_form_explicit G f weight "fps_to_fls F"
proof
  show "fourier has_laurent_expansion fps_to_fls F"
    using has_expansion_at_cusp by (simp add: has_laurent_expansion_fps)
qed

lemma zorder_at_cusp_eq: "zorder_at_cusp period (mero_uhp f) = subdegree F"
  by (simp add: mero.zorder_at_cusp_eq fls_subdegree_fls_to_fps)

lemma expansion_at_cusp_eq_0_iff: "F = 0 \<longleftrightarrow> mero_uhp f = 0"
  using mero.expansion_at_cusp_eq_0_iff by simp

lemma eval_at_cusp_eq:
  "eval_mero_uhp_at_cusp (mero_uhp f) = fps_nth F 0"
  using mero.eval_at_cusp_eq by (simp add: fls_subdegree_fls_to_fps)

end

sublocale modular_form "mero_uhp f" weight G
proof
  have "mero_uhp_rel (mero_uhp f) f"
    by mero_uhp_rel (rule meromorphic_aux)
  thus "holo_uhp (mero_uhp f)"
    by (rule holo_uhp_mero_uhp_rel_transfer) (fact analytic_aux)
  show "\<exists>L. fourier \<midarrow>0\<rightarrow> L"
    using has_expansion_at_cusp continuous_within has_fps_expansion_imp_continuous by blast
qed

lemma fourier_0 [simp]: "fourier 0 = fps_nth F 0"
  using has_expansion_at_cusp has_fps_expansion_imp_0_eq_fps_nth_0 by blast

end



context
  fixes n :: nat and z :: complex
  assumes n: "n > 0" and z: "norm z < 1"
begin

lemma fourier_expansion_fourier_const [simp]: "fourier_expansion.fourier (const_mero_uhp c) n z = c"
proof -
  interpret fourier_expansion "const_mero_uhp c" n
    by standard (use n in auto)
  show ?thesis
    using z fourier_expansion_context.fourier_const fourier_expansion_context.intro by blast
qed

lemma fourier_expansion_fourier_0 [simp]: "fourier_expansion.fourier 0 n z = 0"
  and fourier_expansion_fourier_1 [simp]: "fourier_expansion.fourier 1 n z = 1"
  and fourier_expansion_fourier_of_nat [simp]: "fourier_expansion.fourier (of_nat m) n z = of_nat m"
  and fourier_expansion_fourier_of_int [simp]: "fourier_expansion.fourier (of_int k) n z = of_int k"
  and fourier_expansion_fourier_numeral [simp]: "fourier_expansion.fourier (numeral num) n z = numeral num"
  by (metis const_mero_uhp.hom_zero const_mero_uhp.hom_one const_mero_uhp.hom_of_nat
            const_mero_uhp.hom_of_int const_mero_uhp.hom_numeral fourier_expansion_fourier_const)+

end


definition Eisenstein_G_fps_at_cusp' where
  "Eisenstein_G_fps_at_cusp' k = (if k = 0 then 1 else if odd k \<or> k < 4 then 0 else Eisenstein_G_fps_at_cusp k)"

lemma Eisenstein_G_fps_at_cusp'_0 [simp]: "Eisenstein_G_fps_at_cusp' 0 = 1"
  and Eisenstein_G_fps_at_cusp'_0' [simp]: "odd k \<or> (k > 0 \<and> k < 4) \<Longrightarrow> Eisenstein_G_fps_at_cusp' k = 0"
  and Eisenstein_G_fps_at_cusp'_even [simp]: "even k \<Longrightarrow> k \<notin> {0, 2} \<Longrightarrow> Eisenstein_G_fps_at_cusp' k = Eisenstein_G_fps_at_cusp k"
  unfolding Eisenstein_G_fps_at_cusp'_def by (auto elim: oddE)

lemma fps_nth_0_Eisenstein_G_fps_at_cusp [simp]:
  "fps_nth (Eisenstein_G_fps_at_cusp k) 0 = 2 * zeta k"
  by (simp add: Eisenstein_G_fps_at_cusp_def)

interpretation Eisenstein_G: modular_form_explicit UNIV "Eisenstein_G k" k "Eisenstein_G_fps_at_cusp' k"
  rewrites "mero_uhp (Eisenstein_G k) = \<G> k"
       and "int (subdegree (Eisenstein_G_fps_at_cusp' k)) = 0"
       and "Eisenstein_G.period = Suc 0"
proof -
  interpret weakly_modular_form_explicit UNIV "Eisenstein_G k" k
    by standard (auto intro!: meromorphic_intros simp: complex_is_Real_iff)
  show "modular_form_explicit UNIV (Eisenstein_G k) k (Eisenstein_G_fps_at_cusp' k)"
  proof
    show "fourier has_fps_expansion Eisenstein_G_fps_at_cusp' k"
    proof (cases "odd k \<or> k \<le> 2")
      case k: True
      show ?thesis
      proof (cases "k = 0")
        case True
        have [simp]: "mero_uhp (\<lambda>_. 1) = 1"
          unfolding one_mero_uhp_def const_mero_uhp_def by simp
        have ev: "eventually (\<lambda>q::complex. q \<in> ball 0 1) (nhds 0)"
          by (intro eventually_nhds_in_open) auto
        have "fourier_expansion.fourier 1 period has_fps_expansion 1 \<longleftrightarrow> (\<lambda>_. 1) has_fps_expansion (1 :: complex fps)"
          using period_pos by (intro has_fps_expansion_cong refl eventually_mono[OF ev])
                              (auto simp: Eisenstein_G_def)
        with True period_pos show ?thesis
          by (auto simp: Eisenstein_G_def Eisenstein_G_fps_at_cusp'_def)
      next
        case False
        have [simp]: "mero_uhp (\<lambda>_. 0) = 0"
          unfolding zero_mero_uhp_def const_mero_uhp_def by simp
        have *: "Eisenstein_G k = (\<lambda>_. 0)"
        proof (cases "k = 1 \<or> k = 2")
          case True
          thus ?thesis
            by (auto simp: Eisenstein_G_def)
        qed (use k \<open>k \<noteq> 0\<close> in auto)
        have ev: "eventually (\<lambda>q::complex. q \<in> ball 0 1) (nhds 0)"
          by (intro eventually_nhds_in_open) auto
        have "fourier_expansion.fourier 0 period has_fps_expansion 0 \<longleftrightarrow> (\<lambda>_. 0) has_fps_expansion (0 :: complex fps)"
          using period_pos by (intro has_fps_expansion_cong refl eventually_mono[OF ev])
                              (auto simp: Eisenstein_G_def)
        with * period_pos \<open>k \<noteq> 0\<close> k show ?thesis
          by (auto simp: Eisenstein_G_def Eisenstein_G_fps_at_cusp'_def)
      qed
    next
      case False
      interpret Eisenstein_G_even k
        by standard (use False in \<open>auto simp: not_le\<close>)
      show ?thesis using False has_fps_expansion_at_cusp unfolding G_modform_def
        by (auto simp add: Eisenstein_G_fps_at_cusp'_def)
    qed
  qed (auto intro!: analytic_intros simp: complex_is_Real_iff)
  have "subdegree (Eisenstein_G_fps_at_cusp' k) = 0"
  proof (cases "odd k \<or> k < 4")
    case False
    thus ?thesis using zeta_Re_gt_1_nonzero[of "of_nat k"]                  
      by (intro subdegreeI) (auto simp: Eisenstein_G_fps_at_cusp'_def Eisenstein_G_fps_at_cusp_def)
  qed (simp_all add: Eisenstein_G_fps_at_cusp'_def)
  thus "int (subdegree (Eisenstein_G_fps_at_cusp' k)) = 0"
    by simp
qed (simp_all add: G_modform_def)

lemma eval_at_cusp_G:
   "eval_mero_uhp_at_cusp (\<G> k) = (if k = 0 then 1 else if odd k \<or> k < 4 then 0 else 2 * zeta k)"
  using Eisenstein_G.eval_at_cusp_eq
  by (auto simp: Eisenstein_G_fps_at_cusp'_def Eisenstein_G_fps_at_cusp_def)

lemma eval_at_cusp_G' [simp]:
  "eval_mero_uhp_at_cusp (\<G> 0) = 1"
  "odd k \<or> (k > 0 \<and> k < 4) \<Longrightarrow> eval_mero_uhp_at_cusp (\<G> k) = 0"
  "even k \<Longrightarrow> k \<notin> {0, 2} \<Longrightarrow> eval_mero_uhp_at_cusp (\<G> k) = 2 * zeta k"
  by (subst eval_at_cusp_G; (auto elim: oddE)[])+  

interpretation modular_discr: modular_form_explicit UNIV modular_discr 12 fps_modular_discr
  rewrites "mero_uhp modular_discr = \<Delta>" and
    "int (subdegree fps_modular_discr) = 1" and
    "fps_nth fps_modular_discr 0 = 0"
proof -
  interpret weakly_modular_form_explicit UNIV modular_discr 12
    by standard (auto intro!: meromorphic_intros simp: complex_is_Real_iff)
  show "modular_form_explicit UNIV modular_discr 12 fps_modular_discr"
  proof
    show "fourier has_fps_expansion fps_modular_discr"
      using modular_discr_has_fps_expansion_at_cusp by (simp add: modular_discr_modform_def)
  qed (auto intro!: analytic_intros simp: complex_is_Real_iff)
  define F where "F = Abs_fps (\<lambda>n. complex_of_int (ramanujan_tau n))"
  have F: "fps_nth F 0 = 0" "fps_nth F (Suc 0) = 1"
    by (simp_all add: ramanujan_tau_1 F_def)
  have "subdegree F = 1"
    by (rule subdegreeI) (auto simp: F)
  hence "subdegree (fps_const (complex_of_real ((2 * pi) ^ 12)) * F) = 1"
    by (subst subdegree_mult) auto
  thus "int (subdegree fps_modular_discr) = 1"
    by (simp add: F_def fps_modular_discr_def)
qed (simp_all add: modular_discr_modform_def fps_modular_discr_def)

interpretation Klein_J: meromorphic_form_explicit UNIV Klein_J 0 "fls_const (1 / 12 ^ 3) * fls_Klein_j"
  rewrites "mero_uhp Klein_J = \<J>" and
    "fls_subdegree (fls_const (1 / 12 ^ 3) * fls_Klein_j) = -1"
proof -
  interpret weakly_modular_form_explicit UNIV Klein_J 0
    by standard (auto intro!: meromorphic_intros simp: complex_is_Real_iff)
  show "meromorphic_form_explicit UNIV Klein_J 0 (fls_const (1 / 12 ^ 3) * fls_Klein_j)"
  proof
    show "fourier has_laurent_expansion (fls_const (1 / 12 ^ 3) * fls_Klein_j)"
      using Klein_J_has_laurent_expansion_at_cusp by (simp add: J_modform_def)
  qed
qed (simp_all add: J_modform_def)

interpretation Klein_J: modular_function \<J> UNIV
  rewrites "mero_uhp Klein_J = \<J>"
  by unfold_locales (simp_all add: J_modform_def)

lemmas [simp] = modular_discr.eval_at_cusp_eq

lemmas [simp del] = Eisenstein_G.eval_at_cusp_eq

lemma zorder_at_cusp_G [simp]: "zorder_at_cusp (Suc 0) (\<G> k) = 0"
  using Eisenstein_G.zorder_at_cusp_eq by simp

lemma zorder_at_cusp_modular_discr [simp]: "zorder_at_cusp (Suc 0) \<Delta> = 1"
  using modular_discr.zorder_at_cusp_eq by simp

lemma zorder_at_cusp_J [simp]: "zorder_at_cusp (Suc 0) \<J> = -1"
  using Klein_J.zorder_at_cusp_eq by simp


lemma J_in_MFuns [mform_intros]: "\<J> \<in> MFuns"
  unfolding MeForms_def by (simp add: Klein_J.meromorphic_form_axioms)

lemma G_in_MForms [mform_intros]: "\<G> k \<in> MForms[k]"
  unfolding MForms_def by (simp add: Eisenstein_G.modular_form_axioms)

lemma G_in_MForms' [mform_intros]: "int k = k' \<Longrightarrow> \<G> k \<in> MForms[k']"
  using G_in_MForms[of k] by simp

lemma modular_discr_in_MForms [mform_intros]: "\<Delta> \<in> MForms[12]"
  unfolding MForms_def by (simp add: modular_discr.modular_form_axioms)

lemma modular_discr_in_MForms' [mform_intros]: "k = 12 \<Longrightarrow> \<Delta> \<in> MForms[k]"
  using modular_discr_in_MForms by simp

lemma modular_discr_in_CForms [mform_intros]: "\<Delta> \<in> CForms[12]"
  unfolding CForms_def by (auto intro!: mform_intros)

lemma modular_discr_in_CForms' [mform_intros]: "k = 12 \<Longrightarrow> \<Delta> \<in> CForms[k]"
  unfolding CForms_def by (auto intro!: mform_intros)

lemma G_modform_eq_0_iff [simp]: "\<G> k = 0 \<longleftrightarrow> k = 2 \<or> odd k"
proof -
  have "\<G> k = 0 \<longleftrightarrow> Eisenstein_G_fps_at_cusp' k = 0"
    using Eisenstein_G.expansion_at_cusp_eq_0_iff[of k] by simp
  also have "\<dots> \<longleftrightarrow> k = 2 \<or> odd k"
    by (auto simp: Eisenstein_G_fps_at_cusp'_def)
  finally show ?thesis .
qed    

lemma modular_discr_modform_neq_0 [simp]: "\<Delta> \<noteq> 0"
proof
  assume *: "\<Delta> = 0"
  have "modular_discr \<i> \<noteq> 0"
    by auto
  also have "modular_discr \<i> = eval_mero_uhp \<Delta> \<i>"
    by (subst eval_mero_uhp_modular_discr) auto
  also have "\<dots> = 0"
    by (simp add: *)
  finally show False
    by simp
qed

lemma J_modform_neq_0 [simp]: "\<J> \<noteq> 0"
proof
  assume *: "\<J> = 0"
  have "Klein_J \<i> \<noteq> 0"
    by auto
  also have "Klein_J \<i> = eval_mero_uhp \<J> \<i>"
    by (subst eval_mero_uhp_J) auto
  also have "\<dots> = 0"
    by (simp add: *)
  finally show False
    by simp
qed


subsection \<open>Recurrences for \<^term>\<open>\<G>\<close>\<close>

lemma G_modform_reduce_aux:
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * of_nat n + 1) * (of_nat n - 3) * (2 * of_nat n - 1)"
  shows "\<G> (2*n) = \<langle>3 / C\<rangle> * (\<Sum>i=1..n-3. of_nat (2 * i + 1) * \<G> (2 * i + 2) *
                               (of_nat (2 * n - 2 * i - 3) * \<G> (2 * n - 2 * i - 2)))" (is "_ = ?rhs")
proof -
  have "mero_uhp_rel (\<G> (2*n) - \<langle>3 / C\<rangle> * (\<Sum>i=1..n-3. of_nat (2 * i + 1) * \<G> (2 * i + 2) *
                      (of_nat (2 * n - 2 * i - 3) * \<G> (2 * n - 2 * i - 2))))
                     (\<lambda>z. Eisenstein_G (2*n) z - 3 / C * (\<Sum>i=1..n-3. of_nat (2 * i + 1) * Eisenstein_G (2 * i + 2) z *
                               (of_nat (2 * n - 2 * i - 3) * Eisenstein_G (2 * n - 2 * i - 2) z)))"
    by mero_uhp_rel
  also have "\<dots> = (\<lambda>z. eval_mero_uhp 0 z)"
    by (subst Eisenstein_G_reduce_aux[OF assms(1)]) (simp add: C_def)
  finally have "\<G> (2*n) - ?rhs = 0"
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
  thus ?thesis
    by simp
qed

lemma G_modform_reduce_Bit0 [eisenstein_series_reduce]:
  fixes n' :: num
  defines "n \<equiv> numeral n'"
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * of_nat n + 1) * (of_nat n - 3) * (2 * of_nat n - 1)"
  shows "\<G> (numeral (num.Bit0 n')) = 
           \<langle>3 / C\<rangle> * (\<Sum>i=1..n-3. of_nat (2 * i + 1) * \<G> (2 * i + 2) *
                               (of_nat (2 * n - 2 * i - 3) * \<G> (2 * n - 2 * i - 2)))"
proof -
  have *: "numeral (num.Bit0 n') = 2 * n"
    by (simp add: n_def)
  show ?thesis
    unfolding * C_def by (rule G_modform_reduce_aux) (use assms in auto)
qed

lemma G_modform_odd_eq_0 [simp]: "odd n \<Longrightarrow> \<G> n = 0"
  by (simp add: G_modform_def flip: zero_mero_uhp_def const_mero_uhp_def)

lemma Eisenstein_G_reduce_Bit1 [simp]: "\<G> (numeral (num.Bit1 n)) z = 0"
  by simp

context
  notes [simp] = hom_distribs
begin

lemma G8_modform_eq: "\<G> 8 = 3 / 7 * \<G> 4 ^ 2"
  by eisenstein_series_reduce

lemma G10_modform_eq: "\<G> 10 = 5 / 11 * \<G> 4 * \<G> 6"
  by eisenstein_series_reduce

lemma G12_modform_eq: "\<G> 12 = 18 / 143 * \<G> 4 ^ 3 + 25 / 143 * \<G> 6 ^ 2"
  by eisenstein_series_reduce

lemma G14_modform_eq: "\<G> 14 = 30 / 143 * \<G> 4 ^ 2 * \<G> 6"
  by eisenstein_series_reduce

lemma G14_modform_eq': "\<G> 14 = 6 / 13 * \<G> 4 * \<G> 10"
  by eisenstein_series_reduce

lemma G14_modform_eq'': "\<G> 14 = 70 / 143 * \<G> 6 * \<G> 8"
  by eisenstein_series_reduce

lemma G16_modform_eq: "\<G> 16 = 27225 / 668525 * \<G> 4 ^ 4 + 300 / 2431 * \<G> 4 * \<G> 6 ^ 2"
  by eisenstein_series_reduce

lemma G18_modform_eq: "\<G> 18 = 3915 / 46189 * \<G> 4 ^ 3 * \<G> 6 + 2750 / 92378 * \<G> 6 ^ 3"
  by eisenstein_series_reduce

end

end