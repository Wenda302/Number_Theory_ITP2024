theory More_Analysis imports "HOL-Analysis.Analysis"
begin

subsection \<open>Misc\<close>

(*TODO: move to the distribution*)

lemma analytic_on_gbinomial [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>w. f w gchoose n) analytic_on A"
  unfolding gbinomial_prod_rev by (intro analytic_intros) auto

lemma analytic_on_ln [analytic_intros]:
  assumes "f analytic_on A" "f ` A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {}"
  shows   "(\<lambda>w. ln (f w)) analytic_on A"
proof -
  have *: "ln analytic_on (-\<real>\<^sub>\<le>\<^sub>0)"
    by (subst analytic_on_open) (auto intro!: holomorphic_intros)
  have "(ln \<circ> f) analytic_on A"
    by (rule analytic_on_compose_gen[OF assms(1) *]) (use assms(2) in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_scaleR [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. x *\<^sub>R f w) analytic_on A"
  by (auto simp: scaleR_conv_of_real intro!: analytic_intros)

lemma analytic_on_rGamma [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. rGamma (f w)) analytic_on A"
  using analytic_on_compose[OF _ analytic_rGamma, of f A] by (simp add: o_def)

lemma analytic_on_ln_Gamma [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>\<^sub>\<le>\<^sub>0) \<Longrightarrow> (\<lambda>w. ln_Gamma (f w)) analytic_on A"
  by (rule analytic_on_compose[OF _ analytic_ln_Gamma, unfolded o_def]) (auto simp: o_def)

lemma analytic_on_sin [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. sin (f w)) analytic_on A"
  and analytic_on_cos [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. cos (f w)) analytic_on A"
  and analytic_on_sinh [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. sinh (f w)) analytic_on A"
  and analytic_on_cosh [analytic_intros]: "f analytic_on A \<Longrightarrow> (\<lambda>w. cosh (f w)) analytic_on A"
  unfolding sin_exp_eq cos_exp_eq sinh_def cosh_def
  by (auto intro!: analytic_intros)

lemma analytic_on_tan [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> cos (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. tan (f w)) analytic_on A"
  and analytic_on_cot [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> sin (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. cot (f w)) analytic_on A"
  and analytic_on_tanh [analytic_intros]:
        "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> cosh (f z) \<noteq> 0) \<Longrightarrow> (\<lambda>w. tanh (f w)) analytic_on A"
  unfolding tan_def cot_def tanh_def by (auto intro!: analytic_intros)

lemma has_field_derivative_unique:
  assumes "(f has_field_derivative f'1) (at x within A)"
  assumes "(f has_field_derivative f'2) (at x within A)"
  assumes "at x within A \<noteq> bot"
  shows   "f'1 = f'2"
  using assms unfolding has_field_derivative_iff  using tendsto_unique by blast

lemma has_derivative_bot [intro]: "bounded_linear f' \<Longrightarrow> (f has_derivative f') bot"
  by (auto simp: has_derivative_def)

lemma has_field_derivative_bot [simp, intro]: "(f has_field_derivative f') bot"
  by (auto simp: has_field_derivative_def intro!: has_derivative_bot bounded_linear_mult_right)

lemma Nats_nonempty [simp]: "\<nat> \<noteq> {}"
  unfolding Nats_def by auto

lemma Polygamma_plus_of_nat:
  assumes "\<forall>k<m. z \<noteq> -of_nat k"
  shows   "Polygamma n (z + of_nat m) =
             Polygamma n z + (-1) ^ n * fact n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n)"
  using assms
proof (induction m)
  case (Suc m)
  have "Polygamma n (z + of_nat (Suc m)) = Polygamma n (z + of_nat m + 1)"
    by (simp add: add_ac)
  also have "\<dots> = Polygamma n (z + of_nat m) + (-1) ^ n * fact n * (1 / ((z + of_nat m) ^ Suc n))"
    using Suc.prems by (subst Polygamma_plus1) (auto simp: add_eq_0_iff2)
  also have "Polygamma n (z + of_nat m) =
               Polygamma n z + (-1) ^ n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n) * fact n"
    using Suc.prems by (subst Suc.IH) auto
  finally show ?case
    by (simp add: algebra_simps)
qed auto

lemma tendsto_Gamma [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Gamma (f z)) \<longlongrightarrow> Gamma c) F"
  by (intro isCont_tendsto_compose[OF _ assms(1)] continuous_intros assms)

lemma tendsto_Polygamma [tendsto_intros]:
  fixes f :: "_ \<Rightarrow> 'a :: {real_normed_field,euclidean_space}"
  assumes "(f \<longlongrightarrow> c) F" "c \<notin> \<int>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. Polygamma n (f z)) \<longlongrightarrow> Polygamma n c) F"
  by (intro isCont_tendsto_compose[OF _ assms(1)] continuous_intros assms)

lemma analytic_on_Gamma' [analytic_intros]:
  assumes "f analytic_on A" "\<forall>x\<in>A. f x \<notin> \<int>\<^sub>\<le>\<^sub>0" 
  shows   "(\<lambda>z. Gamma (f z)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_Gamma[of "f ` A"]] assms(2)
  by (auto simp: o_def)

lemma analytic_on_Polygamma' [analytic_intros]:
  assumes "f analytic_on A" "\<forall>x\<in>A. f x \<notin> \<int>\<^sub>\<le>\<^sub>0" 
  shows   "(\<lambda>z. Polygamma n (f z)) analytic_on A"
  using analytic_on_compose_gen[OF assms(1) analytic_on_Polygamma[of "f ` A" n]] assms(2)
  by (auto simp: o_def)

end