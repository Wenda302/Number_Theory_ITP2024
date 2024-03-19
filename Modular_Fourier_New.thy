section \<open>The Fourier expansions of Klein's \<open>j\<close> functions and some related functions\<close>
theory Modular_Fourier_New
imports 
  Klein_J
  Cotangent_PFD_Formula_Extras
  Divisor_Sigma_Powser
  Polylog.Polylog
  Zeta_Function.Zeta_Function
  Fourier_Expansion_Mero_UHP
  Lambert_Series.Lambert_Series
begin

lemma zeta_numeral_neq_zero [simp]:
  assumes "n > num.One"
  shows   "zeta (numeral n) \<noteq> 0"
  using assms by (intro zeta_Re_gt_1_nonzero) auto

lemma zeta_of_nat_neq_0 [simp]:
  assumes "n \<noteq> 1"
  shows   "zeta (of_nat n) \<noteq> 0"
proof -
  from assms consider "n = 0" | "n > 1"
    by force
  thus ?thesis
    by cases (use zeta_Re_gt_1_nonzero[of "of_nat n"] in auto)
qed

lemma zeta_of_int_eq_0_iff [simp]:
  assumes "n \<noteq> 1"
  shows   "zeta (of_int n) = 0 \<longleftrightarrow> n < 0 \<and> even n"
proof -
  from assms consider "n \<le> 0" | "n > 1"
    by linarith
  thus ?thesis
  proof cases
    assume "n > 1"
    thus ?thesis
      using zeta_Re_gt_1_nonzero[of "of_int n"] by auto
  next
    assume "n \<le> 0"
    define k where "k = nat (-n)"
    have "zeta (-of_nat k) = -bernoulli' (Suc k) / Suc k"
      by (subst zeta_neg_of_nat) auto
    also have "\<dots> = 0 \<longleftrightarrow> bernoulli' (Suc k) = 0"
      by (simp del: of_nat_Suc)
    also have "\<dots> \<longleftrightarrow> even k \<and> k > 0"
      by (simp add: bernoulli'_zero_iff conj_commute)
    finally show ?thesis
      using \<open>n \<le> 0\<close> unfolding k_def by (auto simp: even_nat_iff)
  qed
qed


lemma not_rho_equiv_i [simp]: "\<not>(\<^bold>\<rho> \<sim>\<^sub>\<Gamma> \<i>)"
proof
  assume "\<^bold>\<rho> \<sim>\<^sub>\<Gamma> \<i>"
  then obtain g where g: "apply_modgrp g \<^bold>\<rho> = \<i>"
    by (auto simp: modular_group.rel_def)
  have "Klein_j \<^bold>\<rho> = Klein_j \<i>"
    unfolding g[symmetric] modgrp.Klein_j_transform ..
  thus False
    by simp
qed

lemma not_i_equiv_rho [simp]: "\<not>(\<i> \<sim>\<^sub>\<Gamma> \<^bold>\<rho>)"
  by (subst modular_group.rel_commutes) simp

lemma not_modular_group_rel_rho_i [simp]: " z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<i>"
  by (meson modular_group.rel_sym modular_group.rel_trans not_i_equiv_rho)

lemma modular_group_rel_rho_i_cases [case_names rho i neither invalid]:
  obtains "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" "\<not>z \<sim>\<^sub>\<Gamma> \<i>" | "z \<sim>\<^sub>\<Gamma> \<i>" "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" | "Im z > 0" "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" "\<not>z \<sim>\<^sub>\<Gamma> \<i>" | "Im z \<le> 0"
  by (cases "Im z > 0"; cases "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"; cases "z \<sim>\<^sub>\<Gamma> \<i>") auto

text \<open>
  As a first application of the Klein \<open>J\<close> function, we can show that subgroups of the modular
  group have discrete orbits (i.e.\ every point has a neighbourhood in which no equivalent points
  are).
\<close>
lemma (in modgrp_subgroup) isolated_in_orbit:
  assumes "Im y > 0"
  shows   "\<not>y islimpt orbit x"
proof
  assume *: "y islimpt orbit x"
  have "Klein_j z - Klein_j x = 0" if z: "Im z > 0" for z
  proof (rule analytic_continuation[of "\<lambda>z. Klein_j z - Klein_j x"])
    show "(\<lambda>z. Klein_j z - Klein_j x) holomorphic_on {z. Im z > 0}"
      by (auto intro!: holomorphic_intros simp: complex_is_Real_iff)
    show "open {z. Im z > 0}" and "connected {z. Im z > 0}"
      by (auto simp: open_halfspace_Im_gt intro!: convex_connected convex_halfspace_Im_gt)
    show "y islimpt orbit x" by fact
    show "Klein_j z - Klein_j x = 0" if "z \<in> orbit x" for z
    proof -
      have "z \<sim>\<^sub>\<Gamma> x"
        using that by (auto simp: orbit_def rel_commutes intro: rel_imp_rel)
      then obtain g where g: "apply_modgrp g z = x" "Im z > 0" "Im x > 0"
        by (auto simp: modular_group.rel_def)
      show ?thesis
        using g(2,3) by (simp add: modgrp.Klein_j_transform flip: g(1))
    qed
  qed (use assms z in \<open>auto simp: orbit_def\<close>) 
  from this[of "\<^bold>\<rho>"] and this[of \<i>] show False
    by simp
qed

lemma (in modgrp_subgroup) discrete_orbit: "discrete (orbit x)"
  unfolding discrete_def
proof safe
  fix y assume y: "y \<in> orbit x"
  hence "Im y > 0"
    by (simp add: orbit_def rel_imp_Im_pos(2))
  have *: "orbit y = orbit x"
    by (intro orbit_cong) (use y in \<open>auto simp: orbit_def rel_commutes\<close>)
  have "y isolated_in orbit y"
    using isolated_in_orbit[of y] y * \<open>Im y > 0\<close> isolated_in_islimpt_iff by blast
  thus "y isolated_in orbit x" 
    by (simp add: *)
qed

lemma (in modgrp_subgroup) eventually_not_rel_at:
  "Im x > 0 \<Longrightarrow> eventually (\<lambda>y. \<not>rel y x) (at x)"
  using isolated_in_orbit[of x x]
  by (simp add: islimpt_conv_frequently_at frequently_def orbit_def rel_commutes)

lemma (in modgrp_subgroup) closed_orbit [intro]: "closedin (top_of_set {z. Im z > 0}) (orbit x)"
  using isolated_in_orbit[of _ x] by (auto simp: closedin_limpt orbit_imp_Im_pos)




lemma Eisenstein_G_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_G n (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)

lemma Eisenstein_g2_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g2 (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)

lemma Eisenstein_g3_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g3 (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)

lemma modular_discr_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. modular_discr (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)

lemma Klein_J_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_J (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)

lemma Klein_j_meromorphic_on [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_j (f z)) meromorphic_on A"
  by (rule Meromorphic1.meromorphic_on_compose[OF analytic_on_imp_meromorphic_on assms(1) order.refl])
     (use assms(2) in \<open>auto intro!: analytic_intros\<close>)


subsection \<open>Some basic modular forms\<close>

definition G_modform :: "nat \<Rightarrow> mero_uhp" ("\<G>") where
  "G_modform n = mero_uhp (Eisenstein_G n)"

abbreviation G4_modform ("\<G>\<^sub>4") where "G4_modform \<equiv> G_modform 4"
abbreviation G6_modform ("\<G>\<^sub>6") where "G6_modform \<equiv> G_modform 6"

lemma G_modform_0 [simp]: "\<G> 0 = 1"
  by (simp add: G_modform_def) (metis one_mero_uhp_def const_mero_uhp_def)

lemma mero_uhp_rel_G [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp (G_modform n)) (Eisenstein_G n)"
  unfolding G_modform_def 
  by mero_uhp_rel (auto intro!: meromorphic_intros simp: complex_is_Real_iff)?

lemma eval_mero_uhp_G [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp (\<G> k) z = Eisenstein_G k z"
  using mero_uhp_rel_G
  by (rule mero_uhp_rel_imp_eval_mero_uhp_eq)
     (auto intro!: analytic_intros simp: complex_is_Real_iff)

lemmas [meromorphic_intros del] = constant_on_imp_meromorphic_on

definition modular_discr_modform :: mero_uhp ("\<Delta>") where
  "modular_discr_modform = mero_uhp modular_discr"

lemma mero_uhp_rel_modular_discr [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp modular_discr_modform) modular_discr"
  unfolding modular_discr_modform_def 
  by mero_uhp_rel (auto intro!: meromorphic_intros simp: complex_is_Real_iff)?

lemma modular_discr_modform_altdef: "\<Delta> = (60 * \<G> 4) ^ 3 - 27 * (140 * \<G> 6) ^ 2"
  unfolding modular_discr_modform_def G_modform_def modular_discr_def
            Eisenstein_g2_def Eisenstein_g3_def
  by mero_uhp_rel (auto simp: complex_is_Real_iff)  

lemma eval_mero_uhp_modular_discr [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp \<Delta> z = modular_discr z"
  using mero_uhp_rel_modular_discr
  by (rule mero_uhp_rel_imp_eval_mero_uhp_eq)
     (auto intro!: analytic_intros simp: complex_is_Real_iff)


definition J_modform :: mero_uhp ("\<J>") where
  "J_modform = mero_uhp Klein_J"

lemma mero_uhp_rel_J [mero_uhp_rel_intros]:
  "mero_uhp_rel (eval_mero_uhp J_modform) Klein_J"
  unfolding J_modform_def 
  by mero_uhp_rel (auto intro!: meromorphic_intros simp: complex_is_Real_iff)?

lemma modular_J_modform_altdef: "\<J> = (60 * \<G> 4) ^ 3 / \<Delta>"
  unfolding J_modform_def Klein_J_def G_modform_def modular_discr_modform_def
            Eisenstein_g2_def Eisenstein_g3_def
  by mero_uhp_rel (auto simp: complex_is_Real_iff intro!: meromorphic_intros)?

lemma eval_mero_uhp_J [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp \<J> z = Klein_J z"
  using mero_uhp_rel_J
  by (rule mero_uhp_rel_imp_eval_mero_uhp_eq)
     (auto intro!: analytic_intros simp: complex_is_Real_iff)

definition g2_modform ("g\<^sub>2") where "g2_modform \<equiv> mero_uhp Eisenstein_g2"
definition g3_modform ("g\<^sub>3") where "g3_modform \<equiv> mero_uhp Eisenstein_g3"
definition j_modform ("\<j>") where "j_modform \<equiv> mero_uhp Klein_j"

lemma eval_mero_uhp_g\<^sub>2 [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp g\<^sub>2 z = Eisenstein_g2 z"
  unfolding g2_modform_def
  apply (rule eval_mero_uhp_mero_uhp)
  using complex_is_Real_iff by (auto intro!:meromorphic_intros analytic_intros)

lemma eval_mero_uhp_g\<^sub>3 [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp g\<^sub>3 z = Eisenstein_g3 z"
  unfolding g3_modform_def
  apply (rule eval_mero_uhp_mero_uhp)
  using complex_is_Real_iff by (auto intro!:meromorphic_intros analytic_intros)

lemma eval_mero_uhp_\<j> [simp]: "Im z > 0 \<Longrightarrow> eval_mero_uhp \<j> z = Klein_j z"
  unfolding j_modform_def
  apply (rule eval_mero_uhp_mero_uhp)
  using complex_is_Real_iff by (auto intro!:meromorphic_intros analytic_intros)

subsection \<open>Expansion of various concrete functions in terms of \<open>q\<close>\<close>

lemma compose_modgrp_mero_uhp_mero_uhpI:
  assumes "f meromorphic_on {z. 0 < Im z}"
  assumes "\<And>z. 0 < Im z 
              \<Longrightarrow> f analytic_on {apply_modgrp h z} 
                  \<and> f (apply_modgrp h z) = g z
                  \<and> 0 < Im (apply_modgrp h z)" 
  shows "compose_modgrp_mero_uhp (mero_uhp f) h = (mero_uhp g)"
  unfolding compose_modgrp_mero_uhp_def
  apply (rule mero_uhp_cong_weak)
  apply (subst eval_mero_uhp_G mero_uhp_rel_imp_eval_mero_uhp_eq[of "mero_uhp f" f])
  apply (rule mero_uhp_rel_mero_uhp)
  using assms by auto

interpretation Eisenstein_G: fourier_expansion "\<G> k" "Suc 0" 
proof  
  show "compose_modgrp_mero_uhp (\<G> k) 
          (shift_modgrp (int (Suc 0))) = \<G> k"
    unfolding G_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff Eisenstein_G.plus_1)
qed simp

(* TODO: g2, g3 *)
  
interpretation Eisenstein_g2: fourier_expansion g\<^sub>2 "Suc 0"
proof
  show "compose_modgrp_mero_uhp g\<^sub>2 (shift_modgrp (int (Suc 0))) = g\<^sub>2"
    unfolding g2_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff Eisenstein_g2.plus_1)
qed simp

interpretation Eisenstein_g3: fourier_expansion g\<^sub>3 "Suc 0"
proof
  show "compose_modgrp_mero_uhp g\<^sub>3 (shift_modgrp (int (Suc 0))) = g\<^sub>3"
    unfolding g3_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff Eisenstein_g3.plus_1)
qed simp

interpretation modular_discr: fourier_expansion "\<Delta>" "Suc 0"
proof
  show "compose_modgrp_mero_uhp \<Delta> (shift_modgrp (int (Suc 0))) = \<Delta>"
    unfolding modular_discr_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff modular_discr.plus_1)
qed simp

interpretation Klein_J: fourier_expansion "\<J>" "Suc 0"
proof 
  show "compose_modgrp_mero_uhp \<J> (shift_modgrp (int (Suc 0))) = \<J>"
    unfolding J_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff Klein_J.plus_1)
qed simp

(* TODO: Klein_j *)

interpretation Klein_j: fourier_expansion \<j> "Suc 0"
proof 
  show "compose_modgrp_mero_uhp \<j> (shift_modgrp (int (Suc 0))) = \<j>"
    unfolding j_modform_def
    apply (rule compose_modgrp_mero_uhp_mero_uhpI)
    by (auto intro!:meromorphic_intros analytic_intros 
        simp:complex_is_Real_iff Klein_j.plus_1)
qed simp

subsection \<open>The Fourier expansion of $\sum_{m\in\mathbb{Z}} (z + m)^{-n}$\<close>

definition eisenstein_fourier_aux :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fourier_aux n z = (Polygamma (n-1) (1 + z) + Polygamma (n-1) (1 - z)) / fact (n - 1) + 1 / z ^ n"

lemma abs_summable_one_over_const_plus_nat_power:
  assumes "n \<ge> 2"
  shows   "summable (\<lambda>k. norm (1 / (z + of_nat k :: complex) ^ n))"
proof (rule summable_comparison_test_ev)
  have "eventually (\<lambda>k. real k > norm z) at_top"
    by real_asymp
  thus "eventually (\<lambda>k. norm (norm (1 / (z + of_nat k) ^ n)) \<le> 1 / (real k - norm z) ^ n) at_top"
  proof eventually_elim
    case (elim k)
    have "real k - norm z \<le> norm (z + of_nat k)"
      by (metis add.commute norm_diff_ineq norm_of_nat)
    hence "1 / norm (z + of_nat k) ^ n \<le> 1 / norm (real k - norm z) ^ n"
      using elim by (intro power_mono divide_left_mono mult_pos_pos zero_less_power) auto
    thus ?case using elim
      by (simp add: norm_divide norm_power)
  qed
next
  show "summable (\<lambda>k. 1 / (real k - norm z) ^ n)"
  proof (rule summable_comparison_test_bigo)
    show "summable (\<lambda>k. norm (1 / real k ^ n))"
      using inverse_power_summable[of n] assms
      by (simp add: norm_power norm_divide field_simps)
  next
    show "(\<lambda>k. 1 / (real k - norm z) ^ n) \<in> O(\<lambda>k. 1 / real k ^ n)"
      by real_asymp
  qed
qed

lemma abs_summable_one_over_const_minus_nat_power:
  assumes "n \<ge> 2"
  shows   "summable (\<lambda>k. norm (1 / (z - of_nat k :: complex) ^ n))"
proof -
  have "summable (\<lambda>k. norm (1 / ((-z) + of_nat k :: complex) ^ n))"
    using assms by (rule abs_summable_one_over_const_plus_nat_power)
  also have "(\<lambda>k. norm (1 / ((-z) + of_nat k :: complex) ^ n)) =
            (\<lambda>k. norm (1 / (z - of_nat k :: complex) ^ n))"
    by (simp add: norm_divide norm_power norm_minus_commute)
  finally show ?thesis .
qed

lemma even_power_diff_commute: "even n \<Longrightarrow> (x - y) ^ n = (y - x :: 'a :: ring_1) ^ n"
  by (metis Parity.ring_1_class.power_minus_even minus_diff_eq)

lemma has_sum_eisenstein_fourier_aux:
  assumes "n \<ge> 2" and "even n" and "Im z > 0"
  shows   "((\<lambda>m. 1 / (z + of_int m) ^ n) has_sum eisenstein_fourier_aux n z) UNIV"
proof -
  define f where "f = (\<lambda>k. 1 / (z + of_int k) ^ n)"

  from assms have "1 + z \<noteq> 0"
    by (subst add_eq_0_iff) auto
  have "(\<lambda>k. 1 / (((1 + z) + of_nat k) ^ n)) sums (Polygamma (n-1) (1+z) / fact (n-1))"
    using assms Polygamma_LIMSEQ[of "1 + z" "n - 1"] \<open>1 + z \<noteq> 0\<close> by (simp add: field_simps)
  moreover have "summable (\<lambda>k. cmod (1 / (z + (Suc k)) ^ n))"
    by (subst summable_Suc_iff) (rule abs_summable_one_over_const_plus_nat_power, fact)
  ultimately have "((\<lambda>k. 1 / (z + of_nat (Suc k)) ^ n) has_sum (Polygamma (n-1) (1+z) / fact (n-1))) UNIV"
    by (intro norm_summable_imp_has_sum) (simp_all add: algebra_simps)
  also have "?this \<longleftrightarrow> (f has_sum (Polygamma (n-1) (1+z) / fact (n-1))) {1..}" unfolding f_def
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>k. nat (k - 1)" "\<lambda>k. of_int (Suc k)"]) auto
  finally have sum1: "(f has_sum (Polygamma (n-1) (1+z) / fact (n-1))) {1..}" .

  have "1 - z \<noteq> 0"
    using assms by auto
  have "(\<lambda>k. 1 / (((1 - z) + of_nat k) ^ n)) sums (Polygamma (n-1) (1-z) / fact (n-1))"
    using assms Polygamma_LIMSEQ[of "1 - z" "n - 1"] \<open>1 - z \<noteq> 0\<close>
    by (simp add: field_simps)
  also have "(\<lambda>k. ((1 - z) + of_nat k) ^ n) = (\<lambda>k. (z - of_nat (Suc k)) ^ n)"
    using assms by (subst even_power_diff_commute) (auto simp: algebra_simps)
  finally have "(\<lambda>k. 1 / (z - of_nat (Suc k)) ^ n) sums (Polygamma (n-1) (1-z) / fact (n-1))" .
  moreover have "summable (\<lambda>k. cmod (1 / (z - (Suc k)) ^ n))"
    by (subst summable_Suc_iff) (rule abs_summable_one_over_const_minus_nat_power, fact)
  ultimately have "((\<lambda>k. 1 / (z - of_nat (Suc k)) ^ n) has_sum (Polygamma (n-1) (1-z) / fact (n-1))) UNIV"
    by (intro norm_summable_imp_has_sum)
  also have "?this \<longleftrightarrow> (f has_sum (Polygamma (n-1) (1-z) / fact (n-1))) {..-1}" unfolding f_def
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>k. nat (-k-1)" "\<lambda>k. -of_int (Suc k)"])
       (auto simp: algebra_simps)
  finally have sum2: "(f has_sum (Polygamma (n-1) (1-z) / fact (n-1))) {..-1}" .

  have "(f has_sum (Polygamma (n-1) (1+z) / fact (n-1)) + Polygamma (n-1) (1-z) / fact (n-1))
          ({1..} \<union> {..-1})"
    by (intro has_sum_Un_disjoint sum1 sum2) auto
  also have "({1..} \<union> {..-1}) = -{0::int}"
    by auto
  finally have "(f has_sum ((Polygamma (n-1) (1+z) + Polygamma (n-1) (1-z)) / fact (n-1))) (-{0})"
    by (simp add: add_divide_distrib)
  hence "(f has_sum (f 0 + (Polygamma (n-1) (1+z) + Polygamma (n-1) (1-z)) / fact (n-1))) (insert 0 (-{0}))"
    by (intro has_sum_insert) auto
  also have "insert 0 (-{0}) = (UNIV :: int set)"
    by auto
  finally show ?thesis
    by (simp add: eisenstein_fourier_aux_def f_def algebra_simps)
qed

theorem eisenstein_fourier_aux_expansion:
  assumes n: "odd n" and z: "Im z > 0"
  shows   "eisenstein_fourier_aux (n + 1) z =
             (2 * \<i> * pi) ^ Suc n / fact n * polylog (-int n) (cusp_q 1 z)"
proof -
  have eq0: "1 / z + cot_pfd z = -\<i> * pi * (2 * polylog 0 (cusp_q 1 z) + 1)"
    if z: "Im z > 0" for z :: complex
  proof -
    define x where "x = exp (2 * pi * \<i> * z)"
    have *: "exp (2 * pi * \<i> * z) = exp (pi * \<i> * z) ^ 2"
      by (subst exp_double [symmetric]) (simp add: algebra_simps)
    have "norm x < 1"
      using z by (auto simp: x_def)
    hence "x \<noteq> 1"
      by auto

    have "1 / z + cot_pfd z = pi * cot (pi * z)"
      using z by (intro cot_pfd_formula_complex [symmetric]) (auto elim: Ints_cases)
    also have "pi * cos (pi * z) * (x - 1) = pi * \<i> * sin (pi * z) * (x + 1)"
      using z * 
      by (simp add: sin_exp_eq cos_exp_eq x_def exp_minus field_simps power2_eq_square
               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
    hence "pi * cot (pi * z) = \<i> * pi * (x + 1) / (x - 1)"
      unfolding cot_def using z by (auto simp: divide_simps sin_eq_0)
    also have "\<dots> = -\<i> * pi * (-(x + 1) / (x - 1))"
      by (simp add: field_simps)
    also have "-(x + 1) / (x - 1) = 1 + 2 * x / (1 - x)"
      using \<open>x \<noteq> 1\<close> by (simp add: field_simps)
    also have "\<dots> = 2 * polylog 0 x + 1"
      using \<open>norm x < 1\<close> and \<open>x \<noteq> 1\<close> by (simp add: polylog_0_left field_simps)
    finally show ?thesis by (simp only: x_def cusp_q_def) simp
  qed

  define f :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
    "f = (\<lambda>n z. if n = 0 then 1 / z + cot_pfd z
                else (-1) ^ n * Polygamma n (1 - z) - Polygamma n (1 + z) +
                     (-1) ^ n * fact n / z ^ (Suc n))"

  have f_odd_eq: "f n z = -fact n * eisenstein_fourier_aux (n+1) z" if "odd n" for n z
    using that by (auto simp add: f_def eisenstein_fourier_aux_def field_simps)

  have DERIV_f: "(f n has_field_derivative f (Suc n) z) (at z)" if "z \<notin> \<int>" for n z
  proof (cases "n = 0")
    case [simp]: True
    have "((\<lambda>z. 1 / z + cot_pfd z) has_field_derivative f 1 z) (at z)"
      unfolding f_def by (rule derivative_eq_intros refl | use that in force)+
    thus ?thesis by (simp add: f_def)
  next
    case False
    have 1: "1 - z \<notin> \<int>\<^sub>\<le>\<^sub>0" "1 + z \<notin> \<int>\<^sub>\<le>\<^sub>0"
      using that by (metis Ints_1 Ints_diff add_diff_cancel_left' diff_diff_eq2 nonpos_Ints_Int)+
    have 2: "z \<noteq> 0"
      using that by auto

    have "((\<lambda>z. (-1) ^ n * Polygamma n (1 - z) - Polygamma n (1 + z) + (-1) ^ n * fact n / z ^ (Suc n))
           has_field_derivative (-1) ^ Suc n * Polygamma (Suc n) (1 - z) -
             Polygamma (Suc n) (1 + z) + (-1) ^ Suc n * fact (Suc n) / z ^ (Suc (Suc n))) (at z)"
      by (rule derivative_eq_intros refl | use that 1 2 in force)+
    thus ?thesis
      using that False by (simp add: f_def)
  qed

  define g :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
    "g = (\<lambda>n z. -pi * \<i> * (2 * \<i> * pi) ^ n * (2 * polylog (-n) (cusp_q 1 z) + (if n = 0 then 1 else 0)))"

  have g_eq: "g n z = -((2 * \<i> * pi) ^ Suc n) * polylog (-n) (cusp_q 1 z)" if "n > 0" for n z
    using that unfolding g_def by simp

  note [derivative_intros del] = DERIV_sum
  have DERIV_g: "(g n has_field_derivative g (Suc n) z) (at z)" if z: "Im z > 0" for z n
  proof -
    have "norm (cusp_q 1 z) = exp (- (2 * pi * Im z))"
      by simp
    also have "\<dots> < exp 0"
      using that by (subst exp_less_cancel_iff) auto
    finally have "norm (cusp_q (Suc 0) z) \<noteq> 1"
      by auto
    moreover have "norm (1 :: complex) = 1"
      by simp
    ultimately have [simp]: "cusp_q (Suc 0) z \<noteq> 1"
      by metis
    show ?thesis unfolding g_def
      by (rule derivative_eq_intros refl | (use z in simp; fail))+
         (auto simp: algebra_simps minus_diff_commute)
  qed

  have eq: "f n z = g n z" if "Im z > 0" for z n
    using that
  proof (induction n arbitrary: z)
    case (0 z)
    have "norm (cusp_q 1 z) < 1"
      unfolding cusp_q_def using 0 by simp
    hence "polylog 0 (cusp_q 1 z) = cusp_q 1 z / (1 - cusp_q 1 z)"
      by (subst polylog_0_left) auto
    thus ?case
      using eq0[of z] 0 by (auto simp: complex_is_Int_iff f_def g_def)
  next
    case (Suc n z)
    have "(f n has_field_derivative f (Suc n) z) (at z)"
      by (rule DERIV_f) (use Suc.prems in \<open>auto simp: complex_is_Int_iff\<close>)
    also have "?this \<longleftrightarrow> (g n has_field_derivative f (Suc n) z) (at z)"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (nhds z)"
        using Suc.prems by (intro eventually_nhds_in_open) (auto simp: open_halfspace_Im_gt)
      thus "eventually (\<lambda>z. f n z = g n z) (nhds z)"
        by eventually_elim (use Suc.IH in auto)
    qed auto
    finally have "(g n has_field_derivative f (Suc n) z) (at z)" .
    moreover have "(g n has_field_derivative g (Suc n) z) (at z)"
      by (rule DERIV_g) fact
    ultimately show "f (Suc n) z = g (Suc n) z"
      using DERIV_unique by blast
  qed

  from z have "f n z = g n z"
    by (intro eq) auto
  also have "f n z = -fact n * eisenstein_fourier_aux (n+1) z"
    using n by (subst f_odd_eq) auto
  also have "g n z = - ((2 * \<i> * pi) ^ Suc n) * polylog (-n) (cusp_q 1 z)"
    using n by (subst g_eq) (auto elim: oddE)
  finally show ?thesis
    by (simp add: cusp_q_def field_simps)
qed

text \<open>Lemma 3\<close>

corollary eisenstein_fourier_aux_expansion_2:
  assumes z: "Im z > 0"
  shows   "eisenstein_fourier_aux 4 z = 8 / 3 * pi ^ 4 * polylog (-3) (cusp_q 1 z)"
  using eisenstein_fourier_aux_expansion[of 3, OF _ z]
  by (simp add: fact_numeral power_mult_distrib)

corollary eisenstein_fourier_aux_expansion_4:
  assumes z: "Im z > 0"
  shows   "eisenstein_fourier_aux 6 z = -8 / 15 * pi ^ 6 * polylog (-5) (cusp_q 1 z)"
  using eisenstein_fourier_aux_expansion[of 5, OF _ z]
  by (simp add: fact_numeral power_mult_distrib)


subsection \<open>Expansions of various concrete functions\<close>

subsubsection \<open>The Eisenstein series and the invariants \<open>g\<^sub>2\<close> and \<open>g\<^sub>3\<close>\<close>

lemma conv_radius_divisor_sigma_ge:
  fixes a :: "'a :: {nat_power_normed_field, banach}"
  shows "conv_radius (divisor_sigma a) \<ge> 1"
proof (rule conv_radius_geI_ex)
  fix r assume r: "0 < r" "ereal r < 1"
  have "summable (\<lambda>n. divisor_sigma a n * of_real r ^ n)"
    using divisor_sigma_powser_conv_lambert[of "of_real r" a] r
    by (auto simp: sums_iff)
  thus "\<exists>z. norm z = r \<and> summable (\<lambda>n. divisor_sigma a n * z ^ n)"
    by (intro exI[of _ "of_real r"]) (use r in auto)
qed

lemma Eisenstein_G_fourier_expansion_aux:
  fixes z :: complex and k :: nat
  assumes z: "Im z > 0" and k: "k > 2" "even k"
  defines "x \<equiv> cusp_q 1 z"
  shows "((\<lambda>(m,n). 1 / (of_int m + of_int n * z) ^ k) has_sum
           2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) x)) (-{(0,0)})"
proof -
  have x: "norm x < 1"
    using z by (simp add: x_def cusp_q_def)

  define g where "g = (\<lambda>(n,m). 1 / (of_int m + of_int n * z) ^ k)"
  define C where "C = (2 * \<i> * pi) ^ k / fact (k-1)"
  define S where "S = lambert (\<lambda>n. of_nat n ^ (k-1)) x"

  have sum1: "(g has_sum C * S) ({1..} \<times> UNIV)" unfolding g_def
  proof (rule has_sum_SigmaI; (unfold prod.case)?)
    fix n :: int assume n: "n \<in> {1..}"
    show "((\<lambda>y. 1 / (of_int y + of_int n * z) ^ k) has_sum eisenstein_fourier_aux k (of_int n * z)) UNIV"
      using has_sum_eisenstein_fourier_aux[of k "of_int n * z"] n k z by (simp add: add_ac)
  next
    interpret std_lattice z
      using \<open>Im z > 0\<close> by unfold_locales (auto simp: complex_is_Real_iff)
    have "(\<lambda>(m, n). norm (1 / (of_int m + of_int n * z) ^ k)) summable_on UNIV \<times> {1..}"
      by (rule summable_on_subset [OF eisenstein_series_norm_summable']) (use k in auto)
    hence "(\<lambda>(m, n). 1 / (of_int m + of_int n * z) ^ k) summable_on UNIV \<times> {1..}"
      unfolding case_prod_unfold by (rule abs_summable_summable)
    thus "(\<lambda>(n, m). 1 / (of_int m + of_int n * z) ^ k) summable_on {1..} \<times> UNIV"
      by (subst summable_on_swap) auto
  next
    have "((\<lambda>(n,r). of_nat r ^ (k - 1) * x ^ (r * n)) has_sum S) ({1..} \<times> {1..})"
    proof -
      have sum: "((\<lambda>r. of_nat r ^ (k - 1) * x ^ rn) has_sum
                   divisor_sigma (k - 1) rn * x ^ rn) {r. r dvd rn}"
        if x: "norm x < 1" and rn: "rn \<in> {1..}" for rn and x :: complex
        unfolding norm_mult norm_power
      proof (intro has_sum_cmult_left)
        have "((\<lambda>r. of_nat (r ^ (k - 1))) has_sum of_nat (\<Sum>r | r dvd rn. r ^ (k - 1))) {r. r dvd rn}"
          unfolding divisor_sigma_def by (intro has_sum_of_nat has_sum_finite) (use rn in auto)
        thus "((\<lambda>r. of_nat r ^ (k - 1)) has_sum of_nat (divisor_sigma (k - 1) rn)) {r. r dvd rn}"
          by (simp add: divisor_sigma_def)
      qed

      have "((\<lambda>(rn,r). of_nat r ^ (k - 1) * x ^ rn) has_sum S) (SIGMA rn:{1..}. {r. r dvd rn})"
      proof (rule has_sum_SigmaI; (unfold prod.case)?)
        have "(\<lambda>(rn, r). norm (of_nat r ^ (k - 1) * x ^ rn)) summable_on (SIGMA rn:{1..}. {r. r dvd rn})"
        proof (rule summable_on_SigmaI; (unfold prod.case)?)
          show "((\<lambda>r. norm (of_nat r ^ (k - 1) * x ^ rn)) has_sum
                      Re (divisor_sigma (k - 1) rn * norm x ^ rn)) {r. r dvd rn}"
            if rn: "rn \<in> {1..}" for rn
            using has_sum_Re[OF sum[of "norm x" rn]] rn x by (simp add: norm_mult norm_power)
        next
          have "summable (\<lambda>rn. Re (complex_of_real (real (divisor_sigma (k - 1) rn) * cmod x ^ rn)))"
            using abs_summable_divisor_sigma_powser[of "norm x" "k - 1"] x
            by (simp add: norm_mult norm_power)
          hence "(\<lambda>rn. Re (complex_of_real (real (divisor_sigma (k - 1) rn) * cmod x ^ rn))) summable_on UNIV"
            by (intro norm_summable_imp_summable_on) auto
          thus "(\<lambda>rn. Re (complex_of_real (real (divisor_sigma (k - 1) rn) * cmod x ^ rn))) summable_on {1..}"
            by (rule summable_on_subset) auto
        qed auto
        thus "(\<lambda>(rn, r). of_nat r ^ (k - 1) * x ^ rn) summable_on (SIGMA rn:{1..}. {r. r dvd rn})"
          unfolding case_prod_unfold using abs_summable_summable by fast
      next
        show "((\<lambda>r. of_nat r ^ (k - 1) * x ^ rn) has_sum divisor_sigma (k - 1) rn * x ^ rn) {r. r dvd rn}"
          if rn: "rn \<in> {1..}" for rn
        proof (intro has_sum_cmult_left)
          have "((\<lambda>r. of_nat (r ^ (k - 1))) has_sum of_nat (\<Sum>r | r dvd rn. r ^ (k - 1))) {r. r dvd rn}"
            unfolding divisor_sigma_def by (intro has_sum_of_nat has_sum_finite) (use rn in auto)
          thus "((\<lambda>r. of_nat r ^ (k - 1)) has_sum of_nat (divisor_sigma (k - 1) rn)) {r. r dvd rn}"
            by (simp add: divisor_sigma_def)
        qed
      next
        have "(\<lambda>n. of_nat (divisor_sigma (k - 1) n) * x ^ n) sums S"
          unfolding S_def
          using divisor_sigma_powser_conv_lambert[of x "k - 1"] x
          by (simp add: divisor_sigma_of_nat)
        moreover have "summable (\<lambda>n. norm (of_nat (divisor_sigma (k - 1) n) * x ^ n))"
          using x conv_radius_divisor_sigma_ge[of "complex_of_nat (k - 1)"]
          by (intro abs_summable_in_conv_radius) 
             (auto simp flip: divisor_sigma_of_nat simp: ereal_le_less one_ereal_def)
        ultimately have "((\<lambda>r. of_nat (divisor_sigma (k - 1) r) * x ^ r) has_sum S) UNIV"
          using norm_summable_imp_has_sum by fast
        also have "?this \<longleftrightarrow> ((\<lambda>r. of_nat (divisor_sigma (k - 1) r) * x ^ r) has_sum S) {1..}"
          by (intro has_sum_cong_neutral) (auto simp: not_le)
        finally show \<dots> .
      qed
      also have "?this \<longleftrightarrow> ?thesis"
        by (rule has_sum_reindex_bij_witness[of _ "\<lambda>(n, r). (r * n, r)" "\<lambda>(rn, r). (rn div r, r)"]) auto
      finally show ?thesis .
    qed
    also have "?this \<longleftrightarrow> ((\<lambda>(n,r). of_nat r ^ (k - 1) * x ^ (r * n)) has_sum S) ({1..} \<times> UNIV)"
      using k by (intro has_sum_cong_neutral) (auto simp: not_le not_less)
    finally have *: "((\<lambda>(n,r). of_nat r ^ (k - 1) * x ^ (r * n)) has_sum S) ({1..} \<times> UNIV)" .        

    have "((\<lambda>n. polylog (1 - int k) (x ^ n)) has_sum S) {1..}"
    proof (rule has_sum_SigmaD[OF *], unfold prod.case)
      fix n :: nat assume n: "n \<in> {1..}"
      have x': "norm (x ^ n) < 1 ^ n"
        unfolding norm_power using x n by (intro power_strict_mono) auto

      have "(\<lambda>r. of_nat r ^ (k - 1) * x ^ (r * n)) sums polylog (1 - int k) (x ^ n)"
        using sums_polylog'[of "x ^ n" "1 - int k"] x' k
        by (simp flip: power_mult add: mult_ac power_int_def nat_diff_distrib)
      moreover have "summable (\<lambda>r. norm (of_nat r powi (k - 1) * (x ^ n) ^ r))"
        using x' by (intro abs_summable_polylog) auto
      hence "summable (\<lambda>r. norm (of_nat r ^ (k - 1) * x ^ (r * n)))"
        by (simp flip: power_mult add: mult_ac)
      ultimately show "((\<lambda>r. of_nat r ^ (k - 1) * x ^ (r * n))
                         has_sum polylog (1 - int k) (x ^ n)) UNIV"
        by (intro norm_summable_imp_has_sum)
    qed
    also have "?this \<longleftrightarrow> ((\<lambda>n. polylog (1 - int k) (x powi n)) has_sum S) {1..}"
      by (intro has_sum_reindex_bij_witness[of _ nat int]) auto
    finally have "((\<lambda>n. C * polylog (1 - int k) (x powi n)) has_sum C * S) {1..}"
      by (intro has_sum_cmult_right)
    also have "?this \<longleftrightarrow> ((\<lambda>n. eisenstein_fourier_aux k (of_int n * z)) has_sum C * S) {1..}"
    proof (rule has_sum_cong, goal_cases)
      case (1 n)
      thus ?case
        using eisenstein_fourier_aux_expansion[of "k - 1" "of_int n * z"] k z
        by (auto simp: algebra_simps x_def exp_power_int C_def cusp_q_def of_nat_diff)
    qed
    finally show "((\<lambda>x. eisenstein_fourier_aux k (of_int x * z)) has_sum C * S) {1..}" .
  qed

  have "((\<lambda>(n, m). 1 / (-(of_int m + of_int n * z)) ^ k) has_sum C * S) ({1..} \<times> UNIV)"
    using sum1 \<open>even k\<close> by (subst power_minus_even) (auto simp: g_def)
  also have "(\<lambda>n m. 1 / (-(of_int m + of_int n * z)) ^ k) =
             (\<lambda>n m. 1 / (of_int (-m) + of_int (-n) * z) ^ k)"
    by simp
  also have "((\<lambda>(n, m). 1 / (of_int (-m) + of_int (-n) * z) ^ k) has_sum C * S) ({1..} \<times> UNIV) \<longleftrightarrow>
             (g has_sum C * S) ({..-1} \<times> UNIV)"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(n,m). (-n,-m)" "\<lambda>(n,m). (-n,-m)"])
       (auto simp: g_def)
  finally have sum2: "(g has_sum C * S) ({..-1} \<times> UNIV)" .

  have sum3: "(g has_sum 2 * zeta (of_nat k)) ({0} \<times> -{0})"
  proof -
    have "(\<lambda>m. 1 / of_nat (Suc m) ^ k) sums zeta (of_nat k)"
      using k by (intro sums_zeta_nat) auto
    moreover have "summable (\<lambda>m. norm (1 / of_nat (Suc m) ^ k :: complex))"
      using abs_summable_one_over_const_plus_nat_power[of k 0] k
      by (subst summable_Suc_iff) (simp add: norm_power norm_divide del: of_nat_Suc)
    ultimately have *: "((\<lambda>m. 1 / of_nat (Suc m) ^ k) has_sum zeta (of_nat k)) UNIV" (is ?P)
      by (intro norm_summable_imp_has_sum)

    have "?P \<longleftrightarrow> (g has_sum zeta (of_nat k)) ({0} \<times> {1..})"
      by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(_,m). nat (m - 1)" "\<lambda>i. (0, int (Suc i))"])
         (auto simp: g_def)
    hence 1: "(g has_sum zeta (of_nat k)) ({0} \<times> {1..})"
      using * by blast

    have **: "(-a - b) ^ k = (a + b) ^ k" for a b :: complex
      using power_minus_even[OF \<open>even k\<close>, of "a + b"] by (simp add: algebra_simps)
    have "?P \<longleftrightarrow> (g has_sum zeta (of_nat k)) ({0} \<times> {..-1})"
      by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(_,m). nat (-m - 1)" "\<lambda>i. (0, -int (Suc i))"])
         (use ** in \<open>auto simp: g_def\<close>)
    hence 2: "(g has_sum zeta (of_nat k)) ({0} \<times> {..-1})"
      using * by blast

    have "(g has_sum zeta (of_nat k) + zeta (of_nat k)) ({0} \<times> {..-1} \<union> {0} \<times> {1..})"
      by (intro has_sum_Un_disjoint 1 2) auto
    also have "{0} \<times> {..-1} \<union> {0} \<times> {1..} = {0 :: int} \<times> -{0 :: int}"
      by auto
    finally show ?thesis by simp
  qed

  have "(g has_sum C * S + C * S + 2 * zeta k) ({..-1} \<times> UNIV \<union> {1..} \<times> UNIV \<union> {0} \<times> -{0})"
    by (intro has_sum_Un_disjoint sum1 sum2 sum3) auto
  also have "{..-1} \<times> UNIV \<union> {1..} \<times> UNIV \<union> {0} \<times> -{0} = -{(0 :: int, 0 :: int)}"
    by auto
  finally have "(g has_sum 2 * (C * S + zeta k)) (-{(0,0)})"
    by (simp add: algebra_simps)
  also have "?this \<longleftrightarrow> ((g \<circ> (\<lambda>(x,y). (y,x))) has_sum 2 * (C * S + zeta k)) (-{(0,0)})"
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>(x,y). (y,x)" "\<lambda>(x,y). (y,x)"]) auto
  finally show ?thesis
    by (simp_all add: g_def C_def S_def add_ac o_def case_prod_unfold)
qed


text \<open>The following form of Theorem 1.18 closely follows Apostol's presentation:\<close>

theorem Eisenstein_G_fourier_expansion:
  fixes z :: complex and k :: nat
  assumes z: "Im z > 0" and k: "k > 2" "even k"
  shows "Eisenstein_G k z =
           2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) (cusp_q 1 z))"
  by (rule has_sum_unique[OF has_sum_Eisenstein_G Eisenstein_G_fourier_expansion_aux])
     (use assms in \<open>auto simp: complex_is_Real_iff\<close>)

corollary Eisenstein_g2_fourier_expansion:
  fixes z :: complex
  assumes z: "Im z > 0"
  shows "Eisenstein_g2 z = 4 / 3 * pi ^ 4 
            * (1 + 240 * lambert (\<lambda>n. complex_of_nat n ^ 3) (cusp_q 1 z))"
  unfolding Eisenstein_g2_def using assms
  by (subst Eisenstein_G_fourier_expansion) (auto simp: fact_numeral zeta_4 algebra_simps)

corollary Eisenstein_g3_fourier_expansion:
  fixes z :: complex
  assumes z: "Im z > 0"
  shows "Eisenstein_g3 z = 8 / 27 * pi ^ 6 
              * (1 - 504 *  lambert (\<lambda>n. complex_of_nat n ^ 5) (cusp_q 1 z))"
  unfolding Eisenstein_g3_def using assms
  by (subst Eisenstein_G_fourier_expansion) (auto simp: fact_numeral zeta_6 algebra_simps)

(*
corollary Eisenstein_g2_fourier_expansion:
  fixes z :: complex
  assumes z: "Im z > 0"
  shows "Eisenstein_g2 z = 4 / 3 * pi ^ 4 * (1 + 240 * divisor_sigma_powser 3 (cusp_q 1 z))"
  unfolding Eisenstein_g2_def using assms
  by (subst Eisenstein_G_fourier_expansion) (auto simp: fact_numeral zeta_4 algebra_simps)

corollary Eisenstein_g3_fourier_expansion:
  fixes z :: complex
  assumes z: "Im z > 0"
  shows "Eisenstein_g3 z = 8 / 27 * pi ^ 6 * (1 - 504 * divisor_sigma_powser 5 (cusp_q 1 z))"
  unfolding Eisenstein_g3_def using assms
  by (subst Eisenstein_G_fourier_expansion) (auto simp: fact_numeral zeta_6 algebra_simps)
*)


text \<open>
  In the following, we will rephrase the above Fourier expansions in a more pleasant way for
  formula reasoning using formal power series.
\<close>

definition Eisenstein_G_fps_at_cusp :: "nat \<Rightarrow> complex fps" where
  "Eisenstein_G_fps_at_cusp k =
     2 * (fps_const (zeta k) +
          fps_const ((2 * \<i> * pi) ^ k / fact (k - 1)) * of_nat.fps (Abs_fps (divisor_sigma (k-1))))"

lemma Eisenstein_G_fps_at_cusp_nonzero [simp]: "Eisenstein_G_fps_at_cusp k \<noteq> 0"
proof -
  have "fps_nth (Eisenstein_G_fps_at_cusp k) 1 \<noteq> 0"
    by (auto simp: Eisenstein_G_fps_at_cusp_def fps_numeral_nth)
  thus ?thesis
    by auto
qed

(* TODO: Move *)
lemma has_fps_expansionI:
  assumes "open A" "0 \<in> A" "\<And>z. z \<in> A \<Longrightarrow> (\<lambda>n. fps_nth F n * z ^ n) sums f z"
  shows   "f has_fps_expansion F"
  unfolding has_fps_expansion_def
proof
  from assms(1,2) obtain R where R: "ball 0 R \<subseteq> A" "R > 0"
    using open_contains_ball_eq by blast
  have "summable (\<lambda>n. fps_nth F n * z ^ n)" if "z \<in> A" for z
    using that assms(3)[of z] by (auto simp: sums_iff)
  obtain x where x: "x \<in> A - {0}"
    using assms(1,2) by (metis all_not_in_conv insert_Diff_single insert_absorb not_open_singleton)
  have "summable (\<lambda>n. fps_nth F n * x ^ n)"
    using assms(3)[of x] x by (auto simp: sums_iff)
  hence "fps_conv_radius F \<ge> norm x"
    unfolding fps_conv_radius_def using conv_radius_geI by blast
  moreover have "norm x > 0"
    using x by auto
  ultimately show "fps_conv_radius F > 0"
    using ereal_less(2) order_less_le_trans by blast

  have "eventually (\<lambda>z. z \<in> A) (nhds 0)"
    using assms(1,2) by (intro eventually_nhds_in_open)
  thus "eventually (\<lambda>z. eval_fps F z = f z) (nhds 0)"
  proof eventually_elim
    case (elim z)
    with assms(3)[of z] have "(\<lambda>n. fps_nth F n * z ^ n) sums f z"
      by blast
    thus "eval_fps F z = f z"
      unfolding eval_fps_def by (auto simp: sums_iff)
  qed
qed

(* TODO: Move *)
lemma has_fps_expansion_lambert [fps_expansion_intros]:
  "lambert (\<lambda>n. complex_of_nat n ^ k) has_fps_expansion 
     of_nat.fps (Abs_fps (divisor_sigma k))"
proof (rule has_fps_expansionI)
  fix z :: complex
  assume z: "z \<in> ball 0 1"
  show "(\<lambda>n. fps_nth (of_nat.fps (Abs_fps (divisor_sigma k))) n * z ^ n) sums
           lambert (\<lambda>n. complex_of_nat n ^ k) z" 
    using z divisor_sigma_powser_conv_lambert[of z k] by (simp add: divisor_sigma_of_nat)
qed auto


locale Eisenstein_G_even =
  fixes k :: nat
  assumes k: "even k \<and> k > 2"
begin

lemma has_laurent_expansion_at_cusp [laurent_expansion_intros]:
  "Eisenstein_G.fourier k has_laurent_expansion fps_to_fls (Eisenstein_G_fps_at_cusp k)"
proof -
  have "(\<lambda>q. 2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) q))
          has_laurent_expansion fps_to_fls (Eisenstein_G_fps_at_cusp k)"
    unfolding Eisenstein_G_fps_at_cusp_def
    by (intro has_laurent_expansion_fps fps_expansion_intros)
  also have "?this \<longleftrightarrow> Eisenstein_G.fourier k has_laurent_expansion
                         fps_to_fls (Eisenstein_G_fps_at_cusp k)"
  proof (rule has_laurent_expansion_cong)
    have "eventually (\<lambda>q. q \<in> ball 0 1 \<and> q \<noteq> 0 \<and> q \<in> UNIV) (at (0 :: complex))"
      by (intro eventually_at_ball') auto
    thus "eventually (\<lambda>q. 2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) q) =
                           Eisenstein_G.fourier k q) (at 0)"
    proof eventually_elim
      case (elim q)
      have "eval_mero_uhp (\<G> k) (cusp_q_inv (Suc 0) q) =
            Eisenstein_G k (cusp_q_inv (Suc 0) q)"
        using elim by (subst eval_mero_uhp_G) (auto intro!: Im_cusp_q_inv_gt)
      hence "Eisenstein_G.fourier k q = Eisenstein_G k (cusp_q_inv 1 q)"
        using elim unfolding Eisenstein_G.fourier_def by simp
      also have "\<dots> = 2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) q)"
        using elim k by (subst Eisenstein_G_fourier_expansion) (auto intro: Im_cusp_q_inv_gt)
      finally show ?case ..
    qed
  qed auto
  finally show ?thesis .
qed

text \<open>
  The following gives an explicit power series expansion for the Eisenstein series \<open>G\<^sub>k(q)\<close>
  for even \<open>k\<close> where \<open>q \<rightarrow> \<i>\<infinity>\<close>. This is also equivalent to Apostol's Theorem 1.18.
\<close>
theorem has_fps_expansion_at_cusp [fps_expansion_intros]:
  "Eisenstein_G.fourier k has_fps_expansion Eisenstein_G_fps_at_cusp k"
proof -
  have "Eisenstein_G.fourier k \<midarrow>0\<rightarrow> fls_nth (fps_to_fls (Eisenstein_G_fps_at_cusp k)) 0"
    by (intro has_laurent_expansion_imp_tendsto_0[OF has_laurent_expansion_at_cusp]
              fls_subdegree_fls_to_fps_gt0)
  then have "Eisenstein_G.fourier k \<midarrow>0\<rightarrow> 2 * zeta (of_nat k)"
    by (auto simp: Eisenstein_G_fps_at_cusp_def)
  then have "Eisenstein_G.fourier k 0 = Eisenstein_G_fps_at_cusp k $ 0" 
    unfolding Eisenstein_G_fps_at_cusp_def 
    by (simp add: Eisenstein_G.fourier_0_aux Eisenstein_G.fourier_tendsto_0_iff)
  then show ?thesis 
    unfolding has_fps_expansion_to_laurent using has_laurent_expansion_at_cusp
    by simp
qed

lemma fourier_0 [simp]: "Eisenstein_G.fourier k 0 = 2 * zeta k"
proof -
  have "Eisenstein_G.fourier k 0 = fps_nth (Eisenstein_G_fps_at_cusp k) 0"
    using has_fps_expansion_at_cusp by (simp add: has_fps_expansion_imp_0_eq_fps_nth_0)
  also have "\<dots> = 2 * zeta k"
    by (simp add: Eisenstein_G_fps_at_cusp_def)
  finally show ?thesis .
qed

sublocale fourier_expansion_meromorphic "\<G> k" "Suc 0"
proof
  show "Eisenstein_G.fourier k meromorphic_on {0}"
    using has_laurent_expansion_at_cusp by (auto simp: Meromorphic1.meromorphic_on_def)
qed

end

text \<open>
  And the analogous results for \<open>g\<^sub>2\<close> and \<open>g\<^sub>3\<close>:
\<close>

lemma eventually_\<G>_eq_at_cusp:
  "eventually (\<lambda>w. eval_mero_uhp (\<G> k) w = Eisenstein_G k w) at_cusp"
  using eventually_at_cusp[of 0] by eventually_elim auto

lemma eventually_g\<^sub>2_eq_at_cusp:
  "eventually (\<lambda>w. eval_mero_uhp g\<^sub>2 w = Eisenstein_g2 w) at_cusp"
  using eventually_at_cusp[of 0] by eventually_elim auto

lemma eventually_g\<^sub>3_eq_at_cusp:
  "eventually (\<lambda>w. eval_mero_uhp g\<^sub>3 w = Eisenstein_g3 w) at_cusp"
  using eventually_at_cusp[of 0] by eventually_elim auto

lemma eventually_modular_discr_eq_at_cusp:
  "eventually (\<lambda>w. eval_mero_uhp \<Delta> w = modular_discr w) at_cusp"
  using eventually_at_cusp[of 0] by eventually_elim auto

lemma Eisenstein_g2_at_cusp: "(Eisenstein_g2 \<longlongrightarrow> 4 / 3 * pi ^ 4) at_cusp"
proof -
  interpret Eisenstein_G_even 4
    by unfold_locales auto
  have F: "Eisenstein_G.fourier 4 \<midarrow>0\<rightarrow> 2 * zeta 4"
    using has_fps_expansion_at_cusp[THEN has_fps_expansion_imp_tendsto_0
        , unfolded Eisenstein_G_fps_at_cusp_def, simplified] 
    unfolding tendsto_nhds_iff by blast+

  have "(eval_mero_uhp \<G>\<^sub>4 \<longlongrightarrow> 2 * zeta 4) at_cusp"
    using F Eisenstein_G.fourier_tendsto_0_iff
    by auto
  then have "(Eisenstein_G 4 \<longlongrightarrow> 2 * zeta 4) at_cusp"
    apply (elim Lim_transform_eventually)
    using eventually_\<G>_eq_at_cusp .
  then have "(Eisenstein_g2  \<longlongrightarrow> 60 * (2 * zeta 4)) at_cusp"
    unfolding Eisenstein_g2_def [abs_def]
    by (auto intro!: tendsto_eq_intros)+
  thus ?thesis
    by (simp add: zeta_even_numeral fact_numeral)
qed

lemma Eisenstein_g2_fourier_0 [simp]: "Eisenstein_g2.fourier 0 = 4 / 3 * pi ^ 4"
proof (rule Eisenstein_g2.fourier_0_aux)
  show "(eval_mero_uhp g\<^sub>2 \<longlongrightarrow> complex_of_real (4 / 3 * pi ^ 4)) at_cusp"
    by (rule Lim_transform_eventually[OF Eisenstein_g2_at_cusp])
       (use eventually_g\<^sub>2_eq_at_cusp in \<open>simp add: eq_commute\<close>)
qed

lemma Eisenstein_g2_fourier_altdef: "Eisenstein_g2.fourier q = 60 * Eisenstein_G.fourier 4 q"
proof (cases "q = 0")
  case [simp]: True
  interpret Eisenstein_G_even 4
    by unfold_locales auto
  show ?thesis
    by (simp add: zeta_even_numeral fact_numeral)
next
  case False
  define Q where "Q = (cusp_q_inv (Suc 0) q)"
  have "eval_mero_uhp g\<^sub>2 Q = 60 * eval_mero_uhp \<G>\<^sub>4 Q"
  proof (cases "Im Q>0")
    case True
    show ?thesis
      unfolding eval_mero_uhp_G[OF True] eval_mero_uhp_g\<^sub>2[OF True]
      by (meson Eisenstein_g2_def)
  next
    case False
    then show ?thesis by (simp add: eval_mero_uhp_outside)
  qed
  then show ?thesis
    unfolding Eisenstein_g2.fourier_nz_eq[OF False] Q_def 
    using False by (simp add:  Eisenstein_G.fourier_def)
qed

corollary Eisenstein_g2_has_fps_expansion_at_cusp [fps_expansion_intros]:
  "Eisenstein_g2.fourier has_fps_expansion
      fps_const (4 / 3 * pi ^ 4) * (1 + 240 * of_int.fps (Abs_fps (divisor_sigma 3)))"
  (is "_ has_fps_expansion ?F")
proof -
  interpret Eisenstein_G_even 4
    by unfold_locales auto
  have "(\<lambda>\<tau>. 60 * Eisenstein_G.fourier 4 \<tau>) has_fps_expansion ?F"
    by (rule has_fps_expansion_schematicI, (rule fps_expansion_intros)+)
       (simp add: Eisenstein_G_fps_at_cusp_def fact_numeral zeta_4 fps_eq_iff
                  numeral_fps_const algebra_simps)
  thus ?thesis
    by (simp add: Eisenstein_g2_fourier_altdef [abs_def])
qed

interpretation Eisenstein_g2: fourier_expansion_meromorphic g\<^sub>2 "Suc 0"
proof
  show "Eisenstein_g2.fourier meromorphic_on {0}"
    using Eisenstein_g2_has_fps_expansion_at_cusp
    by (simp add: analytic_on_imp_meromorphic_on has_fps_expansion_imp_analytic_0)
qed


lemma Eisenstein_g3_at_cusp: "(Eisenstein_g3 \<longlongrightarrow> 8 / 27 * pi ^ 6) at_cusp"
proof -
  interpret Eisenstein_G_even 6
    by unfold_locales auto
  have F: "Eisenstein_G.fourier 6 \<midarrow>0\<rightarrow> 2 * zeta 6"
    using has_fps_expansion_at_cusp[THEN has_fps_expansion_imp_tendsto_0
        , unfolded Eisenstein_G_fps_at_cusp_def, simplified] 
    unfolding tendsto_nhds_iff by blast+

  have "(eval_mero_uhp \<G>\<^sub>6 \<longlongrightarrow> 2 * zeta 6) at_cusp"
    using F Eisenstein_G.fourier_tendsto_0_iff
    by auto
  then have "(Eisenstein_G 6 \<longlongrightarrow> 2 * zeta 6) at_cusp"
    apply (elim Lim_transform_eventually)
    using eventually_\<G>_eq_at_cusp .
  then have "(Eisenstein_g3  \<longlongrightarrow> 140 * (2 * zeta 6)) at_cusp"
    unfolding Eisenstein_g3_def [abs_def]
    by (auto intro!: tendsto_eq_intros)+
  thus ?thesis
    by (simp add: zeta_even_numeral fact_numeral)
qed

lemma Eisenstein_g3_fourier_0 [simp]: "Eisenstein_g3.fourier 0 = 8 / 27 * pi ^ 6"
proof (rule Eisenstein_g3.fourier_0_aux)
  show "(eval_mero_uhp g\<^sub>3 \<longlongrightarrow> complex_of_real (8 / 27 * pi ^ 6)) at_cusp"
    by (rule Lim_transform_eventually[OF Eisenstein_g3_at_cusp])
       (use eventually_g\<^sub>3_eq_at_cusp in \<open>simp add: eq_commute\<close>)
qed

lemma Eisenstein_g3_fourier_altdef: "Eisenstein_g3.fourier q = 140 * Eisenstein_G.fourier 6 q"
proof (cases "q = 0")
  case [simp]: True
  interpret Eisenstein_G_even 6
    by unfold_locales auto
  show ?thesis
    by (simp add: zeta_even_numeral fact_numeral)
next
  case False
  define Q where "Q = (cusp_q_inv (Suc 0) q)"
  have "eval_mero_uhp g\<^sub>3 Q = 140 * eval_mero_uhp \<G>\<^sub>6 Q"
  proof (cases "Im Q>0")
    case True
    show ?thesis
      unfolding eval_mero_uhp_G[OF True] eval_mero_uhp_g\<^sub>3[OF True]
      by (meson Eisenstein_g3_def)
  next
    case False
    then show ?thesis by (simp add: eval_mero_uhp_outside)
  qed
  then show ?thesis
    unfolding Eisenstein_g3.fourier_nz_eq[OF False] Q_def 
    using False by (simp add:  Eisenstein_G.fourier_def)
qed

corollary Eisenstein_g3_has_fps_expansion_at_cusp [fps_expansion_intros]:
  "Eisenstein_g3.fourier has_fps_expansion
      fps_const (8 / 27 * pi ^ 6) * (1 - 504 * of_int.fps (Abs_fps (divisor_sigma 5)))"
  (is "_ has_fps_expansion ?F")
proof -
  interpret Eisenstein_G_even 6
    by unfold_locales auto
  
  have "(\<lambda>\<tau>. 140 * Eisenstein_G.fourier 6 \<tau>) has_fps_expansion ?F"
    by (rule has_fps_expansion_schematicI, (rule fps_expansion_intros)+)
       (simp add: Eisenstein_G_fps_at_cusp_def fact_numeral zeta_6 fps_eq_iff
                  numeral_fps_const algebra_simps)
  thus ?thesis
    by (simp add: Eisenstein_g3_fourier_altdef [abs_def])
qed

interpretation Eisenstein_g3: fourier_expansion_meromorphic g\<^sub>3 "Suc 0"
proof
  show "Eisenstein_g3.fourier meromorphic_on {0}"
    using Eisenstein_g3_has_fps_expansion_at_cusp
    by (simp add: analytic_on_imp_meromorphic_on has_fps_expansion_imp_analytic_0)
qed


subsubsection \<open>The modular discriminant \<open>\<Delta>\<close>\<close>

definition ramanujan_tau :: "nat \<Rightarrow> int" where
  "ramanujan_tau n =
     (let F = (\<lambda>k. Abs_fps (divisor_sigma k))
      in  fps_nth ((1 + 240 * F 3) ^ 3 - (1 - 504 * F 5) ^ 2) n div 12 ^ 3)"

lemma atLeastAtMost_nat_numeral_right:
  "a \<le> numeral b \<Longrightarrow> {(a::nat)..numeral b} = insert (numeral b) {a..pred_numeral b}"
  by (auto simp: numeral_eq_Suc)

lemma ramanujan_tau_0 [simp]: "ramanujan_tau 0 = 0"
  and ramanujan_tau_1: "ramanujan_tau (Suc 0) = 1"
  and ramanujan_tau_2: "ramanujan_tau 2 = -24"
  and ramanujan_tau_3: "ramanujan_tau 3 = 252"
  and ramanujan_tau_4: "ramanujan_tau 4 = -1472"
  and ramanujan_tau_5: "ramanujan_tau 5 = 4830"
  and ramanujan_tau_6: "ramanujan_tau 6 = -6048"
  by (simp_all add: ramanujan_tau_def power2_eq_square power3_eq_cube fps_mult_nth fps_numeral_nth
                    divisor_sigma_naive fold_atLeastAtMost_nat.simps atLeastAtMost_nat_numeral_right
               flip: numeral_2_eq_2)

lemma modular_discr_at_cusp: "(modular_discr \<longlongrightarrow> 0) at_cusp"
proof -
  note [tendsto_intros] = Eisenstein_g2_at_cusp Eisenstein_g3_at_cusp
  show ?thesis
    unfolding modular_discr_def
    by (rule tendsto_eq_intros refl)+ (simp add: algebra_simps power2_eq_square power3_eq_cube)
qed

lemma modular_discr_fourier_0 [simp]: "modular_discr.fourier 0 = 0"
proof (rule modular_discr.fourier_0_aux)
  show "(eval_mero_uhp \<Delta> \<longlongrightarrow> 0) at_cusp"
    by (rule Lim_transform_eventually[OF modular_discr_at_cusp])
       (use eventually_modular_discr_eq_at_cusp in \<open>simp add: eq_commute\<close>)
qed

lemma modular_discr_fourier_altdef:
  "modular_discr.fourier q = Eisenstein_g2.fourier q ^ 3 - 27 * (Eisenstein_g3.fourier q) ^ 2"
proof (cases "q = 0")
  case False
  define Q where "Q = cusp_q_inv (Suc 0) q"
  have "eval_mero_uhp \<Delta> Q = eval_mero_uhp g\<^sub>2 Q ^ 3 - 27 * (eval_mero_uhp g\<^sub>3 Q)\<^sup>2"
  proof (cases "Im Q>0")
    case True
    then show ?thesis 
      by (simp add:modular_discr_def)
  next
    case False
    then show ?thesis by (simp add: eval_mero_uhp_outside)
  qed
  then show ?thesis
    unfolding modular_discr.fourier_nz_eq[OF False] Eisenstein_g2.fourier_nz_eq[OF False]
              Eisenstein_g3.fourier_nz_eq[OF False] Q_def
    by simp
next
  case [simp]: True
  show ?thesis
    by (simp add: eval_nat_numeral algebra_simps)
qed

definition fps_modular_discr :: "complex fps" where
  "fps_modular_discr = fps_const ((2 * pi) ^ 12) * of_int.fps (Abs_fps ramanujan_tau)"

lemma fps_modular_discr_nonzero [simp]: "fps_modular_discr \<noteq> 0"
proof -
  have "fps_nth fps_modular_discr 1 \<noteq> fps_nth 0 1"
    by (auto simp: fps_modular_discr_def ramanujan_tau_1)
  thus ?thesis by metis
qed  

text \<open>Theorem 1.19\<close>
theorem modular_discr_has_fps_expansion_at_cusp [fps_expansion_intros]:
          "modular_discr.fourier has_fps_expansion fps_modular_discr"
    and conv_radius_ramanujan_tau: "conv_radius (\<lambda>n. of_int (ramanujan_tau n) :: complex) \<ge> 1"
    and fps_conv_radius_modular_discr:
          "fps_conv_radius fps_modular_discr \<ge> 1"
proof -
  define c where "c = complex_of_real ((2 * pi) ^ 12)"
  define A :: "int fps" where "A = Abs_fps (divisor_sigma 3)"
  define B :: "int fps" where "B = Abs_fps (divisor_sigma 5)"
  define C :: "int fps" where "C = Abs_fps (\<lambda>n. (5 * fps_nth A n + 7 * fps_nth B n) div 12)"
  define D where "D = 100 * A ^ 2 - 147 * B ^ 2 + 8000 * A ^ 3"

  define F0 :: "complex fps" where
    "F0 = (fps_const (complex_of_real (4 / 3 * pi ^ 4)) * of_int.fps (1 + 240 * A)) ^ 3 -
          27 * (fps_const (complex_of_real (8 / 27 * pi ^ 6)) * of_int.fps (1 - 504 * B)) ^ 2"
  define F :: "complex fps"  where "F = fps_modular_discr"

  have "12 dvd 5 * fps_nth A n + 7 * fps_nth B n" for n :: nat
  proof -
    have "12 dvd 5 * d ^ 3 + 7 * d ^ 5" for d :: nat
    proof -
      have "d mod 12 \<in> {..<12}"
        by simp
      hence "[0 = 5 * (d mod 12) ^ 3 + 7 * (d mod 12) ^ 5] (mod 12)"
        unfolding lessThan_nat_numeral arith_simps pred_numeral_simps lessThan_0
        by (elim insertE emptyE) (auto simp: Cong.cong_def)
      also have "[5 * (d mod 12) ^ 3 + 7 * (d mod 12) ^ 5 = 5 * d ^ 3 + 7 * d ^ 5] (mod 12)"
        by (intro cong_add cong_mult cong_pow) auto
      finally show ?thesis
        by (metis cong_0_iff cong_iff_lin_nat)
    qed
    hence "int 12 dvd int (\<Sum>d | d dvd n. 5 * d ^ 3 + 7 * d ^ 5)"
      unfolding int_dvd_int_iff by (intro dvd_sum) auto
    also have "\<dots> = 5 * fps_nth A n + 7 * fps_nth B n"
      by (simp add: A_def B_def divisor_sigma_def sum.distrib algebra_simps 
                    sum_distrib_left sum_distrib_right)
    finally show ?thesis by simp
  qed
  hence "5 * A + 7 * B = 12 * C"
    by (auto simp: A_def B_def C_def fps_eq_iff numeral_fps_const)

  have "(1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 =
             12 ^ 2 * (5 * A + 7 * B) + 12 ^ 3 * D"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube D_def)
  also have "5 * A + 7 * B = 12 * C"
    by fact
  also have "12 ^ 2 * (12 * C) = 12 ^ 3 * C"
    by (simp add: eval_nat_numeral)
  finally have eq2: "(1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 = 12 ^ 3 * (C + D)"
    by (simp add: algebra_simps)

  have "(\<lambda>q. Eisenstein_g2.fourier q ^ 3 - 27 * (Eisenstein_g3.fourier q) ^ 2) has_fps_expansion F0"
    apply (rule has_fps_expansion_schematicI, (rule fps_expansion_intros refl)+)
    by  (simp add: F0_def numeral_fps_const A_def B_def)
  also have "(\<lambda>q. Eisenstein_g2.fourier q ^ 3 - 27 * (Eisenstein_g3.fourier q) ^ 2) = modular_discr.fourier"
    by (simp add: modular_discr_fourier_altdef [abs_def])
  finally have has_exp: "modular_discr.fourier has_fps_expansion F0" .

  have "F0 = fps_const (64 / 27 * pi ^ 12) * of_int.fps ((1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2)"
    by (rule fps_ext)
       (simp add: F0_def algebra_simps numeral_fps_const power2_eq_square power3_eq_cube)
  also note eq2
  also have "of_int.fps (12 ^ 3 * (C + D)) = 12 ^ 3 * of_int.fps (C + D)"
    by (simp add: algebra_simps)
  also have "fps_const (complex_of_real (64 / 27 * pi ^ 12)) * (12 ^ 3 * of_int.fps (C + D)) =
             fps_const (complex_of_real (64 / 27 * pi ^ 12) * 12 ^ 3) * of_int.fps (C + D)"
    by (subst fps_const_mult [symmetric]) (simp_all only: numeral_fps_const mult_ac fps_const_power)
  also have "complex_of_real (64 / 27 * pi ^ 12) * 12 ^ 3 = of_real ((2 * pi) ^ 12)"
    by (simp add: power3_eq_cube)
  also have "C + D = Abs_fps ramanujan_tau"
  proof (rule fps_ext)
    fix n :: nat
    have "ramanujan_tau n = fps_nth ((1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2) n div 12 ^ 3"
      by (simp add: ramanujan_tau_def [abs_def] A_def B_def)
    also note eq2
    also have "fps_nth (12 ^ 3 * (C + D)) n div 12 ^ 3 = fps_nth (C + D) n"
      by (simp add: numeral_fps_const)
    finally show "fps_nth (C + D) n = fps_nth (Abs_fps ramanujan_tau) n"
      by simp
  qed
  finally have "F0 = F"
    unfolding F_def c_def fps_modular_discr_def
    by (simp only: F0_def F_def c_def)
  show "modular_discr.fourier has_fps_expansion F"
    using has_exp \<open>F0 = F\<close> by simp

  have "fps_conv_radius F0 \<ge> 1"
    using fps_conv_radius_divisor_sigma[of 3] fps_conv_radius_divisor_sigma[of 5]
    unfolding F0_def A_def B_def of_int.fps_add of_int.fps_mult of_int.fps_diff
    by (intro fps_conv_radius_diff_ge fps_conv_radius_mult_ge fps_conv_radius_add_ge
              order.trans[OF _ fps_conv_radius_power] fps_conv_radius_divisor_sigma) auto
  with \<open>F0 = F\<close> show "fps_conv_radius F \<ge> 1" by simp
  hence "fps_conv_radius (Abs_fps (\<lambda>n. of_int (ramanujan_tau n) :: complex)) \<ge> 1"
    apply (simp add: F_def c_def fps_conv_radius_cmult_left)
    unfolding fps_modular_discr_def by (simp add: fps_conv_radius_cmult_left)
  thus "conv_radius (\<lambda>n. of_int (ramanujan_tau n) :: complex) \<ge> 1"
    by (simp add: fps_conv_radius_def F_def)
qed

interpretation modular_discr: fourier_expansion_meromorphic \<Delta> "Suc 0"
proof
  show "modular_discr.fourier meromorphic_on {0}"
    using modular_discr_has_fps_expansion_at_cusp
    by (simp add: analytic_on_imp_meromorphic_on has_fps_expansion_imp_analytic_0)
qed

(* TODO: there must be an easier way to do this *)
lemma not_is_pole_modular_discr_fourier [simp]: "\<not>is_pole modular_discr.fourier q"
proof (cases "q = 0")
  case True
  have "\<not>is_pole modular_discr.fourier 0"
    by (meson analytic_at_imp_isCont at_cusp_neq_bot has_fps_expansion_imp_analytic_0 isContD 
              modular_discr.fourier_is_pole_0_iff modular_discr.fourier_tendsto_0_iff 
              modular_discr_has_fps_expansion_at_cusp not_tendsto_and_filterlim_at_infinity)
  thus ?thesis
    using True by simp
next
  case False
  show ?thesis
  proof
    assume *: "is_pole modular_discr.fourier q"
    hence q: "norm q < 1"
      using modular_discr.not_pole_eval_fourier_outside by force
    hence q': "Im (cusp_q_inv 1 q) > 0"
      using False by (auto simp: Im_cusp_q_inv_gt)
    hence "is_pole (eval_mero_uhp \<Delta>) (cusp_q_inv 1 q)"
      by (subst modular_discr.fourier_is_pole_cusp_q_iff [symmetric]) (use * False in auto)
    moreover have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at (cusp_q_inv 1 q))"
      using q q' False by (intro eventually_at_in_open') (auto simp: open_halfspace_Im_gt)
    hence "eventually (\<lambda>z. eval_mero_uhp \<Delta> z = modular_discr z) (at (cusp_q_inv 1 q))"
      by eventually_elim auto
    ultimately have "is_pole modular_discr (cusp_q_inv 1 q)"
      using is_pole_transform by blast
    moreover have "modular_discr analytic_on {cusp_q_inv 1 q}"
      by (intro analytic_intros) (use False q q' in \<open>auto simp: complex_is_Real_iff\<close>)
    ultimately show False
      by (simp add: analytic_at_imp_no_pole)
  qed
qed

lemma modular_discr_fourier_expansion:
  assumes \<tau>: "Im \<tau> > 0"
  shows   "(\<lambda>n. (2 * pi) ^ 12 * ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) sums modular_discr \<tau>"
proof -
  define F :: "complex fps"
    where "F = fps_const ((2 * pi) ^ 12) * of_int.fps (Abs_fps ramanujan_tau)"
  have "(\<lambda>n. fps_nth F n * cusp_q 1 \<tau> ^ n) sums eval_fps F (cusp_q 1 \<tau>)"
  proof (rule sums_eval_fps)
    have "ereal (norm (cusp_q 1 \<tau>)) < 1"
      using assms by (simp add: cusp_q_def)
    also have "\<dots> \<le> fps_conv_radius F"
      unfolding F_def 
      using fps_conv_radius_modular_discr fps_modular_discr_def by presburger
    finally show "ereal (norm (cusp_q 1 \<tau>)) < fps_conv_radius F" .
  qed
  also have "eval_fps F (cusp_q 1 \<tau>) = modular_discr.fourier (cusp_q 1 \<tau>)"
  proof (rule has_fps_expansion_imp_eval_fps_eq)
    show "cmod (cusp_q 1 \<tau>) < 1"
      using assms by (simp add: cusp_q_def)
    show "modular_discr.fourier has_fps_expansion F"
      unfolding F_def using modular_discr_has_fps_expansion_at_cusp
      using fps_modular_discr_def by presburger
    show "modular_discr.fourier holomorphic_on ball 0 1"
      by (intro holomorphic_intros) auto
  qed
  also have "modular_discr.fourier (cusp_q 1 \<tau>) = modular_discr \<tau>"
    using assms by simp
  finally show ?thesis unfolding modular_discr.fourier_cusp_q
    by (simp add: F_def mult_ac cusp_q_def flip: exp_of_nat_mult)
qed


lemma modular_discr_fourier_expansion':
  assumes \<tau>: "Im \<tau> > 0"
  shows   "(\<lambda>n. (2 * pi) ^ 12 * ramanujan_tau n * cusp_q 1 \<tau> ^ n) sums modular_discr \<tau>"
  using modular_discr_fourier_expansion[OF assms]
  by (simp flip: exp_of_nat_mult add: mult_ac cusp_q_def)

lemma modular_discr_fourier_expansion'':
  fixes \<tau> :: complex
  assumes "Im \<tau> > 0"
  shows   "(\<lambda>n. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) summable_on {1..}"
    and   "modular_discr \<tau> =
             (2 * pi) ^ 12 * (\<Sum>\<^sub>\<infinity> n\<in>{1..}. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>))"
proof -
  have "summable (\<lambda>n. norm (of_int (ramanujan_tau n) * cusp_q 1 \<tau> ^ n))"
    by (intro abs_summable_in_conv_radius less_le_trans[OF _ conv_radius_ramanujan_tau])
       (use assms in \<open>auto simp: cusp_q_def\<close>)
  hence "summable (\<lambda>n. norm (ramanujan_tau n * exp (2 * pi * \<i> * \<tau>) ^ n))"
    by (simp add: mult_ac cusp_q_def flip: exp_of_nat_mult)
  hence *: "summable (\<lambda>n. norm (ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)))"
    by (simp flip: exp_of_nat_mult add: mult_ac)
  hence "(\<lambda>n. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) summable_on UNIV"
    by (rule norm_summable_imp_summable_on)
  thus "(\<lambda>n. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) summable_on {1..}"
    by (rule summable_on_subset) auto

  have "summable (\<lambda>n. of_real ((2 * pi) ^ 12) * norm (ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)))"
    by (intro summable_mult *)
  hence "((\<lambda>n. (2 * pi) ^ 12 * ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) has_sum
         modular_discr \<tau>) UNIV"
    using modular_discr_fourier_expansion[of \<tau>] assms
    by (intro norm_summable_imp_has_sum) (auto simp: mult_ac norm_mult norm_power)
  also have "?this \<longleftrightarrow> ((\<lambda>n. (2 * pi) ^ 12 * ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)) has_sum
                        modular_discr \<tau>) {1..}"
    by (intro has_sum_cong_neutral) (auto simp: not_le)
  finally have "modular_discr \<tau> =
                  (\<Sum>\<^sub>\<infinity> n\<in>{1..}. of_real ((2 * pi) ^ 12) * (ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>)))"
    by (simp add: infsumI mult_ac)
  also have "\<dots> = (2 * pi) ^ 12 * (\<Sum>\<^sub>\<infinity> n\<in>{1..}. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>))"
    by (subst infsum_cmult_right') auto
  finally show "modular_discr \<tau> =
                  (2 * pi) ^ 12 * (\<Sum>\<^sub>\<infinity> n\<in>{1..}. ramanujan_tau n * exp (2 * pi * \<i> * n * \<tau>))" .
qed
  


subsubsection \<open>Klein's \<open>j\<close> function\<close>

definition Klein_c :: "nat \<Rightarrow> int" where
  "Klein_c n = (let A = of_nat.fps (Abs_fps (divisor_sigma 3));
                    C = fps_left_inverse (fps_shift 1 (Abs_fps ramanujan_tau)) 1
                in  fps_nth (C * (1 + 240 * A) ^ 3) (n + 1))"

definition fls_Klein_j :: "complex fls"
  where "fls_Klein_j = fls_X_inv + fps_to_fls (Abs_fps (\<lambda>x. of_int (Klein_c x)))"

lemma fps_left_inverse_constructor_numeral:
  "fps_left_inverse_constructor a b (numeral n) =
     - (\<Sum>i = 0..pred_numeral n. fps_left_inverse_constructor a b i * a $ (Suc (pred_numeral n) - i)) * b"
  unfolding numeral_eq_Suc fps_left_inverse_constructor.simps ..

lemma Klein_c_0: "Klein_c 0 = 744"
  and Klein_c_1: "Klein_c (Suc 0) = 196884"
  and Klein_c_2: "Klein_c 2 = 21493760"
  and Klein_c_3: "Klein_c 3 = 864299970"
  and Klein_c_4: "Klein_c 4 = 20245856256"
  using ramanujan_tau_2 ramanujan_tau_3 ramanujan_tau_4 ramanujan_tau_5 ramanujan_tau_6
  by (simp_all add: Klein_c_def divisor_sigma_naive fold_atLeastAtMost_nat.simps
                    power3_eq_cube Let_def fps_mult_nth atLeastAtMost_nat_numeral_right
                    numeral_fps_const fps_left_inverse_constructor_numeral
               flip: numeral_2_eq_2)

lemma fls_Klein_j_subdegree [simp]: "fls_subdegree fls_Klein_j = -1"
  by (intro fls_subdegree_eqI) (auto simp: fls_Klein_j_def Klein_c_0)

lemma fls_Klein_j_nonzero [simp]: "fls_Klein_j \<noteq> 0"
proof -
  have "fls_nth fls_Klein_j 0 = 744"
    by (simp add: fls_Klein_j_def Klein_c_0)
  thus ?thesis
    by auto
qed


text \<open>Theorem 1.20\<close>

theorem Klein_j_has_laurent_expansion_at_cusp [laurent_expansion_intros]:
  "Klein_j.fourier has_laurent_expansion fls_Klein_j"
proof -
  define A :: "complex fps" where "A = of_nat.fps (Abs_fps (divisor_sigma 3))"
  define B :: "complex fps" where "B = of_int.fps (Abs_fps ramanujan_tau)"
  define C :: "complex fps" where
    "C = of_int.fps (fps_left_inverse (fps_shift 1 (Abs_fps ramanujan_tau)) 1)"
  have "fps_nth B 1 \<noteq> 0"
    by (simp add: B_def ramanujan_tau_1)
  hence [simp]: "B \<noteq> 0"
    by auto

  note [laurent_expansion_intros] =
    has_laurent_expansion_fps[OF modular_discr_has_fps_expansion_at_cusp]
    has_laurent_expansion_fps[OF Eisenstein_g2_has_fps_expansion_at_cusp]

  define F where "F = fps_to_fls ((1 + 240 * A) ^ 3) / fps_to_fls B"

  have "(\<lambda>z. 12 ^ 3 * (Eisenstein_g2.fourier z ^ 3 / modular_discr.fourier z)) has_laurent_expansion
          (1 + 240 * fps_to_fls A) ^ 3 / fps_to_fls B"
    by (rule has_laurent_expansion_schematicI, (rule laurent_expansion_intros)+)
       (simp add: fps_modular_discr_def A_def B_def fls_times_fps_to_fls fls_const_power divide_simps
             flip: fls_const_mult_const fls_const_divide_const)
  also have "?this \<longleftrightarrow> Klein_j.fourier has_laurent_expansion F"
  proof (rule has_laurent_expansion_cong)
    have "eventually (\<lambda>z::complex. z \<in> ball 0 1 - {0}) (at 0)"
      by (auto simp: eventually_at intro: exI[of _ 1])
    thus "eventually (\<lambda>z. 12 ^ 3 * (Eisenstein_g2.fourier z ^ 3 / modular_discr.fourier z) =
                          Klein_j.fourier z) (at 0)"
      by eventually_elim
         (simp add: Klein_j.fourier_def Klein_j_def Eisenstein_g2.fourier_def 
                    modular_discr_fourier_altdef Im_cusp_q_inv_gt Klein_J_def modular_discr_def
                    Eisenstein_g3.fourier_def)   
  qed (auto simp: fps_to_fls_power fps_to_fls_plus fls_times_fps_to_fls F_def)
  finally have has_exp: "Klein_j.fourier has_laurent_expansion F" .

  note F_def
  also have B_eq: "B = fps_X * fps_shift 1 B"
    by (simp add: B_def fps_eq_iff)
  also have "fps_to_fls ((1 + 240 * A) ^ 3) / fps_to_fls (fps_X * fps_shift 1 B) =
             1 / fls_X * (fps_to_fls ((1 + 240 * A) ^ 3) * inverse (fps_to_fls (fps_shift 1 B)))"
    by (simp add: divide_simps fls_times_fps_to_fls del: fls_divide_X)
  also have "inverse (fps_to_fls (fps_shift 1 B)) = fps_to_fls (inverse (fps_shift 1 B))"
    by (intro fls_inverse_fps_to_fls subdegree_eq_0) (auto simp: B_def ramanujan_tau_1)
  also have "fps_left_inverse (fps_shift 1 (Abs_fps ramanujan_tau)) 1 *
               fps_shift 1 (Abs_fps ramanujan_tau) = 1"
    unfolding C_def by (intro fps_left_inverse) (auto simp: ramanujan_tau_1)
  hence "of_int.fps (fps_left_inverse (fps_shift 1 (Abs_fps ramanujan_tau)) 1 *
           fps_shift 1 (Abs_fps ramanujan_tau)) = of_int.fps 1"
    by (simp only: )
  hence "C * fps_shift 1 B = 1"
    unfolding of_int.fps_1 by (simp add: C_def B_def)
  hence "inverse (fps_shift 1 B) = C"
    by (metis fps_inverse_unique mult.commute)
  also have "fps_to_fls ((1 + 240 * A) ^ 3) * fps_to_fls C = fps_to_fls (C * (1 + 240 * A) ^ 3)"
    by (simp add: fls_times_fps_to_fls mult_ac)
  also have "1 / fls_X * \<dots> = fls_shift 1 (fps_to_fls (C * (1 + 240 * A) ^ 3))"
    by (simp add: fls_shifted_times_simps(2))
  also have "C * (1 + 240 * A) ^ 3 = 1 + fps_X * of_int.fps (Abs_fps Klein_c)"
    by (simp add: Klein_c_def C_def A_def B_def fps_eq_iff fps_nth_power_0 flip: of_int.fps_nth)
  also have "fls_shift 1 (fps_to_fls \<dots>) = fls_X_inv + fps_to_fls (Abs_fps Klein_c)"
    by (rule fls_eqI) (auto simp: nat_add_distrib)
  finally have F_eq: "F = fls_X_inv + fps_to_fls (Abs_fps Klein_c)" .

  from has_exp F_eq show ?thesis
    by (simp add: fls_Klein_j_def)
qed

lemma is_pole_Klein_j_fourier_iff [simp]: "is_pole Klein_j.fourier q \<longleftrightarrow> q = 0"
proof
  assume pole: "is_pole Klein_j.fourier q"
  show "q = 0"
  proof (rule ccontr)
    assume "q \<noteq> 0"
    from pole have "norm q < 1"
      using Klein_j.not_pole_eval_fourier_outside by force
    with \<open>q \<noteq> 0\<close> have q: "q \<in> ball 0 1 - {0}"
      by auto
    from q have q': "Im (cusp_q_inv 1 q) > 0"
      by (auto simp: Im_cusp_q_inv_gt)
    have "is_pole (eval_mero_uhp \<j>) (cusp_q_inv 1 q)"
      by (subst Klein_j.fourier_is_pole_cusp_q_iff [symmetric]) (use pole q in auto)
    moreover have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at (cusp_q_inv 1 q))"
      using q q' by (intro eventually_at_in_open') (auto simp: open_halfspace_Im_gt)
    hence "eventually (\<lambda>z. eval_mero_uhp \<j> z = Klein_j z) (at (cusp_q_inv 1 q))"
      by eventually_elim auto
    ultimately have "is_pole Klein_j (cusp_q_inv 1 q)"
      using is_pole_transform by blast
    moreover have "Klein_j analytic_on {cusp_q_inv 1 q}"
      by (intro analytic_intros) (use q q' in \<open>auto simp: complex_is_Real_iff\<close>)
    ultimately show False
      by (simp add: analytic_at_imp_no_pole)
  qed
next
  assume "q = 0"
  thus "is_pole Klein_j.fourier q"
    using has_laurent_expansion_imp_is_pole_0[OF Klein_j_has_laurent_expansion_at_cusp]
    by auto
qed

lemma Klein_J_fourier_altdef: "Klein_J.fourier q = Klein_j.fourier q / 12 ^ 3"
proof -
  have eq: "Klein_J.fourier q = Klein_j.fourier q / 12 ^ 3" if "q \<noteq> 0" for q
  proof (cases "norm q < 1")
    case True
    thus ?thesis using \<open>q \<noteq> 0\<close>
      by (simp add: Klein_J.fourier_def Klein_j.fourier_def Im_cusp_q_inv_gt Klein_J_conv_Klein_j 
                    eval_mero_uhp_outside)
  qed (simp add: Klein_J.eval_fourier_outside Klein_j.eval_fourier_outside)

  have "is_pole Klein_J.fourier 0"
  proof (rule is_pole_transform)
    show "is_pole (\<lambda>q. 1 / 12 ^ 3 * Klein_j.fourier q) 0"
      by (subst is_pole_cmult_iff) auto
  next
    have "eventually (\<lambda>q. q \<noteq> 0) (at (0 :: complex))"
      using eventually_neq_at_within by auto
    thus "eventually (\<lambda>q. 1 / 12 ^ 3 * Klein_j.fourier q = Klein_J.fourier q) (at 0)"
      by eventually_elim (use eq in auto)
  qed auto
  hence "Klein_J.fourier 0 = 0"
    by (meson Klein_J.fourier_def Klein_J.fourier_is_pole_0_iff at_cusp_neq_bot
              not_tendsto_and_filterlim_at_infinity)
  moreover have "Klein_j.fourier 0 = 0"
    by (metis Klein_j.fourier_def Klein_j.fourier_is_pole_0_iff at_cusp_neq_bot 
              is_pole_Klein_j_fourier_iff not_tendsto_and_filterlim_at_infinity)
  ultimately show ?thesis
    by (cases "q = 0") (use eq[of q] in auto)
qed    

lemma Klein_J_has_laurent_expansion_at_cusp [laurent_expansion_intros]:
  "Klein_J.fourier has_laurent_expansion (fls_const (1 / 12 ^ 3) * fls_Klein_j)"
proof -
  have "(\<lambda>q. Klein_j.fourier q / 12 ^ 3) has_laurent_expansion (fls_const (1 / 12 ^ 3) * fls_Klein_j)"
    by (rule has_laurent_expansion_schematicI, (rule laurent_expansion_intros)+)
       (auto simp flip: fls_const_divide_const)
  also have "(\<lambda>q. Klein_j.fourier q / 12 ^ 3) = Klein_J.fourier"
    using Klein_J_fourier_altdef by auto
  finally show ?thesis .
qed

interpretation Klein_j: fourier_expansion_meromorphic \<j> "Suc 0"
proof
  show "Klein_j.fourier meromorphic_on {0}"
    using Klein_j_has_laurent_expansion_at_cusp by (auto simp: Meromorphic1.meromorphic_on_def)
qed

interpretation Klein_J: fourier_expansion_meromorphic \<J> "Suc 0"
proof
  show "Klein_J.fourier meromorphic_on {0}"
    using Klein_J_has_laurent_expansion_at_cusp by (auto simp: Meromorphic1.meromorphic_on_def)
qed

lemma fls_conv_radius_Klein_c_ge:
  "fls_conv_radius fls_Klein_j \<ge> 1"
proof (rule fls_conv_radius_ge)
  show "Klein_j.fourier has_laurent_expansion fls_Klein_j"
    by (rule Klein_j_has_laurent_expansion_at_cusp)
  show "Klein_j.fourier holomorphic_on eball 0 1 - {0}"
    by (intro holomorphic_intros) auto
qed

lemma conv_radius_Klein_c_ge: "conv_radius (\<lambda>n. of_int (Klein_c n) :: complex) \<ge> 1"
proof -
  have "1 \<le> fls_conv_radius fls_Klein_j"
    by (rule fls_conv_radius_Klein_c_ge)
  also have "fls_conv_radius fls_Klein_j \<le> fls_conv_radius (fls_Klein_j - fls_X_inv)"
    by (rule fls_conv_radius_diff_ge) auto
  also have "\<dots> = conv_radius (\<lambda>n. of_int (Klein_c n) :: complex)"
    by (simp add: fls_Klein_j_def fps_conv_radius_def)
  finally show ?thesis .
qed

theorem Klein_j_fourier_expansion_aux:
  fixes z :: complex
  assumes z: "Im z > 0"
  defines "x \<equiv> cusp_q 1 z"
  shows "(\<lambda>n. of_int (Klein_c n) * x ^ n) sums (Klein_j z - 1 / x)"
proof -
  have [simp]: "fls_nth fls_Klein_j (- 1) = 1"
    by (simp add: fls_Klein_j_def Klein_c_0)
  have x: "x \<noteq> 0" "ereal (norm x) < 1"
    using assms by (auto simp: x_def cusp_q_def)
  have "fls_conv_radius fls_Klein_j \<ge> 1"
    using fls_conv_radius_Klein_c_ge by simp
  hence "(\<lambda>k. fls_nth fls_Klein_j (int k + fls_subdegree fls_Klein_j) *
             x powi (int k + fls_subdegree fls_Klein_j)) sums eval_fls fls_Klein_j x"
    by (intro sums_eval_fls less_le_trans[OF x(2)]) (use x in auto)
  also have "fls_subdegree fls_Klein_j = -1"
    by simp
  finally have "(\<lambda>k. fls_nth fls_Klein_j (int k - 1) * x powi (int k - 1)) sums eval_fls fls_Klein_j x"
    by simp
  hence "(\<lambda>k. fls_nth fls_Klein_j (int (Suc k) - 1) * x powi (int (Suc k) - 1)) sums (eval_fls fls_Klein_j x - 1 / x)"
    by (subst sums_Suc_iff) (auto simp: field_simps)
  also have "eval_fls fls_Klein_j x = Klein_j.fourier x"
  proof (rule eval_fls_eqI)
    show "Klein_j.fourier has_laurent_expansion fls_Klein_j"
      by (rule Klein_j_has_laurent_expansion_at_cusp)
    show "Klein_j.fourier holomorphic_on eball 0 1 - {0}"
      by (intro holomorphic_intros) auto
  qed (use x in auto)
  finally show ?thesis using x z
    by (simp add: fls_Klein_j_def x_def)
qed


subsection \<open>Mapping properties\<close>

text \<open>Remark in Section 2.7\<close>

text \<open>
  The Klein \<open>J\<close> function maps inputs that are symmetric about the imaginary axis to
  conjugate values. Moreover, the borders of the standard fundamental region (i.e.\ the vertical
  lines and the semicircle with radius 0 around the origin) are mapped to real numbers.
\<close>

lemma Klein_j_mirror:
  assumes z: "Im z > 0"
  shows   "Klein_j (-cnj z) = cnj (Klein_j z)"
proof -
  have "(\<lambda>n. of_int (Klein_c n) * (cusp_q 1 (-cnj z)) ^ n) sums (Klein_j (-cnj z) - 1 / cusp_q 1 (-cnj z))"
    using z by (intro Klein_j_fourier_expansion_aux) auto
  also have "cusp_q 1 (-cnj z) = cnj (cusp_q 1 z)"
    by (simp add: cusp_q_def exp_cnj)
  also have "Klein_j (-cnj z) - 1 / cnj (cusp_q 1 z) = cnj (cnj (Klein_j (-cnj z)) - 1 / cusp_q 1 z)"
    by simp
  also have "(\<lambda>n. of_int (Klein_c n) * cnj (cusp_q 1 z) ^ n) =
             (\<lambda>n. cnj (of_int (Klein_c n) * cusp_q 1 z ^ n))" by simp
  finally have "(\<lambda>n. of_int (Klein_c n) * cusp_q 1 z ^ n) sums (cnj (Klein_j (-cnj z)) - 1 / cusp_q 1 z)"
    by (simp only: sums_cnj)
  moreover have "(\<lambda>n. of_int (Klein_c n) * cusp_q 1 z ^ n) sums (Klein_j z - 1 / cusp_q 1 z)"
    using z by (intro Klein_j_fourier_expansion_aux) auto
  ultimately have "cnj (Klein_j (-cnj z)) - 1 / cusp_q 1 z = Klein_j z - 1 / cusp_q 1 z"
    using sums_unique2 by blast
  hence "cnj (Klein_j (-cnj z)) = Klein_j z"
    by simp
  thus "Klein_j (-cnj z) = cnj (Klein_j z)"
    using complex_cnj_cnj by metis
qed

lemma Klein_J_mirror: "Im z > 0 \<Longrightarrow> Klein_J (-cnj z) = cnj (Klein_J z)"
  by (simp add: Klein_J_conv_Klein_j Klein_j_mirror)

lemma Klein_j_arc_is_real:
  assumes "norm z = 1" "Im z > 0"
  shows   "Klein_j z \<in> \<real>"
proof -
  have "cnj (Klein_j z) = Klein_j (-cnj z)"
    using assms by (simp add: Klein_j_mirror)
  also have "-cnj z = -1 / z"
    using assms by (subst complex_div_cnj) auto
  also have "Klein_j (-1 / z) = Klein_j z"
    using assms by (simp add: Klein_j_neg_inverse)
  finally show ?thesis
    by (simp add: complex_is_Real_iff complex_eq_iff)
qed

lemma Klein_J_arc_is_real:
  assumes "norm z = 1" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
  using assms by (simp add: Klein_J_conv_Klein_j Klein_j_arc_is_real)

lemma Klein_j_vertical_onehalf_is_real:
  assumes "\<bar>Re z\<bar> = 1 / 2" "Im z > 0"
  shows   "Klein_j z \<in> \<real>"
proof -
  have "Klein_j z \<in> \<real>" if z: "Re z = -1/2" "Im z > 0" for z
  proof -
    have "cnj (Klein_j z) = Klein_j (-cnj z)"
      using z by (simp add: Klein_j_mirror)
    also have "-cnj z = z + 1"
      using z by (simp add: complex_eq_iff)
    also have "Klein_j (z + 1) = Klein_j z"
      using z by (simp add: Klein_j.plus_1 Klein_J.Klein_j.periodic_simps(7)) 
    finally show "Klein_j z \<in> \<real>"
      by (simp add: complex_is_Real_iff complex_eq_iff)
  qed
  from this[of z] this[of "z - 1"] Klein_j.minus_1[of z] show ?thesis
    using assms Klein_J.Klein_j.periodic_simps(8) 
    by (auto simp: abs_if split: if_splits)
qed


lemma Klein_J_vertical_onehalf_is_real:
  assumes "\<bar>Re z\<bar> = 1 / 2" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
  using assms by (simp add: Klein_J_conv_Klein_j Klein_j_vertical_onehalf_is_real)

lemma Klein_j_imag_axis_is_real:
  assumes "Re z = 0" "Im z > 0"
  shows   "Klein_j z \<in> \<real>"
proof -
  have "cnj (Klein_j z) = Klein_j (-cnj z)"
    using assms by (simp add: Klein_j_mirror)
  also have "-cnj z = z"
    using assms by (simp add: complex_eq_iff)
  finally show ?thesis
    using Reals_cnj_iff by blast
qed

lemma Klein_J_imag_axis_is_real:
  assumes "Re z = 0" "Im z > 0"
  shows   "Klein_J z \<in> \<real>"
  using assms by (simp add: Klein_J_conv_Klein_j Klein_j_imag_axis_is_real)

end