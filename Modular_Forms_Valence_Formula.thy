theory Modular_Forms_Valence_Formula
imports Meromorphic_Forms_Valence_Formula_Proof
begin

(* TODO Move *)
lemma is_pole_plus_analytic_iff1:
  assumes "g analytic_on {x}"
  shows   "is_pole (\<lambda>x. f x + g x) x \<longleftrightarrow> is_pole f x"
proof -
  have 1: "is_pole (\<lambda>x. f x + g x) x" if "is_pole f x" "g analytic_on {x}" for f g
    unfolding is_pole_def
  proof (rule tendsto_add_filterlim_at_infinity')
    show "g \<midarrow>x\<rightarrow> g x"
      by (intro isContD analytic_at_imp_isCont that(2))
  qed (use that(1) in \<open>simp add: is_pole_def\<close>)
  show ?thesis
  proof
    assume 2: "is_pole (\<lambda>x. f x + g x) x"
    have "is_pole (\<lambda>x. f x + g x + (-g x)) x"
      using 2 by (rule 1) (auto intro!: analytic_intros assms)
    thus "is_pole f x"
      by simp
  qed (auto intro!: 1 assms)
qed

lemma is_pole_plus_analytic_iff2:
  assumes "f analytic_on {x}"
  shows   "is_pole (\<lambda>x. f x + g x) x \<longleftrightarrow> is_pole g x"
  by (subst add.commute, rule is_pole_plus_analytic_iff1) fact

lemma is_pole_plus_analytic_mero_uhp_iff1:
  fixes f g :: mero_uhp
  assumes "\<not>is_pole g z"
  shows   "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole f z"
proof (cases "Im z > 0")
  case True
  have "mero_uhp_rel (f + g) (\<lambda>z. f z + g z)"
    by mero_uhp_rel
  hence "eventually (\<lambda>z. eval_mero_uhp (f + g) z = f z + g z) (at z)"
    using True unfolding mero_uhp_rel_def by (intro eventually_cosparse_imp_eventually_at) auto
  hence "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole (\<lambda>z. f z + g z) z"
    by (intro is_pole_cong refl)
  also have "\<dots> \<longleftrightarrow> is_pole f z"
    by (intro is_pole_plus_analytic_iff1 analytic_intros) (use True assms in auto)
  finally show ?thesis .
qed (auto simp: not_is_pole_eval_mero_uhp_outside)

lemma is_pole_plus_analytic_mero_uhp_iff2:
  fixes f g :: mero_uhp
  assumes "\<not>is_pole f z"
  shows   "is_pole (eval_mero_uhp (f + g)) z \<longleftrightarrow> is_pole g z"
  by (subst add.commute, rule is_pole_plus_analytic_mero_uhp_iff1) fact

lemma not_is_pole_const_mero_uhp [simp]:
  assumes "is_const_mero_uhp f"
  shows   "\<not>is_pole f z"
proof (cases "Im z > 0")
  case True
  thus ?thesis using assms
    by (auto simp: is_const_mero_uhp_def) 
qed (auto simp: not_is_pole_eval_mero_uhp_outside)


interpretation fps_to_fls: comm_ring_hom "fps_to_fls :: 'a :: comm_ring_1 fps \<Rightarrow> 'a fls"
  by standard (auto simp: fls_times_fps_to_fls)

interpretation fps_to_fls: inj_idom_hom "fps_to_fls :: 'a :: idom fps \<Rightarrow> 'a fls"
  by standard auto

interpretation fls_const: comm_ring_hom "fls_const :: 'a :: comm_ring_1 \<Rightarrow> 'a fls"
  by standard (auto simp: fls_plus_const)

interpretation fls_const: inj_idom_hom "fls_const :: 'a :: idom \<Rightarrow> 'a fls"
  by standard auto

interpretation fls_const: field_hom "fls_const :: 'a :: field \<Rightarrow> 'a fls"
  by standard auto

instance fls :: (field_char_0) field_char_0 ..

interpretation fls_const: field_char_0_hom "fls_const :: 'a :: field_char_0 \<Rightarrow> 'a fls"
  by standard auto


lemma holo_uhp_J_modform: "holo_uhp \<J>"
proof (rule holo_uhp_mero_uhp_rel_transfer)
  show "mero_uhp_rel \<J> Klein_J"
    by mero_uhp_rel
qed (auto intro!: analytic_intros simp: complex_is_Real_iff)

lemma not_is_pole_J_modform [simp]: "\<not>is_pole \<J> z"
  using holo_uhp_J_modform by (auto simp: holo_uhp_def)

lemma poles_mero_uhp_J_modform [simp]: "poles_mero_uhp \<J> = {}"
  by (auto simp: poles_mero_uhp_def)

lemma Klein_J_cong: "z \<sim>\<^sub>\<Gamma> z' \<Longrightarrow> Klein_J z = Klein_J z'"
  unfolding modular_group.rel_def by auto

lemma Klein_j_cong: "z \<sim>\<^sub>\<Gamma> z' \<Longrightarrow> Klein_j z = Klein_j z'"
  unfolding modular_group.rel_def by (auto simp: Klein_j_def)

lemma is_const_mero_uhp_minus_iff [simp]: "is_const_mero_uhp (-f) = is_const_mero_uhp f"
  by (metis const_mero_uhp.hom_uminus imageE is_const_mero_uhp_const_mero_uhp is_const_mero_uhp_def more_arith_simps(10))

lemma is_const_mero_uhp_add_absorb1 [simp]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (f + g) \<longleftrightarrow> is_const_mero_uhp g"
  by (metis add_diff_cancel_left' add_uminus_conv_diff const_mero_uhp.hom_add image_iff is_const_mero_uhp_const_mero_uhp is_const_mero_uhp_def)

lemma is_const_mero_uhp_add_absorb2 [simp]:
  "is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f + g) \<longleftrightarrow> is_const_mero_uhp f"
  using is_const_mero_uhp_add_absorb1[of g f] by (simp only: add.commute)

lemma is_const_mero_uhp_diff_absorb1 [simp]:
  "is_const_mero_uhp f \<Longrightarrow> is_const_mero_uhp (f - g) \<longleftrightarrow> is_const_mero_uhp g"
  using is_const_mero_uhp_add_absorb1[of f "-g"] by (simp del: is_const_mero_uhp_add_absorb1)

lemma is_const_mero_uhp_diff_absorb2 [simp]:
  "is_const_mero_uhp g \<Longrightarrow> is_const_mero_uhp (f - g) \<longleftrightarrow> is_const_mero_uhp f"
  using is_const_mero_uhp_add_absorb1[of "-g" f] by (simp del: is_const_mero_uhp_add_absorb1)


subsection \<open>The valence formula and its consequences\<close>

text \<open>
  This is also a generalisation of Apostol's Theorem 2.4.
\<close>
lemma MeForms_valence_formula':
  assumes "f \<in> MeForms[k] - {0}"
  defines "C \<equiv> (\<Sum>z\<in>zeros_mero_uhp f \<union> poles_mero_uhp f - {\<i>, \<^bold>\<rho>}. zorder_mero_uhp f z)"
  shows   "12 * C + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> + 12 * zorder_at_cusp 1 f = k"
    (is "?lhs = _")
proof -
  have "12 * (real_of_int k / 12) = ?lhs"
    by (subst MeForms_valence_formula[OF assms(1), symmetric]) (simp add: algebra_simps C_def)
  also have "12 * (real_of_int k / 12) = k"
    by simp
  finally show ?thesis
    by linarith
qed  

lemma MForms_valence_formula':
  assumes "f \<in> MForms[k] - {0}"
  defines "C \<equiv> (\<Sum>z\<in>zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}. zorder_mero_uhp f z)"
  shows   "12 * C + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> + 12 * zorder_at_cusp 1 f = k"
proof -
  interpret modular_form f k UNIV
    using assms(1) by auto
  have f': "f \<in> MeForms[k] - {0}"
    using assms(1) by (auto simp: MeForms_def meromorphic_form_axioms)
  from assms have "poles_mero_uhp f = {}"
    by (auto simp: poles_mero_uhp_def)
  thus ?thesis
    using MeForms_valence_formula'[OF f'] by (simp add: C_def)
qed


lemmas [simp, intro] = modular_group.modgrp_subgroup_periodic_axioms

text \<open>The following four theorems constitute Apostol's Theorem 6.2.\<close>
theorem MForms_0_eq_constant: "MForms[0] = range const_mero_uhp"
proof safe
  show "const_mero_uhp c \<in> MForms[0]" for c
    by auto
next
  fix g assume g: "g \<in> MForms[0]"
  define f where "f = g - const_mero_uhp (g \<i>)"
  have f: "f \<in> MForms[0]"
    by (auto simp: f_def intro!: mform_intros g)
  have [simp]: "\<not>is_pole (eval_mero_uhp g) \<i>"
    using g modular_form.no_poles by blast

  have "f = 0"
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> MForms[0] - {0}"
      by auto
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_cusp 1 f \<ge> 0" using f
      by (metis Diff_iff One_nat_def \<open>f \<noteq> 0\<close> modgrp_subgroup_period_UNIV
                modular_group.modgrp_subgroup_periodic_axioms zorder_at_cusp_nonneg)
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    have "zorder_mero_uhp f \<i> = 0"
      using MForms_valence_formula'[OF f] zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close>
      unfolding C_def [symmetric] by linarith+
    hence "f \<i> \<noteq> 0"
      using f by auto
    also have "f \<i> = 0"
      by (simp add: f_def eval_mero_uhp_diff)
    finally show False
      by simp
  qed
  thus "g \<in> range const_mero_uhp"
    by (auto simp: f_def)
qed
      
theorem MForms_eq_0:
  assumes "k < 0 \<or> k = 2 \<or> odd k"
  shows   "MForms[k] = {0}"
proof -
  have "0 \<in> MForms[k]"
    by auto
  moreover have "f = 0" if f: "f \<in> MForms[k]" for f
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> MForms[k] - {0}"
      by auto
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_cusp 1 f \<ge> 0" using f
      by (metis Diff_iff One_nat_def \<open>f \<noteq> 0\<close> modgrp_subgroup_period_UNIV
                modular_group.modgrp_subgroup_periodic_axioms zorder_at_cusp_nonneg)
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    from f and \<open>f \<noteq> 0\<close> have "f \<in> MForms[k] - {0}"
      by auto
    note valence = MForms_valence_formula'[OF this, folded C_def]
    have "k \<ge> 0"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by linarith
    moreover have "even k"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by presburger
    moreover have "k \<noteq> 2"
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> by presburger
    ultimately show False
      using assms by linarith
  qed
  ultimately show ?thesis by blast
qed

lemma MForms_weight_even: "f \<in> MForms[k] - {0} \<Longrightarrow> even k"
  using MForms_eq_0[of k] by auto

theorem MForms_weight_ge_4: 
  assumes "f \<in> MForms[k]" "\<not>is_const_mero_uhp f"
  shows   "k \<ge> 4"
proof -
  from assms have "k \<noteq> 0"
    by (auto simp: MForms_0_eq_constant)
  have "MForms[k] \<noteq> {0}"
    using assms by force
  with MForms_eq_0[of k] have "k \<ge> 0 \<and> k \<noteq> 2 \<and> even k"
    by linarith
  with \<open>k \<noteq> 0\<close> show ?thesis
    by auto
qed

theorem CForms_eq_0:
  assumes "k < 12"
  shows   "CForms[k] = {0}"
proof -
  have "0 \<in> CForms[k]"
    by auto
  moreover have "f = 0" if f: "f \<in> CForms[k]" for f
  proof (rule ccontr)
    assume "f \<noteq> 0"
    with f have f: "f \<in> MForms[k] - {0}"
      by (auto simp: CForms_def)
    have zorder_ge: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
      using that f by blast
    have zorder_ge': "zorder_at_cusp 1 f > 0" using f
      by (metis One_nat_def \<open>f \<noteq> 0\<close> modgrp_subgroup_period_UNIV
             modular_group.modgrp_subgroup_periodic_axioms that zorder_at_cusp_CForms)
    have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
      using zorder_ge[of "\<^bold>\<rho>"] zorder_ge[of \<i>] f by auto
    define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
    have "C \<ge> 0" unfolding C_def
      by (intro sum_nonneg zorder_ge) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    from f have "f \<in> MForms[k] - {0}"
      by auto
    note valence = MForms_valence_formula'[OF this, folded C_def]
    show False
      using valence zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close> assms by linarith
  qed
  ultimately show ?thesis
    by blast
qed

lemma zeros_MForms_upto_15:
  assumes f [mform_intros]: "f \<in> MForms[k]" and k: "k \<in> {1..15} - {12}"
  assumes [simp]: "f \<noteq> 0"
  shows   "Im z > 0 \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> eval_mero_uhp f z \<noteq> 0"
    and   "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> zorder_mero_uhp f z = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)"
    and   "z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> zorder_mero_uhp f z = (if k \<in> {4, 8} then 0 else 1)"
proof -
  from assms interpret modular_form f k UNIV
    by auto
  from k have k: "k > 0" "k \<le> 15" "k \<noteq> 12"
    by auto
  define m where "m = nat (zorder_mero_uhp f \<^bold>\<rho>)"
  define n where "n = nat (zorder_mero_uhp f \<i>)"
  have zorder_ge_aux: "zorder_mero_uhp f z \<ge> 0" if "Im z > 0" for z
    using that f by (intro zorder_MForms_nonneg[OF f] that) auto
  have zorder_ge': "zorder_at_cusp (Suc 0) f \<ge> 0" using f
    by (metis \<open>f \<noteq> 0\<close> modgrp_subgroup_period_UNIV zorder_at_cusp_nonneg)
  have zorder_ge'': "zorder_mero_uhp f \<^bold>\<rho> \<ge> 0" "zorder_mero_uhp f \<i> \<ge> 0"
    using zorder_ge_aux[of "\<^bold>\<rho>"] zorder_ge_aux[of \<i>] f by auto
  define C where "C = sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
  have "C \<ge> 0" unfolding C_def
    by (intro sum_nonneg zorder_ge_aux) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  define l where "l = nat (zorder_at_cusp (Suc 0) f) + nat C"
  note zorder_ge = zorder_ge' zorder_ge'' \<open>C \<ge> 0\<close>
  from f have f: "f \<in> MForms[k] - {0}"
    by auto
  have "12 * l + 4 * m + 6 * n = k"
    using MForms_valence_formula'[OF f] \<open>C \<ge> 0\<close> zorder_ge
    unfolding l_def C_def m_def n_def by simp
  moreover from this have "l = 0"
    using \<open>k \<noteq> 12\<close> \<open>k \<le> 15\<close> by presburger
  ultimately have valence: "4 * m + 6 * n = k"
    by simp
  from \<open>l = 0\<close> have "C = 0"
    unfolding l_def using zorder_ge by linarith

  have False if z: "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}" for z
  proof -
    have z': "Im z > 0"
      using z by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    have "zorder_mero_uhp f z = 0"
    proof (rule sum_nonneg_0[of _ "zorder_mero_uhp f"])
      show "sum (zorder_mero_uhp f) (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}) = 0"
        using \<open>C = 0\<close> unfolding C_def by simp
      show "finite (zeros_mero_uhp f - {\<i>, \<^bold>\<rho>})"
      proof -
        interpret modular_form f k UNIV
          using f by auto
        show ?thesis
          by auto
      qed
      show "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}"
        by fact
      show "zorder_mero_uhp f z \<ge> 0" if "z \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}" for z
        using that by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    qed
    hence "eval_mero_uhp f z \<noteq> 0" using z' by force
    thus False
      using z by (auto simp: inv_image_mero_uhp_def)
  qed
  hence zeros_subset: "zeros_mero_uhp f \<subseteq> {\<i>, \<^bold>\<rho>}"
    by blast

  show "eval_mero_uhp f z \<noteq> 0" if "Im z > 0" "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>" "\<not>z \<sim>\<^sub>\<Gamma> \<i>"
  proof -
    obtain z' where z': "z \<sim>\<^sub>\<Gamma> z'" "z' \<in> \<R>\<^sub>\<Gamma>'"
      using \<open>0 < Im z\<close> equiv_point_in_std_fund_region' by blast
    then obtain h where h: "z' = apply_modgrp h z"
      by (auto simp: modular_group.rel_def)
    have not_equiv: "z' \<noteq> \<^bold>\<rho>" "z' \<noteq> \<i>"
      using that z' by auto
    have "eval_mero_uhp f z' \<noteq> 0"
    proof
      assume "eval_mero_uhp f z' = 0"
      hence "z' \<in> zeros_mero_uhp f - {\<i>, \<^bold>\<rho>}"
        using z' not_equiv f modular_form.no_poles
        by (auto simp: inv_image_mero_uhp_def)
      with zeros_subset show False
        by blast
    qed
    also have "eval_mero_uhp f z' = modgrp_factor h z powi k * eval_mero_uhp f z"
      using z' h by simp
    finally show ?thesis
      using \<open>Im z > 0\<close> by auto
  qed

  from valence and k have "m \<le> 2 \<and> n \<le> 1"
    by presburger
  hence "(m = 0 \<or> m = 1 \<or> m = 2) \<and> (n = 0 \<or> n = 1)"
    by fastforce
  hence mn: "(m, n) \<in> {(1, 0), (0, 1), (2, 0), (1, 1), (2, 1)}"
    using valence k unfolding insert_iff empty_iff prod.inject
    by (elim disjE conjE) simp_all

  show "zorder_mero_uhp f z = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)" if "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  proof -
    have "zorder_mero_uhp f z = m"
      unfolding m_def using that by (auto intro: rel_imp_zorder_eq)
    also have "m = (if k = 6 then 0 else if k \<in> {8, 14} then 2 else 1)"
      using valence mn by auto
    finally show ?thesis by simp
  qed

  show "zorder_mero_uhp f z = (if k \<in> {4, 8} then 0 else 1)" if "z \<sim>\<^sub>\<Gamma> \<i>"
  proof -
    have "zorder_mero_uhp f z = n"
      unfolding n_def using that by (auto intro: rel_imp_zorder_eq)
    also have "n = (if k \<in> {4, 8} then 0 else 1)"
      using valence mn by auto
    finally show ?thesis by simp
  qed
qed

lemma Eisenstein_G_4_zero_iff [simp]:
  assumes "Im z > 0"
  shows   "Eisenstein_G 4 z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
proof
  assume "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  thus "Eisenstein_G 4 z = 0" using Eisenstein_G_4_rho assms
    by (metis Eisenstein_G.invariant_aux modular_group.rel_def modular_group.rel_sym mult.commute mult_zero_left)
next
  assume *: "Eisenstein_G 4 z = 0"
  have **: "\<G>\<^sub>4 \<in> MForms[4]"
    by (rule mform_intros) auto
  from zeros_MForms_upto_15[OF **, of z] * assms show "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
    by (auto simp: zorder_mero_uhp_eq_0_iff G_modform_eq_0_iff)
qed

lemma Eisenstein_G_6_zero_iff [simp]:
  assumes "Im z > 0"
  shows   "Eisenstein_G 6 z = 0 \<longleftrightarrow> z \<sim>\<^sub>\<Gamma> \<i>"
proof
  assume "z \<sim>\<^sub>\<Gamma> \<i>"
  thus "Eisenstein_G 6 z = 0" using Eisenstein_G_6_i assms
    by (metis Eisenstein_G.invariant_aux modular_group.rel_def modular_group.rel_sym mult.commute mult_zero_left)
next
  assume *: "Eisenstein_G 6 z = 0"
  have **: "\<G>\<^sub>6 \<in> MForms[6]"
    by (rule mform_intros) auto
  from zeros_MForms_upto_15[OF **, of z] * assms show "z \<sim>\<^sub>\<Gamma> \<i>"
    by (auto simp: zorder_mero_uhp_eq_0_iff G_modform_eq_0_iff)
qed

lemma MForms_zorder_ge_imp_same:
  assumes "f \<in> MForms[k]" "g \<in> MForms[k]" "g \<noteq> 0"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> eval_mero_uhp g z = 0 \<Longrightarrow> zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "eval_mero_uhp_at_cusp g = 0 \<Longrightarrow> zorder_at_cusp (Suc 0) f \<ge> zorder_at_cusp (Suc 0) g"
  shows "\<exists>c. f = \<langle>c\<rangle> * g"
proof -
  have "f / g \<in> MForms[0]"
    by (rule mform_intros) (use assms(3-) in \<open>auto intro!: assms(1,2)\<close>)
  then obtain c where "f / g = \<langle>c\<rangle>"
    using MForms_0_eq_constant by auto
  with \<open>g \<noteq> 0\<close> show ?thesis by (intro exI[of _ c]) (auto simp: field_simps)
qed

text \<open>
  Any modular form of weight $k \leq 15$ and $k\neq 12$ is a constant multiple of $G_k$.
\<close>
lemma MForms_upto_15:
  assumes f: "f \<in> MForms[k]" and "k \<in> {0..15} - {12}"
  shows   "\<exists>c. f = \<langle>c\<rangle> * \<G> (nat k)"
proof (cases "k = 0")
  case True
  thus ?thesis using assms
    by (auto simp: MForms_0_eq_constant)
next
  case False
  with assms have k: "k \<in> {1..15} - {12}"
    by auto
  show ?thesis
  proof (cases "f = 0")
    case False
    show ?thesis
    proof (cases "odd k \<or> k < 4")
      case True
      have *: "k < 0 \<or> k = 2 \<or> odd k"
        using \<open>k \<noteq> 0\<close> k True by auto
      thus ?thesis using MForms_eq_0[OF *] k f
        by (intro exI[of _ 0]) simp_all
    next
      case False
      show ?thesis
      proof (rule MForms_zorder_ge_imp_same)
        show "f \<in> MForms[k]" by fact
        show g: "\<G> (nat k) \<in> MForms[k]" by (rule mform_intros) (use k in auto)
        show nz: "\<G> (nat k) \<noteq> 0" 
          using k False by (auto simp: G_modform_eq_0_iff even_nat_iff)
        fix z assume z: "Im z > 0" "eval_mero_uhp (\<G> (nat k)) z = 0"
        note zeros_f = zeros_MForms_upto_15[OF f k \<open>f \<noteq> 0\<close>, of z]
        note zeros_g = zeros_MForms_upto_15[OF g k nz, of z]
        from zeros_g and z have "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<or> z \<sim>\<^sub>\<Gamma> \<i>"
          by blast
        hence "zorder_mero_uhp (\<G> (nat k)) z = zorder_mero_uhp f z"
          using zeros_f(2,3) zeros_g(2,3) by argo
        thus "zorder_mero_uhp (\<G> (nat k)) z \<le> zorder_mero_uhp f z"
          by simp  
      qed (use False in \<open>auto simp: even_nat_iff\<close>)
    qed
  qed (auto intro: exI[of _ 0])
qed

lemma CForms_split:
  assumes "f \<in> CForms[k]"
  obtains g where "g \<in> MForms[k-12]" "f = g * \<Delta>"
proof (cases "f = 0")
  case True
  thus ?thesis
    by (intro that[of 0]) auto
next
  case [simp]: False
  hence k: "k \<ge> 12"
    using CForms_eq_0[of k] assms by (cases "k \<ge> 12") auto
  show ?thesis
  proof (rule that[of "f / \<Delta>"])
    have [mform_intros]: "f \<in> MForms[k]"
      using assms by (auto simp: CForms_def)
    have *: "zorder_at_cusp (Suc 0) f \<ge> 1"
      using assms zorder_at_cusp_CForms[OF assms] by simp
    show "f / \<Delta> \<in> MForms[k - 12]"
      by (rule mform_intros modular_group.modgrp_subgroup_periodic_axioms)+
         (use * in \<open>auto simp: complex_is_Real_iff\<close>)
  qed (auto simp: field_simps)
qed

subsection \<open>Some identities on Eisenstein $G$ series and the divisor $\sigma$ function\<close>

lemma zeta_even_nat':
  assumes "even n"
  shows   "zeta (of_nat n) = 
             of_real ((-1) ^ Suc (n div 2) * bernoulli n * (2 * pi) ^ n / (2 * fact n))"
  using assms by (elim evenE) (auto simp: zeta_even_nat)

(* TODO: This is silly; you don't need all this heavy machinery to prove equalities of
   different G's. We can already do that much earlier. Clean up! *)

notation divisor_sigma ("\<sigma>\<^bsub>_\<^esub>'(_')" 100)
notation bernoulli ("\<B>'(_')" 100)

lemma divisor_sigma_numeral_to_of_nat:
  "NO_MATCH TYPE(nat) (TYPE('a :: {semiring_1, nat_power})) \<Longrightarrow> 
     divisor_sigma (numeral k) n = (of_nat (divisor_sigma (numeral k) n) :: 'a)"
  using divisor_sigma_of_nat[of "numeral k" n] by simp

lemma (in field_char_0_hom) hom_fact [hom_distribs]: "hom (fact n) = fact n"
  by (induction n) (simp_all add: hom_distribs)

locale Eisenstein_G_mult_identity =
  fixes a b c :: nat and C :: complex and D E F :: real
  assumes abc: "a + b = c" "c \<in> {4..15} - {12}" "a \<ge> 4" "b \<ge> 4" "even a" "even b" "even c"
  assumes C: "C = -of_real (bernoulli (a + b) / (bernoulli a * bernoulli b * (c choose a)))"
  assumes D: "D = (b * \<B>(a + b)) / ((a + b) * \<B>(b))"
  assumes E: "E = (a * \<B>(a + b)) / ((a + b) * \<B>(a))"
  assumes F: "F = -2 * a * b * \<B>(a+b) / ((a + b) * \<B>(a) * \<B>(b))"
begin

lemma G_eq: "\<G> c = \<langle>C\<rangle> * \<G> a * \<G> b"
proof -
  have [simp]: "C \<noteq> 0"
    using abc by (auto simp: C bernoulli_zero_iff)
  have "\<G> a * \<G> b \<in> MForms[c]"
    using abc by (auto intro!: mform_intros)
  from MForms_upto_15[OF this] abc obtain C' where C': "\<G> a * \<G> b = \<langle>C'\<rangle> * \<G> c"
    by auto
  have "eval_mero_uhp_at_cusp (\<G> a * \<G> b) = 4 * zeta a * zeta b"
    using abc by (subst eval_mero_uhp_at_cusp_mult) (auto intro!: mform_intros)
  also note C'
  also have "eval_mero_uhp_at_cusp (\<langle>C'\<rangle> * \<G> c) = 2 * C' * zeta c"
    using abc by (subst eval_mero_uhp_at_cusp_mult) (auto intro!: mform_intros)
  finally have "C' = 2 * zeta a * zeta b / zeta c"
    using abc by (simp add: field_simps)
  also have "\<dots> = inverse C" using abc(5-7) unfolding C
    by (simp add: zeta_even_nat' field_simps power_add binomial_fact del: of_nat_add flip: abc(1))
  finally have [simp]: "C' = inverse C" .
  show ?thesis
    using C' by (simp add: hom_distribs field_simps)
qed

lemma Eisenstein_G_eq: "Eisenstein_G c z = C * Eisenstein_G a z * Eisenstein_G b z"
proof -
  write Eisenstein_G ("G")
  have "mero_uhp_rel (\<lambda>z. G c z - C * G a z * G b z) (\<G> c - \<langle>C\<rangle> * \<G> a * \<G> b)"
    by mero_uhp_rel
  also have "\<G> c - \<langle>C\<rangle> * \<G> a * \<G> b = 0"
    by (subst G_eq) simp
  finally have *: "mero_uhp_rel (eval_mero_uhp 0) (\<lambda>z. G c z - C * G a z * G b z)"
    by (simp add: mero_uhp_rel_sym)
  have eq: "G c z = C * G a z * G b z" if "Im z > 0" for z
  proof -
    have "eval_mero_uhp 0 z = G c z - C * G a z * G b z"
      using * by (rule mero_uhp_rel_imp_eval_mero_uhp_eq)
                 (use that in \<open>auto intro!: analytic_intros simp: complex_is_Real_iff\<close>)
    thus ?thesis
      by simp
  qed
  show ?thesis
  proof (cases "Im z" "0 :: real" rule: linorder_cases)
    case greater
    with eq[of z] show ?thesis by simp
  next
    case equal
    hence "z \<in> \<real>"
      by (auto simp: complex_is_Real_iff)
    thus ?thesis using abc by simp
  next
    case less
    have "cnj (G c z - C * G a z * G b z) = G c (cnj z) - cnj C * G a (cnj z) * G b (cnj z)"
      by (simp add: Eisenstein_G_cnj)
    also have "cnj C = C"
      by (simp add: C)
    also have "G c (cnj z) - C * G a (cnj z) * G b (cnj z) = 0"
      by (subst eq) (use less in auto)
    finally show ?thesis
      using eq_iff_diff_eq_0 by blast
  qed
qed

lemmas [simp del] = fls_const_mult_const

lemma divisor_sigma_eq:
  "real (\<sigma>\<^bsub>c - 1\<^esub>(n)) = E * real (\<sigma>\<^bsub>a-1\<^esub>(n)) + D * real (\<sigma>\<^bsub>b-1\<^esub>(n)) +
                        F * real (\<Sum>i\<le>n. \<sigma>\<^bsub>a-1\<^esub>(i) * \<sigma>\<^bsub>b-1\<^esub>(n - i))"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  let ?F = "Eisenstein_G_fps_at_cusp'"
  define G where "G = (\<lambda>k. fps_to_fls (Abs_fps (\<lambda>n. complex_of_nat (divisor_sigma k n))))"
  have nz: "fls_const (complex_of_real pi) ^ c \<noteq> 0"
    by simp

  interpret ab: modular_form_pair "\<G> a" "\<G> b" a b UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
    by unfold_locales auto

  have abc': "a \<ge> 4" "even a" "b \<ge> 4" "even b" "c \<ge> 4" "even c"
    using abc by auto

  define d where "d = 2*\<i>*pi"
  define A1 where "A1 = zeta a * zeta b"
  define A2 where "A2 = d^b / fact (b-1) * zeta a"
  define A3 where "A3 = d^a / fact (a-1) * zeta b"
  define A4 where "A4 = d^(a+b) / (fact (a-1)*fact(b-1))"
  define A where "A = (2 * C * fact (c - 1) / d ^ c)"

  have "fourier_expansion.fourier (\<langle>C\<rangle> * (\<G> a * \<G> b)) (Suc 0) has_laurent_expansion
          (fls_const C * (fps_to_fls (?F a) * fps_to_fls (?F b)))"
    by (rule ab.mult.has_laurent_expansion_at_cusp_cmult_left
             ab.has_laurent_expansion_at_cusp_mult
             Eisenstein_G.has_expansion_at_cusp has_laurent_expansion_fps)+
  moreover have "fourier_expansion.fourier (\<G> c) (Suc 0) has_laurent_expansion 
                   (fps_to_fls (?F c))"
    by (rule Eisenstein_G.has_expansion_at_cusp has_laurent_expansion_fps)+
  ultimately have "fps_to_fls (?F c) = fls_const C * fps_to_fls (?F a) * fps_to_fls (?F b)"
    using G_eq has_laurent_expansion_unique unfolding mult.assoc by metis
  also have "fls_const C * fps_to_fls (?F a) * fps_to_fls (?F b) = 
               4 * fls_const C *
                (fls_const (zeta a) + fls_const (d ^ a / fact (a - 1)) * G (a-1)) *
                (fls_const (zeta b) + fls_const (d ^ b / fact (b - 1)) * G (b-1))"
    using abc'
    apply (simp add: Eisenstein_G_fps_at_cusp_def d_def)
    apply (simp add:  hom_distribs G_def)
    apply (simp add: algebra_simps)
    done
  also have "\<dots> = fls_const (4 * C * A1) + fls_const (4 * C) * (
                  fls_const A2 * G (b-1) +
                  fls_const A3 * G (a-1) +
                  fls_const A4 * G (a-1) * G(b-1))"
    by (simp add: hom_distribs field_simps power_add A1_def A2_def A3_def A4_def)
  also have "fps_to_fls (Eisenstein_G_fps_at_cusp' c) = 
               fls_const (2 * zeta c) + fls_const (2 * d ^ c / fact (c - 1)) * G (c - 1)"
    using abc'
    apply (simp add: Eisenstein_G_fps_at_cusp_def d_def)
    apply (simp add: hom_distribs G_def)
    done
  also have "2 * zeta c = 4 * C * A1"
    using abc(5-7)
    by (simp add: A1_def C zeta_even_nat' bernoulli_zero_iff binomial_fact field_simps power_add 
             flip: abc(1) del: of_nat_add)
  finally have "2 * G (c - 1) = 
                fls_const A * 2 * (fls_const A2 * G (b - 1) + fls_const A3 * G (a - 1) +
                  fls_const A4 * G (a - 1) * G (b - 1))"
    by (simp add: field_simps hom_distribs d_def A_def)
  hence eq: "G (c - 1) = fls_const A * (fls_const A2 * G (b - 1) + fls_const A3 * G (a - 1) +
                           fls_const A4 * G (a - 1) * G (b - 1))" (is "_ = ?rhs")
    by Groebner_Basis.algebra

  have fact_minus_1: "fact (n - Suc 0) = (fact n / n :: complex)" if "n > 0" for n
    using that by (cases n) (auto simp del: of_nat_Suc)

  have "fls_nth (G (c - 1)) n = of_real (\<sigma>\<^bsub>c-1\<^esub>(n))"
    by (simp add: G_def)
  also note eq
  also have "fls_nth ?rhs n =
               A * A2 * of_nat (\<sigma>\<^bsub>b-1\<^esub>(n)) +
               A * A3 * of_nat (\<sigma>\<^bsub>a-1\<^esub>(n)) +
               A * A4 * of_nat (\<Sum>i=0..n. (\<sigma>\<^bsub>a-1\<^esub>(i)) *  (\<sigma>\<^bsub>b-1\<^esub>(n-i)))"
    by (simp add: G_def fps_mult_nth mult.assoc ring_distribs flip: fls_times_fps_to_fls)
  also have "A * A2 = D" using abc'
    by (simp add: D A_def A2_def C binomial_fact d_def power_add field_simps zeta_even_nat'
                  bernoulli_zero_iff fact_minus_1 del: of_nat_add flip: abc(1))
  also have "A * A3 = E" using abc'
    by (simp add: E A_def A3_def C binomial_fact d_def power_add field_simps zeta_even_nat'
                  bernoulli_zero_iff fact_minus_1 del: of_nat_add flip: abc(1))
  also have "A * A4 = F" using abc'
    by (simp add: F A_def A4_def C binomial_fact d_def power_add field_simps zeta_even_nat'
                  bernoulli_zero_iff fact_minus_1 del: of_nat_add flip: abc(1))
  also have "complex_of_real D * complex_of_nat (\<sigma>\<^bsub>b-1\<^esub>(n)) +
             complex_of_real E * complex_of_nat (\<sigma>\<^bsub>a-1\<^esub>(n)) + 
             complex_of_real F * complex_of_nat (\<Sum>i=0..n. \<sigma>\<^bsub>a-1\<^esub>(i) * \<sigma>\<^bsub>b-1\<^esub>(n - i)) =
             complex_of_real (E * \<sigma>\<^bsub>a-1\<^esub>(n) + D * \<sigma>\<^bsub>b-1\<^esub>(n) + F * (\<Sum>i=0..n. \<sigma>\<^bsub>a-1\<^esub>(i) * \<sigma>\<^bsub>b-1\<^esub>(n - i)))"
    by simp
  finally show ?thesis
    by (subst (asm) of_real_eq_iff) (simp add: algebra_simps atLeast0AtMost)
qed

end


context
begin

interpretation Eisenstein_G_mult_identity 4 4 8 "3/7" "1/2" "1/2" "120"
  by standard (simp_all add: binomial_fact fact_reduce)

lemma G8_conv_G4: "\<G> 8 = \<langle>3 / 7\<rangle> * \<G>\<^sub>4 ^ 2"
  using G_eq by (simp add: power2_eq_square)

lemma Eisenstein_G8_conv_G4: "Eisenstein_G 8 z = 3 / 7 * Eisenstein_G 4 z ^ 2"
  using Eisenstein_G_eq[of z] by (simp add: power2_eq_square)

lemma divisor_sigma_7_conv_3:
  "\<sigma>\<^bsub>7\<^esub>(n) = \<sigma>\<^bsub>3\<^esub>(n) + 120 * (\<Sum>x\<le>n. \<sigma>\<^bsub>3\<^esub>(x) * \<sigma>\<^bsub>3\<^esub>(n - x) :: real)"
  using divisor_sigma_eq[of n] by (simp flip: divisor_sigma_of_nat)

end


context
begin

interpretation Eisenstein_G_mult_identity 4 6 10 "5/11" "21/11" "-10/11" "5040/11"
  by standard (simp_all add: binomial_fact fact_reduce)

lemma G10_conv_G4_6: "\<G> 10 = \<langle>5 / 11\<rangle> * \<G> 4 * \<G> 6"
  using G_eq by (simp add: power2_eq_square)

lemma Eisenstein_G10_conv_G4_6: "Eisenstein_G 10 z = 5 / 11 * Eisenstein_G 4 z * Eisenstein_G 6 z"
  using Eisenstein_G_eq[of z] by (simp add: power2_eq_square)

lemma divisor_sigma_9_conv_3_5:
  "\<sigma>\<^bsub>9\<^esub>(n) = -10/11 * \<sigma>\<^bsub>3\<^esub>(n) + 21/11 * \<sigma>\<^bsub>5\<^esub>(n) + 5040 / 11 * (\<Sum>x\<le>n. \<sigma>\<^bsub>3\<^esub>(x) * \<sigma>\<^bsub>5\<^esub>(n - x) :: real)"
  using divisor_sigma_eq[of n] by (simp flip: divisor_sigma_of_nat)

end


context
begin

interpretation Eisenstein_G_mult_identity 4 10 14 "6/13" "11" "-10" "2640"
  by standard (simp_all add: binomial_fact fact_reduce)

lemma G14_conv_G4_10: "\<G> 14 = \<langle>6 / 13\<rangle> * \<G> 4 * \<G> 10"
  using G_eq by (simp add: power2_eq_square)

lemma Eisenstein_G14_conv_G4_10: "Eisenstein_G 14 z = 6 / 13 * Eisenstein_G 4 z * Eisenstein_G 10 z"
  using Eisenstein_G_eq[of z] by (simp add: power2_eq_square)

lemma divisor_sigma_13_conv_3_9:
  "\<sigma>\<^bsub>13\<^esub>(n) = -10 * \<sigma>\<^bsub>3\<^esub>(n) + 11 * \<sigma>\<^bsub>9\<^esub>(n) + 2640 * (\<Sum>x\<le>n. \<sigma>\<^bsub>3\<^esub>(x) * \<sigma>\<^bsub>9\<^esub>(n - x) :: real)"
  using divisor_sigma_eq[of n] by (simp flip: divisor_sigma_of_nat)

end


context
begin

interpretation Eisenstein_G_mult_identity 6 8 14 "70/143" "-20" "21" "10080"
  by standard (simp_all add: binomial_fact fact_reduce)

lemma G14_conv_G6_8: "\<G> 14 = \<langle>70 / 143\<rangle> * \<G> 6 * \<G> 8"
  using G_eq by (simp add: power2_eq_square)

lemma Eisenstein_G14_conv_G6_8: "Eisenstein_G 14 z = 70 / 143 * Eisenstein_G 6 z * Eisenstein_G 8 z"
  using Eisenstein_G_eq[of z] by (simp add: power2_eq_square)

lemma divisor_sigma_13_conv_5_7:
  "\<sigma>\<^bsub>13\<^esub>(n) = 21 * \<sigma>\<^bsub>5\<^esub>(n) - 20 * \<sigma>\<^bsub>7\<^esub>(n) + 10080 * (\<Sum>x\<le>n. \<sigma>\<^bsub>5\<^esub>(x) * \<sigma>\<^bsub>7\<^esub>(n - x) :: real)"
  using divisor_sigma_eq[of n] by (simp flip: divisor_sigma_of_nat)

end

no_notation divisor_sigma ("\<sigma>\<^bsub>_\<^esub>'(_')" 100)
no_notation bernoulli ("\<B>'(_')" 100)



definition weighting_factor :: "complex \<Rightarrow> int"
  where "weighting_factor z =
           (if Im z \<le> 0 then 0 
            else if z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> then 3 else if z \<sim>\<^sub>\<Gamma> \<i> then 2 else 1)"

lemma weighting_factor_ii [simp]:  "weighting_factor \<i> = 2"
  and weighting_factor_rho [simp]: "weighting_factor \<^bold>\<rho> = 3"
  and weighting_factor_ii':       "z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> weighting_factor z = 2"
  and weighting_factor_rho':       "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> weighting_factor z = 3"
  and weighting_factor_eq [simp]:  "Im z > 0 \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> \<not>z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> weighting_factor z = 1"
  by (auto simp: weighting_factor_def)

lemma weighting_factor_nonneg [simp]: "weighting_factor z \<ge> 0"
  by (auto simp: weighting_factor_def)

lemma weighting_factor_not_neg [simp]: "\<not>weighting_factor z < 0"
  by (auto simp: weighting_factor_def)

lemma weighting_factor_pos [simp]: "Im z > 0 \<Longrightarrow> weighting_factor z > 0"
  by (auto simp: weighting_factor_def)

lemma weighting_factor_cong:
  "z \<sim>\<^sub>\<Gamma> z' \<Longrightarrow> weighting_factor z = weighting_factor z'"
  unfolding weighting_factor_def using modular_group.rel_trans modular_group.rel_sym
  by (smt (verit, best) modular_group.Im_nonpos_imp_not_rel)

definition zorder_mform :: "mero_uhp \<Rightarrow> complex \<Rightarrow> int" where
  "zorder_mform f z = (if f = 0 then 0 else zorder (eval_mero_uhp f) z div weighting_factor z)"

lemma (in meromorphic_form) rel_imp_zorder_mform_eq:
  assumes "rel z z'"
  shows   "zorder_mform f z = zorder_mform f z'"
  using assms
  by (auto simp: zorder_mform_def
           intro!: arg_cong2[of _ _ _ _ "(div)"] rel_imp_zorder_eq weighting_factor_cong rel_imp_rel)

lemma
  assumes "f \<in> MFuns - {0}"
  shows    MFuns_zorder_rho_multiple_3: "3 dvd zorder f \<^bold>\<rho>"
  and      MFuns_zorder_i_multiple_2:   "2 dvd zorder f \<i>"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define P  Z where "P = poles_mero_uhp f" and "Z = zeros_mero_uhp f"
  define C where "C = (\<Sum>z\<in>Z\<union>P-{\<i>,\<^bold>\<rho>}. zorder f z)"
  have "12 * C + 4 * zorder f \<^bold>\<rho> + 6 * zorder f \<i> + 12 * zorder_at_cusp 1 f = 0"
    unfolding C_def using MeForms_valence_formula'[OF assms] by (simp add: P_def Z_def)
  hence *: "6 * C + 2 * zorder f \<^bold>\<rho> + 3 * zorder f \<i> + 6 * zorder_at_cusp 1 f = 0" (is "?lhs = 0")
    by simp
  have "3 dvd ?lhs" "2 dvd ?lhs"
    by (subst *; simp; fail)+
  thus "3 dvd zorder f \<^bold>\<rho>" "2 dvd zorder f \<i>"
    by (simp_all add: dvd_add_right_iff dvd_add_left_iff prime_dvd_mult_iff)
qed

lemma MFuns_weighting_factor_dvd_zorder:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "weighting_factor z dvd zorder f z"
proof -
  interpret meromorphic_form f 0 UNIV
    using assms by auto
  show ?thesis
    using MFuns_zorder_rho_multiple_3[OF assms(1)] MFuns_zorder_i_multiple_2[OF assms(1)] assms(2)
          rel_imp_zorder_eq unfolding weighting_factor_def by auto
qed

lemma zorder_conv_zorder_mform:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder f z = zorder_mform f z * weighting_factor z"
  using MFuns_weighting_factor_dvd_zorder[OF assms] assms unfolding zorder_mform_def by auto

lemma zorder_mform_nonneg_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform f z \<ge> 0 \<longleftrightarrow> \<not>is_pole f z"
  by (simp add: assms(2) pos_imp_zdiv_nonneg_iff zorder_mform_def)

lemma zorder_mform_neg_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform f z < 0 \<longleftrightarrow> is_pole f z"
  by (smt (verit, best) assms(1) assms(2) zorder_mform_nonneg_iff)

lemma zorder_mform_pos_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform f z > 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
  using assms zorder_conv_zorder_mform
  by (metis DiffE mult_zero_left less_asym' antisym
        div_0 insertI1 not_le zorder_mero_uhp_eq_0_iff zorder_mform_def zorder_mform_neg_iff)

lemma zorder_mform_nonpos_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform f z \<le> 0 \<longleftrightarrow> is_pole f z \<or> f z \<noteq> 0"
  by (smt (verit) assms(1) assms(2) zorder_mform_pos_iff)

lemma zorder_mform_eq_0_iff [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform f z = 0 \<longleftrightarrow> \<not>is_pole f z \<and> f z \<noteq> 0"
  by (metis assms nle_le zorder_mform_nonneg_iff zorder_mform_nonpos_iff)

lemma zorder_mform_cmult [simp]:
  assumes "Im z > 0" "c \<noteq> 0"
  shows   "zorder_mform (\<langle>c\<rangle> * f) z = zorder_mform f z"
  using assms by (auto simp add: zorder_mform_def)

lemma zorder_mform_cmult' [simp]:
  assumes "Im z > 0" "c \<noteq> 0"
  shows   "zorder_mform (f * \<langle>c\<rangle>) z = zorder_mform f z"
  using assms by (auto simp add: zorder_mform_def)

lemma zorder_mform_uminus [simp]:
  assumes "Im z > 0"
  shows   "zorder_mform (-f) z = zorder_mform f z"
  using assms by (auto simp add: zorder_mform_def)

lemma zorder_mform_const [simp]:
  assumes "Im z > 0"
  shows   "zorder_mform (const_mero_uhp c) z = 0"
proof (cases "c = 0")
  case False
  thus ?thesis
    using assms by (subst zorder_mform_eq_0_iff) auto
qed (auto simp: zorder_mform_def)

lemma zorder_mform_const' [simp]:
  assumes "Im z > 0" "is_const_mero_uhp f"
  shows   "zorder_mform f z = 0"
  using assms by (auto simp: is_const_mero_uhp_def)

lemma zorder_mform_inverse [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (inverse f) z = -zorder_mform f z"
proof -
  from assms have "inverse f \<in> MFuns - {0}"
    by (auto intro!: mform_intros)
  hence "zorder_mform (inverse f) z * weighting_factor z =
         (-zorder_mform f z) * weighting_factor z"
    using zorder_inverse_mero_uhp[of f z] assms
    by (simp add: zorder_conv_zorder_mform algebra_simps)
  thus ?thesis
    using weighting_factor_pos[OF assms(2)]
    by (metis mult_right_cancel not_less_iff_gr_or_eq)
qed

lemma zorder_mform_mult:
  assumes "f \<in> MFuns - {0}" "g \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (f * g) z = zorder_mform f z + zorder_mform g z"
proof -
  from assms have "f * g \<in> MFuns - {0}"
    by (auto intro!: mform_intros)
  hence "zorder_mform (f * g) z * weighting_factor z =
         (zorder_mform f z + zorder_mform g z) * weighting_factor z"
    using zorder_mult_mero_uhp[of f g z] assms
    by (simp add: zorder_conv_zorder_mform algebra_simps)
  thus ?thesis
    using weighting_factor_pos[OF assms(3)] by simp
qed

lemma zorder_mform_divide:
  assumes "f \<in> MFuns - {0}" "g \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (f / g) z = zorder_mform f z - zorder_mform g z"
proof -
  have "zorder_mform (f * inverse g) z = zorder_mform f z - zorder_mform g z"
    using assms by (subst zorder_mform_mult) (auto intro: mform_intros)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma zorder_mform_power_int [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (f powi n) z = n * zorder_mform f z"
proof -
  have "zorder (f powi n) z = n * zorder f z"
    using assms by (intro zorder_power_int_mero_uhp) auto
  thus ?thesis using assms weighting_factor_pos[of z]
    by (subst (asm) (1 2) zorder_conv_zorder_mform)
       (auto simp: zorder_conv_zorder_mform algebra_simps 
             simp del: weighting_factor_pos intro: mform_intros)
qed

lemma zorder_mform_power [simp]:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (f ^ n) z = n * zorder_mform f z"
  using zorder_mform_power_int[OF assms, of "int n"] by (simp del: zorder_mform_power_int)

lemma zorder_mform_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> MFuns - {0}" "Im z > 0"
  shows   "zorder_mform (\<Prod>x\<in>A. f x) z = (\<Sum>x\<in>A. zorder_mform (f x) z)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  have "zorder_mform (f x * prod f A) z = zorder_mform (f x) z + (\<Sum>x\<in>A. zorder_mform (f x) z)"
    using insert by (subst zorder_mform_mult) (auto intro!: mform_intros)
  thus ?case
    using insert.hyps by simp
qed auto


lemma Eisenstein_G4_nonzero:
  assumes z: "z \<in> \<R>\<^sub>\<Gamma>'" "z \<noteq> \<^bold>\<rho>"
  shows   "Eisenstein_G 4 z \<noteq> 0"
proof
  assume zero: "Eisenstein_G 4 z = 0"
  hence [simp]: "z \<noteq> \<i>"
    by auto
  from assms have z': "Im z > 0"
    by (auto simp: in_std_fund_region'_iff)
  note [simp] = G_modform_eq_0_iff
  have *: "\<G>\<^sub>4 \<in> MForms[4] - {0}"
    using assms by (auto intro: mform_intros simp: G_modform_eq_0_iff)
  define C where "C = sum (zorder_mero_uhp \<G>\<^sub>4) (zeros_mero_uhp \<G>\<^sub>4 - {\<i>, \<^bold>\<rho>})"
  let ?N = "zorder_mero_uhp \<G>\<^sub>4"
  have "0 < (\<Sum>w\<in>{z}. ?N w)"
    using assms zero by (auto simp: in_std_fund_region'_iff)
  hence "12 \<le> 12 * (\<Sum>w\<in>{z}. ?N w)"
    by linarith
  also have "\<dots> \<le> 12 * C"
    unfolding C_def using zero assms z' *
    by (intro mult_left_mono sum_mono2 Eisenstein_G.finite_inv_image_mero_uhp finite_Diff)
       (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  also have "\<dots> \<le> 12 * C + 4 * ?N \<^bold>\<rho> + 6 * ?N \<i> + 12 * zorder_at_cusp 1 \<G>\<^sub>4"
    by auto
  also have "\<dots> = 4"
    unfolding C_def using MForms_valence_formula'[OF *] by simp
  finally show False
    by simp
qed

lemma Eisenstein_G6_nonzero:
  assumes z: "z \<in> \<R>\<^sub>\<Gamma>'" "z \<noteq> \<i>"
  shows   "Eisenstein_G 6 z \<noteq> 0"
proof
  assume zero: "Eisenstein_G 6 z = 0"
  hence [simp]: "z \<noteq> \<^bold>\<rho>"
    by auto
  from assms have z': "Im z > 0"
    by (auto simp: in_std_fund_region'_iff)
  note [simp] = G_modform_eq_0_iff
  have *: "\<G>\<^sub>6 \<in> MForms[6] - {0}"
    using assms by (auto intro: mform_intros simp: G_modform_eq_0_iff)
  define C where "C = sum (zorder_mero_uhp \<G>\<^sub>6) (zeros_mero_uhp \<G>\<^sub>6 - {\<i>, \<^bold>\<rho>})"
  let ?N = "zorder_mero_uhp \<G>\<^sub>6"
  have "0 < (\<Sum>w\<in>{z}. ?N w)"
    using assms zero by (auto simp: in_std_fund_region'_iff)
  hence "12 \<le> 12 * (\<Sum>w\<in>{z}. ?N w)"
    by linarith
  also have "\<dots> \<le> 12 * C"
    unfolding C_def using zero assms z' *
    by (intro mult_left_mono sum_mono2 Eisenstein_G.finite_inv_image_mero_uhp finite_Diff)
       (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  also have "\<dots> \<le> 12 * C + 4 * ?N \<^bold>\<rho> + 6 * ?N \<i> + 12 * zorder_at_cusp 1 \<G>\<^sub>4"
    by auto
  also have "\<dots> = 6"
    unfolding C_def using MForms_valence_formula'[OF *] by simp
  finally show False
    by simp
qed

lemma MFuns_valence_formula:
  assumes "f \<in> MFuns - {0}"
  defines "Z \<equiv> zeros_mero_uhp f \<union> poles_mero_uhp f"
  shows   "(\<Sum>z\<in>Z. zorder_mform f z) + zorder_at_cusp 1 f = 0"
proof -
  interpret modular_function f UNIV
    using assms by auto
  define Z' where "Z' = Z - {\<^bold>\<rho>, \<i>}"
  have [intro]: "finite Z"
    unfolding Z_def using assms by auto

  have "(\<Sum>z\<in>Z. zorder_mform f z) = (\<Sum>z\<in>Z' \<union> {\<^bold>\<rho>, \<i>}. zorder_mform f z)"
  proof (intro sum.mono_neutral_left ballI)
    show "zorder_mform f z = 0" if "z \<in> Z' \<union> {\<^bold>\<rho>, \<i>} - Z" for z
    proof -
      from that have z: "z \<in> {\<^bold>\<rho>, \<i>}" "\<not>is_pole f z" "f z \<noteq> 0"
        by (auto simp: Z_def Z'_def inv_image_mero_uhp_def poles_mero_uhp_def)
      hence "zorder f z = 0"
        by (subst zorder_mero_uhp_eq_0_iff) auto
      thus ?thesis
        by (simp add: zorder_mform_def)
    qed
  qed (auto simp: Z'_def)
  also have "12 * \<dots> + 12 * zorder_at_cusp 1 f = 
               12 * (\<Sum>z\<in>Z'. zorder_mform f z) + 12 * zorder_mform f \<^bold>\<rho> + 12 * zorder_mform f \<i> +
               12 * zorder_at_cusp 1 f"
    by (subst sum.union_disjoint) (auto simp: Z'_def)
  also have "(\<Sum>z\<in>Z'. zorder_mform f z) = (\<Sum>z\<in>Z'. zorder f z)"
  proof (intro sum.cong refl)
    fix z assume "z \<in> Z'"
    hence z: "z \<in> \<R>\<^sub>\<Gamma>'" "z \<noteq> \<^bold>\<rho>" "z \<noteq> \<i>"
      by (auto simp: Z'_def Z_def inv_image_mero_uhp_def poles_mero_uhp_def)
    from z have "Im z > 0"
      using in_std_fund_region'_iff by blast
    have "\<not>z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
      using Eisenstein_G4_nonzero[of z] z Eisenstein_G_4_zero_iff by blast
    moreover have "\<not>z \<sim>\<^sub>\<Gamma> \<i>"
      using Eisenstein_G6_nonzero[of z] z Eisenstein_G_6_zero_iff by blast
    ultimately show "zorder_mform f z = zorder f z"
      using assms \<open>Im z > 0\<close> by (simp add: zorder_mform_def)
  qed
  also have "zorder_mform f \<^bold>\<rho> = zorder f \<^bold>\<rho> div 3"
    using assms by (simp add: zorder_mform_def)
  also have "12 * \<dots> = 4 * zorder f \<^bold>\<rho>"
    using MFuns_weighting_factor_dvd_zorder[OF assms(1), of "\<^bold>\<rho>"] by auto
  also have "zorder_mform f \<i> = zorder f \<i> div 2"
    using assms by (simp add: zorder_mform_def)
  also have "12 * \<dots> = 6 * zorder f \<i>"
    using MFuns_weighting_factor_dvd_zorder[OF assms(1), of "\<i>"] by auto
  also have "12 * sum (zorder_mero_uhp f) Z' + 4 * zorder_mero_uhp f \<^bold>\<rho> + 6 * zorder_mero_uhp f \<i> +
               12 * zorder_at_cusp 1 f = 0"
    using MeForms_valence_formula'[OF assms(1)] by (simp add: Z'_def Z_def insert_commute)
  finally show ?thesis by simp
qed



subsection \<open>Degree of a modular function\<close>

definition degree_modfun :: "mero_uhp \<Rightarrow> nat" where
  "degree_modfun f =
     (if is_const_mero_uhp f then 0
      else (\<Sum>z\<in>zeros_mero_uhp f. nat (zorder_mform f z)) + nat (zorder_at_cusp 1 f))"

lemma degree_modfun_is_const [simp]: "is_const_mero_uhp f \<Longrightarrow> degree_modfun f = 0"
  by (simp add: degree_modfun_def)

text \<open>
  The following two statements show that the number of zeros of a modular function is the same
  as the number of poles of a modular function, with all the usual conventions about counting
  zeros and poles of modular functions.
\<close>
lemma int_degree_modfun_conv_zeros:
  assumes "f \<in> MFuns"
  shows "int (degree_modfun f) = (\<Sum>z\<in>zeros_mero_uhp f. zorder_mform f z) + max 0 (zorder_at_cusp 1 f)"
proof (cases "is_const_mero_uhp f")
  case False
  hence "f \<noteq> 0"
    by auto
  have "int (degree_modfun f) =
          (\<Sum>z\<in>zeros_mero_uhp f. max 0 (zorder_mform f z)) + max 0 (zorder_at_cusp 1 f)"
    using assms False by (auto simp: degree_modfun_def max_def)
  also have "(\<Sum>z\<in>zeros_mero_uhp f. max 0 (zorder_mform f z)) = (\<Sum>z\<in>zeros_mero_uhp f. zorder_mform f z)"
    using \<open>f \<noteq> 0\<close> assms
    by (intro sum.cong refl) (auto simp: max_def inv_image_mero_uhp_def in_std_fund_region'_iff)
  finally show ?thesis .
next
  case True
  show ?thesis
  proof (cases "f = 0")
    case True
    thus ?thesis by (simp add: zorder_mform_def)
  next
    case False
    with True obtain c where [simp]: "f = const_mero_uhp c" "c \<noteq> 0"
      by (auto simp: is_const_mero_uhp_def)
    interpret modular_form "const_mero_uhp c" 0 UNIV
      by auto
    have [simp]: "zeros_mero_uhp \<langle>c\<rangle> = {}"
      by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
    show ?thesis
      by (auto simp add: degree_modfun_def)
  qed
qed

lemma int_degree_modfun_conv_poles:
  assumes "f \<in> MFuns"
  shows "int (degree_modfun f) = (\<Sum>z\<in>poles_mero_uhp f. -zorder_mform f z) - min 0 (zorder_at_cusp 1 f)"
proof (cases "f = 0")
  case False
  hence *: "f \<in> MFuns - {0}"
    using assms by auto
  interpret modular_function f UNIV
    using * by auto
  define Z P where "Z = zeros_mero_uhp f" and "P = poles_mero_uhp f"
  have disj: "Z \<inter> P = {}"
    by (auto simp: Z_def P_def inv_image_mero_uhp_def poles_mero_uhp_def)
  have "0 = sum (zorder_mform f) (Z \<union> P) + zorder_at_cusp 1 f"
    using MFuns_valence_formula[OF *] unfolding Z_def P_def ..
  also have "\<dots> = sum (zorder_mform f) Z + max 0 (zorder_at_cusp 1 f) + 
                  sum (zorder_mform f) P + min 0 (zorder_at_cusp 1 f)"
    using * disj by (subst sum.union_disjoint) (auto simp: Z_def P_def)
  also have "sum (zorder_mform f) Z + max 0 (zorder_at_cusp 1 f) = degree_modfun f"
    using * by (subst int_degree_modfun_conv_zeros) (auto simp: Z_def)
  finally show ?thesis
    unfolding P_def by (simp add: algebra_simps sum_negf)
qed auto

lemma abs_zorder_mform_le_degree_modfun:
  assumes "f \<in> MFuns - {0}" "Im z > 0"
  shows   "\<bar>zorder_mform f z\<bar> \<le> degree_modfun f"
proof -
  interpret modular_function f UNIV
    using assms by auto
  have [dest]: "Im z > 0" if "z \<in> \<R>\<^sub>\<Gamma>'" for z
    using that by (auto simp: in_std_fund_region'_iff)
  obtain z' where z': "z' \<in> \<R>\<^sub>\<Gamma>'" "z' \<sim>\<^sub>\<Gamma> z"
    by (meson assms(2) equiv_point_in_std_fund_region' modular_group.rel_sym)
  have z'': "Im z' > 0"
    using z' by (auto simp: in_std_fund_region'_iff)
  have "\<bar>zorder_mform f z'\<bar> \<le> degree_modfun f"
  proof (cases "zorder_mform f z'" "0 :: int" rule: linorder_cases)
    case greater
    hence "z' \<in> zeros_mero_uhp f"
      using z' z'' assms by (simp add: inv_image_mero_uhp_def)
    hence "(\<Sum>w\<in>{z'}. zorder_mform f w) \<le> (\<Sum>w\<in>zeros_mero_uhp f. zorder_mform f w)"
      by (intro sum_mono2 finite_inv_image_mero_uhp)
         (use assms in \<open>auto simp: inv_image_mero_uhp_def\<close>)
    also have "\<dots> \<le> int (degree_modfun f)"
      using assms by (simp add: int_degree_modfun_conv_zeros) 
    finally show ?thesis
      using greater by simp
  next
    case less
    hence "z' \<in> poles_mero_uhp f"
      using z' z'' assms by (simp add: poles_mero_uhp_def)
    hence "(\<Sum>w\<in>{z'}. -zorder_mform f w) \<le> (\<Sum>w\<in>poles_mero_uhp f. -zorder_mform f w)"
      by (intro sum_mono2 finite_poles_mero_uhp)
         (use assms in \<open>auto simp: poles_mero_uhp_def\<close>)
    also have "\<dots> \<le> int (degree_modfun f)"
      using assms by (simp add: int_degree_modfun_conv_poles) 
    finally show ?thesis
      using less by simp
  qed auto
  also have "zorder_mform f z' = zorder_mform f z"
    using z' rel_imp_zorder_mform_eq by blast
  finally show ?thesis .
qed  

lemma abs_zorder_at_cusp_le_degree_modfun:
  assumes "f \<in> MFuns - {0}"
  shows   "\<bar>zorder_at_cusp 1 f\<bar> \<le> degree_modfun f"
proof (cases "zorder_at_cusp 1 f" "0 :: int" rule: linorder_cases)
  case greater
  have "sum (zorder_mform f) (zeros_mero_uhp f) \<ge> 0"
    using assms by (intro sum_nonneg) (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
  thus ?thesis using greater assms
    by (simp add: int_degree_modfun_conv_zeros)
next
  case less
  have "sum (\<lambda>z. -zorder_mform f z) (poles_mero_uhp f) \<ge> 0"
    using assms by (intro sum_nonneg) (auto simp: poles_mero_uhp_def in_std_fund_region'_iff)
  thus ?thesis using less assms
    by (simp add: int_degree_modfun_conv_poles)
qed auto

(* FIXME Manuel: This was much more painful than it should be. *)
text \<open>
  Together with this, the previous two results directly imply Apostol's Theorem~2.5:
  If $f(z)$ is a non-constant modular function, then for any constant $c$, the modular function 
  $f(z) + c$ has the same degree as the modular function $f(z)$. Therefore, the number of zeros of
  $f(z) - c$ is the same as the number of zeros in $f(z)$.

  In other words: $f(z)$ takes every value $z\in\mathbb{C}$ equally (and finitely) often --
  and that number is its degree.
\<close>
lemma degree_modfun_plus_const_eq:
  assumes f: "f \<in> MFuns"
  shows "degree_modfun (f + const_mero_uhp c) = degree_modfun f"
proof (cases "is_const_mero_uhp f")
  case not_const: False
  from not_const have [simp]: "f \<noteq> 0" and "f + \<langle>c\<rangle> \<noteq> 0"
    by (auto simp: add_eq_0_iff2)
  interpret modular_function f UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
    using assms by auto
  interpret modular_function_pair f "\<langle>c\<rangle>" UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
    by unfold_locales auto

  let ?f' = "f + const_mero_uhp c"
  have "int (degree_modfun ?f') =
          (\<Sum>z\<in>poles_mero_uhp ?f'. -zorder_mform ?f' z) - min 0 (zorder_at_cusp 1 ?f')"
    by (intro int_degree_modfun_conv_poles mform_intros assms) auto
  also have "(\<Sum>z\<in>poles_mero_uhp ?f'. -zorder_mform ?f' z) =
             (\<Sum>z\<in>poles_mero_uhp f. -zorder_mform f z)"
  proof (rule sum.cong, goal_cases)
    case 1
    have "is_pole (eval_mero_uhp (f + \<langle>c\<rangle>)) z \<longleftrightarrow> is_pole (eval_mero_uhp f) z" if z: "z \<in> \<R>\<^sub>\<Gamma>'" for z
      by (intro is_pole_plus_analytic_mero_uhp_iff1) auto
    thus "poles_mero_uhp (f + \<langle>c\<rangle>) = poles_mero_uhp f"
      by (auto simp: zorder_mero_uhp_add1 poles_mero_uhp_def)
  next
    case (2 z)
    hence z: "Im z > 0" and [simp]: "f \<noteq> 0"
      by (auto simp: poles_mero_uhp_def in_std_fund_region'_iff)
    have "zorder (f + \<langle>c\<rangle>) z = zorder f z"
    proof (cases "c = 0")
      case [simp]: False
      show ?thesis
        using 2 z by (subst zorder_mero_uhp_add1) (auto simp: poles_mero_uhp_def)
    qed auto
    moreover have "f + \<langle>c\<rangle> \<noteq> 0"
      using 2 by (auto simp: add_eq_0_iff2)
    ultimately show ?case
      by (simp add: zorder_mform_def)
  qed
  also have "min 0 (zorder_at_cusp 1 ?f') = min 0 (zorder_at_cusp 1 f)"
  proof (cases "zorder_at_cusp 1 f \<ge> 0")
    case True
    have freq: "\<exists>\<^sub>F z in at 0. fourier z + c \<noteq> 0"
      using eventually_neq_fourier[of "-c" 0] \<open>f + \<langle>c\<rangle> \<noteq> 0\<close>
      by (intro eventually_frequently) (auto simp: add_eq_0_iff2 hom_distribs)

    from True have "zorder fourier 0 \<ge> 0"
      using zorder_at_cusp_conv_fourier by (simp add: not_le)
    hence not_pole: "\<not>is_pole fourier 0"
      by simp
    hence "\<not>is_pole (\<lambda>q. fourier q + c) 0"
      by (subst is_pole_plus_analytic_iff1) auto
    hence "0 \<le> zorder (\<lambda>q. fourier q + c) 0"
      using not_pole by (intro zorder_ge_0 analytic_intros freq) auto
    also have "\<dots> = zorder add.map.fourier 0"
    proof (intro zorder_cong)
      have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at 0)"
        by (intro eventually_at_in_open') auto
      moreover have "eventually (\<lambda>q. add.map.fourier q = fourier q + modular_group.const.fourier c q) (at 0)"
        using eventually_cosparse_imp_eventually_at[OF fourier_add_eventually_eq, of 0 UNIV] by auto
      ultimately show "eventually (\<lambda>q. fourier q + c = add.map.fourier q) (at 0)"
        by eventually_elim auto
    qed auto
    also have "\<dots> = zorder_at_cusp 1 (f + \<langle>c\<rangle>)"
      using add.zorder_at_cusp_conv_fourier \<open>f + \<langle>c\<rangle> \<noteq> 0\<close> by simp
    finally show ?thesis
      using True by simp
  next
    case False
    have "eventually (\<lambda>q. add.map.fourier q = fourier q + modular_group.const.fourier c q) (at 0)"
      by (intro eventually_cosparse_imp_eventually_at[OF fourier_add_eventually_eq]) auto
    moreover have "eventually (\<lambda>q. q \<in> ball 0 1) (at (0 :: complex))"
      by (rule eventually_at_in_open') auto
    ultimately have ev: "eventually (\<lambda>q. add.map.fourier q = fourier q + c) (at 0)"
      by eventually_elim auto

    from False have "zorder fourier 0 < 0"
      using zorder_at_cusp_conv_fourier by (simp add: not_le)
    hence [intro]: "is_pole fourier 0"
      by simp
    hence "is_pole (\<lambda>q. fourier q + c) 0"
      by (subst is_pole_plus_const_iff [symmetric])
    hence "zorder (\<lambda>q. fourier q + c) 0 = zorder fourier 0"
    proof (cases "c = 0")
      case [simp]: False
      show ?thesis using eventually_neq_fourier[of 0 0]
        by (intro zorder_add1 meromorphic_intros eventually_frequently) auto
    qed auto
    also have "zorder (\<lambda>q. fourier q + c) 0 = zorder add.map.fourier 0"
      by (intro zorder_cong) (use ev in \<open>simp_all add: eq_commute\<close>)
    also have "\<dots> = zorder_at_cusp 1 (f + \<langle>c\<rangle>)"
      using add.zorder_at_cusp_conv_fourier \<open>f + \<langle>c\<rangle> \<noteq> 0\<close> by simp
    finally show ?thesis
      using zorder_at_cusp_conv_fourier by simp
  qed
  also have "(\<Sum>z\<in>poles_mero_uhp f. - zorder_mform f z) - min 0 (zorder_at_cusp 1 f) =
             int (degree_modfun f)"
    by (intro int_degree_modfun_conv_poles[symmetric] assms)
  finally show ?thesis
    by simp
qed auto

lemma WMForms_nonpole_exists:
  assumes "f \<in> WMForms[k]"
  obtains z where "Im z > 0" "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z"
proof -
  interpret weakly_modular_form f k UNIV
    using assms by auto
  have "eventually (\<lambda>z. \<not>is_pole f z) (cosparse {z. Im z > 0})"
    by (simp add: eval_mero_uhp_meromorphic meromorphic_on_imp_not_pole_cosparse)
  hence ev: "eventually (\<lambda>z. z \<in> {z. Im z > 0} \<and> \<not>is_pole f z) (cosparse {z. Im z > 0})"
    by (intro eventually_conj eventually_in_cosparse open_halfspace_Im_gt order.refl)
  moreover have "\<exists>z. Im z > 0"
    by (intro exI[of _ \<i>]) auto
  ultimately obtain z where z: "Im z > 0" "\<not>is_pole f z"
    using eventually_happens[OF ev] by auto
  then obtain z' where z': "z' \<sim>\<^sub>\<Gamma> z" "z' \<in> \<R>\<^sub>\<Gamma>'"
    by (meson equiv_point_in_std_fund_region' modular_group.rel_sym)
  show ?thesis
    using z z' that[of z'] rel_imp_is_pole_iff[OF z'(1)] by auto
qed

text \<open>
  The only modular functions of degree 0 are the constant functions.
\<close>
theorem degree_modfun_eq_0_iff:
  assumes f: "f \<in> MFuns"
  shows   "degree_modfun f = 0 \<longleftrightarrow> is_const_mero_uhp f"
proof
  assume "degree_modfun f = 0"
  from assms interpret modular_function f UNIV
    by auto

  have "f \<in> WMForms[0]"
    using f by (simp add: WMForms_def weakly_modular_form_axioms)
  then obtain z where z: "Im z > 0" "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z"
    using WMForms_nonpole_exists[of f 0] by blast

  show "is_const_mero_uhp f"
  proof (rule ccontr)
    assume not_const: "\<not>is_const_mero_uhp f"
    define c where "c = -f z"
    define g where "g = f + \<langle>c\<rangle>"
    have "g \<noteq> 0"
      using not_const by (auto simp: g_def add_eq_0_iff2)
    hence g: "g \<in> MFuns - {0}"
      using f by (auto simp: g_def intro: mform_intros)
    interpret g: modular_function g UNIV
      using g by auto

    have "0 < sum (zorder_mform g) (zeros_mero_uhp g)"
    proof (rule sum_pos)
      have "mero_uhp_rel g (\<lambda>z. f z + c)"
        unfolding g_def by mero_uhp_rel
      hence "is_pole g z \<longleftrightarrow> is_pole (\<lambda>z. f z + c) z"
        using z by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt mero_uhp_rel_def)
      hence "\<not>is_pole g z"
        using z by (subst (asm) is_pole_plus_const_iff[symmetric]) auto
      with z have "z \<in> zeros_mero_uhp g"
        by (auto simp: inv_image_mero_uhp_def g_def c_def)
      thus "zeros_mero_uhp g \<noteq> {}"
        by auto
    next
      show "zorder_mform g z > 0" if "z \<in> zeros_mero_uhp g" for z
        using that g unfolding inv_image_mero_uhp_def
        by (auto simp: in_std_fund_region'_iff)
    qed (use g in auto)
    also have "\<dots> \<le> int (degree_modfun g)"
      using g by (subst int_degree_modfun_conv_zeros) auto
    also have "degree_modfun g = degree_modfun f"
      using f unfolding g_def by (subst degree_modfun_plus_const_eq) auto
    finally show False
      using \<open>degree_modfun f = 0\<close> by simp
  qed
qed auto

lemma degree_modfun_pos_iff:
  assumes f: "f \<in> MFuns"
  shows   "degree_modfun f > 0 \<longleftrightarrow> \<not>is_const_mero_uhp f"
  using degree_modfun_eq_0_iff[OF f] by auto


text \<open>
  We define the \<^emph>\<open>range\<close> of a meromorphic function on the upper half plane to be the
  set of all the values it takes in the upper half plane (minus the places where it has poles)
  or at the cusp $i\infty$ (if there is one).
\<close>
(* TODO Manuel: This will have to be generalised a bit for functions with more than one cusp *)
definition range_mero_uhp :: "mero_uhp \<Rightarrow> complex set" where
  "range_mero_uhp f = f ` {z\<in>\<H>. \<not>is_pole f z} \<union> {L. (f \<longlongrightarrow> L) at_cusp}"

lemma range_mero_uhpI1:
  assumes "eval_mero_uhp f z = y" "Im z > 0" "\<not>is_pole f z"
  shows   "y \<in> range_mero_uhp f"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhpI2:
  assumes "(eval_mero_uhp f \<longlongrightarrow> y) at_cusp"
  shows   "y \<in> range_mero_uhp f"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhpE:
  assumes "y \<in> range_mero_uhp f"
  obtains z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_cusp"
  using assms unfolding range_mero_uhp_def by blast

lemma range_mero_uhp_altdef1:
  assumes "f \<in> MeForms[G, k]"
  defines "n \<equiv> modgrp_subgroup_period G"
  defines "F \<equiv> fourier_expansion.fourier f n"
  shows   "range_mero_uhp f = F ` {z\<in>ball 0 1. \<not>is_pole F z}"
proof -
  interpret meromorphic_form f k G
    using assms by auto
  show ?thesis
  proof (intro equalityI subsetI; (elim imageE)?)
    fix y
    assume "y \<in> range_mero_uhp f"
    then consider z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_cusp"
      by (elim range_mero_uhpE)
    thus "y \<in> F ` {z\<in>ball 0 1. \<not>is_pole F z}"
    proof cases
      case 1
      hence "F (cusp_q n z) \<in> F ` {z\<in>ball 0 1. \<not>is_pole F z}"
        using period_pos by (intro imageI) (auto simp: n_def F_def fourier_is_pole_cusp_q_iff)
      thus ?thesis
        using 1 by (simp add: n_def F_def)
    next
      case 2
      hence "F 0 = y \<and> \<not>is_pole F 0"
        unfolding F_def n_def using not_tendsto_and_filterlim_at_infinity[of at_cusp f y]
        by (auto simp: fourier_0_aux fourier_is_pole_0_iff)
      thus ?thesis
        by auto
    qed
  next
    fix y q assume q: "q \<in> {z\<in>ball 0 1. \<not>is_pole F z}" "y = F q"
    show "y \<in> range_mero_uhp f"
    proof (cases "q = 0")
      case True
      hence "(eval_mero_uhp f \<longlongrightarrow> F 0) at_cusp"
        using q assms(3) fourier_nicely_meromorphic fourier_tendsto_0_iff n_def nicely_meromorphic_on_def by auto
      thus ?thesis using q True
        by (auto simp: range_mero_uhp_def)
    next
      case False
      define z where "z = cusp_q_inv n q"
      have q_eq: "q = cusp_q n z" and z: "Im z > 0"
        using False assms q
        by (auto simp: z_def n_def modgrp_subgroup_period_pos intro!: Im_cusp_q_inv_gt)
      have z': "fourier q = f z \<and> \<not>is_pole f z"
        using z q by (simp add: q_eq n_def F_def fourier_is_pole_cusp_q_iff)
      have "f z \<in> eval_mero_uhp f ` {z. 0 < Im z \<and> \<not> is_pole (eval_mero_uhp f) z}"
        by (intro imageI) (use z z' in auto)
      also have "f z = y"
        using z' q by (auto simp: F_def n_def)
      finally show ?thesis
        by (simp add: range_mero_uhp_def)
    qed
  qed
qed

lemma range_mero_uhp_altdef2:
  assumes "f \<in> MFuns"
  defines "P \<equiv> (if f \<noteq> 0 \<and> zorder_at_cusp (Suc 0) f \<ge> 0 then {eval_mero_uhp_at_cusp f} else {})"
  shows   "range_mero_uhp f = f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
proof -
  interpret modular_function f UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
    using assms(1) by auto
  show ?thesis
  proof (intro equalityI subsetI; (elim imageE)?)
    fix y
    assume "y \<in> range_mero_uhp f"
    then consider z where "z \<in> \<H>" "\<not>is_pole f z" "f z = y" | "(f \<longlongrightarrow> y) at_cusp"
      by (elim range_mero_uhpE)
    thus "y \<in> f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
    proof cases
      case 1
      then obtain z' where z': "z' \<sim>\<^sub>\<Gamma> z" "z' \<in> \<R>\<^sub>\<Gamma>'"
        by (metis equiv_point_in_std_fund_region' mem_Collect_eq modular_group.rel_sym)
      from z' have "f z' = f z"
        by (meson rel_imp_eval_eq)
      moreover from z' 1 have "\<not>is_pole f z'"
        using rel_imp_is_pole_iff by blast
      ultimately show ?thesis using z'
        using 1 by (auto simp: poles_mero_uhp_def)
    next
      case 2
      show ?thesis
      proof (cases "f = 0")
        case [simp]: False
        from 2 have "\<not>filterlim f at_infinity at_cusp"
          using not_tendsto_and_filterlim_at_infinity[of at_cusp f y] by auto
        hence "\<not>is_pole fourier 0"
          by (subst fourier_is_pole_0_iff)
        hence "zorder fourier 0 \<ge> 0"
          by (subst zorder_fourier_nonneg_iff) auto
        hence "zorder_at_cusp (Suc 0) f \<ge> 0"
          by (subst zorder_at_cusp_conv_fourier) auto
        hence "y \<in> P"
          unfolding P_def using 2 by (auto simp: zorder_at_cusp_conv_fourier fourier_0_aux)
        thus ?thesis
          by blast
      next
        case True
        have "\<i> \<in> \<R>\<^sub>\<Gamma>'"
          by auto
        from True and 2 have "((\<lambda>_. 0) \<longlongrightarrow> y) at_cusp"
          by simp
        hence [simp]: "y = 0"
          using True fourier_0_aux by auto
        show ?thesis using True 2 by (auto simp: P_def)
      qed
    qed
  next
    fix y assume "y \<in> eval_mero_uhp f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f) \<union> P"
    thus "y \<in> range_mero_uhp f"
    proof
      assume y: "y \<in> eval_mero_uhp f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)"
      thus ?thesis
        by (auto simp: range_mero_uhp_def in_std_fund_region'_iff poles_mero_uhp_def intro!: imageI)
    next
      assume "y \<in> P"
      hence "zorder_at_cusp (Suc 0) f \<ge> 0" and [simp]: "f \<noteq> 0" "y = fourier 0"
        by (auto simp: P_def split: if_splits)
      from this(1) have "zorder fourier 0 \<ge> 0"
        by (subst (asm) zorder_at_cusp_conv_fourier) auto
      hence "\<not>is_pole fourier 0"
        by (subst (asm) zorder_fourier_nonneg_iff) auto
      hence "(fourier \<longlongrightarrow> fourier 0) (at 0)"
        by (intro tendsto_intros) auto
      hence "(eval_mero_uhp f \<longlongrightarrow> fourier 0) at_cusp"
        by (subst (asm) fourier_tendsto_0_iff)
      thus "y \<in> range_mero_uhp f"
        by (auto simp: P_def range_mero_uhp_def split: if_splits)
    qed
  qed
qed

text \<open>
  A non-constant meromorphic form w.r.t.\ the full modular group is always surjective.
\<close>
lemma MFuns_surj_obtain:
  assumes f: "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  obtains z where
    "z \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole f z" "f z = c"
  | "zorder_at_cusp 1 f \<ge> 0" "eval_mero_uhp_at_cusp f = c"
proof -
  from assms have [simp]: "f \<noteq> 0"
    by auto
  interpret modular_function f UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
    using f by auto
  interpret modular_function_pair f "const_mero_uhp (-c)" UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0" by unfold_locales auto
  define g where "g = f + \<langle>-c\<rangle>"
  have g: "g \<in> MFuns" "\<not>is_const_mero_uhp g"  
    using assms by (auto simp: g_def intro: mform_intros)

  have "0 < int (degree_modfun g)"
    using g degree_modfun_pos_iff[of g] by auto
  also have "\<dots> = sum (zorder_mform g) (zeros_mero_uhp g) + max 0 (zorder_at_cusp 1 g)"
    using g by (subst int_degree_modfun_conv_zeros) auto
  finally have "zeros_mero_uhp g \<noteq> {} \<or> zorder_at_cusp 1 g > 0"
    by auto
  thus ?thesis
  proof
    assume "zeros_mero_uhp g \<noteq> {}"
    then obtain z' where z': "z' \<in> \<R>\<^sub>\<Gamma>'" "\<not>is_pole g z'" "g z' = 0"
      by (auto simp: inv_image_mero_uhp_def)
    note z'(2)
    also have "mero_uhp_rel g (\<lambda>w. f w + (-c))"
      unfolding g_def by mero_uhp_rel
    hence "is_pole g z' \<longleftrightarrow> is_pole (\<lambda>w. f w + (-c)) z'" using z'
      by (intro is_pole_cong) 
         (auto simp: eventually_cosparse_open_eq open_halfspace_Im_gt 
                     in_std_fund_region'_iff mero_uhp_rel_def)
    also have "\<dots> \<longleftrightarrow> is_pole f z'"
      by (subst is_pole_plus_const_iff [symmetric]) auto
    finally have "\<not>is_pole f z'" .
    moreover from this have "f z' = c"
      using z' by (auto simp: g_def in_std_fund_region'_iff)
    ultimately show ?thesis
      using that(1)[of z'] z' by blast
  next
    assume *: "zorder_at_cusp 1 g > 0"
    from f have [simp]: "f + \<langle>- c\<rangle> \<noteq> 0"
      by (auto simp: add_eq_0_iff2)
    from * have "zorder add.map.fourier 0 > 0"
      using add.zorder_at_cusp_conv_fourier by (simp add: g_def)
    hence "\<not>is_pole add.map.fourier 0"
      by simp
    also have "is_pole add.map.fourier 0 \<longleftrightarrow> is_pole (\<lambda>q. fourier q - c) 0"
    proof (rule is_pole_cong)
      have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at 0)"
        by (rule eventually_at_in_open') auto
      moreover have "eventually (\<lambda>q. add.map.fourier q = fourier q + modular_group.const.fourier (-c) q) (at 0)"
        using eventually_cosparse_imp_eventually_at[OF fourier_add_eventually_eq, of 0 UNIV] by simp
      ultimately show "eventually (\<lambda>q. add.map.fourier q = fourier q - c) (at 0)"
        by eventually_elim auto
    qed auto
    also have "\<dots> \<longleftrightarrow> is_pole fourier 0"
      by (subst is_pole_plus_const_iff[of _ _ c]) auto
    finally have not_pole: "\<not>is_pole fourier 0" .

    from g interpret g: modular_function g UNIV
      rewrites "modgrp_subgroup_period UNIV = Suc 0"
      by auto
    from * have "eval_mero_uhp_at_cusp g = 0"
      by (metis One_nat_def g(2) g.eval_at_cusp_conv_fourier g.zorder_at_cusp_conv_fourier
                g.zorder_fourier_pos_iff is_const_mero_uhp_0 norm_zero zero_less_one_class.zero_less_one)
    also have "eval_mero_uhp_at_cusp g = eval_mero_uhp_at_cusp f - c"
      unfolding g_def using not_pole by (simp add: fourier_add_eq)
    finally have "eval_mero_uhp_at_cusp f = c"
      by simp
    moreover have "zorder fourier 0 \<ge> 0"
      using eventually_neq_fourier[of 0 0] not_pole assms 
      by (intro zorder_ge_0 analytic_intros eventually_frequently) auto
    hence "zorder_at_cusp 1 f \<ge> 0"
      using zorder_at_cusp_conv_fourier by simp
    ultimately show ?thesis
      using that(2) by blast
  qed
qed

theorem MFuns_surj:
  assumes f: "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "range_mero_uhp f = UNIV"
proof safe
  fix c :: complex
  show "c \<in> range_mero_uhp f"
  proof (rule MFuns_surj_obtain[OF assms, of c], goal_cases)
    case (1 z)
    thus ?case
      unfolding range_mero_uhp_altdef2[OF assms(1)]
      by (auto intro!: imageI simp: poles_mero_uhp_def)
  next
    case 2
    thus ?case
      unfolding range_mero_uhp_altdef2[OF assms(1)] by auto
  qed
qed auto

text \<open>
  A modular function of degree 1 is injective on the fundamental region.
  Note that one could prove something stronger, namely that it is injective on its fundamental
  region plus its cusp.
\<close>
lemma MFuns_degree_1_imp_inj_on:
  assumes f: "f \<in> MFuns" "degree_modfun f = 1"
  shows   "inj_on f (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)"
proof -
  interpret modular_function f UNIV
    using assms by auto
  have not_const: "\<not>is_const_mero_uhp f"
    using assms by auto
  have unique: "card (inv_image_mero_uhp f c) \<le> 1" for c
  proof -
    define g where "g = f + \<langle>- c\<rangle>"
    have deg_g: "degree_modfun g = 1"
      unfolding g_def using f by (subst degree_modfun_plus_const_eq) auto
    hence "g \<noteq> 0"
      by auto
    hence g: "g \<in> MFuns - {0}"
      using f by (auto simp: g_def intro: mform_intros)
  
    have "int (card (zeros_mero_uhp g)) = sum (\<lambda>_. 1 :: int) (zeros_mero_uhp g)"
      by simp
    also have "\<dots> \<le> sum (zorder_mform g) (zeros_mero_uhp g)"
    proof (intro sum_mono, goal_cases)
      case (1 z)
      hence "zorder_mform g z > 0"
        using g by (auto simp: inv_image_mero_uhp_def in_std_fund_region'_iff)
      thus ?case
        by linarith
    qed
    also have "\<dots> \<le> int (degree_modfun g)"
      using g by (subst int_degree_modfun_conv_zeros) auto
    also have "\<dots> = 1"
      by (simp add: deg_g)
    finally have "card (zeros_mero_uhp g) \<le> 1"
      by simp
    also have "zeros_mero_uhp g = inv_image_mero_uhp f c"
      by (subst inv_image_mero_uhp_conv_zeros) (simp add: g_def hom_distribs)
    finally show "card (inv_image_mero_uhp f c) \<le> 1" .
  qed

  show ?thesis
  proof
    fix z z' assume z: "z \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f" "z' \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f" "f z = f z'"
    define c where "c = f z"
    from z have "{z, z'} \<subseteq> inv_image_mero_uhp f c"
      by (auto simp: inv_image_mero_uhp_def c_def poles_mero_uhp_def)
    hence "card {z, z'} \<le> card (inv_image_mero_uhp f c)"
      using f not_const by (intro card_mono finite_inv_image_mero_uhp) auto
    also have "\<dots> \<le> 1"
      by (rule unique)
    finally show "z = z'"
      by (cases "z = z'") auto
  qed
qed

text \<open>
  The Klein $J$ function has degree 1.
\<close>
lemma degree_modfun_J: "degree_modfun \<J> = 1"
proof -
  have "int (degree_modfun \<J>) = 1"
    by (subst int_degree_modfun_conv_poles) (auto intro: mform_intros)
  thus ?thesis
    by simp
qed

text \<open>
  Every non-constant modular function either has a pole in the fundamental region or a
  pole at the cusp.
\<close>
theorem MFuns_pole_exists:
  assumes "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "poles_mero_uhp f \<noteq> {} \<or> zorder_at_cusp 1 f < 0"
proof -
  from assms have "int (degree_modfun f) > 0"
    by (simp add: degree_modfun_pos_iff)
  also have "int (degree_modfun f) = 
        (\<Sum>z\<in>poles_mero_uhp f. - zorder_mform f z) - min 0 (zorder_at_cusp (Suc 0) f)"
    using assms by (subst int_degree_modfun_conv_poles) auto
  finally show ?thesis
    by (cases "poles_mero_uhp f = {}") (auto simp: min_def split: if_splits)
qed

text \<open>
  Every non-constant modular function either has a pole or a zero in the fundamental region.
\<close>
lemma MFuns_zero_or_pole_exists:
  assumes "f \<in> MFuns" "\<not>is_const_mero_uhp f"
  shows   "poles_mero_uhp f \<union> zeros_mero_uhp f \<noteq> {}"
proof -
  from MFuns_surj[OF assms] have "0 \<in> range_mero_uhp f"
    by auto
  moreover from MFuns_pole_exists[OF assms] have "poles_mero_uhp f \<noteq> {} \<or> zorder_at_cusp 1 f < 0"
    by auto
  ultimately show ?thesis
    by (subst (asm) range_mero_uhp_altdef2[OF assms(1)])
       (auto simp: inv_image_mero_uhp_def poles_mero_uhp_def)
qed

text \<open>
  Apostol's Theorem~2.6: a bounded modular function is constant.
\<close>
theorem modular_and_bounded_imply_constant:
  assumes "f \<in> MFuns" and "bounded (f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f))"
  shows   "is_const_mero_uhp f"
proof (rule ccontr)
  assume nonconst: "\<not>is_const_mero_uhp f"
  from assms obtain B where B: "\<And>z. z \<in> \<R>\<^sub>\<Gamma>' - poles_mero_uhp f \<Longrightarrow> norm (f z) \<le> B"
    unfolding bounded_iff by blast
  define x y where "x = \<i> * (B + 1)" and "y = \<i> * (B + 2)"
  have [simp]: "norm x > B" "norm y > B"
    by (auto simp: x_def y_def norm_mult)
  have *: "c \<notin> f ` (\<R>\<^sub>\<Gamma>' - poles_mero_uhp f)" if "norm c > B" for c
    using B that by fastforce

  have "eval_mero_uhp_at_cusp f = x"
    by (rule MFuns_surj_obtain[OF assms(1) nonconst, of x])
       (use *[of x] in \<open>auto simp: poles_mero_uhp_def\<close>)
  moreover have "eval_mero_uhp_at_cusp f = y"
    by (rule MFuns_surj_obtain[OF assms(1) nonconst, of y])
       (use *[of y] in \<open>auto simp: poles_mero_uhp_def\<close>)
  ultimately have "x = y"
    by simp
  thus False
    by (simp add: x_def y_def)
qed


text \<open>Theorem 2.7\<close>

lemma zorder_J_modform_conv_Klein_J:
  assumes "Im z > 0"
  shows   "zorder \<J> z = zorder Klein_J z"
proof -
  have "eventually (\<lambda>w. w \<in> {w. Im w > 0}) (at z)"
    by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms in auto)
  hence "eventually (\<lambda>w. \<J> w = Klein_J w) (at z)"
    by eventually_elim auto
  thus ?thesis
    by (intro zorder_cong) auto
qed

lemma zorder_mform_J_minus_const:
  assumes "Im w > 0"
  shows   "zorder_mform (\<J> - \<langle>c\<rangle>) w = (if Klein_J w = c then 1 else 0)"
proof -
  have rel: "mero_uhp_rel (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) (\<lambda>z. Klein_J z - c)"
    by mero_uhp_rel
  hence "is_pole (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) w \<longleftrightarrow> is_pole (\<lambda>z. Klein_J z - c) w"
    using assms
    by (intro is_pole_cong refl)
       (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
  moreover have "(\<lambda>z. Klein_J z - c) analytic_on {w}"
    using assms by (auto intro!: analytic_intros simp: complex_is_Real_iff)
  ultimately have not_pole: "\<not>is_pole (eval_mero_uhp (\<J> - \<langle>c\<rangle>)) w"
    using analytic_at_imp_no_pole by blast

  have "\<not>is_const_mero_uhp \<J>"
    using degree_modfun_J by force
  hence [simp]: "\<J> \<noteq> \<langle>c\<rangle>"
    by (metis is_const_mero_uhp_const_mero_uhp)

  show ?thesis
  proof (cases "Klein_J w = c")
    case False
    have "zorder_mform (\<J> - \<langle>c\<rangle>) w = 0"
      by (subst zorder_mform_eq_0_iff) (use assms not_pole False in \<open>auto intro!: mform_intros\<close>)
    with False show ?thesis
      by simp
  next
    case True
    have "\<bar>zorder_mform (\<J> - \<langle>c\<rangle>) w\<bar> \<le> degree_modfun (\<J> - \<langle>c\<rangle>)"
      by (intro abs_zorder_mform_le_degree_modfun) (use assms in \<open>auto intro!: mform_intros\<close>)
    also have "\<dots> = degree_modfun (\<J> + \<langle>-c\<rangle>)"
      by (simp add: hom_distribs)
    also have "\<dots> = degree_modfun \<J>"
      by (subst degree_modfun_plus_const_eq) (auto intro!: mform_intros)
    also have "\<dots> = 1"
      by (simp add: degree_modfun_J)
    finally have "\<bar>zorder_mform (\<J> - \<langle>c\<rangle>) w\<bar> \<le> 1" .
    moreover have "zorder_mform (\<J> - \<langle>c\<rangle>) w > 0"
      by (subst zorder_mform_pos_iff) (use assms not_pole True in \<open>auto intro!: mform_intros\<close>)
    ultimately have "zorder_mform (\<J> - \<langle>c\<rangle>) w = 1"
      by linarith
    thus ?thesis
      using True by simp
  qed
qed 

lemma zorder_mform_J_rho [simp]: "zorder_mform \<J> \<^bold>\<rho> = 1"
proof -
  have "zorder_mform (\<J> - \<langle>0\<rangle>) \<^bold>\<rho> = 1"
    by (subst zorder_mform_J_minus_const) auto
  thus ?thesis
    by simp
qed

lemma zorder_mform_J_rho' [simp]: "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho> \<Longrightarrow> zorder_mform \<J> z = 1"
  by (force dest: Klein_J.rel_imp_zorder_mform_eq)

lemma zorder_mform_J_ii [simp]: "zorder_mform (\<J> - 1) \<i> = 1"
  unfolding one_mero_uhp_def by (subst zorder_mform_J_minus_const) auto

lemma zorder_mform_J_ii' [simp]: "z \<sim>\<^sub>\<Gamma> \<i> \<Longrightarrow> zorder_mform (\<J> - 1) z = 1"
  by (metis Klein_J_cong const_mero_uhp.hom_one linorder_not_less 
            modular_group.Im_nonpos_imp_not_rel zorder_mform_J_ii zorder_mform_J_minus_const)

lemma zorder_Klein_J: 
  assumes "Im z > 0"
  shows   "zorder (\<lambda>u. Klein_J u - Klein_J z) z = weighting_factor z"
proof -
  have [simp]: "\<J> \<noteq> \<langle>Klein_J z\<rangle>"
    by (metis degree_modfun_J degree_modfun_is_const is_const_mero_uhp_const_mero_uhp zero_neq_one)
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
    by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms in auto)
  hence "eventually (\<lambda>u. Klein_J u - Klein_J z = eval_mero_uhp (\<J> - \<langle>\<J> z\<rangle>) u) (at z)"
    by eventually_elim (use assms in auto)
  hence "zorder (\<lambda>u. Klein_J u - Klein_J z) z = zorder_mero_uhp (\<J> - \<langle>\<J> z\<rangle>) z"
    by (intro zorder_cong) auto
  also have "\<dots> = zorder_mform (\<J> - \<langle>\<J> z\<rangle>) z * weighting_factor z"
    using assms by (subst zorder_conv_zorder_mform) (auto intro!: mform_intros)
  also have "zorder_mform (\<J> - \<langle>\<J> z\<rangle>) z = 1"
    by (subst zorder_mform_J_minus_const) (use assms in auto)
  finally show ?thesis
    by simp
qed

text \<open>
  Apostol's Theorem 2.7
\<close>
lemma zorder_Klein_J_rho: "zorder Klein_J \<^bold>\<rho> = 3"
  using zorder_Klein_J[of "\<^bold>\<rho>"] by simp

lemma zorder_Klein_J_rho':
  assumes "z \<sim>\<^sub>\<Gamma> \<^bold>\<rho>"
  shows   "zorder Klein_J z = 3"
proof -
  have "zorder (\<lambda>u. Klein_J u - Klein_J z) z = weighting_factor z"
    using assms by (intro zorder_Klein_J) (auto simp: modular_group.rel_def)
  also have "Klein_J z = 0"
    using assms by (simp add: Klein_J_cong)
  also have "weighting_factor z = 3"
    using assms by (simp add: weighting_factor_rho')
  finally show ?thesis
    by simp
qed

lemma zorder_Klein_J_ii: "zorder (\<lambda>z. Klein_J z - 1) \<i> = 2"
  using zorder_Klein_J[of \<i>] by simp

lemma zorder_Klein_J_ii':
  assumes "z \<sim>\<^sub>\<Gamma> \<i>"
  shows   "zorder (\<lambda>w. Klein_J w - 1) z = 2"
proof -
  have "zorder (\<lambda>u. Klein_J u - Klein_J z) z = weighting_factor z"
    using assms by (intro zorder_Klein_J) (auto simp: modular_group.rel_def)
  also have "Klein_J z = 1"
    using assms by (simp add: Klein_J_cong)
  also have "weighting_factor z = 2"
    using assms by (simp add: weighting_factor_ii')
  finally show ?thesis
    by simp
qed

subsection \<open>The set of modular forms as a $\mathbb{C}$-vector space\<close>

definition MForms_basis :: "nat \<Rightarrow> nat \<Rightarrow> mero_uhp" where
  "MForms_basis k r = \<G> (k - 12 * r) * \<Delta> ^ r"

definition MForms_basis_indices :: "nat \<Rightarrow> nat set" where
  "MForms_basis_indices k = {r. 12*r \<le> k \<and> k-12*r \<noteq> 2}"

lemma finite_MForms_basis_indices [intro]: "finite (MForms_basis_indices k)"
proof (rule finite_subset)
  show "MForms_basis_indices k \<subseteq> {..k div 12}"
    unfolding MForms_basis_indices_def by auto
qed auto

end