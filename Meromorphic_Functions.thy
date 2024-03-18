theory Meromorphic_Functions imports 
  Meromorphic1
  More_Analysis
begin

lemma
  shows is_pole_Polygamma: "is_pole (Polygamma n) (-of_nat m :: complex)"
  and   zorder_Polygamma:  "zorder (Polygamma n) (-of_nat m) = -int (Suc n)"
  and   residue_Polygamma: "residue (Polygamma n) (-of_nat m) = (if n = 0 then -1 else 0)"
proof -
  define g1 :: "complex \<Rightarrow> complex" where
    "g1 = (\<lambda>z. Polygamma n (z + of_nat (Suc m)) +
              (-1) ^ Suc n * fact n * (\<Sum>k<m. 1 / (z + of_nat k) ^ Suc n))"
  define g :: "complex \<Rightarrow> complex" where
    "g = (\<lambda>z. g1 z + (-1) ^ Suc n * fact n / (z + of_nat m) ^ Suc n)"
  define F where "F = fps_to_fls (fps_expansion g1 (-of_nat m)) + fls_const ((-1) ^ Suc n * fact n) / fls_X ^ Suc n"
  have F_altdef: "F = fps_to_fls (fps_expansion g1 (-of_nat m)) + fls_shift (n+1) (fls_const ((-1) ^ Suc n * fact n))"
    by (simp add: F_def del: power_Suc)

  have "\<not>(-of_nat m) islimpt (\<int>\<^sub>\<le>\<^sub>0 :: complex set)"
    by (intro discrete_imp_not_islimpt[where e = 1])
       (auto elim!: nonpos_Ints_cases simp: dist_of_int)
  hence "eventually (\<lambda>z::complex. z \<notin> \<int>\<^sub>\<le>\<^sub>0) (at (-of_nat m))"
    by (auto simp: islimpt_conv_frequently_at frequently_def)
  hence ev: "eventually (\<lambda>z. Polygamma n z = g z) (at (-of_nat m))"
  proof eventually_elim
    case (elim z)
    hence *: "\<forall>k<Suc m. z \<noteq> - of_nat k"
      by auto
    thus ?case
      using Polygamma_plus_of_nat[of "Suc m" z n, OF *]
      by (auto simp: g_def g1_def algebra_simps)
  qed

  have "(\<lambda>w. g (-of_nat m + w)) has_laurent_expansion F"
    unfolding g_def F_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps analytic_at_imp_has_fps_expansion)
       (auto simp: g1_def intro!: laurent_expansion_intros analytic_intros)
  also have "?this \<longleftrightarrow> (\<lambda>w. Polygamma n (-of_nat m + w)) has_laurent_expansion F"
    using ev by (intro has_laurent_expansion_cong refl)
                (simp_all add: eq_commute at_to_0' eventually_filtermap)
  finally have *: "(\<lambda>w. Polygamma n (-of_nat m + w)) has_laurent_expansion F" .

  have subdegree: "fls_subdegree F = -int (Suc n)" unfolding F_def
    by (subst fls_subdegree_add_eq2) (simp_all add: fls_subdegree_fls_to_fps fls_divide_subdegree)
  have [simp]: "F \<noteq> 0"
    using subdegree by auto
  
  show "is_pole (Polygamma n) (-of_nat m :: complex)"
    using * by (rule has_laurent_expansion_imp_is_pole) (auto simp: subdegree)
  show "zorder (Polygamma n) (-of_nat m :: complex) = -int (Suc n)"
    by (subst has_laurent_expansion_zorder[OF *]) (auto simp: subdegree)
  show "residue (Polygamma n) (-of_nat m :: complex) = (if n = 0 then -1 else 0)"
    by (subst has_laurent_expansion_residue[OF *]) (auto simp: F_altdef)
qed

lemma analytic_on_poly [analytic_intros]: 
  "f analytic_on A \<Longrightarrow> (\<lambda>w. poly p (f w)) analytic_on A"
unfolding poly_altdef by (auto intro!: analytic_intros)

lemma [meromorphic_intros]:
  assumes [analytic_intros]: "f analytic_on A"
  shows meromorphic_on_exp: "(\<lambda>w. exp (f w)) meromorphic_on A"
    and meromorphic_on_ln: "f ` A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> (\<lambda>w. ln (f w)) meromorphic_on A"
    and meromorphic_on_ln_Gamma: "f ` A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> (\<lambda>w. ln_Gamma (f w)) meromorphic_on A"
    and meromorphic_on_csqrt: "f ` A \<inter> \<real>\<^sub>\<le>\<^sub>0 = {} \<Longrightarrow> (\<lambda>w. csqrt (f w)) meromorphic_on A"
    and meromorphic_on_sin: "(\<lambda>w. sin (f w)) meromorphic_on A"
    and meromorphic_on_cos: "(\<lambda>w. cos (f w)) meromorphic_on A"
    and meromorphic_on_sinh: "(\<lambda>w. sinh (f w)) meromorphic_on A"
    and meromorphic_on_cosh: "(\<lambda>w. cosh (f w)) meromorphic_on A"
    and meromorphic_on_poly: "(\<lambda>w. poly p (f w)) meromorphic_on A"
    and meromorphic_on_rGamma: "(\<lambda>w. rGamma (f w)) meromorphic_on A"
    by ((rule analytic_on_imp_meromorphic_on analytic_intros)+; force; fail)+


lemma [meromorphic_intros]:
  assumes [analytic_intros]: "f analytic_on A"
  shows   meromorphic_on_tan: "(\<lambda>w. tan (f w)) meromorphic_on A"
  and     meromorphic_on_cot: "(\<lambda>w. cot (f w)) meromorphic_on A"
  and     meromorphic_on_coth: "(\<lambda>w. tanh (f w)) meromorphic_on A"
  unfolding tan_def cot_def tanh_def
  by (auto intro!: meromorphic_intros analytic_intros)

lemma meromorphic_on_pochhammer [meromorphic_intros]:
  "f meromorphic_on A \<Longrightarrow> (\<lambda>w. pochhammer (f w) n) meromorphic_on A"
  unfolding pochhammer_prod by (intro meromorphic_intros)

lemma meromorphic_on_gbinomial [meromorphic_intros]:
  "f meromorphic_on A \<Longrightarrow> (\<lambda>w. f w gchoose n) meromorphic_on A"
  unfolding gbinomial_prod_rev by (intro meromorphic_intros) auto

lemma not_islimpt_subset_Ints:
  fixes z :: "'a :: real_normed_algebra_1"
  assumes "A \<subseteq> \<int>"
  shows   "\<not>z islimpt A"
proof -
  have "uniform_discrete (\<int> :: 'a set)"
    by (rule uniformI1[of 1]) (auto simp: Ints_def dist_of_int)
  hence "discrete (\<int> :: 'a set)"
    by (rule uniform_discrete_imp_discrete)
  hence "\<not>z islimpt (\<int> :: 'a set)"
    using closed_Ints closed_limpt discreteD isolated_in_islimpt_iff by blast
  thus ?thesis
    using assms islimpt_subset by blast
qed

lemma meromorphic_on_Gamma [meromorphic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>w. Gamma (f w)) meromorphic_on A"
proof (rule meromorphic_on_compose[of Gamma], rule meromorphic_onI_open)
  show "Gamma analytic_on UNIV - \<int>\<^sub>\<le>\<^sub>0"
    by (simp add: Diff_Int_distrib2 analytic_Gamma)
  show "not_essential Gamma z" if "z \<in> \<int>\<^sub>\<le>\<^sub>0" for z
    using that by (auto intro!: is_pole_imp_not_essential is_pole_Gamma elim!: nonpos_Ints_cases')
  show "\<not> z islimpt \<int>\<^sub>\<le>\<^sub>0 \<inter> UNIV" for z :: complex
    by (rule not_islimpt_subset_Ints) auto
qed (use assms in auto)

lemma meromorphic_on_Polygamma [meromorphic_intros]:
  assumes "f analytic_on A"
  shows   "(\<lambda>w. Polygamma n (f w)) meromorphic_on A"
proof (rule meromorphic_on_compose[of "Polygamma n"], rule meromorphic_onI_open)
  show "Polygamma n analytic_on UNIV - \<int>\<^sub>\<le>\<^sub>0"
    by (simp add: Diff_Int_distrib2 analytic_on_Polygamma)
  show "not_essential (Polygamma n) z" if "z \<in> \<int>\<^sub>\<le>\<^sub>0" for z
    using that by (auto intro!: is_pole_imp_not_essential is_pole_Polygamma elim!: nonpos_Ints_cases')
  show "\<not> z islimpt \<int>\<^sub>\<le>\<^sub>0 \<inter> UNIV" for z :: complex
    by (rule not_islimpt_subset_Ints) auto
qed (use assms in auto)

end