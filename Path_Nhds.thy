theory Path_Nhds
  imports "HOL-Complex_Analysis.Complex_Analysis" Library_Extras More_Topology
begin

lemma contour_integral_comp_holoW:
  assumes "open s" "f holomorphic_on s" "valid_path \<gamma>" "path_image \<gamma> \<subseteq> s"
  shows "contour_integral (f \<circ> \<gamma>) g
         = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
proof -
  obtain spikes where "finite spikes" and \<gamma>_diff: "\<gamma> C1_differentiable_on {0..1} - spikes"
    using \<open>valid_path \<gamma>\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto  
  show "contour_integral (f \<circ> \<gamma>) g 
      = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
    unfolding contour_integral_integral
  proof (rule integral_spike[rule_format,OF negligible_finite[OF \<open>finite spikes\<close>]])
    fix t::real assume t:"t \<in> {0..1} - spikes"
    then have "\<gamma> differentiable at t" 
      using \<gamma>_diff unfolding C1_differentiable_on_eq by auto
    moreover have "f field_differentiable at (\<gamma> t)" 
    proof -
      have "\<gamma> t \<in> s" using t assms unfolding path_image_def by auto 
      thus ?thesis 
        using \<open>open s\<close> \<open>f holomorphic_on s\<close>  holomorphic_on_imp_differentiable_at by blast
    qed
    ultimately show "deriv f (\<gamma> t) * g (f (\<gamma> t)) * vector_derivative \<gamma> (at t) =
         g ((f \<circ> \<gamma>) t) * vector_derivative (f \<circ> \<gamma>) (at t)"
      apply (subst vector_derivative_chain_at_general)
      by (simp_all add:field_simps)
  qed
qed

lemma valid_path_compose_analytic:
  assumes "valid_path g" and holo:"f analytic_on S" and "path_image g \<subseteq> S"
  shows "valid_path (f \<circ> g)"
proof (rule valid_path_compose[OF \<open>valid_path g\<close>])
  fix x assume "x \<in> path_image g"
  then show "f field_differentiable at x"
    using analytic_on_imp_differentiable_at analytic_on_open assms holo by blast
next
  show "continuous_on (path_image g) (deriv f)"
    by (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic analytic_intros
              analytic_on_subset[OF holo] assms)
qed

lemma contour_integral_comp_analyticW:
  assumes "f analytic_on s" "valid_path \<gamma>" "path_image \<gamma> \<subseteq> s"
  shows "contour_integral (f \<circ> \<gamma>) g = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
proof -
  obtain spikes where "finite spikes" and \<gamma>_diff: "\<gamma> C1_differentiable_on {0..1} - spikes"
    using \<open>valid_path \<gamma>\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto  
  show "contour_integral (f \<circ> \<gamma>) g 
      = contour_integral \<gamma> (\<lambda>w. deriv f w * g (f w))"
    unfolding contour_integral_integral
  proof (rule integral_spike[rule_format,OF negligible_finite[OF \<open>finite spikes\<close>]])
    fix t::real assume t:"t \<in> {0..1} - spikes"
    then have "\<gamma> differentiable at t" 
      using \<gamma>_diff unfolding C1_differentiable_on_eq by auto
    moreover have "f field_differentiable at (\<gamma> t)" 
    proof -
      have "\<gamma> t \<in> s" using t assms unfolding path_image_def by auto 
      thus ?thesis 
        using \<open>f analytic_on s\<close>  analytic_on_imp_differentiable_at by blast
    qed
    ultimately show "deriv f (\<gamma> t) * g (f (\<gamma> t)) * vector_derivative \<gamma> (at t) =
         g ((f \<circ> \<gamma>) t) * vector_derivative (f \<circ> \<gamma>) (at t)"
      apply (subst vector_derivative_chain_at_general)
      by (simp_all add:field_simps)
  qed
qed


lemma eventually_uniformly_on_iff:
  "eventually P (uniformly_on A f) \<longleftrightarrow> (\<exists>e>0. \<forall>g. (\<forall>y\<in>A. dist (g y) (f y) < e) \<longrightarrow> P g)"
  (is "?lhs = ?rhs")
proof -
  have "eventually P (uniformly_on A f) \<longleftrightarrow>
          (\<exists>X\<subseteq>{0<..}. finite X \<and> eventually P (INF b\<in>X. principal {fa. \<forall>x\<in>A. dist (fa x) (f x) < b}))"
    unfolding uniformly_on_def by (rule eventually_INF)
  also have "\<dots> \<longleftrightarrow> (\<exists>X\<subseteq>{(0::real)<..}. finite X \<and> (\<exists>Q. (\<forall>e\<in>X. \<forall>g. (\<forall>y\<in>A. dist (g y) (f y) < e) \<longrightarrow> Q e g) \<and>
               (\<forall>y. (\<forall>x\<in>X. Q x y) \<longrightarrow> P y)))"
  proof (intro ex_cong1 conj_cong refl, goal_cases)
    case (1 X)
    have "eventually P (INF b\<in>X. principal {fa. \<forall>x\<in>A. dist (fa x) (f x) < b}) \<longleftrightarrow>
          (\<exists>Q. (\<forall>e\<in>X. \<forall>g. (\<forall>y\<in>A. dist (g y) (f y) < e) \<longrightarrow> Q e g) \<and>
               (\<forall>y. (\<forall>x\<in>X. Q x y) \<longrightarrow> P y))"
      using 1 by (subst eventually_INF_finite) (simp_all add: eventually_principal)
    thus ?case .
  qed
  finally have eq: "eventually P (uniformly_on A f) =
                      (\<exists>X\<subseteq>{0<..}. finite X \<and>
                         (\<exists>Q. (\<forall>e\<in>X. \<forall>g. (\<forall>y\<in>A. dist (g y) (f y) < e) \<longrightarrow> Q e g) \<and>
                         (\<forall>y. (\<forall>x\<in>X. Q x y) \<longrightarrow> P y)))" .

  show ?thesis
  proof
    assume ?rhs
    then obtain e where e: "e > 0" "\<And>g. (\<forall>y\<in>A. dist (g y) (f y) < e) \<Longrightarrow> P g"
      by blast
    let ?Q = "\<lambda>e g. \<forall>y\<in>A. dist (g y) (f y) < e"
    show "eventually P (uniformly_on A f)"
      by (subst eq, rule exI[of _ "{e}"], safe intro!: e exI[of _ ?Q]) (use e in auto)
  next
    assume ?lhs
    then obtain X Q where XQ: "X \<subseteq> {0<..}" "finite X"
      "\<And>e g. e \<in> X \<Longrightarrow> (\<forall>y\<in>A. dist (g y) (f y) < e) \<Longrightarrow> Q e g"
      "\<And>g. (\<And>x. x \<in> X \<Longrightarrow> Q x g) \<Longrightarrow> P g"
      by (subst (asm) eq) metis

    show ?rhs
    proof (cases "X = {}")
      case True
      thus ?thesis using XQ
        by (auto intro!: exI[of _ 1])
    next
      case False
      define e where "e = Min X"
      have e: "e > 0" "e \<in> X"
        using False XQ(1,2) by (auto simp: e_def)

      show ?rhs
      proof (rule exI[of _ e], safe)
        show "e > 0"
          by fact
      next
        fix g assume g: "\<forall>y\<in>A. dist (g y) (f y) < e"
        show "P g"
        proof (intro XQ ballI)
          fix e' y assume e': "e' \<in> X" and y: "y \<in> A"
          have "dist (g y) (f y) < e"
            using g y by blast
          also have "e \<le> e'"
            using e' False \<open>finite X\<close> by (simp add: e_def)
          finally show "dist (g y) (f y) < e'" .
        qed auto
      qed
    qed
  qed
qed

lemma eventually_uniformly_onI [intro?]:
  "e > 0 \<Longrightarrow> (\<And>g. (\<And>y. y \<in> A \<Longrightarrow> dist (g y) (f y) < e) \<Longrightarrow> P g) \<Longrightarrow>
     eventually P (uniformly_on A f)"
  unfolding eventually_uniformly_on_iff by blast


abbreviation same_ends
  where "same_ends p q \<equiv> pathstart p = pathstart q \<and> pathfinish p = pathfinish q"

definition path_nhds :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a) filter" where
  "path_nhds \<gamma> = inf (uniformly_on {0..1} \<gamma>) (principal {p. path p \<and> same_ends p \<gamma>})"

lemma eventually_path_nhds_iff:
  "eventually P (path_nhds \<gamma>) \<longleftrightarrow>
     (\<exists>e>0. \<forall>p. path p \<longrightarrow> same_ends p \<gamma> \<longrightarrow> (\<forall>y\<in>{0..1}. dist (p y) (\<gamma> y) < e) \<longrightarrow> P p)"
  unfolding path_nhds_def eventually_uniformly_on_iff eventually_inf_principal
  by blast

lemma frequently_path_nhds_iff:
  "frequently P (path_nhds \<gamma>) \<longleftrightarrow>
     (\<forall>e>0. \<exists>p. path p \<and> same_ends p \<gamma> \<and> (\<forall>y\<in>{0..1}. dist (p y) (\<gamma> y) < e) \<and> P p)"
  unfolding frequently_def eventually_path_nhds_iff by blast

lemma eventually_path_nhdsI [intro?]:
  "e > 0 \<Longrightarrow> (\<And>p. path p \<Longrightarrow> same_ends p \<gamma> \<Longrightarrow> (\<And>y. y \<in> {0..1} \<Longrightarrow> dist (p y) (\<gamma> y) < e) \<Longrightarrow> P p)
     \<Longrightarrow> eventually P (path_nhds \<gamma>)"
  unfolding eventually_path_nhds_iff by blast


definition valid_path_nhds :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a) filter" where
  "valid_path_nhds \<gamma> = inf (uniformly_on {0..1} \<gamma>) (principal {p. valid_path p \<and> same_ends p \<gamma>})"

lemma eventually_valid_path_nhds_iff:
  "eventually P (valid_path_nhds \<gamma>) \<longleftrightarrow>
     (\<exists>e>0. \<forall>p. valid_path p \<longrightarrow> same_ends p \<gamma> \<longrightarrow> (\<forall>y\<in>{0..1}. dist (p y) (\<gamma> y) < e) \<longrightarrow> P p)"
  unfolding valid_path_nhds_def eventually_uniformly_on_iff eventually_inf_principal
  by blast

lemma frequently_valid_path_nhds_iff:
  "frequently P (valid_path_nhds \<gamma>) \<longleftrightarrow>
     (\<forall>e>0. \<exists>p. valid_path p \<and> same_ends p \<gamma> \<and> (\<forall>y\<in>{0..1}. dist (p y) (\<gamma> y) < e) \<and> P p)"
  unfolding frequently_def eventually_valid_path_nhds_iff by blast

lemma eventually_valid_path_nhdsI [intro?]:
  "e > 0 \<Longrightarrow> (\<And>p. valid_path p \<Longrightarrow> same_ends p \<gamma> \<Longrightarrow> (\<And>y. y \<in> {0..1} \<Longrightarrow> dist (p y) (\<gamma> y) < e) \<Longrightarrow> P p)
     \<Longrightarrow> eventually P (valid_path_nhds \<gamma>)"
  unfolding eventually_valid_path_nhds_iff by blast

lemma eventually_path_path_nhds: "eventually (\<lambda>p. path p) (path_nhds \<gamma>)"
  by (rule eventually_path_nhdsI[OF zero_less_one])

lemma eventually_valid_path_valid_path_nhds: "eventually (\<lambda>p. valid_path p) (valid_path_nhds \<gamma>)"
  by (rule eventually_valid_path_nhdsI [OF zero_less_one])

lemma path_nhds_le_valid_path_nhds: "valid_path_nhds \<gamma> \<le> path_nhds \<gamma>"
  by (rule filter_leI)
     (auto simp: eventually_path_nhds_iff eventually_valid_path_nhds_iff valid_path_imp_path)

lemma path_nhds_neq_bot [simp]: "path \<gamma> \<Longrightarrow> path_nhds \<gamma> \<noteq> bot"
  by (auto simp: trivial_limit_def eventually_path_nhds_iff intro!: exI[of _ \<gamma>])

lemma valid_path_nhds_neq_bot [simp]: "valid_path \<gamma> \<Longrightarrow> valid_path_nhds \<gamma> \<noteq> bot"
  by (auto simp: trivial_limit_def eventually_valid_path_nhds_iff intro!: exI[of _ \<gamma>])

lemma valid_path_nhds_eq_bot' [simp]:
  assumes "path (\<gamma> :: real \<Rightarrow> 'a :: euclidean_space)"
  shows   "valid_path_nhds \<gamma> \<noteq> bot"
proof -
  {
    fix e :: real assume e: "e > 0"
    obtain p where p: "polynomial_function p" "pathstart p = pathstart \<gamma>"
      "pathfinish p = pathfinish \<gamma>" "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (p t - \<gamma> t) < e"
      using path_approx_polynomial_function[OF assms(1) e] by blast
    hence "\<exists>p. valid_path p \<and> same_ends p \<gamma> \<and> (\<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e)"
      using valid_path_polynomial_function by (intro exI[of _ p]) (auto simp: dist_norm)
  }
  thus ?thesis
    unfolding trivial_limit_def eventually_valid_path_nhds_iff by blast
qed  

lemma eventually_dist_less_path_nhds:
  assumes "e > 0"
  shows   "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e) (path_nhds \<gamma>)"
  using assms by (intro eventually_path_nhdsI[of e]) auto

lemma eventually_dist_less_valid_path_nhds:
  assumes "e > 0"
  shows   "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e) (valid_path_nhds \<gamma>)"
  using assms by (intro eventually_valid_path_nhdsI[of e]) auto

lemma eventually_same_ends_path_nhds:
        "eventually (\<lambda>p. same_ends p \<gamma>) (path_nhds \<gamma>)"
  and eventually_same_ends_valid_path_nhds: 
        "eventually (\<lambda>p. same_ends p \<gamma>) (valid_path_nhds \<gamma>)"
  by (rule eventually_path_nhdsI[of 1] eventually_valid_path_nhdsI[of 1]; simp)+


lemma eventually_winding_number_eq_path_nhds:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
  shows   "eventually (\<lambda>p. winding_number p z = winding_number \<gamma> z) (path_nhds \<gamma>)"
proof -
  define e where "e = setdist {z} (path_image \<gamma>)"
  show ?thesis
  proof (rule eventually_path_nhdsI; safe?)
    show "e > 0"
      using assms unfolding e_def
      by (subst setdist_gt_0_compact_closed) (auto intro!: closed_path_image)
  next
    fix p assume p: "path p" "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>" 
                    "\<And>y. y \<in> {0..1} \<Longrightarrow> dist (p y) (\<gamma> y) < e"
    show "winding_number p z = winding_number \<gamma> z"
    proof (rule winding_number_nearby_paths_eq)
      fix t :: real assume t: "t \<in> {0..1}"
      have "norm (p t - \<gamma> t) < e"
        using p(4)[OF t] by (simp add: dist_norm)
      also have "\<dots> \<le> dist z (\<gamma> t)"
        unfolding e_def by (rule setdist_le_dist) (use t in \<open>auto simp: path_image_def\<close>)
      finally show "cmod (p t - \<gamma> t) < cmod (\<gamma> t - z)"
        by (simp add: dist_norm norm_minus_commute)
    qed (use p assms in auto)
  qed
qed

lemma eventually_path_nhds_avoid:
  assumes "path \<gamma>" "closed A" "A \<inter> path_image \<gamma> = {}"
  shows   "eventually (\<lambda>p. path_image p \<inter> A = {}) (path_nhds \<gamma>)"
proof (cases "A = {}")
  case False
  define e where "e = setdist (path_image \<gamma>) A"
  have "e > 0"
    using assms False unfolding e_def
    by (subst setdist_gt_0_compact_closed compact_path_image) auto
  hence "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e) (path_nhds \<gamma>)"
    by (rule eventually_dist_less_path_nhds)
  thus ?thesis
  proof eventually_elim
    case (elim p)
    show "path_image p \<inter> A = {}"
    proof (intro equalityI subsetI)
      fix z assume z: "z \<in> path_image p \<inter> A"
      then obtain t where t: "t \<in> {0..1}" "z = p t"
        by (auto simp: path_image_def)
      with elim have "dist (p t) (\<gamma> t) < e"
        by blast
      also have "e \<le> dist (\<gamma> t) z"
        unfolding e_def by (rule setdist_le_dist) (use t z in \<open>auto simp: path_image_def\<close>)
      finally show "z \<in> {}"
        using t by (simp add: dist_commute)
    qed auto
  qed
qed auto

lemma eventually_valid_path_nhds_avoid:
  assumes "path \<gamma>" "closed A" "A \<inter> path_image \<gamma> = {}"
  shows   "eventually (\<lambda>p. path_image p \<inter> A = {}) (valid_path_nhds \<gamma>)"
  using eventually_path_nhds_avoid[OF assms]
        le_filter_def path_nhds_le_valid_path_nhds by blast

lemma winding_number_unique':
  assumes "frequently (\<lambda>p. winding_number p z = n) (valid_path_nhds \<gamma>)"
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
  shows   "winding_number \<gamma> z = n"
proof (rule winding_number_unique)
  fix e :: real
  assume e: "e > 0"
  have "frequently (\<lambda>p. path_image p \<inter> {z} = {} \<and> winding_number p z = n) (valid_path_nhds \<gamma>)"
    using assms by (intro frequently_eventually_conj eventually_valid_path_nhds_avoid) auto
  then obtain p
    where p: "valid_path p" "z \<notin> path_image p" "same_ends p \<gamma>" "winding_number p z = n"
             "(\<forall>y\<in>{0..1}. dist (p y) (\<gamma> y) < e)"
    using e unfolding frequently_valid_path_nhds_iff by fast
  have "contour_integral p (\<lambda>w. 1 / (w - z)) = 2 * complex_of_real pi * \<i> * winding_number p z"
    using p by (subst winding_number_valid_path) auto
  with p show "\<exists>p. winding_number_prop \<gamma> z e p n"
    by (intro exI[of _ p]) (auto simp: winding_number_prop_def dist_norm norm_minus_commute)
qed (use assms in auto)

lemma eventually_path_image_subset_path_nhds:
  assumes "path \<gamma>" "open A" "path_image \<gamma> \<subseteq> A"
  shows   "eventually (\<lambda>p. path_image p \<subseteq> A) (path_nhds \<gamma>)"
proof -
  have "compact (path_image \<gamma>)"
    by (intro compact_path_image assms)
  then obtain e where e: "e > 0" "(\<Union>x\<in>path_image \<gamma>. cball x e) \<subseteq> A"
    using compact_subset_open_imp_cball_epsilon_subset[of "path_image \<gamma>" A] assms \<open>open A\<close>
    by blast
  have "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e) (path_nhds \<gamma>)"
    by (intro eventually_dist_less_path_nhds assms e)
  thus ?thesis
  proof eventually_elim
    case (elim p)
    show "path_image p \<subseteq> A"
      unfolding path_image_def
    proof safe
      fix t :: real assume t: "t \<in> {0..1}"
      have "dist (p t) (\<gamma> t) < e"
        using elim t by blast
      hence "p t \<in> (\<Union>x\<in>path_image \<gamma>. cball x e)"
        unfolding path_image_def using t by (auto simp: dist_commute intro!: less_imp_le)
      also have "\<dots> \<subseteq> A"
        using e by blast
      finally show "p t \<in> A" .
    qed
  qed
qed

lemma eventually_path_image_subset_valid_path_nhds:
  assumes "path \<gamma>" "open A" "path_image \<gamma> \<subseteq> A"
  shows   "eventually (\<lambda>p. path_image p \<subseteq> A) (valid_path_nhds \<gamma>)"
  using eventually_path_image_subset_path_nhds[OF assms]
        le_filter_def path_nhds_le_valid_path_nhds by blast

lemma path_nhds_compose_lipschitz:
  assumes "C-lipschitz_on A f" "path \<gamma>" "path_image \<gamma> \<subseteq> A" "open A"
  shows   "path_nhds (f \<circ> \<gamma>) \<ge> filtermap ((\<circ>) f) (path_nhds \<gamma>)"
proof (rule filter_leI)
  fix P assume *: "eventually P (path_nhds (f \<circ> \<gamma>))"
  then obtain e where e: "e > 0"
     "\<And>p. path p \<Longrightarrow> same_ends p (f \<circ> \<gamma>) \<Longrightarrow> (\<forall>y\<in>{0..1}. dist (p y) ((f \<circ> \<gamma>) y) < e) \<Longrightarrow> P p"
    unfolding eventually_path_nhds_iff by blast
  define C' where "C' = max 1 C"

  have "eventually (\<lambda>p. path_image p \<subseteq> A) (path_nhds \<gamma>)"
    by (intro eventually_path_image_subset_path_nhds assms)
  moreover have "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e / C') (path_nhds \<gamma>)"
    by (intro eventually_dist_less_path_nhds mult_pos_pos e divide_pos_pos) (auto simp: C'_def)
  ultimately show "eventually P (filtermap ((\<circ>) f) (path_nhds \<gamma>))"
    using eventually_same_ends_path_nhds eventually_path_path_nhds
    unfolding eventually_filtermap
  proof eventually_elim
    case (elim p)
    show "P (f \<circ> p)"
    proof (rule e, safe)
      have "continuous_on (path_image p) f"
        by (rule continuous_on_subset [OF lipschitz_on_continuous_on[OF assms(1)]])
           (use elim in auto)
      thus "path (f \<circ> p)"
        by (intro path_continuous_image elim)
    next
      fix t :: real assume t: "t \<in> {0..1}"
      have "dist ((f \<circ> p) t) ((f \<circ> \<gamma>) t) = dist (f (p t)) (f (\<gamma> t))"
        by simp
      also have "\<dots> \<le> C * dist (p t) (\<gamma> t)"
        by (rule lipschitz_onD[OF assms(1)]) (use t assms elim in \<open>auto simp: path_image_def\<close>)
      also have "\<dots> \<le> C' * dist (p t) (\<gamma> t)"
        by (intro mult_right_mono) (auto simp: C'_def)
      also have "\<dots> < C' * (e / C')"
        by (intro mult_strict_left_mono) (use elim t in \<open>auto simp: C'_def\<close>)
      also have "\<dots> = e"
        by (simp add: C'_def)
      finally show "dist ((f \<circ> p) t) ((f \<circ> \<gamma>) t) < e" .      
    qed (use elim in \<open>auto simp: pathfinish_def pathstart_def\<close>)
  qed
qed

lemma valid_path_nhds_compose_analytic_lipschitz:
  assumes "f analytic_on A" "C-lipschitz_on A f" "path \<gamma>" "path_image \<gamma> \<subseteq> A" "open A"
  shows   "valid_path_nhds (f \<circ> \<gamma>) \<ge> filtermap ((\<circ>) f) (valid_path_nhds \<gamma>)"
proof (rule filter_leI)
  fix P assume *: "eventually P (valid_path_nhds (f \<circ> \<gamma>))"
  then obtain e where e: "e > 0"
     "\<And>p. valid_path p \<Longrightarrow> same_ends p (f \<circ> \<gamma>) \<Longrightarrow> (\<forall>y\<in>{0..1}. dist (p y) ((f \<circ> \<gamma>) y) < e) \<Longrightarrow> P p"
    unfolding eventually_valid_path_nhds_iff by blast
  define C' where "C' = max 1 C"

  have "eventually (\<lambda>p. path_image p \<subseteq> A) (valid_path_nhds \<gamma>)"
    by (intro eventually_path_image_subset_valid_path_nhds assms)
  moreover have "eventually (\<lambda>p. \<forall>t\<in>{0..1}. dist (p t) (\<gamma> t) < e / C') (valid_path_nhds \<gamma>)"
    by (intro eventually_dist_less_valid_path_nhds mult_pos_pos e divide_pos_pos) (auto simp: C'_def)
  ultimately show "eventually P (filtermap ((\<circ>) f) (valid_path_nhds \<gamma>))"
    using eventually_same_ends_valid_path_nhds eventually_valid_path_valid_path_nhds
    unfolding eventually_filtermap
  proof eventually_elim
    case (elim p)
    show "P (f \<circ> p)"
    proof (rule e, safe)
      show "valid_path (f \<circ> p)"
        by (intro valid_path_compose_analytic [OF _ assms(1)] elim)
    next
      fix t :: real assume t: "t \<in> {0..1}"
      have "dist ((f \<circ> p) t) ((f \<circ> \<gamma>) t) = dist (f (p t)) (f (\<gamma> t))"
        by simp
      also have "\<dots> \<le> C * dist (p t) (\<gamma> t)"
        by (rule lipschitz_onD[OF assms(2)]) (use t assms elim in \<open>auto simp: path_image_def\<close>)
      also have "\<dots> \<le> C' * dist (p t) (\<gamma> t)"
        by (intro mult_right_mono) (auto simp: C'_def)
      also have "\<dots> < C' * (e / C')"
        by (intro mult_strict_left_mono) (use elim t in \<open>auto simp: C'_def\<close>)
      also have "\<dots> = e"
        by (simp add: C'_def)
      finally show "dist ((f \<circ> p) t) ((f \<circ> \<gamma>) t) < e" .      
    qed (use elim in \<open>auto simp: pathfinish_def pathstart_def\<close>)
  qed
qed

lemma le_filterD_frequently [trans]: "F \<le> G \<Longrightarrow> frequently P F \<Longrightarrow> frequently P G"
  unfolding le_filter_def frequently_def by blast

lemma le_filterD_frequently' [trans]: "frequently P F \<Longrightarrow> F \<le> G \<Longrightarrow> frequently P G"
  unfolding le_filter_def frequently_def by blast

lemma frequently_filtermap: "frequently P (filtermap f F) \<longleftrightarrow> frequently (\<lambda>x. P (f x)) F"
  by (simp add: frequently_def eventually_filtermap)

lemma winding_number_comp':
  assumes f: "f holomorphic_on A" "C-lipschitz_on A f" "inj_on f A" "open A"
  assumes \<gamma>: "path \<gamma>" "path_image \<gamma> \<subseteq> A"
  assumes z: "z \<in> A" "z \<notin> path_image \<gamma>"
  assumes int: "\<exists>\<^sub>F p in valid_path_nhds \<gamma>.
                  contour_integral p (\<lambda>w. deriv f w / (f w - f z)) = 2 * pi * \<i> * c"
  shows   "winding_number (f \<circ> \<gamma>) (f z) = c"
proof -
  have cont: "continuous_on A f"
    using f(1) by (intro holomorphic_on_imp_continuous_on)

  have *: "f z \<notin> f ` X" if "z \<notin> X" "X \<subseteq> A" for X
  proof
    assume "f z \<in> f ` X"
    then obtain z' where z': "z' \<in> X" "f z' = f z"
      by force
    have "z' = z"
      using inj_onD[OF f(3) z'(2)] z'(1) z \<gamma>(2) interior_subset that by auto
    with z'(1) and that show False
      by simp
  qed

  show ?thesis
  proof (rule winding_number_unique')
    show "path (f \<circ> \<gamma>)"
      using assms
      by (intro path_continuous_image \<gamma> continuous_on_subset[OF cont])
  next
    show "f z \<notin> path_image (f \<circ> \<gamma>)"
      unfolding path_image_compose using assms interior_subset by (intro *) auto
  next
    have ev: "\<forall>\<^sub>F p in valid_path_nhds \<gamma>. path_image p \<inter> {z} = {} \<and> path_image p \<subseteq> A \<and> valid_path p"
      by (intro eventually_conj eventually_valid_path_nhds_avoid
                eventually_path_image_subset_valid_path_nhds eventually_valid_path_valid_path_nhds)
         (use assms in auto)
    have freq: "\<exists>\<^sub>Fp in valid_path_nhds \<gamma>. winding_number (f \<circ> p) (f z) = c"
      using frequently_eventually_conj[OF int ev]
    proof (rule frequently_elim1, goal_cases)
      case (1 p)
      have "f z \<notin> path_image (f \<circ> p)"
        unfolding path_image_compose using * 1 by blast
      hence "winding_number (f \<circ> p) (f z) =
               contour_integral (f \<circ> p) (\<lambda>w. 1 / (w - f z)) / (2 * pi * \<i>)" using 1
        by (subst winding_number_valid_path)
           (auto simp: path_image_compose intro!: valid_path_compose_holomorphic
                       holomorphic_on_subset[OF f(1)] \<open>open A\<close>)
      also have "\<dots> = c"
      proof (subst contour_integral_comp_holoW)
        show "f holomorphic_on A" "open A"
          by fact+
        show "valid_path p" "path_image p \<subseteq> A"
          using 1 by auto
      qed (use 1 \<open>open A\<close> in auto)
      finally show ?case .
    qed

    show "\<exists>\<^sub>F p in valid_path_nhds (f \<circ> \<gamma>). winding_number p (f z) = c"
      using valid_path_nhds_compose_analytic_lipschitz
    proof (rule le_filterD_frequently)
      show "f analytic_on A" "C-lipschitz_on A f"
        using assms by (simp_all add: analytic_on_open)
    qed (use assms freq in \<open>auto simp: frequently_filtermap\<close>)
  qed
qed

text \<open>
  A set is defined to be path-connected if any two points in it are connected by a continuous
  path. The following shows that for open sets, one can also take the paths to be piecewise C1.
\<close>
lemma path_connected_open_has_valid_path:
  fixes A :: "'a :: euclidean_space set"
  assumes "path_connected A" "open A" "x \<in> A" "y \<in> A"
  obtains p where "valid_path p" "path_image p \<subseteq> A" "pathstart p = x" "pathfinish p = y"
proof -
  from assms obtain p where p: "path p" "path_image p \<subseteq> A" "pathstart p = x" "pathfinish p = y"
    by (force simp: path_connected_def)
  have "eventually (\<lambda>p'. valid_path p' \<and> path_image p' \<subseteq> A \<and> same_ends p p') (valid_path_nhds p)"
    using eventually_valid_path_valid_path_nhds eventually_same_ends_valid_path_nhds
          eventually_path_image_subset_valid_path_nhds[OF p(1) assms(2) p(2)]
    by eventually_elim auto
  moreover have "valid_path_nhds p \<noteq> bot"
    using p by auto
  ultimately show ?thesis using that
    using eventually_happens' p(3) p(4) by force
qed

text \<open>
  A path \<open>p\<close> always has arbitrarily close smooth paths in its vicinity.
  (i.e. it can be approximated by smooth paths to arbitrary precision)
\<close>
lemma frequently_valid_path:
  assumes "path (p :: real \<Rightarrow> 'a :: euclidean_space)"
  shows   "frequently (\<lambda>p'. valid_path p') (path_nhds p)"
proof -
  have "valid_path_nhds p \<noteq> bot"
    using assms by simp
  thus ?thesis
    by (meson eventually_frequently eventually_valid_path_valid_path_nhds 
              frequently_def le_filter_def path_nhds_le_valid_path_nhds)
qed

text \<open>
  If we have a path \<open>p\<close> and transform it with a function that is continuous
  in some open neighbourhood of \<open>p\<close>, then all the paths that are close to \<open>p\<close>
  are also transformed to paths close to the image of \<open>p\<close>.
\<close>
(* TODO: same for valid_path_nhds? (should be easy) *)
lemma continuous_path_image:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "path p" "continuous_on A f" "open A" "path_image p \<subseteq> A"
  shows "filterlim (\<lambda>p. f \<circ> p) (path_nhds (f \<circ> p)) (path_nhds p)"
  unfolding filterlim_def le_filter_def eventually_filtermap
proof safe
  fix P assume P: "eventually P (path_nhds (f \<circ> p))"
  then obtain \<epsilon> :: real where \<epsilon>: "\<epsilon> > 0"
    "\<And>p'. path p' \<Longrightarrow> same_ends p' (f \<circ> p) \<Longrightarrow> 
            (\<And>t. t \<in> {0..1} \<Longrightarrow> dist (p' t) ((f \<circ> p) t) < \<epsilon>) \<Longrightarrow> P p'"
    unfolding eventually_path_nhds_iff by blast

  obtain r where r: "r > 0" "(\<Union>x\<in>path_image p. cball x r) \<subseteq> A"
    using compact_subset_open_imp_cball_epsilon_subset[of "path_image p" A] assms
    by auto
  define B where "B = (\<Union>x\<in>path_image p. cball x r)"
  have "B \<subseteq> A"
    using r unfolding B_def by blast
  have "compact B"
    unfolding B_def by (intro compact_minkowski_sum_cball compact_path_image assms)
  have "uniformly_continuous_on B f"
    by (intro compact_uniformly_continuous continuous_on_subset[OF assms(2)]) fact+
  then obtain \<delta>' where \<delta>': "\<delta>' > 0" "\<And>x y. x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> dist x y < \<delta>' \<Longrightarrow> dist (f x) (f y) < \<epsilon>"
    using \<open>\<epsilon> > 0\<close> unfolding uniformly_continuous_on_def by fast
  define \<delta> where "\<delta> = min r \<delta>'"
  have \<delta>: "\<delta> > 0" "\<delta> \<le> r" "\<delta> \<le> \<delta>'"
    using \<open>\<delta>' > 0\<close> \<open>r > 0\<close> unfolding \<delta>_def by auto

  show "\<forall>\<^sub>F x in path_nhds p. P (f \<circ> x)"
  proof
    show "\<delta> > 0"
      by fact
  next
    fix p'
    assume p': "path p'" "same_ends p' p" 
      "\<And>t. t \<in> {0..1} \<Longrightarrow> dist (p' t) (p t) < \<delta>"
    have "path_image p \<subseteq> B"
      unfolding B_def using \<open>r > 0\<close> by fastforce
    have "path_image p' \<subseteq> B"
      using p'(3) \<delta> unfolding B_def
      by (force simp: path_image_def dist_commute)
    show "P (f \<circ> p')"
    proof (rule \<epsilon>(2))
      show "path (f \<circ> p')"
        using assms \<open>path_image p' \<subseteq> B\<close> \<open>B \<subseteq> A\<close>
        by (intro path_continuous_image p' continuous_on_subset[OF assms(2)]) auto
      show "same_ends (f \<circ> p') (f \<circ> p)"
        using p' by (simp add: pathstart_compose pathfinish_compose)
      show "dist ((f \<circ> p') t) ((f \<circ> p) t) < \<epsilon>" if "t \<in> {0..1}" for t
      proof -
        have "dist ((f \<circ> p') t) ((f \<circ> p) t) = dist (f (p' t)) (f (p t))"
          by simp
        moreover have "dist (p' t) (p t) < \<delta>'"
          using \<delta>_def min_less_iff_conj p'(3) that by blast
        ultimately show "dist ((f \<circ> p') t) ((f \<circ> p) t) < \<epsilon>"
          unfolding o_def using p' \<open>path_image p \<subseteq> B\<close> \<open>path_image p' \<subseteq> B\<close> \<delta> that
          by (intro \<delta>') (auto simp: path_image_def)
      qed
    qed
  qed
qed

end