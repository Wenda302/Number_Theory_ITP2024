theory Elliptic_Functions
  imports "Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized"
          Modular_Group "HOL-Eisbach.Eisbach"
          Argument_Principle_Sparse
begin

(*TODO: update the one in the library?*)
lemma winding_number_offset: 
  assumes "NO_MATCH 0 z"
  shows "winding_number p z = winding_number (\<lambda>w. p w - z) 0"
  using winding_number_offset by simp

(*Installed in the distribution 25-09-23*)
lemma powi_numeral_reduce: "x powi numeral n = x * x powi pred_numeral n"
  by (simp add: numeral_eq_Suc)

(*Installed in the distribution 25-09-23*)
lemma powi_minus_numeral_reduce: "x powi - (numeral n) = inverse x * x powi - (pred_numeral n)"
  by (simp add: numeral_eq_Suc power_int_def)

(*Installed in the distribution 25-09-23*)
lemma simple_path_continuous_image:
  assumes "simple_path f" "continuous_on (path_image f) g" "inj_on g (path_image f)"
  shows   "simple_path (g \<circ> f)"
  unfolding simple_path_def
proof
  show "path (g \<circ> f)"
    using assms unfolding simple_path_def by (intro path_continuous_image) auto
  from assms have [simp]: "g (f x) = g (f y) \<longleftrightarrow> f x = f y" if "x \<in> {0..1}" "y \<in> {0..1}" for x y
    unfolding inj_on_def path_image_def using that by fastforce
  show "loop_free (g \<circ> f)"
    using assms(1) by (auto simp: loop_free_def simple_path_def)
qed

lemma Times_insert_left: "insert x A \<times> B = (\<lambda>y. (x, y)) ` B \<union> A \<times> B"
  by auto

lemma Times_insert_right: "A \<times> insert y B = (\<lambda>x. (x, y)) ` A \<union> A \<times> B"
  by auto

(*TODO: experimental; not used in fact.*)
definition deriv_p 
      :: "('a:: real_normed_field \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
    where
  "deriv_p f = (\<lambda>x. if is_pole f x then 0 else deriv f x)"

lemma meromorphic_on_deriv_p:
  assumes "f meromorphic_on A"  
  shows "deriv_p f meromorphic_on A"
proof -
  have "\<forall>\<^sub>\<approx>z\<in>A. deriv f z = deriv_p f z"
    unfolding deriv_p_def
    using assms eventually_mono
      meromorphic_on_imp_not_pole_cosparse by force
  moreover have "deriv f meromorphic_on A"
    using assms by (auto intro:meromorphic_intros)
  ultimately show ?thesis using meromorphic_on_cong' by simp
qed

lemma nicely_meromorphic_on_deriv:
  assumes "f nicely_meromorphic_on A"  
  shows "deriv_p f nicely_meromorphic_on A"
proof -
  have "f meromorphic_on A" and 
       p_tends:"(\<forall>z\<in>A. is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z)"
    using assms unfolding nicely_meromorphic_on_def by auto
  have "deriv_p f meromorphic_on A" 
    by (simp add: \<open>f meromorphic_on A\<close> meromorphic_on_deriv_p)
  moreover have "is_pole (deriv_p f) z \<and> deriv_p f z = 0 \<or>
            deriv_p f \<midarrow>z\<rightarrow> deriv_p f z" if "z\<in>A" for z
    using p_tends[rule_format,OF that]
  proof (elim disjE)
    assume asm:"is_pole f z \<and> f z = 0"
    have "is_pole (deriv_p f) z"
    proof - 
      have "isolated_singularity_at f z"
        using \<open>f meromorphic_on A\<close> meromorphic_on_altdef that 
        by blast
      then have "is_pole (deriv f) z "
        by (simp add: asm is_pole_deriv)
      moreover have "\<forall>\<^sub>F x in at z. deriv f x = deriv_p f x"
        using \<open>isolated_singularity_at f z\<close> 
        unfolding deriv_p_def
        by (smt (verit, del_insts) eventually_at_topological 
            eventually_not_pole)
      ultimately show "is_pole (deriv_p f) z"
        using is_pole_cong by auto
    qed
    then show "is_pole (deriv_p f) z \<and> deriv_p f z = 0 \<or>
            deriv_p f \<midarrow>z\<rightarrow> deriv_p f z"
      by (meson asm deriv_p_def)
  next
    assume "f \<midarrow>z\<rightarrow> f z"
    then have "f analytic_on {z}" 
      by (meson assms at_eq_bot_iff is_pole_def 
          nicely_meromorphic_on_imp_analytic_at 
          not_open_singleton 
          not_tendsto_and_filterlim_at_infinity that)
    then have "deriv f analytic_on {z}" 
      using analytic_deriv by auto
    moreover have "\<forall>\<^sub>F x in nhds z. deriv f x = deriv_p f x"
      unfolding deriv_p_def
      by (metis (no_types, lifting) \<open>f analytic_on {z}\<close> 
          analytic_at eventually_nhds not_is_pole_holomorphic)
    ultimately have "deriv_p f analytic_on {z}" 
      using analytic_at_cong by auto
    then have "deriv_p f \<midarrow>z\<rightarrow> deriv_p f z"
      using analytic_at_imp_isCont isContD by blast
    then show "is_pole (deriv_p f) z \<and> deriv_p f z = 0 \<or>
            deriv_p f \<midarrow>z\<rightarrow> deriv_p f z"
      by auto
  qed
  ultimately show ?thesis 
    unfolding nicely_meromorphic_on_def by auto
qed

lemma cosparse_imp_finite:
  assumes "\<forall>\<^sub>\<approx>x\<in>A. \<not> P x" "compact A"
  shows "finite {x\<in>A. P x}"
  using assms sparse_in_compact_finite
  unfolding eventually_cosparse by (auto simp:Collect_conj_eq)

section \<open>is\_zero\<close>

text \<open>TODO: I hope this one can supersede @{term "isolated_zero"}
in the library, which appears a bit weird to me since @{term is_pole}
could also be an @{term isolated_zero}.\<close>
definition is_zero ::
  "('a::topological_space \<Rightarrow> 'b::real_normed_div_algebra) 
      \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_zero f a \<equiv>  (f \<longlongrightarrow> 0) (nhds a) 
      \<and> eventually (\<lambda>x. f x\<noteq>0) (at a)" 

lemma inverse_pole_imp_zero:
  assumes "is_pole f z" "f z=0"
  shows "is_zero (\<lambda>x. inverse (f x)) z"
proof -
  have "(inverse \<circ> f) \<midarrow>z\<rightarrow> 0" 
    by (rule is_pole_tendsto) fact
  then have "((inverse \<circ> f) \<longlongrightarrow> 0) (nhds z)"
    by (simp add: assms(2) tendsto_nhds_iff)
  moreover have "eventually (\<lambda>x. (inverse o f) x\<noteq>0) (at z)"
    using assms(1) non_zero_neighbour_pole by fastforce
  ultimately show ?thesis 
    using is_zero_def unfolding comp_def by blast
qed

lemma inverse_zero_imp_pole:
  assumes "is_zero f z"
  shows "is_pole (\<lambda>x. inverse (f x)) z"
proof -
  have "filterlim f (at 0) (at z)" 
    using assms unfolding is_zero_def
    by (simp add: filterlim_atI tendsto_nhds_iff)
  then show ?thesis
    unfolding is_pole_def
    by (simp flip: filterlim_inverse_at_iff)
qed

lemma zero_is_zero:
  assumes "is_zero f z"
  shows "f z = 0"
  using is_zero_def assms tendsto_nhds_iff by blast

lemma pole_is_not_zero:
  fixes f:: "'a::perfect_space \<Rightarrow> 'b::real_normed_field"
  assumes "is_pole f z" 
  shows "\<not> is_zero f z"
proof 
  assume "is_zero f z"
  then have "filterlim f (nhds 0) (at z)" 
    unfolding is_zero_def using tendsto_nhds_iff by blast
  moreover have "filterlim f at_infinity (at z)" 
    using \<open>is_pole f z\<close> unfolding is_pole_def .
  ultimately show False
    using not_tendsto_and_filterlim_at_infinity[OF at_neq_bot]
    by auto
qed

lemma meromorphic_on_imp_not_zero_cosparse:
  assumes "f meromorphic_on A"
  shows   "eventually (\<lambda>z. \<not>is_zero f z) (cosparse A)"
  by (smt (verit) meromorphic_on_inverse assms 
      eventually_mono inverse_zero_imp_pole 
      meromorphic_on_imp_not_pole_cosparse)

lemma nicely_meromorphic_on_inverse:
  assumes "f nicely_meromorphic_on A"
  shows "(\<lambda>x. inverse (f x)) nicely_meromorphic_on A"
proof -
  have asm: "f meromorphic_on A" 
      "\<forall>z\<in>A. is_pole f z \<and> f z = 0 \<or> f \<midarrow>z\<rightarrow> f z"
    using assms unfolding nicely_meromorphic_on_def by auto

  define ff where "ff = (\<lambda>x. inverse (f x))"

  have "ff meromorphic_on A"
    using asm(1) meromorphic_on_inverse unfolding ff_def 
    by auto
  moreover have "is_pole ff z \<and> ff z = 0 \<or> ff \<midarrow>z\<rightarrow> ff z"
    if "z\<in>A" for z
  proof -
    have "ff \<midarrow>z\<rightarrow> ff z" if "is_pole f z \<and> f z = 0" 
      unfolding ff_def 
      using filterlim_compose is_pole_def 
        tendsto_inverse_0 that by fastforce
    moreover have ?thesis if "f \<midarrow>z\<rightarrow> f z" "f z =0" 
    proof (cases "eventually (\<lambda>x. f x\<noteq>0) (at z)")
      case True
      then have "is_zero f z" unfolding is_zero_def
        using tendsto_nhds_iff that(1) that(2) by auto
      from inverse_zero_imp_pole[OF this] zero_is_zero[OF this]
      have "is_pole ff z \<and> ff z = 0"
        unfolding ff_def comp_def by simp
      then show ?thesis by simp
    next
      case False
      then have "\<exists>\<^sub>F x in at z. f x = 0"
        using frequently_def by blast
      moreover have "isolated_singularity_at f z"
          "not_essential f z"
        using asm(1) \<open>z\<in>A\<close> 
        by (auto intro:meromorphic_on_isolated_singularity 
            meromorphic_on_not_essential 
            elim:meromorphic_on_subset)
      ultimately have "\<forall>\<^sub>F z in at z. f z = 0"
        using not_essential_frequently_0_imp_eventually_0 by blast
      then have "ff \<midarrow>z\<rightarrow> ff z"
        unfolding ff_def using \<open>f z=0\<close> 
        by (simp add: tendsto_eventually)
      then show ?thesis by simp
    qed 
    moreover have ?thesis if "f \<midarrow>z\<rightarrow> f z" "f z \<noteq>0" 
      using tendsto_inverse[OF that]
      unfolding ff_def by blast
    ultimately show ?thesis using asm(2) that by blast
  qed
  ultimately show ?thesis unfolding nicely_meromorphic_on_def
    ff_def comp_def by simp
qed

lemma is_pole_zero_at_nicely_mero:
  assumes "f nicely_meromorphic_on A" "is_pole f z" "z\<in>A"
  shows "f z=0"
  by (meson assms at_neq_bot 
      is_pole_def nicely_meromorphic_on_def 
      not_tendsto_and_filterlim_at_infinity)

lemma zero_or_pole:
  assumes mero:"f nicely_meromorphic_on A" 
    and "z\<in>A" "f z=0" and event:"\<forall>\<^sub>F x in at z. f x \<noteq> 0"
  shows "is_zero f z \<or> is_pole f z"
proof -
  from mero \<open>z\<in>A\<close>
  have "(is_pole f z \<and> f z=0) \<or> f \<midarrow>z\<rightarrow> f z"
    unfolding nicely_meromorphic_on_def by simp
  moreover have "is_zero f z" if "f \<midarrow>z\<rightarrow> f z" 
    unfolding is_zero_def
    using \<open>f z=0\<close> that event tendsto_nhds_iff by auto
  ultimately show ?thesis by auto
qed

lemma is_zero_imp_not_essential [intro]:
  "is_zero f z \<Longrightarrow> not_essential f z"
  unfolding is_zero_def not_essential_def
  using tendsto_nhds_iff by blast

section \<open>Elliptic Functions\<close>

(* definition p.4 in 1.4 *)
(*
definition is_elliptic:: "[complex \<Rightarrow> complex, complex set] \<Rightarrow> bool" where
  "is_elliptic f pts \<equiv> (\<exists>\<omega>1 \<omega>2. is_doubly_periodic \<omega>1 \<omega>2 f) \<and> (f meromorphic_on UNIV)"
*)
definition is_elliptic:: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "is_elliptic f \<equiv> (\<exists>\<omega>1 \<omega>2. is_doubly_periodic \<omega>1 \<omega>2 f) 
      \<and> (f nicely_meromorphic_on UNIV)"

abbreviation is_constant 
  where "is_constant f \<equiv> f constant_on UNIV"

definition mostly_constant_on :: 
    "('a::topological_space \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"  
  (infixl "(mostly'_constant'_on)" 50) where
    "f mostly_constant_on A = (\<exists>c. (\<forall>\<^sub>\<approx>z\<in>A. f z = c))"

lemma small_periodic_imp_constant:
  assumes f: "f analytic_on S" 
    and S: "open S" "connected S"
    and per: "\<And>x. x > 0 \<Longrightarrow> \<exists>\<omega>. \<omega> \<noteq> 0 
                  \<and> cmod \<omega> < x \<and> is_periodic \<omega> f"
  shows "f constant_on S"
proof -
  have "continuous_on S f"
    using analytic_imp_holomorphic assms(1) 
      holomorphic_on_imp_continuous_on 
    by presburger
  moreover have "(f has_field_derivative 0) (at z)"
      if "z \<in> S" for z
  proof -
    have "\<forall>n. \<exists>z. cmod z < 1 / of_nat(Suc n) 
            \<and> is_periodic z f \<and> z \<noteq> 0"
      by (metis per of_nat_0_less_iff zero_less_Suc 
          zero_less_divide_1_iff)
    then obtain \<xi> where "\<And>n. cmod (\<xi> n) < 1 / Suc n" 
      and \<section>: "\<And>n. is_periodic (\<xi> n) f" "\<And>n. \<xi> n \<noteq> 0"
      by metis
    with LIMSEQ_inverse_real_of_nat have 0: "\<xi> \<longlonglongrightarrow> 0"
      by (simp add: LIMSEQ_norm_0)
    have "(\<lambda>n. (f (z + \<xi> n) - f z) / \<xi> n) \<longlonglongrightarrow> 0"
      using \<section> by (simp add: is_periodic_def)
    moreover have "f field_differentiable at z"
      using analytic_on_imp_differentiable_at f that by blast
    ultimately show ?thesis
      unfolding field_differentiable_def
      using \<section> 0 field_derivative_lim_unique [where s=\<xi>] by blast 
  qed
  ultimately show ?thesis
    unfolding constant_on_def
    using DERIV_zero_connected_constant S \<open>continuous_on S f\<close>
    by (metis (mono_tags, lifting) Diff_empty finite.intros(1))
qed

lemma constant_fun_is_periodic:
  assumes "is_constant f" shows "is_periodic \<omega> f"
  by (metis UNIV_I assms constant_on_def is_periodic_def)

lemma remove_sings_eq_on_constant:
  assumes "f constant_on A" "open A" "x\<in>A"
  shows "remove_sings f x= f x"
  using remove_sings_at_analytic analytic_at_two assms
    constant_on_imp_holomorphic_on by blast

lemma constant_fun_is_elliptic:                                   
  assumes "is_constant f"
  shows "is_elliptic f"
proof -
  have "\<exists>\<omega>1 \<omega>2. is_doubly_periodic \<omega>1 \<omega>2 f"
    unfolding is_doubly_periodic_def
    by (metis assms constant_fun_is_periodic div_by_1 imaginary_unit.sel(2) zero_neq_one)
  moreover have "f nicely_meromorphic_on UNIV"
    using assms constant_on_imp_nicely_meromorphic_on by blast
  ultimately show ?thesis
    unfolding is_elliptic_def by simp
qed

lemma nonconstant_elliptic_min_period:
  assumes "\<not> is_constant f" and "is_elliptic f"
  obtains r where "r > 0" 
      and "\<And>\<omega>. \<lbrakk>is_periodic \<omega> f; cmod \<omega> < r\<rbrakk> \<Longrightarrow> \<omega> = 0"
proof -
  have "f nicely_meromorphic_on UNIV"
    using \<open>is_elliptic f\<close> unfolding is_elliptic_def by auto
  from nicely_meromorphic_onE[OF this] 
  obtain pts where 
      [simp]:"f analytic_on UNIV - pts" "pts sparse_in UNIV"
      and pts:"\<And>z. z \<in> pts \<Longrightarrow> is_pole f z \<and> f z = 0"
    by metis

  have "f analytic_on -pts" 
    by (simp add: Compl_eq_Diff_UNIV)
  moreover have "open (-pts)"
    by (auto simp add: Compl_eq_Diff_UNIV open_diff_sparse_pts)
  moreover have "connected (-pts)"
    unfolding Compl_eq_Diff_UNIV
    by (rule sparse_imp_connected) auto
  moreover have "\<not> f constant_on (-pts)"
  proof (cases "pts={}")
    case True
    then show ?thesis by (simp add: assms(1))
  next
    case False
    then obtain p where "p\<in>pts" by auto
    then have "is_pole f p" using pts(1) by auto
    moreover have "open (insert p (- pts))"
    proof -
      from \<open>pts sparse_in UNIV\<close>
      have "pts-{p} sparse_in UNIV"
        by (meson Diff_subset sparse_in_subset2)
      then show ?thesis 
        by (metis Compl_insert Diff_eq double_compl 
            inf_top_left open_UNIV open_diff_sparse_pts)
    qed
    ultimately show ?thesis
      by (elim pole_imp_not_constant) auto
  qed
  ultimately have "\<not> (\<forall>x>0. (\<exists>\<omega>. \<omega> \<noteq> 0 
    \<and> cmod \<omega> < x \<and> is_periodic \<omega> f))"
    using small_periodic_imp_constant[of f "-pts"]  
    by blast
  then show ?thesis using that by blast
qed

lemma bounded_periodic_finite:
  assumes "\<not> is_constant f" "is_elliptic f" "bounded B" 
  shows "finite ({\<omega>. is_periodic \<omega> f} \<inter> B)"
proof -
  obtain r where "r > 0" and 
      r: "\<And>\<omega>. \<lbrakk>\<omega> \<noteq> 0; norm \<omega> < r\<rbrakk> \<Longrightarrow> \<not> is_periodic \<omega> f"
    by (meson assms nonconstant_elliptic_min_period)
  have False if x: "x islimpt {\<omega>. is_periodic \<omega> f}" for x
  proof -
    have ex_per: "\<exists>y. is_periodic y f \<and> y \<noteq> x \<and> dist y x < e" if "e>0" for e
      by (metis x islimpt_approachable mem_Collect_eq that)
    then obtain x' where "is_periodic x' f" "x' \<noteq> x" and x': "dist x' x < r / 2"
      by (meson \<open>0 < r\<close> half_gt_zero)
    then obtain x'' where "is_periodic x'' f" "x'' \<noteq> x" and x'': "dist x'' x < min (r/2) (dist x x')"
      by (metis \<open>0 < r\<close> ex_per dist_pos_lt min_less_iff_conj zero_less_divide_iff zero_less_numeral)
    then have "x' \<noteq> x''"
      by (smt (verit, ccfv_SIG) dist_commute)
    moreover have "dist x' x'' < r"
      using dist_triangle_half_l x' x'' by auto
    ultimately show False
      by (metis \<open>is_periodic x' f\<close> \<open>is_periodic x'' f\<close> add.left_neutral diff_add_cancel dist_norm is_periodic_minus is_periodic_plus r uminus_add_conv_diff)
  qed
  then show ?thesis
    by (meson inf.bounded_iff islimpt_subset \<open>bounded B\<close> bounded_infinite_imp_islimpt bounded_subset eq_refl)
qed

text \<open>theorem 1.3 p. 5\<close>
theorem nonconstant_elliptic_fun_has_fundamental_pair:
  assumes "\<not> is_constant f" and "is_elliptic f"
  shows "\<exists>\<omega>1 \<omega>2. fundamental_pair_old \<omega>1 \<omega>2 f"
proof -
  obtain W1 W2 where W12:"is_doubly_periodic W1 W2 f"
    using \<open>is_elliptic f\<close> unfolding is_elliptic_def by auto
  then interpret gen_lattice W1 W2
    using gen_lattice.intro is_doubly_periodic_def by blast

  obtain r where "r > 0" and r: "\<And>\<omega>. \<lbrakk>\<omega> \<noteq> 0; norm \<omega> < r\<rbrakk> \<Longrightarrow> \<not> is_periodic \<omega> f"
    by (meson assms nonconstant_elliptic_min_period)
  have discrete: "dist \<omega>1 \<omega>2 \<ge> r" if "is_periodic \<omega>1 f" "is_periodic \<omega>2 f" "\<omega>1 \<noteq> \<omega>2" for \<omega>1 \<omega>2
    using r that
    by (smt (verit) dist_norm dist_pos_lt is_periodic_minus is_periodic_plus norm_eq_zero uminus_add_conv_diff)

  define r12 where "r12 = max (norm W1) (norm W2)"
  define PF where "PF \<equiv> ({\<omega>. is_periodic \<omega> f} \<inter> (cball 0 r12 - {0}))"
  then have "finite PF"
    by (metis assms bounded_periodic_finite bounded_cball bounded_diff)
  then have "finite (norm ` PF)"
    by blast
  moreover have "W1 \<in> PF" "W2 \<in> PF"
    using W12 by (force simp add: PF_def is_doubly_periodic_def r12_def)+
  ultimately obtain r1 where "r1 \<in> norm ` PF" and r1: "\<And>x. x \<in> norm ` PF \<Longrightarrow> r1 \<le> x"
    using Min_le Min_in PF_def by (metis empty_iff image_is_empty)
  then obtain \<omega>1 where \<omega>1: "\<omega>1 \<in> PF" "norm \<omega>1 = r1"
    by blast 
  then have "is_periodic \<omega>1 f" "\<omega>1 \<noteq> 0" "r1 > 0"
    by (auto simp: PF_def)
  have min1: "\<And>z. \<lbrakk>is_periodic z f; z \<noteq> 0\<rbrakk> \<Longrightarrow> r1 \<le> norm z"
    using r1 \<omega>1 by (fastforce simp add: PF_def)

  have fp: "fundamental_pair_old \<omega>1 \<omega>2 f" 
    if \<omega>2: "is_periodic \<omega>2 f" "Im (\<omega>2/\<omega>1) \<noteq> 0" and "\<omega>2 \<noteq> 0" and "r1 \<le> norm \<omega>2"
      and le: "norm \<omega>1 \<le> norm \<omega>2" and min2: "\<And>z. \<lbrakk>is_periodic z f; Im (z/\<omega>1) \<noteq> 0\<rbrakk> \<Longrightarrow> norm \<omega>2 \<le> norm z" 
      for \<omega>2 
  proof (rule is_fundamental_pair_old [OF \<open>is_periodic \<omega>1 f\<close> \<omega>2])
    fix z
    assume "z \<in> Complex_Lattices.triangle \<omega>1 \<omega>2 - {0, \<omega>1, \<omega>2}"
    then obtain \<alpha> \<beta> where non0: "z \<noteq> 0" and 1: "z \<noteq> \<omega>1" and 2: "z \<noteq> \<omega>2"
      and "0 \<le> \<alpha>" "0 \<le> \<beta>" "\<alpha> + \<beta> \<le> 1"
      and zeq: "z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2"
      by(auto simp: triangle_def)
    show "\<not> is_periodic z f"
    proof 
      define r2 where "r2 \<equiv> norm \<omega>2"
      assume per: "is_periodic z f"
      have norm_le: "norm z \<le> norm (\<alpha> * \<omega>1) + norm (\<beta> * \<omega>2)"
        using zeq norm_triangle_ineq by blast
      have eq: "norm (\<alpha> * \<omega>1) + norm (\<beta> * \<omega>2) = \<alpha> * r1 + \<beta> * r2"
        using \<open>0 \<le> \<alpha>\<close> \<open>0 \<le> \<beta>\<close>
        by (simp add: norm_mult \<open>norm \<omega>1 = r1\<close> r2_def)
      also have le_abr2: "\<dots> \<le> (\<alpha> + \<beta>) * r2"
        using \<open>0 \<le> \<alpha>\<close> \<open>0 \<le> \<beta>\<close>
        by (simp add: distrib_right mult_left_mono r2_def \<open>r1 \<le> norm \<omega>2\<close>)
      also have "\<dots> \<le> r2"
        using \<open>0 < r1\<close> \<open>\<alpha> + \<beta> \<le> 1\<close> r2_def
        by (simp add: mult.commute mult_left_le)
      finally have le_r2: "norm (\<alpha> * \<omega>1) + norm (\<beta> * \<omega>2) \<le> r2" 
        by simp
      have "\<beta> \<noteq> 0"
        using "1" zeq \<open>0 < r1\<close> \<open>\<alpha> + \<beta> \<le> 1\<close> eq min1 non0 per by fastforce
      have non_coll: "\<not> collinear {0,\<omega>1,\<omega>2}"
        using \<omega>2 collinear_iff_Reals complex_is_Real_iff by presburger
      have Im_eq_0: "Im (z / \<omega>1) \<noteq> 0"
        by (simp add: zeq Im_divide_mult_iff \<omega>2 add_divide_distrib \<open>\<beta> \<noteq> 0\<close> \<open>\<omega>1 \<noteq> 0\<close>)
      then have "\<alpha> \<noteq> 0"
        using "2" zeq le_r2 min2 [OF per] using eq
        using r2_def by fastforce
      moreover have "\<not> norm z < r1"
        using per non0 min1 by (meson not_le)
      moreover have "\<not> collinear {0, \<alpha>*\<omega>1, \<beta>*\<omega>2}"
        using non_coll collinear_scaleR_iff [where 'a=complex]
        by (simp add: \<open>\<alpha> \<noteq> 0\<close> \<open>\<beta> \<noteq> 0\<close> scaleR_conv_of_real) 
      moreover have less_r2: "norm (\<alpha> * \<omega>1) + norm (\<beta> * \<omega>2) \<le> (\<alpha>+\<beta>) * r2"
        by (simp add: le_abr2 eq)
      moreover have "\<not> norm z < r2"
        using non0 min2 [OF per] local.Im_eq_0 r2_def by linarith
      ultimately show False
        using \<open>(\<alpha> + \<beta>) * r2 \<le> r2\<close> local.norm_le norm_triangle_eq_imp_collinear zeq by force
    qed  
  qed
  obtain \<omega>2 where "fundamental_pair_old \<omega>1 \<omega>2 f"
  proof (cases "\<exists>\<omega>2. is_periodic \<omega>2 f \<and> norm \<omega>2 = r1 \<and> Im (\<omega>2/\<omega>1) \<noteq> 0")
    case True \<comment>\<open>the other period lies on the same circle\<close>
    with \<omega>1 obtain \<omega>2 where \<omega>2: "is_periodic \<omega>2 f" "Im (\<omega>2/\<omega>1) \<noteq> 0" 
            and "\<omega>2 \<noteq> 0" and same: "norm \<omega>2 = norm \<omega>1" 
      by fastforce
    with min1 \<omega>1 \<open>\<omega>2 \<noteq> 0\<close> same show thesis
      by (force intro!: fp[OF \<omega>2] that)
  next
    case False \<comment>\<open>the other period is further out\<close>
    have "Im (W1/\<omega>1) \<noteq> 0 \<or> Im (W2/\<omega>1) \<noteq> 0" 
        by (meson Im_divide_zero_iff Im_divide_zero_trans \<open>\<omega>1 \<noteq> 0\<close> ratio_notin_real)
    then obtain W where "W \<in> PF" "Im (W/\<omega>1) \<noteq> 0"
      using \<open>W1 \<in> PF\<close> \<open>W2 \<in> PF\<close> by blast
    then obtain r2 where "r2 \<in> norm ` (PF \<inter> {W. Im (W/\<omega>1) \<noteq> 0})" and r2: "\<And>x. x \<in> norm ` (PF \<inter> {W. Im (W/\<omega>1) \<noteq> 0}) \<Longrightarrow> r2 \<le> x"
      using Min_le Min_in PF_def
      by (metis (mono_tags, lifting) IntI \<open>finite PF\<close> empty_iff empty_is_image finite_Int finite_imageI mem_Collect_eq)
    then obtain \<omega>2 where \<omega>2: "is_periodic \<omega>2 f" "Im (\<omega>2/\<omega>1) \<noteq> 0" and "\<omega>2 \<in> PF" "norm \<omega>2 = r2" "\<omega>2 \<noteq> 0"
      using PF_def by blast
    then have "r1 < r2" "0 < r2"
      using False PF_def r1 by fastforce+
    have min2: "\<And>z. \<lbrakk>is_periodic z f; Im (z/\<omega>1) \<noteq> 0\<rbrakk> \<Longrightarrow> r2 \<le> norm z"
      using r2 \<open>\<omega>2 \<in> PF\<close> \<open>norm \<omega>2 = r2\<close> by (force simp: PF_def)
    with \<omega>1 \<open>\<omega>2 \<noteq> 0\<close> \<open>is_periodic \<omega>2 f\<close> \<open>cmod \<omega>2 = r2\<close> \<open>r1 < r2\<close> show thesis
      by (force intro!: fp[OF \<omega>2] that)
  qed
  then show ?thesis 
    by blast
qed

text \<open>
Definition of a period parallelogram: @{term "period_parallelogram \<omega>1 \<omega>2 m n"} describes the parallelogram
with vertices $m\omega_1+n\omega_2, (m+1)\omega_1+n\omega_2, (m+1)\omega_1+(n+1)\omega_2, 
m\omega_1+(n+1)\omega_2$, where the vertices are described anticlockwise. 
Thus, the parallelogram with vertices $0, \omega_1, \omega_1+\omega_2 \text{ and } \omega_2$ is for 
instance simply @{term "period_parallelogram \<omega>1 \<omega>2 0 0"}. 
\<close>

definition period_parallelogram :: "[complex, complex, int, int] \<Rightarrow> complex set" where
  "period_parallelogram \<omega>1 \<omega>2 m n \<equiv> 
     {(of_real x) * \<omega>1 + (of_real y) * \<omega>2 |x y. m \<le> x \<and> x \<le> m + 1 \<and> n \<le> y \<and> y \<le> n + 1}"

definition period_parallelogram' :: "[complex, complex, int, int] \<Rightarrow> complex set" where
  "period_parallelogram' \<omega>1 \<omega>2 m n \<equiv> 
     {(of_real x) * \<omega>1 + (of_real y) * \<omega>2 |x y. m \<le> x \<and> x < m + 1 \<and> n \<le> y \<and> y < n + 1}"

definition path_of_parallelogram:: "[complex, complex, real] \<Rightarrow> complex" where
  "path_of_parallelogram \<omega>1 \<omega>2 \<equiv> 
      (linepath 0 \<omega>1 +++ (linepath \<omega>1 (\<omega>1 + \<omega>2)) +++ 
      (linepath (\<omega>1+\<omega>2) \<omega>2) +++ (linepath \<omega>2 0))"

definition boundary_of_period_parallelogram:: "[complex, complex, int, int] \<Rightarrow> complex set" where
  "boundary_of_period_parallelogram \<omega>1 \<omega>2 m n \<equiv> 
      path_image ((+)(of_int m * \<omega>1 + of_int n * \<omega>2) \<circ> path_of_parallelogram \<omega>1 \<omega>2)"

lemma compact_parallelogram [intro]: "compact (period_parallelogram \<omega>1 \<omega>2 m n)"
proof -
  let ?S = "(\<lambda>x. (of_real x) * \<omega>1) ` {of_int m..of_int m + 1}"
  let ?T = "(\<lambda>x. (of_real x) * \<omega>2) ` {of_int n..of_int n + 1}"
  have \<section>: "period_parallelogram \<omega>1 \<omega>2 m n = {x + y | x y. x \<in> ?S \<and> y \<in> ?T}"
    unfolding period_parallelogram_def by force
  show ?thesis
    unfolding \<section>
    by (intro compact_sums compact_continuous_image)
       (use continuous_on_mult_right continuous_on_of_real_id in blast)+
qed

lemma nonempty_parallelogram: "period_parallelogram \<omega>1 \<omega>2 m n \<noteq> {}"
proof -
  have "m * \<omega>1 + n * \<omega>2 \<in> period_parallelogram \<omega>1 \<omega>2 m n"
    unfolding period_parallelogram_def
    apply safe
    apply (rule exI[of _ "of_int m :: real"], rule exI[of _ "of_int n :: real"])
    by auto
  thus ?thesis by blast
qed

lemma shift_period_parallelogram:
  assumes "z \<in> period_parallelogram \<omega>1 \<omega>2 m' n'"
  shows "z + ((m-m') * \<omega>1 + (n-n') * \<omega>2) \<in> period_parallelogram \<omega>1 \<omega>2 m n"
proof -
  obtain x y where zeq: "z = of_real x * \<omega>1 + of_real y * \<omega>2"
      and "of_int m' \<le> x" "x \<le> of_int m' + 1"
      and "of_int n' \<le> y" "y \<le> of_int n' + 1"
    using assms by (auto simp add: period_parallelogram_def)
  then show ?thesis
    apply (simp add: period_parallelogram_def)
    apply (rule_tac x="x + (m-m')" in exI)
    apply (rule_tac x="y + (n-n')" in exI)
    apply (simp add: algebra_simps)
    done
qed

lemma path_of_parallelogram_altdef:
  fixes \<omega>1 \<omega>2 :: complex
  defines "g \<equiv> (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2)"
  shows   "path_of_parallelogram \<omega>1 \<omega>2 = g \<circ> rectpath 0 (1 + \<i>)"
  by (simp add: path_of_parallelogram_def rectpath_def g_def Let_def o_def joinpaths_def
                fun_eq_iff linepath_def scaleR_conv_of_real algebra_simps)
  
lemma simple_path_parallelogram:
  assumes "Im (\<omega>2 / \<omega>1) \<noteq> 0"
  shows   "simple_path (path_of_parallelogram \<omega>1 \<omega>2)"
  unfolding path_of_parallelogram_altdef
proof (rule simple_path_continuous_image)
  show "simple_path (rectpath 0 (1 + \<i>))"
    by (intro simple_path_rectpath) auto
  show "continuous_on (path_image (rectpath 0 (1 + \<i>))) (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2)"
    by (intro continuous_intros)
  show "inj_on (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2) (path_image (rectpath 0 (1 + \<i>)))"
  proof -
    interpret gen_lattice \<omega>1 \<omega>2
      by unfold_locales fact
    have 1: "inj_on (\<lambda>z. (Re z, Im z)) UNIV"
      by (auto simp: inj_on_def complex_eq_iff)
    have 2: "inj_on of_\<omega>12_coords UNIV"
      by (auto simp: inj_on_def of_\<omega>12_coords_eq_iff)
    have "inj_on (of_\<omega>12_coords \<circ> (\<lambda>z. (Re z, Im z))) (path_image (rectpath 0 (1 + \<i>)))"
      by (intro comp_inj_on inj_on_subset[OF 1] inj_on_subset[OF 2]) auto
    also have "(of_\<omega>12_coords \<circ> (\<lambda>z. (Re z, Im z))) = (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2)"
      by (simp add: case_prod_unfold o_def fun_eq_iff of_\<omega>12_coords_def scaleR_conv_of_real)
    finally show ?thesis .
  qed
qed

lemma (in pre_gen_lattice) period_parallelogram_altdef:
  "period_parallelogram \<omega>1 \<omega>2 m n =
     of_\<omega>12_coords ` ({of_int m..of_int (m+1)} \<times> {of_int n..of_int (n+1)})"
proof -
  have "period_parallelogram \<omega>1 \<omega>2 m n =
          {of_\<omega>12_coords (x, y) |x y. real_of_int m \<le> x \<and>
             x \<le> real_of_int (m + 1) \<and> real_of_int n \<le> y \<and> y \<le> real_of_int (n + 1)}"
    unfolding period_parallelogram_def of_\<omega>12_coords_def by simp
  also have "\<dots> = of_\<omega>12_coords ` {(x, y) |x y. real_of_int m \<le> x \<and>
             x \<le> real_of_int (m + 1) \<and> real_of_int n \<le> y \<and> y \<le> real_of_int (n + 1)}"
    (is "_ = _ ` ?A") by blast
  also have "?A = {x. real_of_int m \<le> x \<and> x \<le> real_of_int (m + 1)} \<times>
                  {y. real_of_int n \<le> y \<and> y \<le> real_of_int (n + 1)}"
    by blast
  also have "\<dots> = {of_int m..of_int (m+1)} \<times> {of_int n..of_int (n+1)}"
    by auto
  finally show ?thesis .
qed

lemma (in pre_gen_lattice) period_parallelogram'_altdef:
  "period_parallelogram' \<omega>1 \<omega>2 m n =
     of_\<omega>12_coords ` ({of_int m..<of_int (m+1)} \<times> {of_int n..<of_int (n+1)})"
proof -
  have "period_parallelogram' \<omega>1 \<omega>2 m n =
          {of_\<omega>12_coords (x, y) |x y. real_of_int m \<le> x \<and>
             x < real_of_int (m + 1) \<and> real_of_int n \<le> y \<and> y < real_of_int (n + 1)}"
    unfolding period_parallelogram'_def of_\<omega>12_coords_def by simp
  also have "\<dots> = of_\<omega>12_coords ` {(x, y) |x y. real_of_int m \<le> x \<and>
             x < real_of_int (m + 1) \<and> real_of_int n \<le> y \<and> y < real_of_int (n + 1)}"
    (is "_ = _ ` ?A") by blast
  also have "?A = {x. real_of_int m \<le> x \<and> x < real_of_int (m + 1)} \<times>
                  {y. real_of_int n \<le> y \<and> y < real_of_int (n + 1)}"
    by blast
  also have "\<dots> = {of_int m..<of_int (m+1)} \<times> {of_int n..<of_int (n+1)}"
    by auto
  finally show ?thesis .
qed

lemma (in gen_lattice) \<omega>12_coords_path_of_parallelogram:
  "\<omega>12_coords ` path_image (path_of_parallelogram \<omega>1 \<omega>2) =
     {0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1}"
proof -
  have "\<omega>12_coords ` path_image (path_of_parallelogram \<omega>1 \<omega>2) =
        path_image (\<omega>12_coords \<circ> path_of_parallelogram \<omega>1 \<omega>2)"
    by (simp add: path_image_compose)
  also have "\<dots> = path_image (linepath (0,0) (1,0) +++ linepath (1,0) (1,1) +++
                    linepath (1,1) (0,1) +++ linepath (0,1) (0,0))"
    unfolding path_image_def
    by (intro image_cong)
       (simp_all add: path_image_def path_of_parallelogram_def joinpaths_def
                      \<omega>12_coords_linepath zero_prod_def del: linepath_0)
  also have "\<dots> = {0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1}"
    by (auto simp: path_image_join closed_segment_same_fst closed_segment_same_snd 
                   closed_segment_eq_real_ivl)
  finally show ?thesis .
qed

lemma convex_period_parallelogram[simp]:
  "convex (period_parallelogram \<omega>1 \<omega>2 m n)"
proof -
  interpret pre_gen_lattice \<omega>1 \<omega>2 .
  have "linear of_\<omega>12_coords"
    by unfold_locales auto
  thus ?thesis unfolding period_parallelogram_altdef
    by (intro convex_linear_image convex_Times) auto
qed

lemma path_image_path_of_parallelogram_subset:
  "path_image (path_of_parallelogram \<omega>1 \<omega>2) \<subseteq> period_parallelogram \<omega>1 \<omega>2 0 0"
proof -
  interpret pre_gen_lattice \<omega>1 \<omega>2 .
  have "path_image (path_of_parallelogram \<omega>1 \<omega>2) = 
          (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2) `
            ({z. Re z \<in> {Re 0, Re (1 + \<i>)} \<and> Im z \<in> {Im 0..Im (1 + \<i>)}} \<union>
             {z. Im z \<in> {Im 0, Im (1 + \<i>)} \<and> Re z \<in> {Re 0..Re (1 + \<i>)}})"
    (is "_ = _ ` ?S")
    unfolding path_of_parallelogram_altdef period_parallelogram_altdef path_image_compose
    by (subst path_image_rectpath) auto
  also have "(\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2) = of_\<omega>12_coords \<circ> (\<lambda>z. (Re z, Im z))"
    by (simp add: fun_eq_iff of_\<omega>12_coords_def complex_eq_iff)
  also have "\<dots> ` ?S \<subseteq> of_\<omega>12_coords ` ({0..1} \<times> {0..1})"
    unfolding image_comp [symmetric] by (intro image_mono) auto
  also have "\<dots> = period_parallelogram \<omega>1 \<omega>2 0 0"
    unfolding period_parallelogram_altdef by simp
  finally show ?thesis
    by blast
qed

lemma winding_number_parallelogram_outside:
  assumes "w \<notin> (period_parallelogram \<omega>1 \<omega>2 0 0)"
  shows "winding_number (path_of_parallelogram \<omega>1 \<omega>2) w = 0"
  apply (rule winding_number_zero_outside)
  using assms path_image_path_of_parallelogram_subset 
  unfolding path_of_parallelogram_def by auto

lemma period_parallelogram_commute:
  shows "period_parallelogram \<omega>2 \<omega>1 m n = period_parallelogram \<omega>1 \<omega>2 n m"
  unfolding period_parallelogram_def
  by (auto simp:algebra_simps)
 
lemma period_parallelogram_\<omega>1_0:
  assumes "\<omega>1 = 0"
  shows "period_parallelogram \<omega>1 \<omega>2 0 0 = closed_segment 0 \<omega>2"
proof -
  have "period_parallelogram \<omega>1 \<omega>2 0 0 = { of_real y * \<omega>2 |(x::real) (y::real).
            0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1}"
    unfolding period_parallelogram_def using assms by auto
  also have "\<dots> = { of_real y * \<omega>2 |(y::real). 0 \<le> y \<and> y \<le> 1}"
    by auto
  also have "\<dots> = closed_segment 0 \<omega>2"
    by (auto simp: in_segment of_real_def)
  finally show ?thesis .
qed

lemma period_parallelogram_\<omega>2_0:
  assumes "\<omega>2=0"
  shows "period_parallelogram \<omega>1 \<omega>2 0 0 = closed_segment 0 \<omega>1"
  apply (subst period_parallelogram_commute)
  using period_parallelogram_\<omega>1_0[OF assms] by simp

lemma pathfinish_parallelogram[simp]:
  "pathfinish (path_of_parallelogram \<omega>1 \<omega>2) = 0"
  unfolding path_of_parallelogram_def
  by auto

lemma pathstart_parallelogram[simp]:
  "pathstart (path_of_parallelogram \<omega>1 \<omega>2) = 0"
  unfolding path_of_parallelogram_def
  by auto

lemma period_parallelogram_\<omega>1\<omega>2_lined:
  assumes "\<omega>1 = r *\<^sub>R \<omega>2"
  shows "period_parallelogram \<omega>1 \<omega>2 0 0 = 
            (if r\<ge>0 then closed_segment 0 (\<omega>1+\<omega>2)
             else closed_segment \<omega>1 \<omega>2)" (is "_ = ?R")
proof -
  interpret pre_gen_lattice \<omega>1 \<omega>2 .
  have "period_parallelogram \<omega>1 \<omega>2 0 0 = of_\<omega>12_coords ` ({0..1} \<times> {0..1})"
    by (simp add: period_parallelogram_altdef)
  also have "\<dots> = ((\<lambda>x. x *\<^sub>R \<omega>2) \<circ> (\<lambda>(x,y). r * x + y)) ` ({0..1::real} \<times> {0..1::real})"
    unfolding of_\<omega>12_coords_def [abs_def] using assms
    by (intro image_cong) (auto simp: algebra_simps scaleR_conv_of_real)
  also note image_comp [symmetric]
  also have "(\<lambda>(x,y). r * x + y) ` ({0..1::real} \<times> {0..1::real}) =
             (if r \<ge> 0 then {0..1+r} else {r..1})" (is "?lhs = ?rhs")
  proof (intro equalityI subsetI)
    fix x assume "x \<in> ?lhs"
    then obtain a b where ab: "a \<in> {0..1}" "b \<in> {0..1}" "x = r * a + b"
      by auto
    have "r * a \<in> (*) r ` {0..1}"
      using ab by blast
    hence "r * a \<in> (if r \<ge> 0 then {0..r} else {r..0})"
      by (subst (asm) image_mult_atLeastAtMost_if; cases r "0 :: real" rule: linorder_cases) auto
    moreover have "r * 1 + 0 \<le> r * a + b" if "r < 0"
      using that ab by (intro add_mono mult_left_mono_neg) auto
    ultimately show "x \<in> (if r \<ge> 0 then {0..1 + r} else {r..1})"
      using ab by auto
  next
    fix x assume x: "x \<in> (if r \<ge> 0 then {0..1 + r} else {r..1})"
    define z :: "real \<times> real" where "z = (if r \<ge> 0 then ((x - min x 1) / r, min x 1) else ((x - max x 0) / r, max x 0))"
    have "z \<in> {0..1} \<times> {0..1}" 
      using x by (auto simp: z_def divide_simps)
    moreover have "x = (\<lambda>(x, y). r * x + y) z" using x
      by (simp add: case_prod_unfold z_def split: if_splits)
    ultimately show "x \<in> (\<lambda>(x, y). r * x + y) ` ({0..1} \<times> {0..1})"
      by blast
  qed
  finally show ?thesis
    by (simp split: if_splits add: assms algebra_simps
             flip: closed_segment_eq_real_ivl1 closed_segment_linear_image)
qed

lemma path_image_parallelogram_\<omega>1\<omega>2_lined:
  assumes "\<omega>1 = r *\<^sub>R \<omega>2"
  shows "path_image (path_of_parallelogram \<omega>1 \<omega>2) = 
            (if r\<ge>0 then closed_segment 0 (\<omega>1+\<omega>2)
             else closed_segment \<omega>1 \<omega>2)" (is "?L = ?R")
proof -
  interpret pre_gen_lattice \<omega>1 \<omega>2 .
  have "path_image (path_of_parallelogram \<omega>1 \<omega>2) = 
          (\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2) `
            ({z. Re z \<in> {0, 1} \<and> Im z \<in> {0..1}} \<union>
             {z. Im z \<in> {0, 1} \<and> Re z \<in> {0..1}})"
    (is "_ = _ ` ?S")
    unfolding path_of_parallelogram_altdef path_image_compose
    by (subst path_image_rectpath) auto
  also have "?S = (\<lambda>(x,y). Complex x y) ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1})"
    by (auto simp: case_prod_unfold image_iff complex_eq_iff bex_Un)
  also have "(\<lambda>z. Re z *\<^sub>R \<omega>1 + Im z *\<^sub>R \<omega>2) ` \<dots> =
             of_\<omega>12_coords ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1})"
    unfolding image_image by (intro image_cong) (auto simp: scaleR_conv_of_real of_\<omega>12_coords_def)
  also have "\<dots> = ((\<lambda>x. x *\<^sub>R \<omega>2) \<circ> (\<lambda>(x,y). r * x + y)) ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1})"
    unfolding of_\<omega>12_coords_def [abs_def]
    by (intro image_cong)
       (auto simp: assms complex_eq_iff case_prod_unfold scaleR_conv_of_real algebra_simps)
  also have "\<dots> = (\<lambda>x. x *\<^sub>R \<omega>2) ` (\<lambda>(x,y). r * x + y) ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1})"
    by (simp add: image_comp o_def)
  also have "(\<lambda>(x,y). r * x + y) ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1}) =
             (closed_segment 0 1 \<union> closed_segment 0 r) \<union>
             (closed_segment r (1 + r) \<union> (\<lambda>x. r * x + 1) ` closed_segment 0 1)"
    by (simp add: image_Un case_prod_unfold Times_insert_left Times_insert_right image_comp Un_ac add.commute[of 1]
             flip: closed_segment_linear_image closed_segment_eq_real_ivl1 closed_segment_translation)
  also have "(\<lambda>x. r * x + 1) ` closed_segment 0 1 = (+) 1 ` (*) r ` closed_segment 0 1"
    by (simp add: image_comp o_def algebra_simps)
  also have "\<dots> = closed_segment 1 (1 + r)"
    by (simp flip: closed_segment_linear_image closed_segment_translation)
  also have "(closed_segment 0 1 \<union> closed_segment 0 r \<union>
             (closed_segment r (1 + r) \<union> closed_segment 1 (1 + r))) =
             (if r \<ge> 0 then closed_segment 0 (1 + r) else closed_segment r 1)"
    by (auto simp: closed_segment_eq_real_ivl)
  also have "(\<lambda>x. x *\<^sub>R \<omega>2) ` \<dots> = ?R"
    by (simp add: assms algebra_simps flip: closed_segment_linear_image)
  finally show ?thesis .
qed

lemma Im_cnj_imp_lined:
  assumes "Im (\<omega>1 * cnj \<omega>2) = 0" and "\<omega>2 \<noteq>0"
  shows "\<exists>r. \<omega>1 = r *\<^sub>R \<omega>2"
proof -
  have "Im (\<omega>1 / \<omega>2) = 0"
    using Im_complex_div_eq_0 assms(1) by auto
  then obtain r::real where "\<omega>1 / \<omega>2 = r"
    by (metis complex_is_Real_iff of_real_Re)
  then have "\<omega>1 = r * \<omega>2" 
    using \<open>\<omega>2 \<noteq>0\<close> by (auto simp:field_simps)
  then show ?thesis by (simp add: scaleR_conv_of_real)
qed

lemma period_parallelogram_interior_imp:
  assumes "(period_parallelogram \<omega>1 \<omega>2 0 0) 
              - path_image (path_of_parallelogram \<omega>1 \<omega>2) \<noteq> {}"
  shows "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0" "\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2" "Im (\<omega>1 * cnj \<omega>2) \<noteq> 0" "Im (\<omega>2 / \<omega>1) \<noteq> 0"
proof -
  show "\<omega>1 \<noteq> 0"
  proof 
    assume "\<omega>1 = 0"
    then have "path_image (path_of_parallelogram \<omega>1 \<omega>2) 
        = closed_segment 0 \<omega>2"
      unfolding path_of_parallelogram_def
      by (auto simp:path_image_join closed_segment_commute)
    then show False
      using assms period_parallelogram_\<omega>1_0[OF \<open>\<omega>1 = 0\<close>]
      by auto
  qed
  show "\<omega>2 \<noteq> 0"
  proof 
    assume "\<omega>2 = 0"
    then have "path_image (path_of_parallelogram \<omega>1 \<omega>2) 
        = closed_segment \<omega>1 0"
      unfolding path_of_parallelogram_def
      by (auto simp:path_image_join closed_segment_commute)
    then show False
      using assms period_parallelogram_\<omega>2_0[OF \<open>\<omega>2 = 0\<close>]
      by (auto simp:closed_segment_commute)
  qed
  show "\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2"
  proof (rule ccontr)
    assume "\<not> (\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2)"
    then obtain r where "\<omega>1 = r *\<^sub>R \<omega>2" by auto
    from period_parallelogram_\<omega>1\<omega>2_lined[OF this]
         path_image_parallelogram_\<omega>1\<omega>2_lined[OF this]
    have "(period_parallelogram \<omega>1 \<omega>2 0 0) 
              - path_image (path_of_parallelogram \<omega>1 \<omega>2) = {}"
      by auto
    then show False using assms by auto
  qed
  show "Im (\<omega>1 * cnj \<omega>2) \<noteq>0"
    using Im_cnj_imp_lined[OF _ \<open>\<omega>2 \<noteq> 0\<close>] \<open>\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2\<close> by auto
  thus "Im (\<omega>2 / \<omega>1) \<noteq> 0"
    by (auto simp: Im_divide mult_ac)
qed

lemma period_parallelogram_interior_eq:
  assumes w_in:"w \<in> (period_parallelogram \<omega>1 \<omega>2 0 0)
                - path_image (path_of_parallelogram \<omega>1 \<omega>2)"
  obtains x y where "w = of_real x * \<omega>1 + of_real y * \<omega>2"
                and "0 < x" "x < 1" "0 < y" "y < 1"
proof -
  obtain x y where w_eq:"w = of_real x * \<omega>1 + of_real y * \<omega>2"
                and x:"0\<le>x \<and> x\<le>1" and y:"0\<le>y \<and> y\<le> 1"
    using w_in unfolding period_parallelogram_def
    by auto
  moreover have "x\<noteq>0" 
  proof
    assume "x = 0"
    then have "w = of_real y * \<omega>2" using w_eq by auto
    then have "w\<in>closed_segment 0 \<omega>2"
      using y 
      by (metis add.left_neutral in_segment(1) 
          scaleR_conv_of_real scale_zero_right)
    then have "w\<in>path_image (path_of_parallelogram \<omega>1 \<omega>2)" 
      unfolding path_of_parallelogram_def
      by (simp add: closed_segment_commute path_image_join)
    then show False using w_in by auto
  qed
  moreover have "x\<noteq>1"
  proof 
    assume "x = 1"
    then have "w = \<omega>1 + of_real y * \<omega>2" using w_eq by auto
    then have "w\<in>closed_segment \<omega>1 (\<omega>1 + \<omega>2)"
      using y unfolding in_segment
      by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1) 
          scaleR_add_right scaleR_collapse scaleR_conv_of_real)
    then have "w\<in>path_image (path_of_parallelogram \<omega>1 \<omega>2)" 
      unfolding path_of_parallelogram_def
      by (simp add: closed_segment_commute path_image_join)
    then show False using w_in by auto
  qed
  moreover have "y\<noteq>0" 
  proof
    assume "y = 0"
    then have "w = of_real x * \<omega>1" using w_eq by auto
    then have "w\<in>closed_segment 0 \<omega>1"
      using x
      by (metis add.left_neutral in_segment(1) 
          scaleR_conv_of_real scale_zero_right)
    then have "w\<in>path_image (path_of_parallelogram \<omega>1 \<omega>2)" 
      unfolding path_of_parallelogram_def
      by (simp add: closed_segment_commute path_image_join)
    then show False using w_in by auto
  qed
  moreover have "y\<noteq>1" 
  proof
    assume "y = 1"
    then have "w = of_real x * \<omega>1 + \<omega>2" using w_eq by auto
    then have "w\<in>closed_segment (\<omega>1+\<omega>2) \<omega>2"
      using x unfolding in_segment
      by (smt (verit, ccfv_threshold) ab_semigroup_add_class.add_ac(1) 
          scaleR_add_right scaleR_collapse scaleR_conv_of_real)
    then have "w\<in>path_image (path_of_parallelogram \<omega>1 \<omega>2)" 
      unfolding path_of_parallelogram_def
      by (simp add: closed_segment_commute path_image_join)
    then show False using w_in by auto
  qed
  ultimately show ?thesis using that by auto
qed

lemma period_parallelogram_interior_Im_neg:
  assumes w_in: "w \<in> (period_parallelogram \<omega>1 \<omega>2 0 0)
                       - path_image (path_of_parallelogram \<omega>1 \<omega>2)"
  shows "Im (\<omega>1 * cnj w) * Im (\<omega>2 * cnj w) < 0"
proof -
  obtain x y where w_eq:"w = of_real x * \<omega>1 + of_real y * \<omega>2"
                and x:"0<x \<and> x<1" and y:"0<y \<and> y< 1"
    using w_in period_parallelogram_interior_eq
    by metis
  define w1 w2 w12 where "w1 = \<omega>1 * cnj \<omega>1" 
                     and "w2 = \<omega>2 * cnj \<omega>2"  
                     and "w12 = \<omega>1 * cnj \<omega>2" 

  have "Im (\<omega>1 * cnj w) * Im (\<omega>2 * cnj w)
        = Im (x * w1 + y * w12) * Im (x * cnj w12 + y * w2)"
    unfolding w_eq w1_def w2_def w12_def
    by (simp add:algebra_simps)
  also have "\<dots> = Im ( y * w12) * Im (x * cnj w12 )"
    unfolding w1_def w2_def by auto
  also have "\<dots> = - x * y * (Im w12)^2"
    by (simp add: power2_eq_square)
  finally have "Im (\<omega>1 * cnj w) * Im (\<omega>2 * cnj w) = - x * y * (Im w12)\<^sup>2 " .
  moreover have "- x * y * (Im w12)\<^sup>2  < 0"
  proof -
    have "Im w12 \<noteq> 0" 
    proof 
      assume asm:"Im w12 = 0"
      have "\<omega>2 \<noteq> 0" "\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2"
        using period_parallelogram_interior_imp w_in 
        by blast+
      with Im_cnj_imp_lined \<open>Im w12 = 0\<close>
      have "\<exists>r. \<omega>1 = r *\<^sub>R \<omega>2"
        unfolding w12_def by auto
      with \<open>\<forall>r. \<omega>1 \<noteq> r *\<^sub>R \<omega>2\<close> show False by auto
    qed
    with x y show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma winding_number_linepath_neg_lt:
    assumes "0 < Im ((a - b) * cnj (a - z))"
      shows "Re(winding_number(linepath a b) z) < 0"
proof -
  have z: "z \<notin> path_image (linepath a b)"
    using assms
    by (simp add: closed_segment_def) (force simp: algebra_simps)
  
  have "Re(winding_number(linepath a b) z) = 
          - Re(winding_number(reversepath (linepath a b)) z)"
    apply (subst winding_number_reversepath)
    using z by auto
  also have "\<dots> = - Re(winding_number(linepath b a) z)"
    by simp
  finally have "Re (winding_number (linepath a b) z)  
      = - Re (winding_number (linepath b a) z)" .
  moreover have "0 < Re (winding_number (linepath b a) z)"
    using winding_number_linepath_pos_lt[OF assms] .
  ultimately show ?thesis by auto
qed

lemma winding_number_parallelogram_inside:
  assumes w_in:"w \<in> (period_parallelogram \<omega>1 \<omega>2 0 0) 
                    - path_image (path_of_parallelogram \<omega>1 \<omega>2)"
  shows "Im (\<omega>1 * cnj \<omega>2) <0 
          \<Longrightarrow> winding_number (path_of_parallelogram \<omega>1 \<omega>2) w = 1"
    and "Im (\<omega>1 * cnj \<omega>2) >0 
          \<Longrightarrow> winding_number (path_of_parallelogram \<omega>1 \<omega>2) w = -1"
proof -
   obtain x y where w_eq:"w = of_real x * \<omega>1 + of_real y * \<omega>2"
                and x:"0<x \<and> x<1" and y:"0<y \<and> y< 1"
    using w_in period_parallelogram_interior_eq
    by metis
  have "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0"
    using period_parallelogram_interior_imp w_in by blast+

  define W where "W=winding_number (path_of_parallelogram \<omega>1 \<omega>2) w"

  have W_simple:"W \<in> {- 1, 0, 1}" unfolding W_def
  proof (rule simple_closed_path_winding_number_cases)
    show "simple_path (path_of_parallelogram \<omega>1 \<omega>2)"
      apply (rule simple_path_parallelogram)
      using period_parallelogram_interior_imp w_in by blast
  qed (use w_in in auto)
     
  let ?w1 = "winding_number (linepath 0 \<omega>1) w" and 
      ?w2 = "winding_number (linepath \<omega>1 (\<omega>1 + \<omega>2)) w" and 
      ?w3 = "winding_number (linepath (\<omega>1 + \<omega>2) \<omega>2) w" and  
      ?w4 = "winding_number (linepath \<omega>2 0) w"
  define w1 w2 w12 where "w1 = \<omega>1 * cnj \<omega>1" 
                     and "w2 = \<omega>2 * cnj \<omega>2"  
                     and "w12 = \<omega>1 * cnj \<omega>2" 
  show "W = 1"
    if "Im (\<omega>1 * cnj \<omega>2) <0"
  proof -
    have "W = ?w1 + ?w2 + ?w3 + ?w4"
      using w_in unfolding W_def path_of_parallelogram_def 
      by (auto simp add:winding_number_join path_image_join)
    moreover have "Re(?w1) > 0"
    proof (rule winding_number_linepath_pos_lt)
      have "Im (\<omega>1* cnj (\<omega>1 - w)) = Im ((1-x)*w1 - y*w12)"
        unfolding w_eq w1_def w12_def by (auto simp:algebra_simps)
      moreover have "Im ((1-x)*w1) = 0" 
        unfolding w1_def by simp
      moreover have "Im (y*w12) <0" 
        using y that unfolding w12_def 
        using mult_pos_neg by force
      ultimately show " 0 < Im ((\<omega>1 - 0) * cnj (\<omega>1 - w))" by auto
    qed
    moreover have "Re(?w2) > 0"
    proof (rule winding_number_linepath_pos_lt)
      have "Im (\<omega>2* cnj (\<omega>1+\<omega>2 - w)) = Im ((1-y)*w2 + (1-x)*cnj w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im ((1-x)*w2) = 0" 
        unfolding w2_def by simp
      moreover have "Im ((1-x)*cnj w12) >0" 
        using x that unfolding w12_def by auto
      ultimately show "0 < Im ((\<omega>1 + \<omega>2 - \<omega>1) * cnj (\<omega>1 + \<omega>2 - w))" by auto
    qed
    moreover have "Re(?w3) > 0"
    proof (rule winding_number_linepath_pos_lt)
      have "Im (- \<omega>1* cnj (\<omega>2 - w)) = Im (x*w1 - (1-y)* w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im (x*w1) = 0" 
        unfolding w1_def by simp
      moreover have "Im ((1-y)* w12) <0" 
        using y that unfolding w12_def 
        by (metis diff_gt_0_iff_gt mult_less_0_iff scaleR_complex.simps(2)
              scaleR_conv_of_real)
      ultimately show "0 < Im ((\<omega>2 - (\<omega>1 + \<omega>2)) * cnj (\<omega>2 - w))" 
        by auto
    qed
    moreover have "Re(?w4) > 0"
    proof (rule winding_number_linepath_pos_lt)
      have "Im (\<omega>2 * cnj w) = Im (y*w2 + x * cnj w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im (y*w2) = 0" 
        unfolding w2_def by simp
      moreover have "Im (x * cnj w12) >0" 
        using x that unfolding w12_def 
        by auto
      ultimately show "0 < Im ((0 - \<omega>2) * cnj (0 - w))" 
        by auto
    qed
    ultimately have "Re W > 0"
      by auto
    then show "W=1" using W_simple by auto
  qed

  show "W = -1"
    if "Im (\<omega>1 * cnj \<omega>2) >0"
  proof -
    have "W = ?w1 + ?w2 + ?w3 + ?w4"
      using w_in unfolding W_def path_of_parallelogram_def 
      by (auto simp add:winding_number_join path_image_join)
    moreover have "Re(?w1) < 0"
    proof (rule winding_number_linepath_neg_lt)
      have "Im (\<omega>1* cnj (w)) = Im (x*w1 + y*w12)"
        unfolding w_eq w1_def w12_def 
        by (auto simp:algebra_simps)
      moreover have "Im (y*w12) >0" 
        using y that unfolding w12_def 
        using mult_pos_neg by force
      ultimately show " 0 < Im ((0 - \<omega>1) * cnj (0 - w))" 
        unfolding w1_def by auto
    qed
    moreover have "Re(?w2) < 0"
    proof (rule winding_number_linepath_neg_lt)
      have "Im (- \<omega>2* cnj (\<omega>1 - w)) = Im (-y*w2 - (1-x)*cnj w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im (- (1-x)*cnj w12) >0" 
        using x that unfolding w12_def 
        using zero_less_mult_iff by fastforce
      ultimately show " 0 < Im ((\<omega>1 - (\<omega>1 + \<omega>2)) * cnj (\<omega>1 - w))" 
        unfolding w2_def 
        using mult_less_0_iff that w12_def x by fastforce
    qed
    moreover have "Re(?w3) < 0"
    proof (rule winding_number_linepath_neg_lt)
      have "Im (\<omega>1* cnj (\<omega>1+\<omega>2 - w)) = Im ((1-x)*w1 + (1-y)* w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im ((1-y)* w12) >0" 
        using y that unfolding w12_def by auto
      ultimately show "0 < Im ((\<omega>1 + \<omega>2 - \<omega>2) * cnj (\<omega>1 + \<omega>2 - w))" 
        unfolding w1_def by auto
    qed
    moreover have "Re(?w4) < 0"
    proof (rule winding_number_linepath_neg_lt)
      have "Im (\<omega>2 * cnj (\<omega>2 - w)) = Im ((1+y)*w2 - x * cnj w12)"
        unfolding w_eq w1_def w2_def w12_def by (auto simp:algebra_simps)
      moreover have "Im (- x * cnj w12) >0" 
        using x that unfolding w12_def 
        by (metis add.inverse_inverse cnj.simps(2) minus_mult_commute 
            mult_pos_pos scaleR_complex.simps(2) scaleR_conv_of_real)
      ultimately show "0 < Im ((\<omega>2 - 0) * cnj (\<omega>2 - w))" 
        unfolding w2_def by auto
    qed
    ultimately have "Re W < 0"
      by auto
    then show "W=-1" using W_simple by auto
  qed
qed

context gen_lattice
begin

lemma boundary_of_period_parallelogram_altdef:
  "boundary_of_period_parallelogram \<omega>1 \<omega>2 m n =
      of_\<omega>12_coords ` ({m,m+1} \<times> {n..n+1} \<union> {m..m+1} \<times> {n,n+1})"
proof -
  define f where "f=(+) (of_int m * \<omega>1 + of_int n * \<omega>2)"

  have f_coords:
    "f 0 = of_\<omega>12_coords (of_int m,of_int n)"
    "f \<omega>1 = of_\<omega>12_coords (of_int m+1,of_int n)"
    "f (\<omega>1+ \<omega>2) = of_\<omega>12_coords (of_int m+1,of_int n+1)"
    "f ( \<omega>2) = of_\<omega>12_coords (of_int m,of_int n+1)"
    unfolding f_def of_\<omega>12_coords_def 
    by (auto simp:algebra_simps)
  have f_comp:"f (linepath a b x) = linepath (f a) (f b) x" for a b x
    unfolding linepath_def f_def comp_def scaleR_conv_of_real
    by (auto simp:algebra_simps)

  have "boundary_of_period_parallelogram \<omega>1 \<omega>2 m n
          = path_image (f \<circ> path_of_parallelogram \<omega>1 \<omega>2)"
    unfolding boundary_of_period_parallelogram_def f_def by simp
  also have "\<dots> = path_image (linepath (f 0) (f \<omega>1) +++
      linepath (f \<omega>1) (f (\<omega>1 + \<omega>2)) +++ linepath (f (\<omega>1 + \<omega>2)) (f \<omega>2)
       +++ linepath (f \<omega>2) (f 0))"
    unfolding path_image_def 
    apply (rule image_cong)
    by (simp_all add:path_of_parallelogram_def comp_def joinpaths_def 
          f_comp del: linepath_0)
   also have "\<dots> = of_\<omega>12_coords ` path_image
     (linepath (real_of_int m, real_of_int n) 
        (real_of_int m + 1, real_of_int n) 
      +++
      linepath (real_of_int m + 1, real_of_int n)
        (real_of_int m + 1, real_of_int n + 1) 
      +++
      linepath (real_of_int m + 1, real_of_int n + 1) 
        (real_of_int m, real_of_int n + 1)
       +++
      linepath (real_of_int m, real_of_int n + 1) 
        (real_of_int m, real_of_int n))"
    by (simp flip:path_image_compose add:f_coords 
        of_\<omega>12_coords_linepath' path_compose_join 
        path_image_compose)
  also have "\<dots> = of_\<omega>12_coords ` 
                    ({of_int m,of_int m+1} \<times> {real_of_int n..of_int n+1} 
                    \<union> {of_int m..of_int m+1} \<times> {of_int n,of_int n+1})"
  proof - (* TODO: Can this proof be improved? *)
    have ccontr1:"\<forall>u\<le>1. 0 \<le> u \<longrightarrow> b + u \<noteq> 1 + real_of_int n \<Longrightarrow> False" 
      if "real_of_int n \<le> b" "b \<le> 1 + real_of_int n"for b n 
      by (smt (verit) diff_ge_0_iff_ge that(1) that(2))
    have ccontr2:"\<forall>u\<le>1. 0 \<le> u \<longrightarrow> b \<noteq> u + real_of_int n  \<Longrightarrow> False"
      if "real_of_int n \<le> b" "b \<le> 1 + real_of_int n"
      for b n 
      by (metis add.commute add_le_cancel_left diff_add_cancel 
          diff_ge_0_iff_ge that(1) that(2))
    show ?thesis
    apply (intro image_cong)
    apply (auto simp add:path_image_join in_segment algebra_simps 
            dest:ccontr1 ccontr2)
      by (meson ccontr1)
  qed
  finally show ?thesis .
qed

lemma UN_parallelogram_UNIV: "(\<Union>m n. period_parallelogram \<omega>1 \<omega>2 m n) = UNIV"
proof -
  have "\<exists>m n. z \<in> period_parallelogram \<omega>1 \<omega>2 m n" for z
  proof -
    have "z \<in> span {\<omega>1,\<omega>2}"
      by (simp add: span12)
    then obtain t1 t2 where t12: "z = of_real t1 * \<omega>1 + of_real t2 * \<omega>2"
      by (metis add.commute diff_add_cancel right_minus_eq 
          scaleR_conv_of_real singletonD span_breakdown_eq span_empty)
    have "z \<in> period_parallelogram \<omega>1 \<omega>2 (floor t1) (floor t2)"
      unfolding period_parallelogram_def t12
      using of_int_floor_le real_of_int_floor_add_one_ge by fastforce
    then show ?thesis
      by metis
  qed
  then show ?thesis
    by auto
qed

(* TODO: rewrite using \<omega>12_coords *)
lemma in_parallelogram: "x \<in> period_parallelogram \<omega>1 \<omega>2 m n 
    \<Longrightarrow> (m'-m) * \<omega>1 + (n'-n) * \<omega>2 + x \<in> period_parallelogram \<omega>1 \<omega>2 m' n'"
  unfolding period_parallelogram_def
  apply safe
  apply (rule_tac x="xa+m'-m" in exI)
  apply (rule_tac x="y+n'-n" in exI)
  apply (simp add: algebra_simps)
  done

lemma in_parallelogram': "x \<in> period_parallelogram' \<omega>1 \<omega>2 m n
     \<Longrightarrow> (m'-m) * \<omega>1 + (n'-n) * \<omega>2 + x \<in> period_parallelogram' \<omega>1 \<omega>2 m' n'"
  unfolding period_parallelogram'_def
  apply safe
  apply (rule_tac x="xa+m'-m" in exI)
  apply (rule_tac x="y+n'-n" in exI)
  apply (simp add: algebra_simps)
  done

lemma in_parallelogram_iff: "x \<in> period_parallelogram \<omega>1 \<omega>2 m n 
    \<longleftrightarrow> (m'-m) * \<omega>1 + (n'-n) * \<omega>2 + x \<in> period_parallelogram \<omega>1 \<omega>2 m' n'"
  by (smt (z3) in_parallelogram add_diff_cancel add_diff_cancel_left' 
      minus_diff_eq mult_minus_left uminus_add_conv_diff)

lemma in_parallelogram'_iff: "x \<in> period_parallelogram' \<omega>1 \<omega>2 m n 
    \<longleftrightarrow> (m'-m) * \<omega>1 + (n'-n) * \<omega>2 + x \<in> period_parallelogram' \<omega>1 \<omega>2 m' n'"
  by (smt (z3) in_parallelogram' add_diff_cancel add_diff_cancel_left' 
      minus_diff_eq mult_minus_left uminus_add_conv_diff)

lemma f_parallelograms_map:
   "(+) ((m' - m) * \<omega>1 + (n' - n) * \<omega>2) ` period_parallelogram \<omega>1 \<omega>2 m n 
    = period_parallelogram \<omega>1 \<omega>2 m' n'" (is "?lhs = ?rhs")
  by (force simp: set_eq_iff image_iff algebra_simps in_parallelogram_iff [of _ m' n' m n])

lemma f_parallelograms'_map:
   "(+) ((m' - m) * \<omega>1 + (n' - n) * \<omega>2) ` period_parallelogram' \<omega>1 \<omega>2 m n
     = period_parallelogram' \<omega>1 \<omega>2 m' n'" (is "?lhs = ?rhs")
  by (force simp: set_eq_iff image_iff algebra_simps in_parallelogram'_iff [of _ m' n' m n])

lemma f_parallelograms_eq: 
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "f ` period_parallelogram \<omega>1 \<omega>2 m n = f ` period_parallelogram \<omega>1 \<omega>2 m' n'"
proof -
  have "f ` period_parallelogram \<omega>1 \<omega>2 m n 
      = f ` (+) ((m-m') * \<omega>1 + (n-n') * \<omega>2) ` period_parallelogram \<omega>1 \<omega>2 m' n'"
    by (simp add: f_parallelograms_map)
  also have "\<dots> = f ` period_parallelogram \<omega>1 \<omega>2 m' n'"
    by (meson assms is_doubly_periodic_image)
  finally show ?thesis .
qed

lemma f_parallelograms'_eq: 
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "f ` period_parallelogram' \<omega>1 \<omega>2 m n = f ` period_parallelogram' \<omega>1 \<omega>2 m' n'"
proof -
  have "f ` period_parallelogram' \<omega>1 \<omega>2 m n 
      = f ` (+) ((m-m') * \<omega>1 + (n-n') * \<omega>2) ` period_parallelogram' \<omega>1 \<omega>2 m' n'"
    by (simp add: f_parallelograms'_map)
  also have "\<dots> = f ` period_parallelogram' \<omega>1 \<omega>2 m' n'"
    by (meson assms is_doubly_periodic_image)
  finally show ?thesis .
qed

lemma f_parallelogram:
  assumes is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "f ` period_parallelogram \<omega>1 \<omega>2 m n = range f"
proof -
  have "f z \<in> f ` period_parallelogram \<omega>1 \<omega>2 m n" for z
  proof -
    have "z \<in> span {\<omega>1,\<omega>2}"
      by (simp add: span12)
    then obtain t1 t2 where t12: "z = of_real t1 * \<omega>1 + of_real t2 * \<omega>2"
      by (metis add.commute diff_add_cancel right_minus_eq 
          scaleR_conv_of_real singletonD span_breakdown_eq span_empty)
    have "z \<in> period_parallelogram \<omega>1 \<omega>2 (floor t1) (floor t2)"
      by (force simp: period_parallelogram_def t12)
    then show ?thesis
      using f_parallelograms_eq is_doubly_periodic by blast
  qed
  then show ?thesis
    by auto
qed

lemma f_parallelogram':
  assumes is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "f ` period_parallelogram' \<omega>1 \<omega>2 m n = range f"
proof -
  have "f z \<in> f ` period_parallelogram' \<omega>1 \<omega>2 m n" for z
  proof -
    have "z \<in> span {\<omega>1,\<omega>2}"
      by (simp add: span12)
    then obtain t1 t2 where t12: "z = of_real t1 * \<omega>1 + of_real t2 * \<omega>2"
      by (metis add.commute diff_add_cancel right_minus_eq 
          scaleR_conv_of_real singletonD span_breakdown_eq span_empty)
    have "z \<in> period_parallelogram' \<omega>1 \<omega>2 (floor t1) (floor t2)"
      by (force simp: period_parallelogram'_def t12)
    then show ?thesis
      using f_parallelograms'_eq is_doubly_periodic by blast
  qed
  then show ?thesis
    by auto
qed

end

locale elliptic_fun' =
  fixes f:: "complex \<Rightarrow> complex" and \<omega>1 \<omega>2:: complex
  assumes is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 f" 
      and is_meromorphic: "f meromorphic_on UNIV"

locale elliptic_fun = elliptic_fun'+
  assumes nicely_mero:"(\<forall>z. (is_pole f z \<and> f z=0) \<or> f \<midarrow>z\<rightarrow> f z)"
begin

lemma nicely_meromorphic:"f nicely_meromorphic_on UNIV"
  using nicely_mero elliptic_fun_axioms 
    is_meromorphic nicely_meromorphic_on_def 
  by force

end

sublocale elliptic_fun' \<subseteq> gen_lattice
proof
  show "Im (\<omega>2/\<omega>1) \<noteq> 0"
    by (meson is_doubly_periodic is_doubly_periodic_def)
qed

lemma is_periodic_deriv_quotient:
  assumes per: "is_periodic \<omega> f"
  shows "is_periodic \<omega> (\<lambda>z. deriv f z / f z)"
proof -
  have "deriv f (z + \<omega>) / f (z + \<omega>) = deriv f z / f z"  for z
  proof -
    have "\<forall>\<^sub>F x in nhds 0. f ((z + x) + \<omega>) = f (z + x)"
      using per unfolding is_periodic_def by auto
    then have "deriv f (z + \<omega>) = deriv f z"
      apply (subst (1 2) deriv_shift_0)
      by (auto intro!: deriv_cong_ev simp:algebra_simps)  
    then show ?thesis
      using per by (simp add: is_periodic_def)
  qed
  then show ?thesis unfolding is_periodic_def by auto
qed

lemma is_periodic_is_pole:
  fixes f ::"'a :: real_normed_vector
                 \<Rightarrow> 'b::real_normed_vector"
  assumes "is_periodic \<omega> f"
  shows   "is_periodic \<omega> (is_pole f)"
  unfolding is_periodic_def
proof
  fix z :: 'a
  have "f (z + \<omega> + x) = f (z + x)" for x
    using is_periodicD[OF assms, of "z + x"] 
    by (simp add: algebra_simps)
  thus "is_pole f (z + \<omega>) = is_pole f z"
    by (subst (1 2) is_pole_shift_0) auto
qed

lemma is_periodic_is_zero:
  fixes f ::"'a :: real_normed_vector
                 \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "is_periodic \<omega> f"
  shows   "is_periodic \<omega> (is_zero f)"
proof -
  have "(f \<longlongrightarrow> 0) (nhds (z + \<omega>)) 
          = (f \<longlongrightarrow> 0) (nhds z)" for z
  proof -
    have "\<And>x. f ((z + x) + \<omega> ) = f (z + x)"
      by (metis assms is_periodicD)
    then have "((\<lambda>x. f (z + \<omega> + x)) \<longlongrightarrow> 0) (nhds 0) =
        ((\<lambda>x. f (z + x)) \<longlongrightarrow> 0) (nhds 0)" 
      by (auto intro!: tendsto_cong eventuallyI 
          simp:algebra_simps)
    then show ?thesis
      by (simp add:nhds_to_0' filterlim_filtermap)
  qed
  moreover have " (\<forall>\<^sub>F x in at (z + \<omega>). f x \<noteq> 0)
          = (\<forall>\<^sub>F x in at z. f x \<noteq> 0)" for z
  proof -
    have "(\<forall>\<^sub>F x in at (z + \<omega>). f x \<noteq> 0)
        =  (\<forall>\<^sub>F x in at 0. f (x + (z + \<omega>)) \<noteq> 0)"
      by (subst at_to_0;subst eventually_filtermap;rule refl)
    also have "... = (\<forall>\<^sub>F x in at 0. f (x + z ) \<noteq> 0)"
      apply (intro eventually_subst eventuallyI)
      by (metis ab_semigroup_add_class.add_ac(1) 
          assms is_periodicD)
    also have "... = (\<forall>\<^sub>F x in at z. f x \<noteq> 0)" 
      by (subst at_to_0;subst eventually_filtermap;rule refl)
    finally show ?thesis .
  qed
  ultimately show ?thesis 
    unfolding is_zero_def is_periodic_def by blast
qed

context elliptic_fun'
begin

lemma is_doubly_periodic_is_pole:
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f"
  shows   "is_doubly_periodic \<omega>1 \<omega>2 (is_pole f)"
  using assms by (auto intro!: is_periodic_is_pole 
      simp: ratio_notin_real is_doubly_periodic_def)

lemma is_doubly_periodic_is_zero:
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f"
  shows   "is_doubly_periodic \<omega>1 \<omega>2 (is_zero f)"
  using assms by (auto intro!: is_periodic_is_zero 
      simp: ratio_notin_real is_doubly_periodic_def)

lemma is_periodic_zorder:
  assumes "is_periodic \<omega> f"
  shows   "is_periodic \<omega> (zorder f)"
  unfolding is_periodic_def
proof
  fix z :: complex
  have "f (x + (z + \<omega>)) = f (x + z)" for x
    using is_periodicD[OF assms, of "z + x"] by (simp add: algebra_simps)
  thus "zorder f (z + \<omega>) = zorder f z"
    by (subst (1 2) zorder_shift) auto
qed

lemma is_doubly_periodic_zorder:
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f"
  shows   "is_doubly_periodic \<omega>1 \<omega>2 (zorder f)"
  using assms by (auto intro!: is_periodic_zorder simp: ratio_notin_real is_doubly_periodic_def)

lemma is_periodic_mnf: "is_periodic (of_int m * \<omega>1 + of_int n * \<omega>2) f"
  by (simp add: is_doubly_periodic omegaI omega_is_periodic)

lemma is_zero_mnf_iff: "f (z + (of_int m * \<omega>1 + of_int n * \<omega>2)) = 0 \<longleftrightarrow> f z = 0"
  by (metis is_periodic_def is_periodic_mnf)

lemma is_pole_mnf_iff: "is_pole f (z + (of_int m * \<omega>1 + of_int n * \<omega>2)) \<longleftrightarrow> is_pole f z"
  by (simp add: is_periodic_mnf is_periodic_pole_plus)

lemma isolated_singularity_at [intro,simp]: "isolated_singularity_at f z"
  using is_meromorphic meromorphic_on_altdef by blast

(* Theorem 1.4 *)
theorem no_pole_in_some_period_parallelogram_implies_no_poles:
  fixes m n:: int 
  assumes "\<And>z. z \<in> period_parallelogram' \<omega>1 \<omega>2 m n \<Longrightarrow> \<not> is_pole f z"
  shows   "\<not>is_pole f z"
proof -
  define a where "a = \<lfloor>\<omega>1_coord z - m\<rfloor>"
  define b where "b = \<lfloor>\<omega>2_coord z - n\<rfloor>"
  have *: "is_periodic (of_\<omega>12_coords (-a, -b)) (is_pole f)"
    by (intro is_periodic_is_pole omega_is_periodic is_doubly_periodic)
       (auto simp: of_\<omega>12_coords_in_omega_iff)
  have "z + of_\<omega>12_coords (-a, -b) \<in> period_parallelogram' \<omega>1 \<omega>2 m n"
    unfolding period_parallelogram'_altdef of_\<omega>12_coords_image_eq
    by (auto simp: mem_Times_iff a_def b_def) linarith+
  hence "\<not>is_pole f (z + of_\<omega>12_coords (-a, -b))"
    by (rule assms)
  also have "is_pole f (z + of_\<omega>12_coords (-a, -b)) \<longleftrightarrow> is_pole f z"
    using is_periodicD[OF *, of z] by simp
  finally show ?thesis .
qed

theorem (in elliptic_fun) no_pole_in_some_period_parallelogram_implies_is_constant:
  fixes m n :: int 
  assumes "\<And>z. z \<in> period_parallelogram' \<omega>1 \<omega>2 m n \<Longrightarrow> \<not> is_pole f z"
  shows   "is_constant f"
proof -
  have "\<not>is_pole f z" for z
    by (rule no_pole_in_some_period_parallelogram_implies_no_poles[OF assms])
  then have "f analytic_on UNIV"
    using is_meromorphic nicely_mero nicely_meromorphic_on_def 
      nicely_meromorphic_without_singularities 
    by presburger
  thus ?thesis 
    by (simp add: analytic_imp_holomorphic 
        holomorphic_is_doubly_periodic_const is_doubly_periodic)
qed

text \<open>Theorem 1.5\<close>
corollary (in elliptic_fun) has_no_zero_in_some_period_parallelogram_implies_is_constant:
  fixes m n:: int
  assumes "\<And>z. z \<in> period_parallelogram' \<omega>1 \<omega>2 m n 
      \<Longrightarrow> \<not> is_zero f z"
  shows "is_constant f"
proof -
  define ff where "ff = (\<lambda>x. inverse (f x))"
  have ff_nicely:"ff nicely_meromorphic_on UNIV"
      by (simp add: ff_def nicely_meromorphic 
            nicely_meromorphic_on_inverse)

  interpret ff:elliptic_fun ff
  proof unfold_locales
    show "is_doubly_periodic \<omega>1 \<omega>2 ff"
      by (metis ff_def is_doubly_periodic 
          is_doubly_periodic_def is_periodic_def)
    from ff_nicely show "ff meromorphic_on UNIV"
      "\<forall>z. is_pole ff z \<and> ff z = 0 \<or> ff \<midarrow>z\<rightarrow> ff z"
      using nicely_meromorphic_on_def by auto
  qed

  have False if "z \<in> period_parallelogram' \<omega>1 \<omega>2 m n" 
    "is_pole ff z" for z
  proof -
    from ff_nicely have "ff z=0" 
      using is_pole_zero_at_nicely_mero that(2) by blast
    then have "f z =0" unfolding ff_def by auto
    then have "is_zero f z"
      using that(2) inverse_pole_imp_zero unfolding ff_def 
      by force
    moreover have "\<not> is_zero f z" using assms that(1) by auto
    ultimately show ?thesis by simp
  qed
  then have "is_constant ff"
    using ff.no_pole_in_some_period_parallelogram_implies_is_constant
    by auto
  then show ?thesis unfolding ff_def 
    by (metis (no_types, lifting) constant_on_def inverse_inverse_eq)
qed

text \<open>definition at bottom of page 5\<close>

text \<open>
  shifted period parallelogram with new origin @{term orig} and congruent to
  \<^const>\<open>period_parallelogram\<close>
\<close>

definition shifted_period_parallelogram :: "complex \<Rightarrow> complex set" where
  "shifted_period_parallelogram orig \<equiv> (+)orig ` period_parallelogram \<omega>1 \<omega>2 0 0" 

definition shifted_period_parallelogram' :: "complex \<Rightarrow> complex set" where
  "shifted_period_parallelogram' orig \<equiv> (+)orig ` period_parallelogram' \<omega>1 \<omega>2 0 0" 

lemma compact_shifted_parallelogram [intro]: "compact (shifted_period_parallelogram orig)"
  unfolding shifted_period_parallelogram_def
  by (intro compact_continuous_image continuous_intros) auto

definition contour_of_cell:: "real \<Rightarrow> complex" where
  "contour_of_cell \<equiv> path_of_parallelogram \<omega>1 \<omega>2"

definition shifted_contour_of_cell:: "complex \<Rightarrow> real \<Rightarrow> complex" where
  "shifted_contour_of_cell orig \<equiv> ((+) orig) \<circ> path_of_parallelogram \<omega>1 \<omega>2"

definition is_cell:: "complex \<Rightarrow> bool" where
  "is_cell orig \<equiv> (\<forall>z 
      \<in> path_image (shifted_contour_of_cell orig). 
        f z \<noteq> 0 \<and> f analytic_on {z})"

(*TODO: add to the library?*)
lemma closed_segment_altdef:
  "closed_segment a b 
        = {u *\<^sub>R a + (1-u) *\<^sub>R b |u. 0 \<le> u \<and> u \<le> 1}"
  unfolding closed_segment_def 
  by (metis (no_types, opaque_lifting) add_diff_cancel_right' 
                diff_ge_0_iff_ge le_add_diff_inverse)

lemma image_of_path_of_parallelogram:
  "path_image (path_of_parallelogram \<omega>1 \<omega>2)
      = of_\<omega>12_coords ` ({0,1} \<times> {0..1} \<union> {0..1} \<times> {0,1})"
proof -
  have "closed_segment 0 \<omega>1 = 
          of_\<omega>12_coords ` ({0..1} \<times> 0)"
       "closed_segment \<omega>1 (\<omega>1 + \<omega>2)
          =  of_\<omega>12_coords ` (1 \<times> {0..1})"
       
    unfolding of_\<omega>12_coords_def closed_segment_def
    by (auto intro!:image_eqI simp:scaleR_conv_of_real 
        algebra_simps)
  moreover have "closed_segment (\<omega>1 + \<omega>2) \<omega>2 
          =  of_\<omega>12_coords ` ({0..1} \<times> 1)"
       "closed_segment \<omega>2 0 =  of_\<omega>12_coords ` (0 \<times> {0..1})"
    unfolding of_\<omega>12_coords_def closed_segment_altdef
    by (auto intro!:image_eqI simp:scaleR_conv_of_real 
        algebra_simps)
  ultimately show ?thesis

  unfolding path_of_parallelogram_def 
  apply (subst path_image_join;simp)+
  by blast
qed

lemma shifted_period_parallelogram_eq_union:
  "shifted_period_parallelogram orig 
          = shifted_period_parallelogram' orig 
                \<union> path_image (shifted_contour_of_cell orig)"
proof -
  have "period_parallelogram \<omega>1 \<omega>2 0 0 = 
          period_parallelogram' \<omega>1 \<omega>2 0 0 \<union>
            path_image (path_of_parallelogram \<omega>1 \<omega>2)"
    unfolding period_parallelogram_altdef 
              period_parallelogram'_altdef
              image_of_path_of_parallelogram
    by fastforce
  then show ?thesis
    unfolding shifted_period_parallelogram'_def
      shifted_period_parallelogram_def
      shifted_contour_of_cell_def path_image_compose
    by auto
qed

lemma \<omega>12_coords_boundary_of_shifted_period_parallelogram:
   "\<omega>12_coords ` path_image (shifted_contour_of_cell orig) =
       {\<omega>1_coord orig, \<omega>1_coord orig + 1} \<times> {\<omega>2_coord orig..1 + \<omega>2_coord orig} \<union>
       {\<omega>1_coord orig..1 + \<omega>1_coord orig} \<times> {\<omega>2_coord orig, \<omega>2_coord orig + 1}" (is "_ = ?rhs")
proof -
  have *: "(+) z = map_prod ((+) (fst z)) ((+) (snd z))" for z :: "real \<times> real"
    by (cases z) (auto simp: fun_eq_iff)
  have "\<omega>12_coords ` path_image (shifted_contour_of_cell orig) =
          ((+) (\<omega>12_coords orig)) 
      ` \<omega>12_coords ` boundary_of_period_parallelogram \<omega>1 \<omega>2 0 0"
    unfolding shifted_contour_of_cell_def 
      boundary_of_period_parallelogram_def
    by (auto simp:path_image_compose intro!:image_eqI)
  also have "\<dots> = ?rhs"
    by (simp add: boundary_of_period_parallelogram_def 
        \<omega>12_coords_path_of_parallelogram * image_Un map_prod_image)
  finally show ?thesis .
qed

lemma shifted_period_parallelogram_altdef:
  "shifted_period_parallelogram orig =
     (let (a,b) = \<omega>12_coords orig in of_\<omega>12_coords ` ({a..a+1} \<times> {b..b+1}))"
proof -
  define a where "a = \<omega>1_coord orig"
  define b where "b = \<omega>2_coord orig"
  have "shifted_period_parallelogram orig =
          (of_\<omega>12_coords \<circ> (\<lambda>z. z + \<omega>12_coords orig)) ` ({0..1} \<times> {0..1})"
    by (simp add: o_def a_def b_def case_prod_unfold shifted_period_parallelogram_def
                  period_parallelogram_altdef image_image add_ac)
  also have "\<dots> = of_\<omega>12_coords ` (\<lambda>z. z + \<omega>12_coords orig) ` ({0..1} \<times> {0..1})"
    by (subst image_comp [symmetric]) simp
  also have "(\<lambda>z. z + \<omega>12_coords orig) = map_prod ((+) a) ((+) b)"
    by (auto simp: add_ac plus_prod_def a_def b_def)
  also have "\<dots> ` ({0..1} \<times> {0..1}) = {a..a+1} \<times> {b..b+1}"
    by (simp add: map_prod_image add_ac)
  finally show ?thesis
    by (simp add: a_def b_def case_prod_unfold Let_def)
qed

lemma shifted_period_parallelogram'_altdef:
  "shifted_period_parallelogram' orig =
     (let (a,b) = \<omega>12_coords orig in of_\<omega>12_coords ` ({a..<a+1} \<times> {b..<b+1}))"
proof -
  define a where "a = \<omega>1_coord orig"
  define b where "b = \<omega>2_coord orig"
  have "shifted_period_parallelogram' orig =
          (of_\<omega>12_coords \<circ> (\<lambda>z. z + \<omega>12_coords orig)) ` ({0..<1} \<times> {0..<1})"
    by (simp add: o_def a_def b_def case_prod_unfold shifted_period_parallelogram'_def
                  period_parallelogram'_altdef image_image add_ac)
  also have "\<dots> = of_\<omega>12_coords ` (\<lambda>z. z + \<omega>12_coords orig) ` ({0..<1} \<times> {0..<1})"
    by (subst image_comp [symmetric]) simp
  also have "(\<lambda>z. z + \<omega>12_coords orig) = map_prod ((+) a) ((+) b)"
    by (auto simp: add_ac plus_prod_def a_def b_def)
  also have "\<dots> ` ({0..<1} \<times> {0..<1}) = {a..<a+1} \<times> {b..<b+1}"
    by (simp add: map_prod_image add_ac)
  finally show ?thesis
    by (simp add: a_def b_def case_prod_unfold Let_def)
qed

lemma boundary_of_period_parallelogram:
  "boundary_of_period_parallelogram \<omega>1 \<omega>2 m n = path_image ((+)(m * \<omega>1 + n * \<omega>2) \<circ> contour_of_cell)"
  by (simp add: boundary_of_period_parallelogram_def contour_of_cell_def)

lemma valid_path_shifted_contour_of_cell[simp]:
  "valid_path (shifted_contour_of_cell orig)"
  unfolding shifted_contour_of_cell_def path_of_parallelogram_def valid_path_translation_eq 
  by auto

lemma valid_path_cell[simp]:"valid_path contour_of_cell"
  unfolding contour_of_cell_def path_of_parallelogram_def
  by auto

lemma pathfinish_contour_of_cell[simp]:
  "pathfinish contour_of_cell = 0"
  unfolding contour_of_cell_def path_of_parallelogram_def
  by simp

lemma pathstart_contour_of_cell[simp]:
  "pathstart contour_of_cell = 0"
  unfolding contour_of_cell_def path_of_parallelogram_def
  by simp

lemma pathfinish_shifted_contour_of_cell[simp]:
  "pathfinish (shifted_contour_of_cell orig) = orig"
  unfolding shifted_contour_of_cell_def 
  apply (subst pathfinish_translation)
  by simp

lemma pathstart_shifted_contour_of_cell[simp]:
  "pathstart (shifted_contour_of_cell orig) = orig"
  unfolding shifted_contour_of_cell_def 
  apply (subst pathstart_translation)
  by simp

lemma compact_boundary_of_period_parallelogram:
  "compact (boundary_of_period_parallelogram \<omega>1 \<omega>2 0 0)"
  unfolding boundary_of_period_parallelogram_def
  by (rule compact_path_image) (simp add: path_of_parallelogram_def)

lemma shifted_period_parallelogram_avoid:
  assumes "countable avoid"
  obtains orig where "path_image (shifted_contour_of_cell orig) \<inter> avoid = {}"
proof -
  define avoid' where "avoid' = \<omega>12_coords ` avoid"

  define avoid1 where "avoid1 = fst ` avoid'"
  define avoid2 where "avoid2 = snd ` avoid'"
  define avoid''
    where "avoid'' = (avoid1 \<union> (\<lambda>x. x - 1) ` avoid1) \<times> UNIV \<union> UNIV \<times> (avoid2 \<union> (\<lambda>x. x - 1) ` avoid2)"

  obtain orig where orig: "orig \<notin> avoid''"
  proof -
    have *: "avoid1 \<union> (\<lambda>x. x - 1) ` avoid1 \<in> null_sets lborel"
            "avoid2 \<union> (\<lambda>x. x - 1) ` avoid2 \<in> null_sets lborel"
      by (rule null_sets.Un; rule countable_imp_null_set_lborel;
          use assms in \<open>force simp: avoid1_def avoid2_def avoid'_def\<close>)+
    have "avoid'' \<in> null_sets lborel"
      unfolding lborel_prod[symmetric] avoid''_def using * by (intro null_sets.Un) auto
    hence "AE z in lborel. z \<notin> avoid''"
      using AE_not_in by blast
    from eventually_happens[OF this] show ?thesis using that
      by (auto simp: ae_filter_eq_bot_iff)
  qed

  have *: "(\<lambda>x. x - 1) ` X = ((+) 1) -` X" for X :: "real set"
    by force

  have fst_orig: "fst z \<notin> {fst orig, fst orig + 1}" if "z \<in> avoid'" for z
  proof
    assume"fst z \<in> {fst orig, fst orig + 1}"
    hence "orig \<in> (avoid1 \<union> (\<lambda>x. x - 1) ` avoid1) \<times> UNIV"
      using that unfolding avoid1_def * by (cases orig; cases z) force
    thus False using orig
      by (auto simp: avoid''_def)
  qed

  have snd_orig: "snd z \<notin> {snd orig, snd orig + 1}" if "z \<in> avoid'" for z
  proof
    assume "snd z \<in> {snd orig, snd orig + 1}"
    hence "orig \<in> UNIV \<times> (avoid2 \<union> (\<lambda>x. x - 1) ` avoid2)"
      using that unfolding avoid2_def * by (cases orig; cases z) force     
    thus False using orig
      by (auto simp: avoid''_def)
  qed

  show ?thesis
  proof (rule that[of "of_\<omega>12_coords orig"], safe)
    fix z assume z: "z \<in> path_image (shifted_contour_of_cell (of_\<omega>12_coords orig))" "z \<in> avoid"
    have "\<omega>12_coords z \<in> \<omega>12_coords `path_image (shifted_contour_of_cell (of_\<omega>12_coords orig))"
      using z(1) by blast
    thus "z \<in> {}" using z(2) fst_orig[of "\<omega>12_coords z"] snd_orig[of "\<omega>12_coords z"]
      unfolding \<omega>12_coords_boundary_of_shifted_period_parallelogram
      by (auto simp: avoid'_def)
  qed
qed

lemma shifted_period_parallelogram_avoid_wlog [consumes 1, case_names shift avoid]:
  assumes "\<And>z. \<not>z islimpt avoid"
  assumes "\<And>orig d. finite (shifted_period_parallelogram orig \<inter> avoid) \<Longrightarrow>
                    finite (shifted_period_parallelogram (orig + d) \<inter> avoid) \<Longrightarrow> 
                    P orig \<Longrightarrow> P (orig + d)"
  assumes "\<And>orig. finite (shifted_period_parallelogram orig \<inter> avoid) \<Longrightarrow>
                   path_image (shifted_contour_of_cell  orig) \<inter> avoid = {} \<Longrightarrow>
                   P orig"
  shows   "P orig"
proof -
  from assms have countable: "countable avoid"
    using no_limpt_imp_countable by blast

  from shifted_period_parallelogram_avoid[OF countable]
  obtain orig' where orig': "path_image (shifted_contour_of_cell  orig') 
        \<inter> avoid = {}"
      by blast
  define d where "d = \<omega>12_coords (orig - orig')"

  have "compact (shifted_period_parallelogram orig)" for orig
    unfolding shifted_period_parallelogram_def
    by (intro compact_continuous_image compact_parallelogram continuous_intros)
  hence fin: "finite (shifted_period_parallelogram orig \<inter> avoid)" for orig
    using assms by (intro finite_not_islimpt_in_compact) auto

  from orig' have "P orig'"
    by (intro assms fin)
  have "P (orig' + (orig - orig'))"
    by (rule assms(2)) fact+
  thus ?thesis
    by (simp add: algebra_simps)
qed

text \<open>Towards theorem 1.6. A cell has no poles along the boundary. 
But its vertices need not be periods!\<close>

lemma contour_integral_along_boundary_cell_is_zero_aux:
  fixes orig:: complex
  assumes "f holomorphic_on S" "open S" "path_image (shifted_contour_of_cell orig ) \<subseteq> S"
  shows "(f has_contour_integral 0) (shifted_contour_of_cell orig)"
  using assms
proof -
  define p1 where "p1 \<equiv> \<lambda>t. orig + linepath 0 \<omega>1 t"
  define p2 where "p2 \<equiv> \<lambda>t. orig + linepath \<omega>1 (\<omega>1 + \<omega>2) t"
  define p3 where "p3 \<equiv> \<lambda>t. orig + linepath (\<omega>1 + \<omega>2) \<omega>2 t"
  define p4 where "p4 \<equiv> \<lambda>t. orig + linepath \<omega>2 0 t"

  have cc:"shifted_contour_of_cell orig = p1+++p2+++p3+++p4"
    unfolding shifted_contour_of_cell_def path_of_parallelogram_def
      p1_def p2_def p3_def p4_def comp_def joinpaths_def
    by auto
  have [simp]: "pathfinish p1 = orig + \<omega>1" "pathstart p2 = pathfinish p1"
    by (auto simp add: pathfinish_def p1_def pathstart_def
        p2_def algebra_simps linepath_def)
  have [simp]: "pathfinish p2 = orig + \<omega>1 + \<omega>2" "pathstart p3 = pathfinish p2"
    by (auto simp add: pathfinish_def p2_def pathstart_def 
        p3_def algebra_simps linepath_def)
  have [simp]: "pathfinish p3 = orig + \<omega>2" "pathstart p4 = pathfinish p3"
    by (auto simp add: pathfinish_def p3_def pathstart_def 
        p4_def algebra_simps linepath_def)
  have pi_cc: "path_image (shifted_contour_of_cell orig) 
      = path_image p1 \<union> path_image p2 \<union> path_image p3 \<union> path_image p4"
    by (auto simp add: cc path_image_join)
  have vp: "valid_path p1" "valid_path p2" "valid_path p3" "valid_path p4"
    unfolding p1_def p2_def p3_def p4_def
    by (subst valid_path_translation_eq[of orig,unfolded comp_def],simp)+
  have "pathfinish p1 = pathstart p2" "pathfinish p3 = pathstart p4"
    by (auto simp: p1_def p2_def p3_def p4_def path_defs linepath_def)
  then have vpp: "valid_path (p1 +++ p2)" "valid_path (p3 +++ p4)"
    by (auto intro: valid_path_join vp)
  have diff34: "p3 differentiable at t" "p4 differentiable at t" for t
    unfolding p3_def p4_def linepath_def by (intro exI derivative_intros)+
  have cp1: "(f has_contour_integral contour_integral p1 f) p1"
    using assms contour_integrable_holomorphic_simple has_contour_integral_integral pi_cc vp(1) by auto
  have cp2: "(f has_contour_integral contour_integral p2 f) p2"
    using assms contour_integrable_holomorphic_simple has_contour_integral_integral pi_cc vp(2) by auto
  have cp3: "(f has_contour_integral contour_integral p3 f) p3"
    using assms contour_integrable_holomorphic_simple has_contour_integral_integral pi_cc vp(3) by auto
  have cp4: "(f has_contour_integral contour_integral p4 f) p4"
    using assms contour_integrable_holomorphic_simple has_contour_integral_integral pi_cc vp(4) by auto
  have "is_periodic \<omega>1 f" "is_periodic \<omega>2 f"
    using is_doubly_periodic is_doubly_periodic_def by blast+
  have f13: "f (p1 t) = f (reversepath p3 t)" if "0 \<le> t" "t \<le> 1" for t::real
    using \<open>is_periodic \<omega>2 f\<close> 
    apply (simp add: p1_def p3_def is_periodic_def reversepath_def 
            linepath_def algebra_simps)
    by (metis add.commute)
  have f24: "f (p2 t) = f (reversepath p4 t)" if "0 \<le> t" "t \<le> 1" for t::real
    apply (simp add: p2_def p4_def reversepath_def linepath_def algebra_simps)
    by (metis \<open>is_periodic \<omega>1 f\<close> add.commute is_periodic_def)
  have p3_o: "p3 \<circ> (-) 1 = (\<lambda>t. 2 * orig + \<omega>1 + \<omega>2 * 2 - p3 t)"
    by (auto simp: fun_eq_iff p3_def algebra_simps linepath_def)
  have p3_rev: "\<And>t. vector_derivative (reversepath p3) (at t) = - vector_derivative p3 (at t)" 
    by (simp add: reversepath_o p3_o diff34)
  have p3p1: "\<And>t. - vector_derivative p3 (at t) = vector_derivative p1 (at t)" 
    by (simp add: p1_def p3_def algebra_simps linepath_def)
  have "((\<lambda>t. f (p1 t) * vector_derivative (reversepath p3) (at t within {0..1})) has_integral
     contour_integral p1 f) {0..1}"
    using cp1
    by (simp add: has_contour_integral has_integral_localized_vector_derivative p3_rev p3p1)
  then have "(f has_contour_integral contour_integral p1 f) (reversepath p3)"
    unfolding has_contour_integral_def
    by (smt (verit, best) cp1 atLeastAtMost_iff f13 has_integral_eq)
  then have "contour_integral p1 f = - contour_integral p3 f"
    by (metis \<open>valid_path p3\<close> contour_integral_reversepath contour_integral_unique)
  moreover 
  have p4_o: "p4 \<circ> (-) 1 = (\<lambda>t. (2 * orig + \<omega>2) - p4 t)" 
    by (auto simp: fun_eq_iff p4_def algebra_simps linepath_def)
  have p4_rev: "\<And>t. vector_derivative (reversepath p4) (at t) = - vector_derivative p4 (at t)" 
    by (simp add: reversepath_o p4_o diff34)
  have p4p2: "\<And>t. - vector_derivative p4 (at t) = vector_derivative p2 (at t)" 
    by (simp add: p2_def p4_def algebra_simps linepath_def)
  have "((\<lambda>t. f (p2 t) * vector_derivative (reversepath p4) (at t within {0..1})) has_integral
     contour_integral p2 f) {0..1}"
    using cp2
    by (simp add: has_contour_integral has_integral_localized_vector_derivative p4_rev p4p2)
  then have "(f has_contour_integral contour_integral p2 f) (reversepath p4)"
    unfolding has_contour_integral_def
    by (smt (verit, best) cp1 atLeastAtMost_iff f24 has_integral_eq)
  then have "contour_integral p2 f = - contour_integral p4 f"
    by (metis \<open>valid_path p4\<close> contour_integral_reversepath contour_integral_unique)
  moreover have "(f has_contour_integral (contour_integral p1 f + (contour_integral p2 f + 
                                         (contour_integral p3 f + contour_integral p4 f)))) 
                  (shifted_contour_of_cell orig)"
    unfolding cc 
    apply (intro has_contour_integral_join)
    using cp1 cp2 cp3 cp4 vp vpp by auto
  ultimately show ?thesis by simp
qed

text \<open>theorem 1.6\<close>
theorem contour_integral_along_boundary_cell_is_zero:
  fixes orig:: complex
  assumes "is_cell orig"
  shows "(f has_contour_integral 0) (shifted_contour_of_cell orig )"
proof -
  obtain pts where pts:"pts sparse_in UNIV" "f analytic_on - pts"
    by (metis Compl_eq_Diff_UNIV is_meromorphic meromorphic_onE)
  define pts1 where "pts1 = pts 
      - path_image (shifted_contour_of_cell  orig)"
  have "f analytic_on - pts1"
    using assms pts(2) unfolding pts1_def is_cell_def 
    by (metis Compl_Diff_eq UnE analytic_on_analytic_at)
  have "pts1 sparse_in UNIV"
    by (metis Diff_subset pts(1) pts1_def sparse_in_subset2)

  have "path_image (shifted_contour_of_cell orig) \<subseteq> UNIV - pts1"
    unfolding pts1_def 
    by (simp add:  
        contour_of_cell_def shifted_contour_of_cell_def subsetI)
  moreover have "f holomorphic_on -pts1" 
    using \<open>f analytic_on - pts1\<close>
    by (simp add: analytic_imp_holomorphic)
  moreover have "open (-pts1)" 
    using \<open>pts1 sparse_in UNIV\<close>
    by (simp add: Compl_eq_Diff_UNIV open_diff_sparse_pts)
  ultimately show "(f has_contour_integral 0) (shifted_contour_of_cell orig)"
    using contour_integral_along_boundary_cell_is_zero_aux
    by auto
qed

definition zeros_in_period_parallelogram :: "complex \<Rightarrow> complex set" where
  "zeros_in_period_parallelogram orig =
     shifted_period_parallelogram' orig \<inter> {z. is_zero f z}"

definition poles_in_period_parallelogram :: "complex \<Rightarrow> complex set" where
  "poles_in_period_parallelogram orig =
     shifted_period_parallelogram' orig \<inter> {z. is_pole f z}"

lemma mostly_constant_imp_deriv_0:
  assumes "f mostly_constant_on A" "open A"
  shows "\<forall>\<^sub>\<approx>z\<in>A. (f has_field_derivative 0) (at z)"
proof -
  obtain c where "\<forall>x\<in>A. \<forall>\<^sub>F z in at x. f z = c" 
    using assms(1) unfolding eventually_cosparse_open_eq[OF \<open>open A\<close>] 
      mostly_constant_on_def
    by auto
  then have "\<forall>x\<in>A. \<forall>\<^sub>F z in at x. \<forall>\<^sub>F w in nhds z. f w = c"
    by (smt (verit) assms at_within_open 
          eventually_at_topological eventually_nhds_conv_at)
  then have "\<forall>x\<in>A. \<forall>\<^sub>F z in at x. (f has_field_derivative 0) (at z)"
    by (auto elim!: eventually_mono simp add: DERIV_cong_ev)
  then show ?thesis 
    unfolding eventually_cosparse_open_eq[OF \<open>open A\<close>] .
qed

lemma constant_imp_mostly_constant:
  assumes "f constant_on A - pts" "pts sparse_in A" "open A"
  shows "f mostly_constant_on A"
proof - 
  from \<open>f constant_on A - pts\<close> 
  obtain c where "\<forall>x\<in>A - pts. f x = c"
    unfolding constant_on_def by auto
  then have "{x\<in>A. f x \<noteq> c} \<subseteq> pts" by auto
  then have "{x\<in>A. f x \<noteq> c} sparse_in A"
    using assms(2) sparse_in_subset2 by auto
  then have "{x. f x \<noteq> c} sparse_in A"
    unfolding sparse_in_eventually_iff[OF \<open>open A\<close>] using \<open>open A\<close>
    by (smt (verit, best)  at_within_open 
        eventually_at_topological mem_Collect_eq)
  then show ?thesis
    unfolding mostly_constant_on_def constant_on_def 
    unfolding eventually_cosparse by auto
qed

lemma deriv_0_imp_mostly_constant:
  assumes "\<forall>\<^sub>\<approx>z\<in>A. (f has_field_derivative 0) (at z)" 
    "open A" "connected A"
  shows "f mostly_constant_on A"
proof -
  have "\<forall>x\<in>A. \<forall>\<^sub>F z in at x. (f has_field_derivative 0) (at z)"
    using assms(1) unfolding eventually_cosparse_open_eq[OF \<open>open A\<close>] .
  from get_sparse_from_eventually[OF this \<open>open A\<close>]
  obtain pts where pts:"pts sparse_in A" 
                   "\<forall>x\<in>A - pts. (f has_field_derivative 0) (at x)"
    .
  have "f constant_on A - pts"
  proof (rule has_field_derivative_0_imp_constant_on)
    show "connected (A - pts)" 
      by (simp add: assms(2) assms(3) pts(1) sparse_imp_connected)
    show "open (A - pts)"
      by (simp add: assms(2) open_diff_sparse_pts pts(1))
    show "\<And>z. z \<in> A - pts \<Longrightarrow> (f has_field_derivative 0) (at z)"
      using pts(2) by simp
  qed 
  then show ?thesis 
    using constant_imp_mostly_constant pts(1) \<open>open A\<close> by simp
qed

lemma deriv_meromorphic_not_zero_corsparse:
  assumes mero: "f meromorphic_on A" and A: "open A" "connected A"
  shows "f mostly_constant_on A \<or> (\<forall>\<^sub>\<approx>z\<in>A. deriv f z \<noteq> 0)"
proof -
  have "deriv f meromorphic_on A" using mero 
    by (intro meromorphic_intros)
  then have "(\<forall>\<^sub>\<approx>z\<in>A. deriv f z = 0) \<or> (\<forall>\<^sub>\<approx>z\<in>A. deriv f z \<noteq> 0)"
    using meromorphic_imp_constant_or_avoid[OF _ A] by simp
  moreover have "f mostly_constant_on A \<longleftrightarrow> (\<forall>\<^sub>\<approx>z\<in>A. deriv f z = 0)"
  proof 
    assume "f mostly_constant_on A"
    then have "\<forall>\<^sub>\<approx>z\<in>A. (f has_field_derivative 0) (at z)"
      using mostly_constant_imp_deriv_0 \<open>open A\<close> by simp
    then show "\<forall>\<^sub>\<approx>z\<in>A. deriv f z = 0" 
      apply (elim eventually_mono)
      using DERIV_imp_deriv by blast
  next
    assume "\<forall>\<^sub>\<approx>z\<in>A. deriv f z = 0"
    moreover have "\<forall>\<^sub>\<approx>z\<in>A. f field_differentiable at z" 
      using meromorphic_on_imp_analytic_cosparse[OF mero]
      apply (elim eventually_mono)
      by (simp add: analytic_on_imp_differentiable_at)
    ultimately have "\<forall>\<^sub>\<approx>z\<in>A. (f has_field_derivative 0) (at z)"
      apply eventually_elim
      by (metis field_differentiable_derivI)
    then show "f mostly_constant_on A"
      apply (elim deriv_0_imp_mostly_constant)
      by fact+
  qed
  ultimately show ?thesis by auto
qed

lemma (in elliptic_fun) cell_exists:
  assumes nonconst:"\<not> is_constant f"
  obtains orig where "is_cell orig"
proof -
  have "\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0"
    using nicely_meromorphic_imp_constant_or_avoid
        [OF nicely_meromorphic]
    by (meson Convex.connected_UNIV assms constant_on_def open_UNIV)
  then have "{x. f x =0} sparse_in UNIV"
    using eventually_cosparse by force
  then have "countable {x. f x =0}"
    using sparse_imp_countable
    by (metis inf_top_left open_UNIV)
  then obtain orig where
    "path_image (shifted_contour_of_cell orig)
          \<inter> ({z. f z = 0}) = {}"
    using shifted_period_parallelogram_avoid by blast
  moreover have "f analytic_on {z}" if "f z\<noteq>0" for z
    using is_pole_zero_at_nicely_mero 
      nicely_meromorphic 
      nicely_meromorphic_on_imp_analytic_at that
    by blast
  ultimately show ?thesis
    by (intro that[of orig]) (auto simp: is_cell_def)
qed

lemma period_parallelogram'_subset:
  "period_parallelogram' \<omega>1 \<omega>2 m n \<subseteq> period_parallelogram \<omega>1 \<omega>2 m n"
  unfolding period_parallelogram'_altdef period_parallelogram_altdef
  by (intro image_mono) auto

lemma boundary_of_shifted_period_parallelogram_altdef:
  "path_image (shifted_contour_of_cell orig) =
   (let (a, b) = \<omega>12_coords orig in of_\<omega>12_coords ` ({a,a+1}\<times>{b..b+1} \<union> {a..a+1}\<times>{b,b+1}))"
  (is "_ = ?rhs")
proof -
  have "of_\<omega>12_coords ` \<omega>12_coords ` path_image (shifted_contour_of_cell orig) = ?rhs"
    unfolding \<omega>12_coords_boundary_of_shifted_period_parallelogram[of orig] image_Un by auto
  thus ?thesis
    by (subst (asm) image_image) simp
qed

lemma shifted_period_parallelogram'_subset:
  "shifted_period_parallelogram' orig \<subseteq> shifted_period_parallelogram orig"
  unfolding shifted_period_parallelogram_def shifted_period_parallelogram'_def
            period_parallelogram_altdef period_parallelogram'_altdef
  by (intro image_mono) auto

lemma shifted_period_parallelogram_diff_on_boundary:
  "shifted_period_parallelogram orig - shifted_period_parallelogram' orig \<subseteq>
      path_image (shifted_contour_of_cell orig)"
proof -
  obtain a b where ab: "\<omega>12_coords orig = (a, b)"
    using prod.exhaust by metis
  have "shifted_period_parallelogram orig - shifted_period_parallelogram' orig =
             of_\<omega>12_coords ` ({a..a + 1} \<times> {b..b + 1} - {a..<a + 1} \<times> {b..<b + 1})"
    unfolding shifted_period_parallelogram_altdef shifted_period_parallelogram'_altdef ab
    by (subst image_set_diff) (auto intro!: injI simp: of_\<omega>12_coords_eq_iff)
  also have "{a..a+1} \<times> {b..b+1} - {a..<a+1} \<times> {b..<b+1} = {a+1} \<times> {b..b+1} \<union> {a..a+1} \<times> {b+1}"
    by auto
  also have "of_\<omega>12_coords ` \<dots> \<subseteq> path_image (shifted_contour_of_cell orig)"
    unfolding boundary_of_shifted_period_parallelogram_altdef ab by auto
  finally show ?thesis .
qed

lemma finite_zeros_in_pp [intro]: 
  shows "finite (zeros_in_period_parallelogram orig)"
proof -
  have "\<forall>\<^sub>\<approx>z\<in>UNIV. \<not>is_zero f z"
    by (rule meromorphic_on_imp_not_zero_cosparse)
       (simp add: is_meromorphic)
  then have "{x. is_zero f x} sparse_in 
      (shifted_period_parallelogram orig)"
    unfolding eventually_cosparse
    by (auto elim: sparse_in_subset)
  moreover have "compact (shifted_period_parallelogram orig)"
    by auto
  ultimately have "finite
     (shifted_period_parallelogram orig \<inter>
          {x. is_zero f x})"
    by (elim sparse_in_compact_finite)
  then show ?thesis
    apply (elim rev_finite_subset)
    using shifted_period_parallelogram'_subset 
          zeros_in_period_parallelogram_def 
    by auto    
qed

lemma finite_poles_in_pp [intro]: 
    "finite (poles_in_period_parallelogram orig)"
proof -
  have "\<forall>\<^sub>\<approx>z\<in>UNIV. \<not>is_pole f z"
    by (rule meromorphic_on_imp_not_pole_cosparse)
       (simp add: is_meromorphic)
  then have "{x. is_pole f x} sparse_in 
      (shifted_period_parallelogram orig)"
    unfolding eventually_cosparse
    by (auto elim: sparse_in_subset)
  moreover have "compact (shifted_period_parallelogram orig)"
    by auto
  ultimately have "finite
     (shifted_period_parallelogram orig \<inter>
          {x. is_pole f x})"
    by (elim sparse_in_compact_finite)
  then show ?thesis
    apply (elim rev_finite_subset)
    using shifted_period_parallelogram'_subset 
          poles_in_period_parallelogram_def 
    by auto    
qed

text \<open>Theorem 1.7\<close>

lemma not_pole_on_the_contour_of_cell:
  assumes "is_cell orig" 
    "w\<in>path_image (shifted_contour_of_cell orig)"
  shows "\<not> is_pole f w"
  using analytic_at_imp_no_pole assms(1) assms(2) is_cell_def
  by blast

lemma not_zero_on_the_contour_of_cell:
  assumes "is_cell orig" 
    "w\<in>path_image (shifted_contour_of_cell orig)"
  shows "\<not> is_zero f w"
  using assms zero_is_zero unfolding is_cell_def 
  by blast
  
theorem (in elliptic_fun) sum_residues_at_poles_in_period_parallelogram:
  fixes orig:: complex
  assumes "is_cell orig"
  shows "(\<Sum>z\<in>shifted_period_parallelogram' orig 
          \<inter> {x. is_pole f x}. residue f z) = 0"
proof -
  define pts where "pts = {x. is_pole f x}"
  define pts' where "pts' = shifted_period_parallelogram orig 
      \<inter> {x. is_pole f x}"
  define c_path where "c_path = shifted_contour_of_cell orig"

  have w_pts:"w-orig \<in> period_parallelogram \<omega>1 \<omega>2 0 0
                  - path_image (path_of_parallelogram \<omega>1 \<omega>2)"
    if "w\<in>pts'" for w
  proof -
    have "is_pole f w"
      using pts'_def using that by force
    then have "w-orig\<notin>path_image (path_of_parallelogram \<omega>1 \<omega>2)"
      using not_pole_on_the_contour_of_cell[OF assms]
      unfolding shifted_contour_of_cell_def
      by (metis add.commute diff_add_cancel image_eqI 
          path_image_compose)
    then show ?thesis
      using \<open>w\<in>pts'\<close>
      unfolding pts'_def shifted_period_parallelogram_def
      by auto
  qed

  have "contour_integral c_path f = (2 * pi) * \<i> *
          (\<Sum>p\<in>pts'. winding_number c_path p * residue f p)"
  proof (rule Residue_theorem[of "UNIV - (pts - pts')"])
    have "pts' \<subseteq> pts" unfolding pts'_def pts_def by auto
    have sparse:"pts sparse_in UNIV" unfolding pts_def
      by (simp add: not_islimpt_poles sparse_in_open)

    show "open (UNIV - (pts - pts'))" 
      by (meson Diff_subset open_UNIV 
          open_diff_sparse_pts sparse sparse_in_subset2)
    show "connected (UNIV - (pts - pts'))"
      by (metis Convex.connected_UNIV DIM_complex 
          Diff_subset open_UNIV order.refl 
          sparse sparse_imp_connected sparse_in_subset2)
    show "finite pts'" 
      unfolding pts'_def
      apply (rule sparse_in_compact_finite)
      subgoal by (metis UNIV_I pts_def sparse sparse_in_def)
      by (simp add: compact_shifted_parallelogram)
    
    have "f holomorphic_on - pts" 
      unfolding pts_def
      by (metis UNIV_I analytic_imp_holomorphic 
          analytic_on_analytic_at mem_Collect_eq 
          mem_simps(5) nicely_meromorphic 
          nicely_meromorphic_on_imp_analytic_at)
    then show "f holomorphic_on UNIV - (pts - pts') - pts'"
      by auto
    show "path_image c_path \<subseteq> UNIV - (pts - pts') - pts'"
    proof -
      have "p \<notin> pts" if "p\<in>path_image c_path" for p 
      proof -
        have "p\<in>path_image (shifted_contour_of_cell orig)" 
          using that unfolding c_path_def contour_of_cell_def 
            boundary_of_period_parallelogram_def 
            shifted_contour_of_cell_def
          by (simp add: image_image path_defs(4))
        then show ?thesis 
          using assms is_cell_def 
          using analytic_at_imp_no_pole pts_def by blast
      qed
      then show ?thesis 
        using \<open>pts' \<subseteq> pts\<close> by auto
    qed
    show " \<forall>z. z \<notin> UNIV - (pts - pts') 
        \<longrightarrow> winding_number c_path z = 0"
    proof clarify
      fix z assume "z \<notin> UNIV - (pts - pts')"
      then have "z\<notin>shifted_period_parallelogram orig" 
        using pts'_def pts_def by blast
      then have "z-orig \<notin>  period_parallelogram \<omega>1 \<omega>2 0 0"
        unfolding shifted_period_parallelogram_def by force
      from winding_number_parallelogram_outside[OF this]
      have "winding_number (path_of_parallelogram \<omega>1 \<omega>2) (z - orig) = 0"
        .
      then show "winding_number c_path z = 0"
        unfolding c_path_def contour_of_cell_def shifted_contour_of_cell_def
        by (simp add:winding_number_offset algebra_simps)
    qed
    show "valid_path c_path" 
         "pathfinish c_path = pathstart c_path "
      unfolding c_path_def by auto 
  qed 
  moreover have "(f has_contour_integral 0) c_path"
    using contour_integral_along_boundary_cell_is_zero[OF \<open>is_cell orig\<close>
      ,folded c_path_def] .
  ultimately have "(\<Sum>p\<in>pts'. winding_number c_path p * residue f p) = 0"
    using contour_integral_unique by auto
  moreover have "Im (\<omega>1 * cnj \<omega>2) \<noteq> 0" 
    by (meson Im_complex_div_eq_0 Im_divide_zero_iff ratio_notin_real)
  moreover have "(\<Sum>p\<in>pts'. winding_number c_path p * residue f p)
      = (\<Sum>p\<in>pts'. residue f p)" if "Im (\<omega>1 * cnj \<omega>2) < 0" 
  proof (rule sum.cong)
    fix w assume "w \<in> pts'"
    then have "w-orig \<in> period_parallelogram \<omega>1 \<omega>2 0 0
                  - path_image (path_of_parallelogram \<omega>1 \<omega>2)"
      using w_pts by auto
    from winding_number_parallelogram_inside(1)[OF this \<open>Im (\<omega>1 * cnj \<omega>2) < 0\<close>]
    have " winding_number (path_of_parallelogram \<omega>1 \<omega>2) (w - orig) = 1"
      .
    then have "winding_number c_path w = 1"
      unfolding c_path_def shifted_contour_of_cell_def comp_def
      by (simp add: winding_number_offset algebra_simps)
    then show "winding_number c_path w * residue f w = residue f w"
      by simp
  qed simp
  moreover have "(\<Sum>p\<in>pts'. winding_number c_path p * residue f p)
      = - (\<Sum>p\<in>pts'. residue f p)" 
      if "Im (\<omega>1 * cnj \<omega>2) > 0"
    unfolding sum_negf[symmetric]
  proof (rule sum.cong)
    fix w assume "w \<in> pts'"
    then have "w-orig \<in> period_parallelogram \<omega>1 \<omega>2 0 0
                  - path_image (path_of_parallelogram \<omega>1 \<omega>2)" 
      using w_pts by auto
    from winding_number_parallelogram_inside(2)[OF this \<open>Im (\<omega>1 * cnj \<omega>2) > 0\<close>]
    have "winding_number (path_of_parallelogram \<omega>1 \<omega>2) (w - orig) = -1"
      .
    then have "winding_number c_path w = - 1"
      unfolding c_path_def shifted_contour_of_cell_def comp_def
      by (simp add: winding_number_offset algebra_simps)
    then show "winding_number c_path w * residue f w = - residue f w"
      by simp
  qed simp
  ultimately have "sum (residue f) pts' = 0" by force
  moreover have "pts' = shifted_period_parallelogram' orig \<inter> pts" 
    unfolding pts'_def poles_in_period_parallelogram_def 
      shifted_period_parallelogram_eq_union pts_def
    using analytic_at_imp_no_pole assms is_cell_def 
    by fastforce
  ultimately show ?thesis using pts_def by blast
qed

text \<open>Theorem 1.8\<close>
lemma (in elliptic_fun) number_of_zeros_in_period_parallelogram_aux:
  fixes orig:: complex
  assumes "is_cell orig"
    and "\<forall>z\<in>path_image (shifted_contour_of_cell orig). 
                deriv f z \<noteq> 0"
  shows "(\<Sum>z\<in>{w\<in>shifted_period_parallelogram orig. 
    is_zero f w \<or> is_pole f w}. zorder f z) = 0"
proof -
  define ff where "ff = (\<lambda>z. deriv f z / f z) "
  interpret ff:elliptic_fun' ff \<omega>1 \<omega>2 
  proof unfold_locales
    have "is_periodic \<omega>1 f" "is_periodic \<omega>2 f"
      using is_doubly_periodic is_doubly_periodic_def by blast+
    then have "is_periodic \<omega>1 ff" "is_periodic \<omega>2 ff"
      using is_periodic_deriv_quotient 
      unfolding ff_def by auto
    then show "is_doubly_periodic \<omega>1 \<omega>2 ff"
      by (simp add: is_doubly_periodic_def ratio_notin_real)
    show "ff meromorphic_on UNIV"
      unfolding ff_def using is_meromorphic
      by (auto intro:meromorphic_intros)
  qed

  define pts where "pts = {w. is_zero f w \<or> is_pole f w}"

  have "pts sparse_in UNIV"
  proof -
    have "{x. is_zero f x} sparse_in UNIV"
      using meromorphic_on_imp_not_zero_cosparse[OF is_meromorphic]
      unfolding eventually_cosparse by simp
    moreover have "{x. is_pole f x} sparse_in UNIV"
      using meromorphic_on_imp_not_pole_cosparse[OF is_meromorphic]
      unfolding eventually_cosparse by simp
    ultimately show ?thesis unfolding pts_def
      using sparse_in_union
      by (metis Collect_disj_eq Int_absorb)
  qed

  define c_path where "c_path = shifted_contour_of_cell orig"
  let ?para = "shifted_period_parallelogram orig"
  define c where "c=(if Im (\<omega>1 * cnj \<omega>2) < 0 
      then 1::complex else -1)"

  have "contour_integral c_path ff =
          2 * pi * \<i> * (\<Sum>\<^sub>\<infinity>p\<in>pts. 
          winding_number c_path p * of_int (zorder f p))"
  unfolding ff_def
  proof (rule argument_principle_sparse)
    have "\<exists>x. f x\<noteq>0" 
    proof -
      have "path_image (shifted_contour_of_cell orig)\<noteq>{}"
        unfolding shifted_contour_of_cell_def by simp
      then show ?thesis using assms(1) unfolding is_cell_def
        by blast
    qed
    then have "(\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
      using nicely_meromorphic_imp_constant_or_avoid
              [OF nicely_meromorphic]
      by auto
    then have event_p:"\<forall>\<^sub>F x in at p. f x \<noteq> 0" for p
        using \<open>\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0\<close> 
          eventually_cosparse_imp_eventually_at 
        by blast
  
    show "f p \<noteq> 0" if "p \<in> UNIV - pts" for p
    proof 
      assume "f p = 0"
      from zero_or_pole[OF nicely_meromorphic _ this event_p]
      have "is_zero f p \<or> is_pole f p" by simp
      then show False using that unfolding pts_def by auto
    qed

    show "pts sparse_in UNIV" by fact
    show "\<forall>p\<in>pts. not_essential f p" unfolding pts_def by auto
    show "f analytic_on UNIV - pts"
      unfolding pts_def
      using analytic_on_analytic_at nicely_meromorphic 
        nicely_meromorphic_on_imp_analytic_at 
      by blast
    show "valid_path c_path" 
         "pathfinish c_path = pathstart c_path"
      unfolding c_path_def by auto
    show "path_image c_path \<subseteq> UNIV - pts"
      using assms(1) not_pole_on_the_contour_of_cell zero_is_zero
      unfolding pts_def c_path_def is_cell_def by blast
  qed simp
  moreover have "(ff has_contour_integral 0) c_path"
  proof -
    have "ff.is_cell orig" 
      unfolding ff.is_cell_def
    proof 
      fix w assume
        w:"w \<in> path_image (ff.shifted_contour_of_cell orig)"
      then have "f w \<noteq> 0" "f analytic_on {w}"
        using \<open>is_cell orig\<close> unfolding is_cell_def by auto 
      then have "ff analytic_on {w}"
        unfolding ff_def 
        using analytic_deriv analytic_on_divide by blast
      moreover have "ff w \<noteq> 0"
        using \<open>f w \<noteq> 0\<close> assms(2) divide_eq_0_iff w 
        unfolding ff_def by blast  
      ultimately show "ff w \<noteq> 0 \<and> ff analytic_on {w}"
        by simp
    qed
    from ff.contour_integral_along_boundary_cell_is_zero[OF this]
    show ?thesis unfolding c_path_def .
  qed
  ultimately have "(\<Sum>\<^sub>\<infinity>p\<in>pts. 
          winding_number c_path p * of_int (zorder f p)) = 0"
    by (simp add: contour_integral_unique)
  moreover have "(\<Sum>\<^sub>\<infinity>p\<in>pts. 
          winding_number c_path p * of_int (zorder f p))
    = c*(\<Sum>z\<in>{w\<in>?para. is_zero f w \<or> is_pole f w}.
           zorder f z)" (is "?L =?R")
  proof -
    have "?L = (\<Sum>\<^sub>\<infinity>p\<in>pts \<inter> ?para. 
          winding_number c_path p * of_int (zorder f p))"
    proof (rule infsum_cong_neutral)
      fix x
      assume asm:"x \<in> pts - pts 
                \<inter> ff.shifted_period_parallelogram orig"
      have "winding_number c_path x = 0"
      proof (rule winding_number_zero_outside)
        show "convex (ff.shifted_period_parallelogram orig)"
          by (simp add: shifted_period_parallelogram_def)
        show "path c_path"
             "pathfinish c_path = pathstart c_path"
             "path_image c_path 
                \<subseteq> ff.shifted_period_parallelogram orig"
          using shifted_period_parallelogram_eq_union
          unfolding c_path_def 
          by (auto simp add: valid_path_imp_path)
        show "x \<notin> ff.shifted_period_parallelogram orig"
          using asm by blast
      qed
      then show "winding_number c_path x * (zorder f x) = 0"
        by simp
    qed auto
    also have "... = (\<Sum>p\<in>pts \<inter> ?para. 
          winding_number c_path p * of_int (zorder f p))"
    proof (rule infsum_finite)
      have "compact ?para"
        by (simp add: ff.compact_shifted_parallelogram)
      moreover have "pts sparse_in ?para"
        using \<open>pts sparse_in UNIV\<close> sparse_in_subset by blast
      ultimately show "finite (pts \<inter> ?para)"
        using sparse_in_compact_finite 
        by (metis Int_commute) 
    qed
    also have "... = (\<Sum>p\<in>pts \<inter> ?para. 
          c * of_int (zorder f p))"
    proof (rule sum.cong)
      fix w assume w:"w \<in> pts \<inter> ?para"

      have w_orig:"w-orig \<in> period_parallelogram \<omega>1 \<omega>2 0 0 -
                  path_image (path_of_parallelogram \<omega>1 \<omega>2)"
      proof -
        have "w \<notin> path_image (ff.shifted_contour_of_cell orig)"
          using w \<open>is_cell orig\<close> unfolding pts_def 
          using not_pole_on_the_contour_of_cell not_zero_on_the_contour_of_cell 
          by force 
        then have "w-orig \<notin>path_image (path_of_parallelogram \<omega>1 \<omega>2)"
          unfolding shifted_contour_of_cell_def
          by (metis add.commute diff_add_cancel image_iff 
              path_image_compose)
        then show ?thesis using w 
          using ff.shifted_period_parallelogram_def by force
      qed
      have "winding_number c_path w = c"
      proof (cases "Im (\<omega>1 * cnj \<omega>2) < 0")
        case True
        from winding_number_parallelogram_inside(1)
             [OF w_orig this]
        have "winding_number (path_of_parallelogram \<omega>1 \<omega>2) 
                  (w - orig) = 1" .
        then show ?thesis unfolding c_path_def c_def
          shifted_contour_of_cell_def comp_def
          using True
          by (auto simp add:winding_number_offset algebra_simps)
      next
        case False
        then have "Im (\<omega>1 * cnj \<omega>2) > 0"
          using Im_complex_div_eq_0 Im_divide_zero_iff 
            ratio_notin_real 
          by fastforce
        from winding_number_parallelogram_inside(2)
             [OF w_orig this]
        have "winding_number (path_of_parallelogram \<omega>1 \<omega>2) 
                  (w - orig) = - 1" .
        then show ?thesis 
          unfolding c_path_def c_def
          shifted_contour_of_cell_def comp_def
          using False
          by (auto simp add:winding_number_offset algebra_simps)
      qed
      then show "winding_number c_path w 
                    * complex_of_int (zorder f w) =
                        c * complex_of_int (zorder f w)"
        by simp
    qed simp
    also have "... = c * (\<Sum>p\<in>pts \<inter> ?para. 
                            of_int (zorder f p))"
      using sum_distrib_left by metis
    also have "... = ?R" unfolding pts_def 
      by (simp add: Collect_conj_eq Int_commute)
    finally show ?thesis .
  qed
  moreover have "c\<noteq>0" unfolding c_def by simp
  ultimately show "(\<Sum>z\<in>{w\<in>?para. is_zero f w \<or> is_pole f w}.
           zorder f z) = 0"
    by (metis (no_types, lifting) no_zero_divisors of_int_0_eq_iff)
qed

lemma sum_over_shifted_period_parallelogram':
  fixes d :: complex
  defines "P1 \<equiv> shifted_period_parallelogram' d"
  defines "P2 \<equiv> period_parallelogram' \<omega>1 \<omega>2 0 0"
  assumes g: "is_doubly_periodic \<omega>1 \<omega>2 g"
  assumes A: "is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. x \<in> A)"
  shows   "(\<Sum>x\<in>P1\<inter>A. g x) = (\<Sum>x\<in>P2\<inter>A. g x)"
proof -
  define A' where "A' = \<omega>12_coords ` A"
  have A'_altdef: "A' = of_\<omega>12_coords -` A"
    unfolding A'_def \<omega>12_coords_def using bij_of_\<omega>12_coords
    by (rule bij_vimage_eq_inv_image [symmetric])
  define d' where "d' = \<omega>12_coords d"
  define P1' where "P1' = {fst d'..<fst d' + 1} \<times> {snd d'..<snd d' + 1}"
  define P2' :: "(real \<times> real) set" where "P2' = {0..<1} \<times> {0..<1}"
  define g' where "g' = g \<circ> of_\<omega>12_coords"
  define h_aux :: "real \<Rightarrow> real \<Rightarrow> int" where
    "h_aux = (\<lambda>d x. if x + of_int \<lfloor>d\<rfloor> \<ge> d then \<lfloor>d\<rfloor> else \<lfloor>d\<rfloor> + 1)"
  define h :: "(real \<times> real) \<Rightarrow> (real \<times> real)"
    where "h = (\<lambda>(x,y). (frac x, frac y))"
  define h' :: "(real \<times> real) \<Rightarrow> (real \<times> real)"
    where "h' = map_prod (\<lambda>x. x + of_int (h_aux (fst d') x)) (\<lambda>y. y + of_int (h_aux (snd d') y))"

  have g'_frac: "g' (x, y) = g' (frac x, frac y)" for x y
  proof -
    have "is_periodic (of_int (-\<lfloor>x\<rfloor>) * \<omega>1 + of_int (-\<lfloor>y\<rfloor>) * \<omega>2) g"
      by (intro is_doubly_periodic_imp_is_periodic[OF g])
    thus ?thesis
      by (simp add: g'_def frac_def is_periodic_def algebra_simps of_\<omega>12_coords_def)
  qed

  have A'_frac: "(x, y) \<in> A' \<longleftrightarrow> (frac x, frac y) \<in> A'" for x y
  proof -
    have "is_periodic (of_int (-\<lfloor>x\<rfloor>) * \<omega>1 + of_int (-\<lfloor>y\<rfloor>) * \<omega>2) (\<lambda>z. z \<in> A)"
      by (intro is_doubly_periodic_imp_is_periodic[OF A])
    thus ?thesis
      by (simp add: A'_altdef frac_def is_periodic_def algebra_simps of_\<omega>12_coords_def)
  qed

  have "(\<Sum>x\<in>P1\<inter>A. g x) = (\<Sum>x\<in>P1'\<inter>A'. g' x)"
    unfolding P1'_def P1_def shifted_period_parallelogram'_altdef Let_def of_\<omega>12_coords_image_eq
    by (intro sum.reindex_bij_witness[of _ of_\<omega>12_coords \<omega>12_coords])
       (auto simp: A'_def g'_def d'_def mem_Times_iff)
  also have "\<dots> = (\<Sum>x\<in>P2'\<inter>A'. g' x)"
  proof (rule sum.reindex_bij_witness[of _ h' h])
    show "h' (h z) = z" if "z \<in> P1' \<inter> A'" for z
      using that by (auto simp: h'_def h_def h_aux_def P1'_def frac_def not_le) (linarith+)?
  next
    show "h (h' z) = z" if "z \<in> P2' \<inter> A'" for z
      using that by (auto simp: h'_def h_def h_aux_def P2'_def frac_def not_le) (linarith+)?
  next
    show "h z \<in> P2' \<inter> A'" if "z \<in> P1' \<inter> A'" for z
    proof
      show "h z \<in> P2'"
        using that by (auto simp: h_def P2'_def frac_lt_1 split: prod.splits)
      have "(fst z, snd z) \<in> A' \<longleftrightarrow> h z \<in> A'"
        by (subst A'_frac) (auto simp: h_def frac_def case_prod_unfold)
      thus "h z \<in> A'"
        using that by auto
    qed
  next
    show "h' z \<in> P1' \<inter> A'" if "z \<in> P2' \<inter> A'" for z
    proof
      show "h' z \<in> P1'" unfolding h_aux_def h'_def
        using that by (auto simp: P2'_def P1'_def frac_lt_1 split: prod.splits) (linarith+)?
      have "(fst z, snd z) \<in> A' \<longleftrightarrow> (fst (h' z), snd (h' z)) \<in> A'"
        by (subst (1 2) A'_frac) (auto simp: h'_def frac_def)
      thus "h' z \<in> A'" using that
        by auto
    qed
  next
    show "g' (h z) = g' z" if "z \<in> P1' \<inter> A'" for z
    proof -
      have "g' (h z) = g' (fst z, snd z)"
        by (subst g'_frac) (auto simp: h_def case_prod_unfold)
      thus ?thesis
        by simp
    qed
  qed
  also have "\<dots> = (\<Sum>x\<in>P2\<inter>A. g x)"
    unfolding P2'_def P2_def period_parallelogram'_altdef of_\<omega>12_coords_image_eq
    by (intro sum.reindex_bij_witness[of _ \<omega>12_coords of_\<omega>12_coords])
       (auto simp: A'_def g'_def d'_def mem_Times_iff)
  finally show ?thesis .
qed

(*TODO: move out of elliptic fun?*)
theorem (in elliptic_fun) zero_or_pole_iff:
  assumes "f w\<noteq>0" 
  shows "f z =0 \<longleftrightarrow> (is_zero f z \<or> is_pole f z)"
proof 
  assume "f z=0"
  have "\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0"
    using nicely_meromorphic_imp_constant_or_avoid
            [OF nicely_meromorphic] \<open>f w\<noteq>0\<close> by auto
  then have "\<forall>\<^sub>F x in at z. f x \<noteq> 0" for z
    using eventually_cosparse_imp_eventually_at by blast
  then show "is_zero f z \<or> is_pole f z"
    using zero_or_pole[OF nicely_meromorphic _ \<open>f z=0\<close>] 
    by fast
next
  assume "is_zero f z \<or> is_pole f z"
  then show "f z =0"
    by (metis is_pole_zero_at_nicely_mero iso_tuple_UNIV_I
        nicely_meromorphic zero_is_zero)
qed

lemma mostly_imp_constant:
  assumes "f nicely_meromorphic_on A" "f mostly_constant_on A"
  shows "f constant_on A" 
proof -
  obtain c where c:"\<forall>\<^sub>\<approx>z\<in>A. f z = c" 
    using \<open>f mostly_constant_on A\<close> unfolding mostly_constant_on_def
    by auto
  have "f x = c" if "x\<in>A" for x
  proof -
    have event_c:"\<forall>\<^sub>F z in at x. f z = c" 
      using eventually_cosparse_imp_eventually_at[OF c \<open>x\<in>A\<close>] .
    then have "\<not> is_pole f x" 
      by (simp add: is_pole_cong)
    then have "f analytic_on {x}"
      using assms(1) nicely_meromorphic_on_imp_analytic_at that by blast
    then  show ?thesis 
      using event_c
      by (metis Meromorphic1.remove_sings_eqI 
          analytic_at_imp_isCont continuous_within tendsto_eventually)
  qed
  then show ?thesis unfolding constant_on_def by auto
qed

theorem (in elliptic_fun) 
    number_of_zeros_in_period_parallelogram:
  shows   "(\<Sum>z\<in>{w\<in>shifted_period_parallelogram' orig. 
              is_zero f w \<or> is_pole f w}. zorder f z) = 0"
proof (cases "\<not> f mostly_constant_on UNIV \<and> (\<exists>w. f w\<noteq>0)")
  case True
  then obtain w where "f w\<noteq>0" by auto
  have "\<not> z islimpt {w. is_zero f w \<or> is_pole f w 
      \<or> deriv f w = 0}" for z
  proof -
    have "\<forall>\<^sub>\<approx>w\<in>UNIV. \<not> is_zero f w" 
      by (simp add: is_meromorphic meromorphic_on_imp_not_zero_cosparse)
    moreover have "\<forall>\<^sub>\<approx>w\<in>UNIV. \<not> is_pole f w" 
      by (simp add: is_meromorphic meromorphic_on_imp_not_pole_cosparse)
    moreover have "\<forall>\<^sub>\<approx>w\<in>UNIV. deriv f w\<noteq>0" 
      using True deriv_meromorphic_not_zero_corsparse is_meromorphic by blast
    ultimately have "\<forall>\<^sub>\<approx>w\<in>UNIV. \<not> is_zero f w \<and> \<not> is_pole f w \<and> deriv f w\<noteq>0"
      by eventually_elim auto
    then show ?thesis 
      by (simp add: eventually_cosparse_imp_eventually_at 
          islimpt_iff_eventually)
  qed
  thus ?thesis
  proof (induction orig rule: shifted_period_parallelogram_avoid_wlog)
    case (shift orig d)
    define A where "A = 
              (\<lambda>orig. shifted_period_parallelogram' orig 
                  \<inter> {w. is_zero f w \<or> is_pole f w})"

    have "(\<Sum>w\<in>A (orig + d). zorder f w) = (\<Sum>w\<in>A orig. zorder f w)"
      unfolding A_def
    proof (subst (1 2) sum_over_shifted_period_parallelogram')
      show "is_doubly_periodic \<omega>1 \<omega>2 (zorder f)"
        by (intro is_doubly_periodic_zorder is_doubly_periodic)
      have "is_doubly_periodic \<omega>1 \<omega>2 (is_zero f)"
          "is_doubly_periodic \<omega>1 \<omega>2 (is_pole f)"
        by (intro is_doubly_periodic_is_zero 
            is_doubly_periodic_is_pole is_doubly_periodic)+
      from is_doubly_periodic_compose2[OF this]
      show "is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. x \<in> {w. is_zero f w \<or> is_pole f w})"
        unfolding mem_Collect_eq by blast
    qed auto
    with shift show ?case by (simp add: A_def Int_def)
  next
    case (avoid orig)
    then have "is_cell orig"
      unfolding is_cell_def using \<open>f w\<noteq>0\<close>
      by (metis (no_types, lifting) Int_Collect UNIV_I 
          empty_iff nicely_meromorphic 
          nicely_meromorphic_on_imp_analytic_at 
          zero_or_pole_iff)
    moreover have "\<forall>z\<in>path_image (shifted_contour_of_cell orig). 
            deriv f z \<noteq> 0"
      using avoid(2) by auto
    ultimately have "sum (zorder f)
        {w \<in> shifted_period_parallelogram orig.
            is_zero f w \<or> is_pole f w} = 0"
      using number_of_zeros_in_period_parallelogram_aux by blast
    also have "{w \<in> shifted_period_parallelogram orig. 
        is_zero f w \<or> is_pole f w} =
               {w \<in> shifted_period_parallelogram' orig. 
        is_zero f w \<or> is_pole f w}"
      using shifted_period_parallelogram_diff_on_boundary[of orig]
            shifted_period_parallelogram'_subset[of orig] avoid(2) 
      by auto
    finally show ?case .
  qed
next
  case False
  then have const:"f constant_on UNIV" 
    by (meson constant_on_def mostly_imp_constant nicely_meromorphic)
  then have "\<not> is_zero f w" for w
    by (metis UNIV_I constant_on_def constant_on_imp_holomorphic_on 
        inverse_zero_imp_pole not_is_pole_holomorphic open_UNIV)
  moreover have "\<not> is_pole f w" for w
    using constant_on_imp_holomorphic_on not_is_pole_holomorphic const 
    by blast
  ultimately have "{w\<in>shifted_period_parallelogram' orig. 
              is_zero f w \<or> is_pole f w} = {}"
    by simp
  then show ?thesis by (metis sum.empty)
qed

lemma period_parallelogram_conv_shifted_period_parallelogram:
  "shifted_period_parallelogram' (of_\<omega>12_coords (real_of_int m, real_of_int n)) =
   period_parallelogram' \<omega>1 \<omega>2 m n"
  by (simp add: shifted_period_parallelogram'_altdef period_parallelogram'_altdef)

definition order :: "nat" where
  "order = (\<Sum>z\<in>poles_in_period_parallelogram 0. nat (-zorder f z))"

lemma zorder_at_pole_less_0: "is_pole f w \<Longrightarrow> zorder f w < 0"
  using isolated_pole_imp_neg_zorder by auto

(*
  TODO: This is not strong enough. What we actually want here is

    (\<Sum>z\<in>shifted_period_parallelogram orig \<inter> {z. is_pole f z}. zorder f z) = -int order

  Should be fairly easy to show though.
  Perhaps we should get rid of "period_parallelogram" entirely and replace it with something
  like "fundamental_parallelogram" which always starts at (0, 0).
*)
lemma order_poles': "(\<Sum>z\<in>poles_in_period_parallelogram orig. nat (-zorder f z)) = order"
  and order_poles: "(\<Sum>z\<in>poles_in_period_parallelogram orig. zorder f z) = -int order"
proof -
  have *: "is_doubly_periodic \<omega>1 \<omega>2 (zorder f)" "is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. x \<in> {x. is_pole f x})"
    using is_doubly_periodic_zorder[OF is_doubly_periodic]
          is_doubly_periodic_is_pole[OF is_doubly_periodic] by auto

  have "(\<Sum>z\<in>poles_in_period_parallelogram orig. nat (-zorder f z)) =
        (\<Sum>z\<in>period_parallelogram' \<omega>1 \<omega>2 0 0 \<inter> {x. is_pole f x}. nat (-zorder f z))"
    unfolding poles_in_period_parallelogram_def
    by (intro sum_over_shifted_period_parallelogram' * *[THEN is_doubly_periodic_compose])
  also have "\<dots> = order"
    by (simp add: order_def poles_in_period_parallelogram_def shifted_period_parallelogram'_def)
  finally show **: "(\<Sum>z\<in>poles_in_period_parallelogram orig. nat (-zorder f z)) = order" .

  have "int order = (\<Sum>z\<in>poles_in_period_parallelogram orig. int (nat (-zorder f z)))"
    by (simp flip: **)
  also have "\<dots> = (\<Sum>z\<in>poles_in_period_parallelogram orig. -zorder f z)"
    by (intro sum.cong refl)
       (auto simp: poles_in_period_parallelogram_def dest: zorder_at_pole_less_0)
  finally show "(\<Sum>z\<in>poles_in_period_parallelogram orig. zorder f z) = -int order"
    by (simp add: sum_negf)
qed

lemma (in elliptic_fun) order_zeros': 
  assumes "f a\<noteq>0" 
  shows "(\<Sum>z\<in>zeros_in_period_parallelogram orig. nat (zorder f z)) = order"
proof -
  define Z where "Z = zeros_in_period_parallelogram orig"
  define P where "P = poles_in_period_parallelogram orig"
  have disjoint: "Z \<inter> P = {}"
    unfolding Z_def P_def zeros_in_period_parallelogram_def 
      poles_in_period_parallelogram_def
    using pole_is_not_zero by fastforce
  have "(\<Sum>w\<in>{w \<in> shifted_period_parallelogram' orig. 
      is_zero f w \<or> is_pole f w}. zorder f w) = 0"
    by (intro number_of_zeros_in_period_parallelogram)
  also have "{w \<in> shifted_period_parallelogram' orig. 
      is_zero f w \<or> is_pole f w} = Z \<union> P"
    by (auto simp: zeros_in_period_parallelogram_def poles_in_period_parallelogram_def
                   period_parallelogram_conv_shifted_period_parallelogram Z_def P_def)
  also have "(\<Sum>w\<in>\<dots>. zorder f w) = (\<Sum>w\<in>Z. zorder f w) + (\<Sum>w\<in>P. zorder f w)"
    using disjoint  
    by (subst sum.union_disjoint) (auto simp: Z_def P_def)
  also have "(\<Sum>w\<in>Z. zorder f w) = (\<Sum>w\<in>Z. int (nat (zorder f w)))"
  proof (intro sum.cong refl)
    fix w assume "w \<in> Z"
    hence "zorder f w \<ge> 0" 
    proof -
      assume "w \<in> Z"
      then have "\<not> is_pole f w"
        using disjoint 
        unfolding P_def Z_def poles_in_period_parallelogram_def
          zeros_in_period_parallelogram_def 
        by force
      moreover obtain F where F:"(\<lambda>x. f (w + x)) has_laurent_expansion F"
        by (metis UNIV_I is_meromorphic 
            meromorphic_on_imp_has_laurent_expansion)
      ultimately have "fls_subdegree F \<ge> 0"
        using is_pole_fls_subdegree_iff by auto
      moreover have "F\<noteq>0" 
      proof -
        have "(\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
          using nicely_meromorphic_imp_constant_or_avoid
            [OF nicely_meromorphic, of 0] \<open>f a\<noteq>0\<close>
          by auto
        then have " \<forall>\<^sub>F z in at w. f z \<noteq> 0"
          using eventually_cosparse_imp_eventually_at by blast
        then show ?thesis 
          using F has_laurent_expansion_eventually_nonzero_iff by blast
      qed
      ultimately show ?thesis 
        using has_laurent_expansion_zorder[OF F] by auto
    qed
    thus "zorder f w = int (nat (zorder f w))"
      by simp     
  qed
  also have "(\<Sum>w\<in>P. zorder f w) = (\<Sum>w\<in>P. -int (nat (-zorder f w)))"
    by (intro sum.cong refl)
       (auto simp: P_def poles_in_period_parallelogram_def 
         dest: zorder_at_pole_less_0)
  finally show ?thesis
    unfolding of_nat_sum[symmetric] sum_negf 
    unfolding order_poles' Z_def P_def by linarith
qed

lemma (in elliptic_fun) order_zeros: 
  assumes "f a\<noteq>0" 
  shows "(\<Sum>z\<in>zeros_in_period_parallelogram orig. zorder f z) = int order"
proof -
  have "int order = (\<Sum>z\<in>zeros_in_period_parallelogram orig. int (nat (zorder f z)))"
    apply (subst order_zeros' [symmetric])
    using \<open>f a\<noteq>0\<close> by auto
  also have "\<dots> = (\<Sum>z\<in>zeros_in_period_parallelogram orig. zorder f z)"
  proof (intro sum.cong refl) 
    fix w assume "w \<in> zeros_in_period_parallelogram orig"
    hence "zorder f w \<ge> 0"
    proof -
      assume "w \<in> zeros_in_period_parallelogram orig"
      then have "\<not> is_pole f w"
        unfolding  poles_in_period_parallelogram_def
          zeros_in_period_parallelogram_def 
        using pole_is_not_zero by auto
      moreover obtain F where F:"(\<lambda>x. f (w + x)) has_laurent_expansion F"
        by (metis UNIV_I is_meromorphic 
            meromorphic_on_imp_has_laurent_expansion)
      ultimately have "fls_subdegree F \<ge> 0"
        using is_pole_fls_subdegree_iff by auto
      moreover have "F\<noteq>0" 
      proof -
        have "(\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
          using nicely_meromorphic_imp_constant_or_avoid
            [OF nicely_meromorphic, of 0] \<open>f a\<noteq>0\<close>
          by auto
        then
        have " \<forall>\<^sub>F z in at w. f z \<noteq> 0"
          using eventually_cosparse_imp_eventually_at by blast
        then show ?thesis 
          using F has_laurent_expansion_eventually_nonzero_iff by blast
      qed
      ultimately show ?thesis 
        using has_laurent_expansion_zorder[OF F] by auto
    qed
    thus "int (nat (zorder f w)) = zorder f w"
      by simp     
  qed
  finally show ?thesis
    by simp
qed

lemma card_poles_le_order: "card (poles_in_period_parallelogram orig) \<le> order"
proof -
  have "-order = (\<Sum>w\<in>poles_in_period_parallelogram orig. zorder f w)"
    by (simp add: order_poles)
  also have "\<dots> \<le> (\<Sum>w\<in>poles_in_period_parallelogram orig. -1)"
  proof (rule sum_mono)
    fix w assume "w \<in> poles_in_period_parallelogram orig"
    with zorder_at_pole_less_0[of w] show "zorder f w \<le> -1"
      by (auto simp: poles_in_period_parallelogram_def)
  qed
  finally show ?thesis
    by simp
qed

lemma (in elliptic_fun) card_zeros_le_order: 
  assumes "f a\<noteq>0" 
  shows "card (zeros_in_period_parallelogram orig) \<le> order"
proof -
  have "(\<Sum>w\<in>zeros_in_period_parallelogram orig. 1) \<le>
        (\<Sum>w\<in>zeros_in_period_parallelogram orig. zorder f w)"
  proof (rule sum_mono)
    fix w assume "w \<in> zeros_in_period_parallelogram orig"
    then have "f \<midarrow>w\<rightarrow> 0" 
      by (simp add: Elliptic_Functions.is_zero_def tendsto_nhds_iff 
          zeros_in_period_parallelogram_def)
    moreover obtain F where F:"(\<lambda>x. f (w + x)) has_laurent_expansion F"
      by (metis UNIV_I is_meromorphic 
          meromorphic_on_imp_has_laurent_expansion)
    moreover have "F\<noteq>0" (*TODO: this proof has been repeated a few times*)
    proof -
      have "(\<forall>\<^sub>\<approx>x\<in>UNIV. f x \<noteq> 0)"
        using nicely_meromorphic_imp_constant_or_avoid
          [OF nicely_meromorphic, of 0] \<open>f a\<noteq>0\<close>
        by auto
      then have " \<forall>\<^sub>F z in at w. f z \<noteq> 0"
        using eventually_cosparse_imp_eventually_at by blast
      then show ?thesis 
        using F has_laurent_expansion_eventually_nonzero_iff by blast
    qed
    ultimately have "0 < fls_subdegree F"
      using tendsto_0_subdegree_iff by auto
    then show "1 \<le> zorder f w"
      using has_laurent_expansion_zorder[OF F \<open>F\<noteq>0\<close>] by auto
  qed
  thus ?thesis
    by (simp add: order_zeros[OF \<open>f a\<noteq>0\<close>])
qed

lemma (in elliptic_fun) order_eq_0_iff: "order = 0 \<longleftrightarrow> is_constant f"
proof -
  have "order = 0 \<longleftrightarrow> poles_in_period_parallelogram 0 = {}"
  proof
    assume "order = 0"
    hence "card (poles_in_period_parallelogram 0) = 0"
      using card_poles_le_order[of 0] by simp
    thus "poles_in_period_parallelogram 0 = {}"
      using finite_poles_in_pp by simp
  next
    assume "poles_in_period_parallelogram 0 = {}"
    thus "order = 0"
      using order_poles[of 0] by simp
  qed
  also have "\<dots> \<longleftrightarrow> is_constant f"
  proof
    assume "poles_in_period_parallelogram 0 = {}"
    thus "is_constant f"
      using no_pole_in_some_period_parallelogram_implies_is_constant[of 0]
      by (auto simp: poles_in_period_parallelogram_def shifted_period_parallelogram'_def)
  next
    assume "is_constant f"
    hence "f holomorphic_on UNIV"
      by (rule constant_on_imp_holomorphic_on)
    hence "\<not>is_pole f z" for z
      by (meson UNIV_I not_is_pole_holomorphic open_UNIV)
    thus "poles_in_period_parallelogram 0 = {}"
      by (auto simp: poles_in_period_parallelogram_def)
  qed
  finally show ?thesis .
qed

lemma (in elliptic_fun) order_gt_0_iff: 
    "order > 0 \<longleftrightarrow> \<not>is_constant f"
  using order_eq_0_iff by linarith

(* Note p. 6 *)
lemma (in elliptic_fun) nonconstant_has_order_geq2:
  assumes "\<not> is_constant f"
  shows "order \<ge> 2"
proof (rule ccontr)
  assume "\<not>(order \<ge> 2)"
  moreover from assms have "order > 0"
    by (simp add: order_gt_0_iff)
  ultimately have [simp]: "order = 1"
    by auto

  obtain orig where orig: "is_cell orig"
    using assms cell_exists by blast
  define P where "P = poles_in_period_parallelogram orig"
  have [simp]: "finite P"
    unfolding P_def by auto

  have "P \<noteq> {}"
    using order_poles[of orig] by (auto simp: P_def)
  hence "card P > 0"
    by (simp add: card_gt_0_iff)    
  moreover have "card P \<le> 1"
    using card_poles_le_order by (simp add: P_def)
  ultimately have "card P = 1"
    by linarith
  then obtain z0 where P: "P = {z0}"
    using card_1_singletonE by blast

  define F where "F = laurent_expansion f z0"
  have F: "(\<lambda>w. f (z0 + w)) has_laurent_expansion F"
    unfolding F_def 
    using nicely_mero not_essential_has_laurent_expansion by blast
  have [simp]: "F \<noteq> 0"
    using has_laurent_expansion_imp_is_pole_iff[OF F] P
    by (auto simp: P_def poles_in_period_parallelogram_def)

  have "zorder f z0 = -1"
    using order_poles[of orig] P by (simp add: P_def)
  moreover have "residue f z0 = 0"
  proof -
    have "shifted_period_parallelogram' orig \<inter> {x. is_pole f x} = P" 
      by (simp add: P_def poles_in_period_parallelogram_def)
    then show ?thesis
    using sum_residues_at_poles_in_period_parallelogram[OF orig] P
      by simp
  qed
  ultimately have "fls_residue F = 0" "fls_subdegree F = -1"
    using has_laurent_expansion_residue[OF F] has_laurent_expansion_zorder[OF F]
    by auto
  thus False
    unfolding fls_residue_def using \<open>F \<noteq> 0\<close>
    by (metis nth_fls_subdegree_nonzero)
qed

end (* end elliptic_fun' *)

(*TODO: the first assumption can probably be simplified to g being a rational function.
  Check Prop 7.15 in https://www.math.uwaterloo.ca/~dgwagner/co430I.pdf*)
lemma elliptic_fun_compose:
  assumes mero: "\<And>f. f meromorphic_on UNIV 
              \<Longrightarrow> (\<lambda>x. g (f x)) meromorphic_on UNIV"
  assumes "elliptic_fun' f \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. g (f x)) \<omega>1 \<omega>2"
proof -
  interpret f: elliptic_fun' f \<omega>1 \<omega>2 by fact
  show ?thesis
  proof
    show "is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. g (f x))"
      using f.is_doubly_periodic by (intro is_doubly_periodic_compose[where g = g])
  next
    show "(\<lambda>x. g (f x)) meromorphic_on UNIV"
      by (intro mero f.is_meromorphic)
  qed
qed

lemma elliptic_fun_compose2:
  assumes mero: "\<And>f g. f meromorphic_on UNIV \<Longrightarrow> g meromorphic_on UNIV \<Longrightarrow>
                        (\<lambda>x. h (f x) (g x)) meromorphic_on UNIV"
  assumes "elliptic_fun' f \<omega>1 \<omega>2" "elliptic_fun' g \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. h (f x) (g x)) \<omega>1 \<omega>2"
proof -
  interpret f: elliptic_fun' f \<omega>1 \<omega>2 by fact
  interpret g: elliptic_fun' g \<omega>1 \<omega>2 by fact
  show ?thesis
  proof
    show "is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. h (f x) (g x))"
      using f.is_doubly_periodic g.is_doubly_periodic
      by (intro is_doubly_periodic_compose2[where h = h])
  next
    show "(\<lambda>x. h (f x) (g x)) meromorphic_on UNIV"
      by (intro mero f.is_meromorphic g.is_meromorphic)
  qed
qed

named_theorems elliptic_fun_intros

lemmas (in gen_lattice) [elliptic_fun_intros] = ratio_notin_real

lemma elliptic_fun_const [elliptic_fun_intros]:
  assumes "Im (\<omega>2 / \<omega>1) \<noteq> 0"
  shows   "elliptic_fun' (\<lambda>x. c) \<omega>1 \<omega>2"  
  by (simp add: meromorphic_on_const assms elliptic_fun'.intro is_doubly_periodic_const)

lemma elliptic_fun_uminus [elliptic_fun_intros]:
  assumes "elliptic_fun' f \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. -f x) \<omega>1 \<omega>2"
  by (intro elliptic_fun_compose[where g = uminus] assms meromorphic_intros)

lemma elliptic_fun_add [elliptic_fun_intros]:
  assumes "elliptic_fun' f \<omega>1 \<omega>2" "elliptic_fun' g \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. f x + g x) \<omega>1 \<omega>2"
  by (intro elliptic_fun_compose2[where h = "(+)"] assms meromorphic_intros)

lemma elliptic_fun_diff [elliptic_fun_intros]:
  assumes "elliptic_fun' f \<omega>1 \<omega>2" "elliptic_fun' g \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. f x - g x) \<omega>1 \<omega>2"
  by (intro elliptic_fun_compose2[where h = "(-)"] assms meromorphic_intros)

lemma elliptic_fun_mult [elliptic_fun_intros]:
  assumes "elliptic_fun' f \<omega>1 \<omega>2" "elliptic_fun' g \<omega>1 \<omega>2"
  shows   "elliptic_fun' (\<lambda>x. f x * g x) \<omega>1 \<omega>2"
  by (intro elliptic_fun_compose2[where h = "(*)"] assms meromorphic_intros)

lemma elliptic_fun_power [elliptic_fun_intros]:
  assumes "elliptic_fun' f \<omega>1 \<omega>2" "Im (\<omega>2 / \<omega>1) \<noteq> 0"
  shows   "elliptic_fun' (\<lambda>x. f x ^ n) \<omega>1 \<omega>2"
  by (induction n) (auto intro!:elliptic_fun_intros assms)

lemma (in elliptic_fun) elliptic_fun_deriv:
  assumes not_pole:"\<And>x. \<not>is_pole f x  \<Longrightarrow> (f has_field_derivative f' x) (at x)"
  assumes at_pole:"\<And>x. is_pole f x \<Longrightarrow> f' x = 0"
  shows   "elliptic_fun f' \<omega>1 \<omega>2"
proof
  have event_eq:"\<forall>\<^sub>F x in at z. deriv f x = f' x" for z
  proof -
    have "\<forall>\<^sub>F x in at z. \<not>is_pole f x"
      by (simp add: eventually_not_pole)
    then show ?thesis
      apply (elim eventually_mono)
      by (simp add: DERIV_imp_deriv assms(1))
  qed

  have f'_pole:"is_pole f' z" if "is_pole f z" for z 
  proof -
    have "is_pole (deriv f) z" 
      by (simp add: is_pole_deriv that)
    with event_eq[of z] 
    show "is_pole f' z"
      using is_pole_cong by auto
  qed
  have f'_not_pole:"f' analytic_on {z}" if "\<not> is_pole f z" for z 
  proof -
    have "f analytic_on {z}" 
      using nicely_meromorphic nicely_meromorphic_on_imp_analytic_at that by blast
    then have "deriv f analytic_on {z}" 
      by (simp add: analytic_deriv)
    moreover have "\<forall>\<^sub>F x in nhds z. deriv f x = f' x"
      using event_eq 
      by (simp add: DERIV_imp_deriv eventually_nhds_conv_at not_pole that)
    ultimately show "f' analytic_on {z}"
      using analytic_at_cong by blast
  qed
  
  define pts where "pts = {x. is_pole f x}"
  show "f' meromorphic_on UNIV"
  proof (rule meromorphic_onI_weak)
    show "f' analytic_on UNIV - pts" 
      unfolding pts_def 
      by (metis DiffD2 analytic_on_analytic_at f'_not_pole mem_Collect_eq)
    show "\<And>z. z \<in> pts \<Longrightarrow> not_essential f' z" 
      using f'_pole pts_def by blast
    show "pts sparse_in UNIV" 
      by (simp add: \<open>pts \<equiv> Collect (is_pole f)\<close> not_islimpt_poles sparse_in_open)
    show "pts \<inter> frontier UNIV = {}" by simp
  qed 
  have *: "is_periodic \<omega> f'" if \<omega>: "\<omega> \<in> \<Omega>" for \<omega>
    unfolding is_periodic_def
  proof
    fix z
    show "f' (z + \<omega>) = f' z"
    proof (cases "z \<in> pts")
      case True
      hence "z + \<omega> \<in> pts"
        unfolding pts_def using \<omega> 
        by (metis is_pole_mnf_iff mem_Collect_eq omegaE)
      with True show "f' (z + \<omega>) = f' z"
        by (simp add: assms(2) pts_def)
    next
      case False
      hence "z + \<omega> \<notin> pts"
        using \<omega> unfolding pts_def
        by (simp add: is_doubly_periodic is_periodic_pole_plus pre_gen_lattice.omega_is_periodic)
      hence "((\<lambda>z. f (z + \<omega>)) has_field_derivative f' (z + \<omega>)) (at z)"
        using False \<omega> unfolding pts_def 
        using DERIV_shift assms(1) by blast
      also have "(\<lambda>z. f (z + \<omega>)) = f"
        using omega_is_periodic[OF \<omega> is_doubly_periodic] by (simp add: is_periodic_def)
      finally have "(f has_field_derivative f' (z + \<omega>)) (at z)" .
      moreover have "(f has_field_derivative f' z) (at z)"
        using False assms unfolding pts_def by simp
      ultimately show "f' (z + \<omega>) = f' z"
        using DERIV_unique by blast
    qed
  qed
  show "is_doubly_periodic \<omega>1 \<omega>2 f'"
    unfolding is_doubly_periodic_def by (intro conjI ratio_notin_real * omegaI1 omegaI2)

  have "is_pole f' z \<and> f' z = 0" if "is_pole f z" for z 
    by (simp add: assms(2) f'_pole that)
  moreover have "f' \<midarrow>z\<rightarrow> f' z" if "\<not> is_pole f z" for z 
    using analytic_at_imp_isCont continuous_within f'_not_pole that by blast
  ultimately show "\<forall>z. is_pole f' z \<and> f' z = 0 \<or> f' \<midarrow>z\<rightarrow> f' z" by auto
qed

section \<open>Construction of Elliptic Functions\<close>

context gen_lattice
begin

definition omega_sum where "omega_sum \<alpha> n \<equiv> \<Sum>k=1..n. \<Sum>\<omega>\<in>omega_iter k. norm \<omega> powr -\<alpha>"

lemma omega_sum_Suc [simp]: "omega_sum \<alpha> (Suc n) = omega_sum \<alpha> n + (\<Sum>\<omega>\<in>omega_iter (Suc n). norm \<omega> powr -\<alpha>)"
  by (simp add: omega_sum_def)

lemma \<omega>_upper:
  assumes "\<omega> \<in> omega_iter k" and "\<alpha> > 0" and "k > 0"
  shows "norm \<omega> powr -\<alpha> \<le> (k*Inf_para) powr -\<alpha>"
  using omega_iter_le_norm Inf_para_positive assms powr_mono2' by force

lemma sum_\<omega>_upper:
  assumes "\<alpha> > 0" and "k > 0"
  shows "(\<Sum>\<omega> \<in> omega_iter k. norm \<omega> powr -\<alpha>) \<le> 8 * k powr (1-\<alpha>) * Inf_para powr -\<alpha>"
    (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> (8 * k) * (k*Inf_para) powr -\<alpha>"
    using sum_bounded_above [OF \<omega>_upper] card_omega_iter [OF \<open>k>0\<close>] assms
    by fastforce
  also have "\<dots> = ?rhs"
    using Inf_para_positive by (simp add: powr_diff powr_minus powr_mult divide_simps)
  finally show ?thesis .
qed

lemma \<omega>_lower:
  assumes \<omega>: "\<omega> \<in> omega_iter k" and "k > 0"
  shows "(k * (if \<alpha> > 0 then Sup_para else Inf_para)) powr -\<alpha> \<le> norm \<omega> powr -\<alpha>"
proof (cases "\<alpha> > 0")
  case True
  thus ?thesis
    using omega_iter_ge_norm [OF \<omega>] Inf_para_positive assms
    by (auto simp add: powr_diff powr_minus powr_mult divide_simps powr_mono2)
next
  case False
  thus ?thesis
    using assms Inf_para_positive omega_iter_le_norm[of \<omega> k] by (intro powr_mono2) auto
qed

lemma sum_\<omega>_lower:
  assumes "k > 0"
  shows "8 * k powr (1-\<alpha>) * (if \<alpha> > 0 then Sup_para else Inf_para) powr -\<alpha> \<le> (\<Sum>\<omega> \<in> omega_iter k. norm \<omega> powr -\<alpha>)"
    (is "?lhs \<le> ?rhs")
proof -
  have "?lhs = (8 * k) * (k * (if \<alpha> > 0 then Sup_para else Inf_para)) powr -\<alpha>"
    using Sup_para_positive Inf_para_positive
    by (simp add: powr_diff powr_minus powr_mult divide_simps)
  also have "\<dots> \<le> ?rhs"
    using sum_bounded_below [OF \<omega>_lower, of "omega_iter k" "\<lambda>x. x" k \<alpha>]
          card_omega_iter [OF \<open>k > 0\<close>] assms by simp
  finally show ?thesis .
qed

(* lemma 1. p.7 *)
lemma omega_mz_eq: "\<Omega>* = (\<Union>i\<in>{0<..}. omega_iter i)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding omega_minus_zero_def omega_iter_covers
    by (smt (verit, ccfv_threshold) DiffE UN_iff greaterThan_iff neq0_conv omega_iter_0 subsetI) 
  show "?rhs \<subseteq> ?lhs"
    using omega_iter_covers omega_minus_zero_def by force
qed

lemma converges_absolutely_iff_aux1:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2"
  shows   "summable (\<lambda>i. \<Sum>\<omega>\<in>omega_iter (Suc i). 1 / norm \<omega> powr \<alpha>)"
proof (rule summable_comparison_test')
  show "norm (\<Sum>\<omega>\<in>omega_iter (Suc n). 1 / norm \<omega> powr \<alpha>) \<le>
          8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>" for n
  proof -
    have "norm (\<Sum>\<omega>\<in>omega_iter (Suc n). 1 / norm \<omega> powr \<alpha>) =
          (\<Sum>\<omega>\<in>omega_iter (Suc n). norm \<omega> powr -\<alpha>)"
      unfolding real_norm_def
      by (subst abs_of_nonneg) (auto intro!: sum_nonneg simp: powr_minus field_simps)
    also have "\<dots> \<le> 8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>"
      using sum_\<omega>_upper[of \<alpha> "Suc n"] assms by simp
    finally show ?thesis .
  qed
next
  show "summable (\<lambda>n. 8 * real (Suc n) powr (1 - \<alpha>) * Inf_para powr -\<alpha>)"
    by (subst summable_Suc_iff, intro summable_mult summable_mult2, subst summable_real_powr_iff)
       (use assms in auto)
qed

lemma converges_absolutely_iff_aux2:
  fixes \<alpha> :: real
  assumes "summable (\<lambda>i. \<Sum>\<omega>\<in>omega_iter (Suc i). 1 / norm \<omega> powr \<alpha>)"
  shows   "\<alpha> > 2"
proof -
  define C where "C = (if \<alpha> > 0 then Sup_para else Inf_para)"
  have "C > 0"
    using Sup_para_positive Inf_para_positive by (auto simp: C_def)

  have "summable (\<lambda>n. 8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>)"
  proof (rule summable_comparison_test')
    show "norm (8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>) \<le>
            (\<Sum>\<omega>\<in>omega_iter (Suc n). 1 / norm \<omega> powr \<alpha>)" for n
    proof -
      have "norm (8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>) =
            8 * real (Suc n) powr (1 - \<alpha>) * C powr -\<alpha>"
        unfolding real_norm_def by (subst abs_of_nonneg) (auto intro!: sum_nonneg)
      also have "\<dots> \<le> (\<Sum>\<omega>\<in>omega_iter (Suc n). 1 / norm \<omega> powr \<alpha>)"
        using sum_\<omega>_lower[of "Suc n" \<alpha>] by (simp add: powr_minus field_simps C_def)
      finally show ?thesis .
    qed
  qed fact
  hence "summable (\<lambda>n. 8 * C powr -\<alpha> * real n powr (1 - \<alpha>))"
    by (subst (asm) summable_Suc_iff) (simp add: mult_ac)
  hence "summable (\<lambda>n. real n powr (1 - \<alpha>))"
    using \<open>C > 0\<close> by (subst (asm) summable_cmult_iff) auto
  thus "\<alpha> > 2"
    by (subst (asm) summable_real_powr_iff) auto
qed

text \<open>Apostol's Lemma 1\<close>
lemma converges_absolutely_iff:
  fixes \<alpha>:: real
  shows "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Omega>* \<longleftrightarrow> \<alpha> > 2"
    (is "?P \<longleftrightarrow> _")
proof -
  have "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Omega>* \<longleftrightarrow>
        (\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on (\<Union>i \<in> {0<..}. omega_iter i)"
    by (simp add: omega_mz_eq)
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. \<Sum>\<omega>\<in>omega_iter i. 1 / norm \<omega> powr \<alpha>) summable_on {0<..}"
    using omega_iter_disjoint
    by (intro summable_on_Union_iff has_sum_finite finite_omega_iter refl)
       (auto simp: disjoint_family_on_def)
  also have "{0<..} = Suc ` UNIV"
    by (auto simp: image_iff) presburger?
  also have "(\<lambda>i. \<Sum>\<omega>\<in>omega_iter i. 1 / norm \<omega> powr \<alpha>) summable_on Suc ` UNIV \<longleftrightarrow>
             (\<lambda>i. \<Sum>\<omega>\<in>omega_iter (Suc i). 1 / norm \<omega> powr \<alpha>) summable_on UNIV"
    by (subst summable_on_reindex) (auto simp: o_def)
  also have "\<dots> \<longleftrightarrow> summable (\<lambda>i. \<Sum>\<omega>\<in>omega_iter (Suc i). 1 / norm \<omega> powr \<alpha>)"
    by (rule summable_on_UNIV_nonneg_real_iff) (auto intro: sum_nonneg)
  also have "\<dots> \<longleftrightarrow> \<alpha> > 2"
    using converges_absolutely_iff_aux1 converges_absolutely_iff_aux2 by blast
  finally show ?thesis .
qed

subsection \<open>Apostol's Lemma 2\<close>

lemma omega_not_limpt:
  shows "\<not> x islimpt \<Omega>"
proof
  show False if x: "x islimpt \<Omega>" for x
  proof -
    have ex_per: "\<exists>y. y \<in> \<Omega> \<and> y \<noteq> x \<and> dist y x < e" if "e > 0" for e
      by (metis x islimpt_approachable that)
    then obtain x' where x': "x' \<in> \<Omega>" "x' \<noteq> x" "dist x' x < Inf_para/2"
      by (meson Inf_para_positive half_gt_zero)
    then obtain x'' where x'': "x'' \<in> \<Omega>" "x'' \<noteq> x" "dist x x'' < min (Inf_para/2) (dist x x')"
      by (metis dist_commute ex_per min.commute min.strict_order_iff zero_less_dist_iff)
    then have "x' \<noteq> x''"
      by auto
    moreover have "dist x' x'' < Inf_para"
      using x' x'' by (metis dist_triangle_half_l dist_commute min_less_iff_conj)
    then have "x' = x''"
      using x' x'' by (smt (verit) Inf_para_le_norm dist_norm eq_iff_diff_eq_0 insert_iff omega_diff omega_omega_minus_zero)
    ultimately  show False ..
  qed
qed

corollary bounded_omega_finite:
  assumes "bounded B"
  shows "finite (\<Omega> \<inter> B)"
  by (meson omega_not_limpt inf.bounded_iff islimpt_subset \<open>bounded B\<close> bounded_infinite_imp_islimpt bounded_subset eq_refl)

corollary closed_omega: "closed \<Omega>"
  by (simp add: closed_limpt omega_not_limpt)

lemma closed_subset_omega: "\<Omega>' \<subseteq> \<Omega> \<Longrightarrow> closed \<Omega>'"
  unfolding closed_limpt using omega_not_limpt islimpt_subset by blast

corollary closed_omega_minus_zero: "closed \<Omega>*"
  unfolding omega_minus_zero_def by (rule closed_subset_omega) auto
  
abbreviation "disk R \<equiv> cball 0 R"

lemma lemma_2_bound:
  assumes "\<alpha> \<ge> 1" and "R > 0" 
  obtains M where "M > 0" "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Omega>; cmod \<omega> > R; cmod z \<le> R\<rbrakk> \<Longrightarrow> (cmod(z - \<omega>) powr -\<alpha>) \<le> M * (cmod \<omega> powr -\<alpha>)"
proof -
  obtain m where m: "of_int m > R / norm \<omega>1" "m \<ge> 0"
    by (metis ex_less_of_int le_less_trans linear not_le of_int_0_le_iff)
  obtain W where W: "W \<in> (\<Omega> - disk R) \<inter> disk (norm W)"
  proof 
    show "of_int m * \<omega>1 \<in> (\<Omega> - cball 0 R) \<inter> disk (norm (of_int m * \<omega>1))"
      using m omegaI [of m 0]
      by (simp add: field_simps norm_mult)
  qed
  define PF where "PF \<equiv> (\<Omega> - disk R) \<inter> disk (norm W)"
  have "finite PF"
    by (simp add: PF_def Diff_Int_distrib2 bounded_omega_finite)
  then have "finite (norm ` PF)"
    by blast
  then obtain r where "r \<in> norm ` PF"  "r \<le> norm W" and r: "\<And>x. x \<in> norm ` PF \<Longrightarrow> r \<le> x"
    using PF_def W Min_le Min_in by (metis empty_iff image_eqI)
  then obtain \<omega>r where \<omega>r: "\<omega>r \<in> PF" "norm \<omega>r = r"
    by blast 
  with assms have "\<omega>r \<in> \<Omega>" "\<omega>r \<noteq> 0" "r > 0"
    by (auto simp: PF_def)
  have minr: "r \<le> cmod \<omega>" if "\<omega> \<in> \<Omega>" "cmod \<omega> > R" for \<omega>
    using r  \<open>r \<le> cmod W\<close> that unfolding PF_def by fastforce
  have "R < r"
    using \<omega>r by (simp add: PF_def)
  with \<open>R > 0\<close> have R_iff_r: "cmod \<omega> > R \<longleftrightarrow> cmod \<omega> \<ge> r" if "\<omega> \<in> \<Omega>" for \<omega>
    using that by (auto simp: minr)
  define M where "M \<equiv> (1 - R/r) powr -\<alpha>"
  have "M > 0"
    unfolding M_def using \<open>R < r\<close> by auto
  moreover
  have "cmod (z - \<omega>) powr -\<alpha> \<le> M * cmod \<omega> powr -\<alpha>" 
    if "\<omega> \<in> \<Omega>" "cmod z \<le> R" "R < cmod \<omega>" for z \<omega>
  proof -
    have "r \<le> cmod \<omega>"
      using minr that by blast
    then have "\<omega> \<noteq> 0"
      using \<open>0 < r\<close> that by force
    have "1 - R/r \<le> 1 - norm (z/\<omega>)"
      using that \<open>0 < r\<close> \<open>0 < R\<close> \<open>\<omega> \<noteq> 0\<close> \<open>r \<le> cmod \<omega>\<close>
      by (simp add: field_simps norm_divide) (metis mult.commute mult_mono norm_ge_zero)
    also have "\<dots> \<le> norm (1 - z/\<omega>)"
      by (metis norm_one norm_triangle_ineq2)
    also have "\<dots> = norm ((z - \<omega>) / \<omega>)"
      by (simp add: \<open>\<omega> \<noteq> 0\<close> norm_minus_commute diff_divide_distrib)
    finally have *: "1 - R/r \<le> norm ((z - \<omega>) / \<omega>)" .
    have ge_rR: "cmod (z - \<omega>) \<ge> r - R"
      by (smt (verit) \<open>r \<le> cmod \<omega>\<close> norm_minus_commute norm_triangle_ineq2 that(2))
    have "1/M \<le> norm ((z - \<omega>) / \<omega>) powr \<alpha>"
    proof -
      have "1/M = (1 - R / r) powr \<alpha>"
        by (simp add: M_def powr_minus_divide)
      also have "\<dots> \<le> norm ((z - \<omega>) / \<omega>) powr \<alpha>"
        using * \<open>0 < r\<close> \<open>R < r\<close> \<open>1 \<le> \<alpha>\<close> powr_mono2 by force
      finally show ?thesis .
    qed
    then show ?thesis
      using \<open>R > 0\<close> \<open>M > 0\<close> \<open>\<omega> \<noteq> 0\<close>
      by (simp add: mult.commute divide_simps powr_divide norm_divide powr_minus)
  qed
  ultimately show thesis
    using that by presburger
qed

text \<open>Lemma 2 on Apostol p. 8\<close>
lemma converges_absolutely_in_disk:
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> disk R"
  shows "(\<lambda>\<omega>. cmod (z - \<omega>) powr -\<alpha>) summable_on (\<Omega> - disk R)"
proof -
  have \<Omega>: "\<Omega> - disk R \<subseteq> \<Omega>*"
    using assms omega_omega_minus_zero by auto
  obtain M where "M > 0" and M: "\<And>\<omega>. \<lbrakk>\<omega> \<in> \<Omega>; cmod \<omega> > R\<rbrakk> \<Longrightarrow> cmod(z - \<omega>) powr -\<alpha> \<le> M * (cmod \<omega> powr -\<alpha>)"
    using lemma_2_bound assms
    by (smt (verit, del_insts) less_eq_real_def mem_cball_0 one_le_numeral)
  have \<section>: "((\<lambda>\<omega>. 1 / cmod \<omega> powr \<alpha>) summable_on \<Omega>*)"
    using \<open>\<alpha> > 2\<close> converges_absolutely_iff by blast
  have "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Omega>*"
    using summable_on_cmult_right [OF \<section>] by (simp add: powr_minus field_class.field_divide_inverse)
  with \<Omega> have "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Omega> - disk R"
    using summable_on_subset_banach by blast
  then show ?thesis
    by (rule summable_on_comparison_test) (use M in auto)
qed

lemma converges_absolutely_in_disk':
  fixes \<alpha> :: nat and R :: real and z:: complex
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> disk R"
  shows "(\<lambda>\<omega>. 1 / norm (z - \<omega>) ^ \<alpha>) summable_on (\<Omega> - disk R)"
proof -
  have "(\<lambda>\<omega>. norm (z - \<omega>) powr -of_nat \<alpha>) summable_on (\<Omega> - disk R)"
    using assms by (intro converges_absolutely_in_disk) auto
  also have "?this \<longleftrightarrow> ?thesis"
    unfolding powr_minus
    by (intro summable_on_cong refl, subst powr_realpow)
       (use assms in \<open>auto simp: field_simps\<close>)
  finally show ?thesis .
qed

lemma converges_in_disk':
  fixes \<alpha> :: nat and R :: real and z:: complex
  assumes "\<alpha> > 2" and "R > 0" and "z \<in> disk R"
  shows "(\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) summable_on (\<Omega> - disk R)"
  by (rule abs_summable_summable)
     (use converges_absolutely_in_disk'[OF assms] in \<open>simp add: norm_divide norm_power\<close>)

lemma converges_absolutely:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2" and "\<Omega>' \<subseteq> \<Omega>"
  shows "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Omega>'"
proof (cases "z = 0")
  case True
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Omega>*"
    using converges_absolutely_iff[of \<alpha>] assms by (simp add: powr_minus field_simps)
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on \<Omega>"
    by (simp add: omega_omega_minus_zero summable_on_insert_iff)
  thus ?thesis
    by (rule summable_on_subset_banach) fact
next
  case [simp]: False
  define R where "R = norm z"
  have "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on (\<Omega> - disk R)"
    using assms by (intro converges_absolutely_in_disk) (auto simp: R_def)
  hence "(\<lambda>\<omega>. norm (z - \<omega>) powr -\<alpha>) summable_on (\<Omega> - disk R) \<union> (\<Omega> \<inter> disk R)"
    by (intro bounded_omega_finite summable_on_union[OF _ summable_on_finite]) auto
  also have "\<dots> = \<Omega>"
    by blast
  finally show ?thesis
    by (rule summable_on_subset) fact
qed

lemma converges_absolutely':
  fixes \<alpha> :: nat
  assumes "\<alpha> > 2" and "\<Omega>' \<subseteq> \<Omega>"
  shows "(\<lambda>\<omega>. 1 / norm (z - \<omega>) ^ \<alpha>) summable_on \<Omega>'"
  using converges_absolutely[of "of_nat \<alpha>" \<Omega>' z] assms
  by (simp add: powr_nat' powr_minus field_simps norm_power norm_divide powr_realpow')

lemma converges:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2" and "\<Omega>' \<subseteq> \<Omega>"
  shows "(\<lambda>\<omega>. (z - \<omega>) powr -\<alpha>) summable_on \<Omega>'"
  by (rule abs_summable_summable)
     (use converges_absolutely[OF assms] in \<open>simp add: norm_divide norm_powr_real_powr'\<close>)

lemma converges':
  fixes \<alpha> :: nat
  assumes "\<alpha> > 2" and "\<Omega>' \<subseteq> \<Omega>"
  shows "(\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) summable_on \<Omega>'"
  using converges[of "of_nat \<alpha>" \<Omega>' z] assms 
  by (simp add: powr_nat' powr_minus field_simps)

lemma
  fixes \<alpha> R :: real
  assumes "\<alpha> > 2" "R > 0"
  shows converges_absolutely_uniformly_in_disk:
          "uniform_limit (disk R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. norm ((z - \<omega>) powr -\<alpha>))
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. norm ((z - \<omega>) powr -\<alpha>))
                         (finite_subsets_at_top (\<Omega> - disk R))" (is ?th1)
  and   converges_uniformly_in_disk:
          "uniform_limit (disk R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. (z - \<omega>) powr -\<alpha>)
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. (z - \<omega>) powr -\<alpha>)
                         (finite_subsets_at_top (\<Omega> - disk R))" (is ?th2)
proof -
  obtain M where M:
    "M > 0" "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Omega>; norm \<omega> > R; norm z \<le> R\<rbrakk> \<Longrightarrow> norm (z - \<omega>) powr -\<alpha> \<le> M * norm \<omega> powr -\<alpha>"
    using lemma_2_bound[of \<alpha> R] assms by auto

  have 1: "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on (\<Omega> - cball 0 R)"
  proof -
    have "(\<lambda>\<omega>. 1 / norm \<omega> powr \<alpha>) summable_on \<Omega>*"
      using assms by (subst converges_absolutely_iff) auto
    hence "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on \<Omega>*"
      by (intro summable_on_cmult_right) (auto simp: powr_minus field_simps)
    thus "(\<lambda>\<omega>. M * norm \<omega> powr -\<alpha>) summable_on (\<Omega> - cball 0 R)"
      by (rule summable_on_subset) (use assms in \<open>auto simp: omega_minus_zero_def\<close>)
  qed

  have 2: "norm ((z - \<omega>) powr -\<alpha>) \<le> M * norm \<omega> powr -\<alpha>"
    if "\<omega> \<in> \<Omega> - cball 0 R" "z \<in> cball 0 R" for \<omega> z
  proof -
    have "norm ((z - \<omega>) powr -\<alpha>) = norm (z - \<omega>) powr -\<alpha>"
      by (auto simp add: powr_def)
    also have "\<dots> \<le> M * norm \<omega> powr -\<alpha>"
      using that by (intro M) auto
    finally show "norm ((z - \<omega>) powr -\<alpha>) \<le> M * norm \<omega> powr -\<alpha>"
      by simp
  qed

  show ?th1 ?th2
    by (rule Weierstrass_m_test_general[OF _ 1]; use 2 in simp)+
qed

definition eisenstein_fun :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fun n z =
     (if n = 0 then 1 else if n < 3 \<or> z \<in> \<Omega>* then 0 else (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (z - \<omega>) ^ n))"

lemma eisenstein_fun_at_pole_eq_0: "n > 0 \<Longrightarrow> z \<in> \<Omega>* \<Longrightarrow> eisenstein_fun n z = 0"
  by (simp add: eisenstein_fun_def)

lemma eisenstein_fun_has_sum:
  assumes "n \<ge> 3" "z \<notin> \<Omega>*"
  shows   "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum eisenstein_fun n z) \<Omega>*"
proof -
  have "eisenstein_fun n z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (z - \<omega>) ^ n)"
    using assms by (simp add: eisenstein_fun_def)
  also have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum \<dots>) \<Omega>*"
    using assms by (intro has_sum_infsum converges') (auto simp: omega_minus_zero_def)
  finally show ?thesis .
qed

lemma eisenstein_fun_minus: "eisenstein_fun n (-z) = (-1) ^ n * eisenstein_fun n z"
proof (cases "n < 3 \<or> z \<in> \<Omega>*")
  case False
  have "eisenstein_fun n (-z) = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (- z - \<omega>) ^ n)"
    using False by (auto simp: eisenstein_fun_def omega_minus_zero_minus_iff)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity>\<omega>\<in>uminus ` \<Omega>*. 1 / (\<omega> - z) ^ n)"
    by (subst infsum_reindex) (auto simp: o_def minus_diff_commute inj_on_def)
  also have "uminus ` \<Omega>* = \<Omega>*"
    by (auto simp: omega_minus_zero_minus_iff image_def intro: bexI[of _ "-x" for x])
  also have "(\<lambda>\<omega>. 1 / (\<omega> - z) ^ n) = (\<lambda>\<omega>. (-1) ^ n * (1 / (z - \<omega>) ^ n))"
  proof
    fix \<omega> :: complex
    have "1 / (\<omega> - z) ^ n = (1 / (\<omega> - z)) ^ n"
      by (simp add: power_divide)
    also have "1 / (\<omega> - z) = (-1) / (z - \<omega>)"
      by (simp add: divide_simps)
    also have "\<dots> ^ n = (-1) ^ n * (1 / (z - \<omega>) ^ n)"
      by (subst power_divide) auto
    finally show "1 / (\<omega> - z) ^ n = (-1) ^ n * (1 / (z - \<omega>) ^ n)" .
  qed
  also have "(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. (-1) ^ n * (1 / (z - \<omega>) ^ n)) = (-1) ^ n * eisenstein_fun n z"
    using False by (subst infsum_cmult_right') (auto simp: eisenstein_fun_def)
  finally show ?thesis .
qed (auto simp: eisenstein_fun_def omega_minus_zero_minus_iff)

lemma eisenstein_fun_even_minus: "even n \<Longrightarrow> eisenstein_fun n (-z) = eisenstein_fun n z"
  by (simp add: eisenstein_fun_minus)

lemma eisenstein_fun_odd_minus: "odd n \<Longrightarrow> eisenstein_fun n (-z) = -eisenstein_fun n z"
  by (simp add: eisenstein_fun_minus)

(* TODO generalise. The ball is not needed. *)
lemma eisenstein_fun_has_field_derivative_aux:
  fixes \<alpha> :: nat and R :: real
  defines "F \<equiv> (\<lambda>\<alpha> z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>) ^ \<alpha>)"
  assumes "\<alpha> > 2" "R > 0" "w \<in> ball 0 R"
  shows   "(F \<alpha> has_field_derivative -of_nat \<alpha> * F (Suc \<alpha>) w) (at w)"
proof -
  define \<alpha>' where "\<alpha>' = \<alpha> - 1"
  have \<alpha>': "\<alpha> = Suc \<alpha>'"
    using assms by (simp add: \<alpha>'_def)
  have 1: "\<forall>\<^sub>F n in finite_subsets_at_top (\<Omega> - cball 0 R).
            continuous_on (cball 0 R) (\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>) ^ \<alpha>) \<and>
            (\<forall>z\<in>ball 0 R. ((\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>) ^ \<alpha>) has_field_derivative (\<Sum>\<omega>\<in>n. -\<alpha> / (z - \<omega>) ^ Suc \<alpha>)) (at z))"
    (* TODO FIXME: ugly *)
  proof (intro eventually_finite_subsets_at_top_weakI conjI continuous_intros derivative_intros ballI)
    fix z::complex and X n
    assume "finite X"  "X \<subseteq> \<Omega> - cball 0 R"
        and "z \<in> ball 0 R"  "n \<in> X"
    then show "((\<lambda>z. 1 / (z - n) ^ \<alpha>) has_field_derivative of_int (- int \<alpha>) / (z - n) ^ Suc \<alpha>) (at z)"
     apply (auto intro!: derivative_eq_intros simp: divide_simps)
      apply (simp add: algebra_simps \<alpha>')
      done
  qed auto

  have "uniform_limit (disk R)
                      (\<lambda>X z. \<Sum>\<omega>\<in>X. (z - \<omega>) powr of_real (-of_nat \<alpha>))
                      (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. (z - \<omega>) powr of_real (-of_nat \<alpha>))
                      (finite_subsets_at_top (\<Omega> - disk R))"
    using assms by (intro converges_uniformly_in_disk) auto
  also have "?this \<longleftrightarrow> uniform_limit (disk R) (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>) ^ \<alpha>) (F \<alpha>)
                         (finite_subsets_at_top (\<Omega> - disk R))"
    using assms unfolding F_def
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI)
       (auto simp: powr_minus powr_nat field_simps intro!: sum.cong infsum_cong)
  finally have 2: \<dots> .

  have 3: "finite_subsets_at_top (\<Omega> - cball 0 R) \<noteq> bot"
    by simp

  obtain g where g: "continuous_on (cball 0 R) (F \<alpha>)"
                    "\<And>w. w \<in> ball 0 R \<Longrightarrow> (F \<alpha> has_field_derivative g w) (at w) \<and>
                        ((\<lambda>\<omega>. -of_nat \<alpha> / (w - \<omega>) ^ Suc \<alpha>) has_sum g w) (\<Omega> - cball 0 R)"
    unfolding has_sum_def using has_complex_derivative_uniform_limit[OF 1 2 3 \<open>R > 0\<close>] by auto

  have "((\<lambda>\<omega>. -of_nat \<alpha> * (1 / (w - \<omega>) ^ Suc \<alpha>)) has_sum -of_nat \<alpha> * F (Suc \<alpha>) w) (\<Omega> - cball 0 R)"
    unfolding F_def using assms
    by (intro has_sum_cmult_right has_sum_infsum converges_in_disk') auto
  moreover have "((\<lambda>\<omega>.  -of_nat \<alpha> * (1 / (w - \<omega>) ^ Suc \<alpha>)) has_sum g w) (\<Omega> - cball 0 R)"
    using g(2)[of w] assms by simp
  ultimately have "g w = -of_nat \<alpha> * F (Suc \<alpha>) w"
    by (metis infsumI)
  thus ?thesis
    using g(2)[of w] assms by (simp add: F_def)
qed

lemma eisenstein_fun_has_field_derivative:
  assumes z: "z \<notin> \<Omega>*" and n: "n \<ge> 3"
  shows   "(eisenstein_fun n has_field_derivative -of_nat n * eisenstein_fun (Suc n) z) (at z)"
proof -
  define R where "R = norm z + 1"
  have R: "R > 0" "norm z < R"
    by (auto simp: R_def add_nonneg_pos)
  have "finite (\<Omega> \<inter> cball 0 R)"
    by (simp add: bounded_omega_finite)
  moreover have "\<Omega>* \<inter> cball 0 R \<subseteq> \<Omega> \<inter> cball 0 R"
    unfolding omega_minus_zero_def by blast
  ultimately have fin: "finite (\<Omega>* \<inter> cball 0 R)"
    using finite_subset by blast
  define n' where "n' = n - 1"
  from n have n': "n = Suc n'"
    by (simp add: n'_def)

  define F1 where "F1 = (\<lambda>n z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>) ^ n)"
  define F2 where "F2 = (\<lambda>n z. \<Sum>\<omega>\<in>\<Omega>*\<inter>disk R. 1 / (z - \<omega>) ^ n)"

  have "(F1 n has_field_derivative -of_nat n * F1 (Suc n) z) (at z)"
    unfolding F1_def
    by (rule eisenstein_fun_has_field_derivative_aux) (use n in \<open>auto simp: R_def add_nonneg_pos\<close>)
  moreover have "(F2 n has_field_derivative -of_nat n * F2 (Suc n) z) (at z)"
    unfolding F2_def sum_distrib_left omega_minus_zero_def
    by (rule derivative_eq_intros refl sum.cong | use R z n in \<open>force simp: omega_minus_zero_def\<close>)+
       (simp add: divide_simps power3_eq_cube power4_eq_xxxx n')
  ultimately have "((\<lambda>z. F1 n z + F2 n z) has_field_derivative
                     (-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z)) (at z)"
    by (intro derivative_intros)
  also have "?this \<longleftrightarrow> (eisenstein_fun n has_field_derivative (-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z)) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z'. z' \<in> -\<Omega>*) (nhds z)"
      using z by (intro eventually_nhds_in_open) (auto simp: closed_omega_minus_zero)
    thus "\<forall>\<^sub>F x in nhds z. x \<in> UNIV \<longrightarrow> F1 n x + F2 n x = eisenstein_fun n x"
    proof eventually_elim
      case (elim z)
      have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum (F1 n z + F2 n z)) ((\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R))"
        unfolding F1_def F2_def using R fin n
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite]
                  summable_on_subset[OF converges']) auto
      also have "(\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R) = \<Omega>*"
        using R unfolding omega_minus_zero_def by auto
      finally show ?case using elim n 
        unfolding F1_def F2_def by (simp add: infsumI eisenstein_fun_def)
    qed
  qed auto
  also have "(-of_nat n * F1 (Suc n) z) + (-of_nat n * F2 (Suc n) z) = -of_nat n * (F1 (Suc n) z + F2 (Suc n) z)"
    by (simp add: algebra_simps)
  also have "F1 (Suc n) z + F2 (Suc n) z = eisenstein_fun (Suc n) z"
  proof -
    have "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ Suc n) has_sum (F1 (Suc n) z + F2 (Suc n) z)) ((\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R))"
      unfolding F1_def F2_def using R fin n
      by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite] converges') auto
    also have "(\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R) = \<Omega>*"
      using R unfolding omega_minus_zero_def by auto
    finally show ?thesis using n z
      unfolding F1_def F2_def eisenstein_fun_def by (simp add: infsumI)
  qed
  finally show ?thesis .
qed

lemmas eisenstein_fun_has_field_derivative' [derivative_intros] =
  DERIV_chain2[OF eisenstein_fun_has_field_derivative]

lemma higher_deriv_eisenstein_fun:
  assumes z: "z \<notin> \<Omega>*" and n: "n \<ge> 3"
  shows   "(deriv ^^ m) (eisenstein_fun n) z =
             (-1) ^ m * pochhammer (of_nat n) m * eisenstein_fun (n + m) z"
  using z n
proof (induction m arbitrary: z n)
  case 0
  thus ?case by simp
next
  case (Suc m z n)
  have ev: "eventually (\<lambda>z. z \<in> -\<Omega>*) (nhds z)"
    using Suc.prems closed_omega_minus_zero by (intro eventually_nhds_in_open) auto
  have "(deriv ^^ Suc m) (eisenstein_fun n) z = deriv ((deriv ^^ m) (eisenstein_fun n)) z"
    by simp
  also have "\<dots> = deriv (\<lambda>z. (-1)^ m * pochhammer (of_nat n) m * eisenstein_fun (n + m) z) z"
    by (intro deriv_cong_ev eventually_mono[OF ev]) (use Suc in auto)
  also have "\<dots> = (-1) ^ Suc m * pochhammer (of_nat n) (Suc m) * eisenstein_fun (Suc (n + m)) z"
    using Suc.prems
    by (intro DERIV_imp_deriv)
       (auto intro!: derivative_eq_intros simp: pochhammer_Suc algebra_simps)
  finally show ?case
    by simp
qed

lemma eisenstein_fun_holomorphic: "n \<ge> 3 \<Longrightarrow> eisenstein_fun n holomorphic_on -\<Omega>*"
  using closed_omega_minus_zero
  by (subst holomorphic_on_open) (auto intro!: eisenstein_fun_has_field_derivative)

lemma eisenstein_fun_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*" "n \<ge> 3"
  shows   "(\<lambda>z. eisenstein_fun n (f z)) holomorphic_on A"
proof -
  have "eisenstein_fun n \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms eisenstein_fun_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun_analytic: "n \<ge> 3 \<Longrightarrow> eisenstein_fun n analytic_on -\<Omega>*"
  by (simp add: analytic_on_open closed_omega_minus_zero open_Compl eisenstein_fun_holomorphic)  

lemma eisenstein_fun_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*" "n \<ge> 3"
  shows   "(\<lambda>z. eisenstein_fun n (f z)) analytic_on A"
proof -
  have "eisenstein_fun n \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms eisenstein_fun_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun_continuous_on: "n \<ge> 3 \<Longrightarrow> continuous_on (-\<Omega>*) (eisenstein_fun n)"
  using holomorphic_on_imp_continuous_on eisenstein_fun_holomorphic by blast

lemma eisenstein_fun_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*" "n \<ge> 3"
  shows   "continuous_on A (\<lambda>z. eisenstein_fun n (f z))"
  by (rule continuous_on_compose2[OF eisenstein_fun_continuous_on assms(1)]) (use assms in auto)

lemma translate:
  fixes \<alpha> :: real
  assumes "\<alpha> > 2"
  shows   "(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>. (z + w - \<omega>) powr -\<alpha>) = (\<Sum>\<^sub>\<infinity>\<omega>\<in>(+) (-w) ` \<Omega>. (z - \<omega>) powr -\<alpha>)"
  by (subst infsum_reindex) (auto simp: o_def algebra_simps)

lemma holomorphic:
  assumes "\<alpha> > 2" "\<Omega>' \<subseteq> \<Omega>" "finite (\<Omega> - \<Omega>')"
  shows   "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on -\<Omega>'"
proof -
  define M where "M = Max (insert 0 (norm ` (\<Omega> - \<Omega>')))"
  have M: "M \<ge> 0" "\<And>\<omega>. \<omega> \<in> \<Omega> - \<Omega>' \<Longrightarrow> M \<ge> norm \<omega>"
    using assms by (auto simp: M_def)
  have [simp]: "closed \<Omega>'"
    using assms(2) by (rule closed_subset_omega)

  have *: "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on ball 0 R - \<Omega>'" if R: "R > M" for R
  proof -
    define F where "F = (\<lambda>\<alpha> z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>) ^ \<alpha>)"
    define G where "G = (\<lambda>\<alpha> z. \<Sum>\<omega>\<in>\<Omega>'\<inter>disk R. 1 / (z - \<omega>) ^ \<alpha>)"

    have "(F \<alpha> has_field_derivative -of_nat \<alpha> * F (Suc \<alpha>) z) (at z)" if z: "z \<in> ball 0 R" for z
      unfolding F_def using assms R M(1) z by (intro eisenstein_fun_has_field_derivative_aux) auto
    hence "F \<alpha> holomorphic_on ball 0 R - \<Omega>'"
      using holomorphic_on_open \<open>closed \<Omega>'\<close> by blast
    hence "(\<lambda>z. F \<alpha> z + G \<alpha> z) holomorphic_on ball 0 R - \<Omega>'"
      unfolding G_def using assms M R by (intro holomorphic_intros) auto
    also have "(\<lambda>z. F \<alpha> z + G \<alpha> z) = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>'. 1 / (z - \<omega>) ^ \<alpha>)"
    proof
      fix z :: complex
      have "finite (\<Omega> \<inter> cball 0 R)"
        by (intro bounded_omega_finite) auto
      moreover have "\<Omega>' \<inter> cball 0 R \<subseteq> \<Omega> \<inter> cball 0 R"
        using assms by blast
      ultimately have "finite (\<Omega>' \<inter> cball 0 R)"
        using finite_subset by blast
      hence "((\<lambda>\<omega>. 1 / (z - \<omega>) ^ \<alpha>) has_sum (F \<alpha> z + G \<alpha> z)) ((\<Omega> - disk R) \<union> (\<Omega>' \<inter> disk R))"
        unfolding F_def G_def using assms
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite] converges') auto
      also have "(\<Omega> - disk R) \<union> (\<Omega>' \<inter> disk R) = \<Omega>'"
        using M R assms by (force simp: not_le)
      finally show "F \<alpha> z + G \<alpha> z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>'. 1 / (z - \<omega>) ^ \<alpha>)"
        by (simp add: infsumI)
    qed
    finally show ?thesis .
  qed

  have "(\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>'. 1 / (z - \<omega>) ^ \<alpha>) holomorphic_on (\<Union>R\<in>{R. R > M}. ball 0 R - \<Omega>')"
    by (rule holomorphic_on_UN_open) (use * \<open>closed \<Omega>'\<close> in auto)
  also have "\<dots> = (\<Union>R\<in>{R. R > M}. ball 0 R) - \<Omega>'"
    by blast
  also have "(\<Union>R\<in>{R. R > M}. ball 0 R) = (UNIV :: complex set)"
  proof (safe intro!: UN_I)
    fix z :: complex
    show "norm z + M + 1 > M" "z \<in> ball 0 (norm z + M + 1)"
      using M(1) by (auto intro: add_nonneg_pos)
  qed auto
  finally show ?thesis
    by (simp add: Compl_eq_Diff_UNIV)
qed

definition eisenstein_fun' :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fun' n z = (if n < 3 \<or> z \<in> \<Omega> then 0 else (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>. 1 / (z - \<omega>) ^ n))"

lemma eisenstein_fun'_has_sum:
  "n \<ge> 3 \<Longrightarrow> z \<notin> \<Omega> \<Longrightarrow> ((\<lambda>\<omega>. 1 / (z - \<omega>) ^ n) has_sum eisenstein_fun' n z) \<Omega>"
  unfolding eisenstein_fun'_def by (auto intro!: has_sum_infsum converges')

lemma eisenstein_fun'_at_pole_eq_0: "z \<in> \<Omega> \<Longrightarrow> eisenstein_fun' n z = 0"
  by (simp add: eisenstein_fun'_def)

lemma eisenstein_fun'_conv_eisenstein_fun:
  assumes "n \<ge> 3" "z \<notin> \<Omega>"
  shows   "eisenstein_fun' n z = eisenstein_fun n z + 1 / z ^ n"
proof -
  from assms have "eisenstein_fun' n z = (\<Sum>\<^sub>\<infinity>\<omega>\<in>insert 0 \<Omega>*. 1 / (z - \<omega>) ^ n)"
    by (simp add: eisenstein_fun'_def omega_omega_minus_zero)
  also from assms have "\<dots> = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (z - \<omega>) ^ n) + 1 / z ^ n"
    by (subst infsum_insert)
       (auto intro!: converges' simp: zero_notin_omega_mz omega_omega_minus_zero)
  also from assms have "\<dots> = eisenstein_fun n z + 1 / z ^ n"
    by (simp add: eisenstein_fun_def omega_omega_minus_zero)
  finally show ?thesis .
qed

lemma eisenstein_fun'_altdef:
  "eisenstein_fun' n z = (if n < 3 \<or> z \<in> \<Omega> then 0 else eisenstein_fun n z + 1 / z ^ n)"
  using eisenstein_fun'_conv_eisenstein_fun[of n z]
  by (auto simp: eisenstein_fun'_def eisenstein_fun_def omega_minus_zero_def)

lemma eisenstein_fun'_minus: "eisenstein_fun' n (-z) = (-1) ^ n * eisenstein_fun' n z"
  by (auto simp: eisenstein_fun'_altdef eisenstein_fun_minus omega_minus_iff power_minus' divide_simps)
     (auto simp: algebra_simps)

lemma eisenstein_fun'_even_minus: "even n \<Longrightarrow> eisenstein_fun' n (-z) = eisenstein_fun' n z"
  by (simp add: eisenstein_fun'_minus)

lemma eisenstein_fun'_odd_minus: "odd n \<Longrightarrow> eisenstein_fun' n (-z) = -eisenstein_fun' n z"
  by (simp add: eisenstein_fun'_minus)

lemma eisenstein_fun'_has_field_derivative:
  assumes "n \<ge> 3" "z \<notin> \<Omega>"
  shows   "(eisenstein_fun' n has_field_derivative -of_nat n * eisenstein_fun' (Suc n) z) (at z)"
proof -
  define n' where "n' = n - 1"
  have n': "n = Suc n'"
    using assms by (simp add: n'_def)
  have ev: "eventually (\<lambda>z. z \<in> -\<Omega>) (nhds z)"
    using assms closed_omega by (intro eventually_nhds_in_open) auto

  have "((\<lambda>z. eisenstein_fun n z + 1 / z ^ n) has_field_derivative
        -of_nat n * eisenstein_fun' (Suc n) z) (at z)"
    using assms
    apply (auto intro!: derivative_eq_intros)
     apply (auto simp: eisenstein_fun'_conv_eisenstein_fun omega_omega_minus_zero field_simps n')
    done
  also have "?this \<longleftrightarrow> ?thesis"
    using assms by (intro has_field_derivative_cong_ev refl eventually_mono[OF ev])
                   (auto simp: eisenstein_fun'_conv_eisenstein_fun)
  finally show ?thesis .
qed

lemmas eisenstein_fun'_has_field_derivative' [derivative_intros] =
  DERIV_chain2[OF eisenstein_fun'_has_field_derivative]

lemma eisenstein_fun'_holomorphic: "n \<ge> 3 \<Longrightarrow> eisenstein_fun' n holomorphic_on -\<Omega>"
  using closed_omega
  by (subst holomorphic_on_open) (auto intro!: eisenstein_fun'_has_field_derivative)

lemma higher_deriv_eisenstein_fun':
  assumes z: "z \<notin> \<Omega>" and n: "n \<ge> 3"
  shows   "(deriv ^^ m) (eisenstein_fun' n) z =
             (-1) ^ m * pochhammer (of_nat n) m * eisenstein_fun' (n + m) z"
  using z n
proof (induction m arbitrary: z n)
  case 0
  thus ?case by simp
next
  case (Suc m z n)
  have ev: "eventually (\<lambda>z. z \<in> -\<Omega>) (nhds z)"
    using Suc.prems closed_omega by (intro eventually_nhds_in_open) auto
  have "(deriv ^^ Suc m) (eisenstein_fun' n) z = deriv ((deriv ^^ m) (eisenstein_fun' n)) z"
    by simp
  also have "\<dots> = deriv (\<lambda>z. (-1)^ m * pochhammer (of_nat n) m * eisenstein_fun' (n + m) z) z"
    by (intro deriv_cong_ev eventually_mono[OF ev]) (use Suc in auto)
  also have "\<dots> = (-1) ^ Suc m * pochhammer (of_nat n) (Suc m) * eisenstein_fun' (Suc (n + m)) z"
    using Suc.prems
    by (intro DERIV_imp_deriv)
       (auto intro!: derivative_eq_intros simp: pochhammer_Suc algebra_simps)
  finally show ?case
    by simp
qed

lemma eisenstein_fun'_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>" "n \<ge> 3"
  shows   "(\<lambda>z. eisenstein_fun' n (f z)) holomorphic_on A"
proof -
  have "eisenstein_fun' n \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms eisenstein_fun'_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun'_analytic: "n \<ge> 3 \<Longrightarrow> eisenstein_fun' n analytic_on -\<Omega>"
  by (simp add: analytic_on_open closed_omega open_Compl eisenstein_fun'_holomorphic)  

lemma eisenstein_fun'_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>" "n \<ge> 3"
  shows   "(\<lambda>z. eisenstein_fun' n (f z)) analytic_on A"
proof -
  have "eisenstein_fun' n \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms eisenstein_fun'_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma eisenstein_fun'_continuous_on: "n \<ge> 3 \<Longrightarrow> continuous_on (-\<Omega>) (eisenstein_fun' n)"
  using holomorphic_on_imp_continuous_on eisenstein_fun'_holomorphic by blast

lemma eisenstein_fun'_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>" "n \<ge> 3"
  shows   "continuous_on A (\<lambda>z. eisenstein_fun' n (f z))"
  by (rule continuous_on_compose2[OF eisenstein_fun'_continuous_on assms(1)]) (use assms in auto)

(* TODO Move *)
lemma omega_plus_right_cancel [simp]: "y \<in> \<Omega> \<Longrightarrow> x + y \<in> \<Omega> \<longleftrightarrow> x \<in> \<Omega>"
  by (metis add_diff_cancel_right' omega_add omega_diff)

lemma omega_plus_left_cancel [simp]: "x \<in> \<Omega> \<Longrightarrow> x + y \<in> \<Omega> \<longleftrightarrow> y \<in> \<Omega>"
  by (metis add.commute omega_plus_right_cancel)

lemma eisenstein_fun'_is_periodic:
  assumes n: "n \<ge> 3" and \<omega>: "\<omega> \<in> \<Omega>"
  shows   "is_periodic \<omega> (eisenstein_fun' n)"
    unfolding is_periodic_def
proof
  fix z :: complex
  show "eisenstein_fun' n (z + \<omega>) = eisenstein_fun' n z"
  proof (cases "z \<in> \<Omega>")
    case False
    have "(\<Sum>\<^sub>\<infinity>\<omega>'\<in>\<Omega>. (z + \<omega> - \<omega>') powr of_real (-of_nat n)) =
          (\<Sum>\<^sub>\<infinity>\<omega>'\<in>(\<lambda>x. x - \<omega>) ` \<Omega>. (z - \<omega>') powr -real n)"
      using n by (subst translate) auto
    also have "(\<lambda>x. x - \<omega>) ` \<Omega> = \<Omega>"
      using omega_shift_omega[of "-\<omega>"] \<omega> by (simp add: omega_minus_iff)          
    finally show ?thesis using False \<omega>
      by (auto simp: eisenstein_fun'_def powr_minus field_simps powr_nat')
  qed (use \<omega> in \<open>auto simp: eisenstein_fun'_at_pole_eq_0\<close>)
qed

lemma eisenstein_fun'_is_doubly_periodic:
  assumes n: "n \<ge> 3"
  shows   "is_doubly_periodic \<omega>1 \<omega>2 (eisenstein_fun' n)"
  unfolding is_doubly_periodic_def
  by (intro conjI ratio_notin_real eisenstein_fun'_is_periodic assms omegaI1 omegaI2)

lemma is_pole_eisenstein_fun':
  assumes n: "n \<ge> 3" and \<omega>:  "\<omega> \<in> \<Omega>"
  shows   "is_pole (eisenstein_fun' n) \<omega>"
proof -
  have "is_pole (eisenstein_fun' n) 0"
  proof -
    have "eventually (\<lambda>z. z \<in> -\<Omega>*) (nhds 0)"
      using closed_omega_minus_zero 
      by (intro eventually_nhds_in_open) (auto simp: zero_notin_omega_mz)
    hence ev: "eventually (\<lambda>z. z \<notin> \<Omega>) (at 0)"
      unfolding eventually_at_filter by eventually_elim (auto simp: omega_minus_zero_def)
    have "\<Omega> - \<Omega>* = {0}" "\<Omega>* \<subseteq> \<Omega>"
      by (auto simp: insert_Diff_if omega_omega_minus_zero zero_notin_omega_mz)
    hence "eisenstein_fun n holomorphic_on -\<Omega>*"
      using n by (auto intro!: holomorphic_intros)
    hence "continuous_on (-\<Omega>*) (eisenstein_fun n)"
      using holomorphic_on_imp_continuous_on by blast
    moreover have "0 \<in> -\<Omega>*"
      by (auto simp: omega_minus_zero_def)
    ultimately have "(eisenstein_fun n \<longlongrightarrow> eisenstein_fun n 0) (at 0)"
      using closed_omega_minus_zero by (metis at_within_open closed_open continuous_on_def)
    moreover have "filterlim (\<lambda>z::complex. 1 / z ^ n) at_infinity (at 0)"
      using is_pole_inverse_power[of n 0] n by (simp add: is_pole_def)
    ultimately have "filterlim (\<lambda>z. eisenstein_fun n z + 1 / z ^ n) at_infinity (at 0)"
      by (rule tendsto_add_filterlim_at_infinity)
    also have "?this \<longleftrightarrow> filterlim (eisenstein_fun' n) at_infinity (at 0)"
      by (intro filterlim_cong refl eventually_mono[OF ev])
         (use n in \<open>auto simp: eisenstein_fun'_conv_eisenstein_fun\<close>)
    finally show ?thesis
      by (simp add: is_pole_def)
  qed
  thus "is_pole (eisenstein_fun' n) \<omega>"
    using is_periodic_pole_minus[OF eisenstein_fun'_is_periodic[OF n, of "-\<omega>"], of 0] \<omega>
    by (simp add: omega_minus_iff)
qed

lemma isolated_singularity_at_eisenstein_fun':
  assumes n: "n \<ge> 3"
  shows   "isolated_singularity_at (eisenstein_fun' n) \<omega>"
proof -
  have "\<not>\<omega> islimpt \<Omega>"
    by (simp add: omega_not_limpt)
  then obtain r where r: "r > 0" "ball \<omega> r \<inter> \<Omega> - {\<omega>} = {}"
    by (subst (asm) islimpt_approachable) (auto simp: dist_commute ball_def)
  hence "eisenstein_fun' n analytic_on ball \<omega> r - {\<omega>}"
    using n by (intro analytic_intros) auto
  thus "isolated_singularity_at (eisenstein_fun' n) \<omega>"
    unfolding isolated_singularity_at_def using \<open>r > 0\<close> by blast
qed



  
lemma eisenstein_fun'_nicely_meromorphic [meromorphic_intros]:
  assumes "n \<ge> 3"
  shows "eisenstein_fun' n nicely_meromorphic_on UNIV"
proof (rule nicely_meromorphic_onI_open)
  show "eisenstein_fun' n analytic_on UNIV - \<Omega>"
    using eisenstein_fun'_analytic[OF \<open>n\<ge>3\<close>] 
    by (simp add: Compl_eq_Diff_UNIV)
  show "\<And>x. x \<in> \<Omega> 
      \<Longrightarrow> is_pole (eisenstein_fun' n) x \<and> eisenstein_fun' n x = 0"
    by (simp add: assms gen_lattice.eisenstein_fun'_def 
        gen_lattice_axioms is_pole_eisenstein_fun')
  show "\<And>x. isolated_singularity_at (eisenstein_fun' n) x"
    using assms isolated_singularity_at_eisenstein_fun' by auto
qed simp

lemma eisenstein_fun'_meromorphic [meromorphic_intros]:
  assumes "n \<ge> 3"
  shows "eisenstein_fun' n meromorphic_on UNIV"
  using assms eisenstein_fun'_nicely_meromorphic 
    nicely_meromorphic_on_def by blast

(* Theorem 1.9 p.9 *)
theorem eisenstein_fun'_is_elliptic [elliptic_fun_intros]: 
  assumes n: "n \<ge> 3"
  shows   "elliptic_fun (eisenstein_fun' n) \<omega>1 \<omega>2"
proof 
  show "\<forall>z. is_pole (eisenstein_fun' n) z \<and> eisenstein_fun' n z = 0 
            \<or> eisenstein_fun' n \<midarrow>z\<rightarrow> eisenstein_fun' n z"
    by (metis Compl_iff analytic_at_imp_isCont analytic_on_analytic_at 
        assms eisenstein_fun'_at_pole_eq_0 gen_lattice.eisenstein_fun'_analytic 
        gen_lattice.is_pole_eisenstein_fun' gen_lattice_axioms isContD)
  show "is_doubly_periodic \<omega>1 \<omega>2 (eisenstein_fun' n)"
    using eisenstein_fun'_is_doubly_periodic assms by simp
  show "eisenstein_fun' n meromorphic_on UNIV"
    using eisenstein_fun'_meromorphic assms by simp
qed

end

section \<open>The Weierstra\ss \<open>\<wp>\<close> Function\<close>

context gen_lattice begin

lemma minus_omega_eq: "uminus ` \<Omega> = \<Omega>"
proof -
  have "uminus ` \<Omega> \<subseteq> \<Omega>"
    apply (clarsimp simp: omega_def algebra_simps)
    by (metis add.right_inverse minus_mult_right of_int_minus pth_d)
  then show ?thesis
    using equation_minus_iff by blast
qed

lemma minus_omegamz_eq: "uminus ` \<Omega>* = \<Omega>*"
  by (simp add: omega_minus_zero_def inj_on_def image_set_diff minus_omega_eq)

lemma bij_minus_omegamz: "bij_betw uminus \<Omega>* \<Omega>*"
  by (simp add: bij_betw_def inj_on_def minus_omegamz_eq)


definition weierstrass_fun_deriv ("\<wp>''") where
  "weierstrass_fun_deriv z = -2 * eisenstein_fun' 3 z"


lemma weierstrass_fun_deriv_elliptic [elliptic_fun_intros]: "elliptic_fun' \<wp>' \<omega>1 \<omega>2"
  unfolding weierstrass_fun_deriv_def 
proof (intro elliptic_fun_intros)
  show "elliptic_fun' (eisenstein_fun' 3)  \<omega>1 \<omega>2"
    by (simp add: eisenstein_fun'_is_elliptic elliptic_fun.axioms(1))
qed

lemma weierstrass_fun_deriv_is_periodic: "\<omega> \<in> \<Omega> \<Longrightarrow> is_periodic \<omega> \<wp>'"
  using eisenstein_fun'_is_periodic[of 3 \<omega>]
  unfolding is_periodic_def weierstrass_fun_deriv_def by simp

lemma weierstrass_fun_deriv_minus [simp]: "\<wp>' (-z) = -\<wp>' z"
  by (simp add: weierstrass_fun_deriv_def eisenstein_fun'_odd_minus)

lemma weierstrass_fun_deriv_has_field_derivative:
  assumes "z \<notin> \<Omega>"
  shows   "(\<wp>' has_field_derivative 6 * eisenstein_fun' 4 z) (at z)"
  unfolding weierstrass_fun_deriv_def
  using assms by (auto intro!: derivative_eq_intros)

lemmas weierstrass_fun_deriv_has_field_derivative' [derivative_intros] =
  weierstrass_fun_deriv_has_field_derivative [THEN DERIV_chain2]

lemma weierstrass_fun_deriv_holomorphic: "\<wp>' holomorphic_on -\<Omega>"
  unfolding weierstrass_fun_deriv_def by (auto intro!: holomorphic_intros)

lemma weierstrass_fun_deriv_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "(\<lambda>z. \<wp>' (f z)) holomorphic_on A"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: holomorphic_intros)

lemma weierstrass_fun_deriv_analytic: "\<wp>' analytic_on -\<Omega>"
  unfolding weierstrass_fun_deriv_def by (auto intro!: analytic_intros)

lemma weierstrass_fun_deriv_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "(\<lambda>z. \<wp>' (f z)) analytic_on A"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: analytic_intros)

lemma weierstrass_fun_deriv_continuous_on: "continuous_on (-\<Omega>) \<wp>'"
  unfolding weierstrass_fun_deriv_def by (auto intro!: continuous_intros)

lemma weierstrass_fun_deriv_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "continuous_on A (\<lambda>z. \<wp>' (f z))"
  using assms unfolding weierstrass_fun_deriv_def by (auto intro!: continuous_intros)


text \<open>
  The following is the Weierstrass function minus its pole at the origin. By convention, it
  returns 0 at all its remaining poles.
\<close>
definition weierstrass_fun_aux :: "complex \<Rightarrow> complex" where
  "weierstrass_fun_aux z = (if z \<in> \<Omega>* then 0 else (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Omega>*. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))"

(* Definition p.10 *)
text \<open>
  This is now the Weierstra\ss function. Again, it returns 0 at all its poles.
\<close>
definition weierstrass_fun:: "complex \<Rightarrow> complex" ("\<wp>")
  where "\<wp> z = (if z \<in> \<Omega> then 0 else 1 / z\<^sup>2 + weierstrass_fun_aux z)"

lemma weierstrass_fun_aux_0 [simp]: "weierstrass_fun_aux 0 = 0"
  by (simp add: weierstrass_fun_aux_def)

lemma weierstrass_fun_at_pole: "\<omega> \<in> \<Omega> \<Longrightarrow> \<wp> \<omega> = 0"
  by (simp add: weierstrass_fun_def)


lemma
  fixes R :: real
  assumes "R > 0"
  shows weierstrass_fun_aux_converges_absolutely_uniformly_in_disk:
          "uniform_limit (disk R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2))
                         (finite_subsets_at_top (\<Omega> - disk R))" (is ?th1)
  and   weierstrass_fun_aux_converges_uniformly_in_disk:
          "uniform_limit (disk R)
                         (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                         (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                         (finite_subsets_at_top (\<Omega> - disk R))" (is ?th2)
proof -
  obtain M where M:
    "M > 0" "\<And>\<omega> z. \<lbrakk>\<omega> \<in> \<Omega>; norm \<omega> > R; norm z \<le> R\<rbrakk> \<Longrightarrow> norm (z - \<omega>) powr -2 \<le> M * norm \<omega> powr -2"
    using lemma_2_bound[of 2 R] assms by auto

  have 1: "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on (\<Omega> - cball 0 R)"
  proof -
    have "(\<lambda>\<omega>. 1 / norm \<omega> powr 3) summable_on \<Omega>*"
      using assms by (subst converges_absolutely_iff) auto
    hence "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on \<Omega>*"
      by (intro summable_on_cmult_right) (auto simp: powr_minus field_simps)
    thus "(\<lambda>\<omega>. 3 * M * R * norm \<omega> powr -3) summable_on (\<Omega> - cball 0 R)"
      by (rule summable_on_subset) (use assms in \<open>auto simp: omega_minus_zero_def\<close>)
  qed

  have 2: "norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) \<le> 3 * M * R * norm \<omega> powr -3"
    if "\<omega> \<in> \<Omega> - cball 0 R" "z \<in> cball 0 R" for \<omega> z
  proof -
    from that have nz: "\<omega> \<noteq> 0" "\<omega> \<noteq> z"
      using \<open>R > 0\<close> by auto
    hence "1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2 = z * (2 * \<omega> - z) / (\<omega>\<^sup>2 * (z - \<omega>)\<^sup>2)"
      using that by (auto simp: field_simps) (auto simp: power2_eq_square algebra_simps)
    also have "norm \<dots> = norm z * norm (2 * \<omega> - z) / norm \<omega> ^ 2 * norm (z - \<omega>) powr - 2"
      by (simp add: norm_divide norm_mult norm_power powr_minus divide_simps)
    also have "\<dots> \<le> R * (2 * norm \<omega> + norm z) / norm \<omega> ^ 2 * (M * norm \<omega> powr -2)"
      using assms that
      by (intro mult_mono frac_le mult_nonneg_nonneg M order.trans[OF norm_triangle_ineq4]) auto
    also have "\<dots> = M * R * (2 + norm z / norm \<omega>) / norm \<omega> ^ 3"
      using nz by (simp add: field_simps powr_minus power2_eq_square power3_eq_cube)
    also have "\<dots> \<le> M * R * 3 / norm \<omega> ^ 3"
      using nz assms M(1) that by (intro mult_left_mono divide_right_mono) auto
    finally show ?thesis
      by (simp add: field_simps powr_minus)
  qed

  show ?th1 ?th2 unfolding weierstrass_fun_aux_def
     by (rule Weierstrass_m_test_general[OF _ 1]; use 2 in simp)+
qed

lemma weierstrass_fun_has_field_derivative_aux:
  fixes R :: real
  defines "F \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  defines "F' \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>) ^ 3)"
  assumes "R > 0" "w \<in> ball 0 R"
  shows   "(F has_field_derivative -2 * F' w) (at w)"
proof -
  have 1: "\<forall>\<^sub>F n in finite_subsets_at_top (\<Omega> - cball 0 R).
            continuous_on (cball 0 R) (\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) \<and>
            (\<forall>z\<in>ball 0 R. ((\<lambda>z. \<Sum>\<omega>\<in>n. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_field_derivative (\<Sum>\<omega>\<in>n. -2 / (z - \<omega>)^3)) (at z))"
    (* TODO FIXME: ugly *)
    apply (intro eventually_finite_subsets_at_top_weakI conjI continuous_intros derivative_intros ballI)
     apply force
    apply (rule derivative_eq_intros refl | force)+
    apply (simp add: divide_simps, simp add: algebra_simps power4_eq_xxxx power3_eq_cube)
    done

  have "uniform_limit (disk R)
                      (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                      (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)
                      (finite_subsets_at_top (\<Omega> - disk R))"
    using assms by (intro weierstrass_fun_aux_converges_uniformly_in_disk) auto
  also have "?this \<longleftrightarrow> uniform_limit (disk R) (\<lambda>X z. \<Sum>\<omega>\<in>X. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) F
                         (finite_subsets_at_top (\<Omega> - disk R))"
    using assms unfolding F_def
    by (intro uniform_limit_cong eventually_finite_subsets_at_top_weakI)
       (auto simp: powr_minus powr_nat field_simps intro!: sum.cong infsum_cong)
  finally have 2: \<dots> .

  have 3: "finite_subsets_at_top (\<Omega> - cball 0 R) \<noteq> bot"
    by simp

  obtain g where g: "continuous_on (cball 0 R) F"
                    "\<And>w. w \<in> ball 0 R \<Longrightarrow> (F has_field_derivative g w) (at w) \<and>
                        ((\<lambda>\<omega>. -2 / (w - \<omega>) ^ 3) has_sum g w) (\<Omega> - cball 0 R)"
    unfolding has_sum_def using has_complex_derivative_uniform_limit[OF 1 2 3 \<open>R > 0\<close>] by auto

  have "((\<lambda>\<omega>. (-2) * (1 / (w - \<omega>) ^ 3)) has_sum (-2) * F' w) (\<Omega> - cball 0 R)"
    unfolding F'_def using assms
    by (intro has_sum_cmult_right has_sum_infsum converges_in_disk') auto
  moreover have "((\<lambda>\<omega>.  -2 * (1 / (w - \<omega>) ^ 3)) has_sum g w) (\<Omega> - cball 0 R)"
    using g(2)[of w] assms by simp
  ultimately have "g w = -2 * F' w"
    by (metis infsumI)
  thus "(F has_field_derivative -2 * F' w) (at w)"
    using g(2)[of w] assms by simp
qed

lemma norm_summable_weierstrass_fun_aux: "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on \<Omega>"
proof -
  define R where "R = norm z + 1"
  have "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on (\<Omega> - cball 0 R)"
    unfolding summable_iff_has_sum_infsum has_sum_def
    by (rule tendsto_uniform_limitI[OF weierstrass_fun_aux_converges_absolutely_uniformly_in_disk])
       (auto simp: R_def add_nonneg_pos)
  hence "(\<lambda>\<omega>. norm (1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)) summable_on ((\<Omega> - cball 0 R) \<union> (\<Omega> \<inter> cball 0 R))"
    by (intro summable_on_union[OF _ summable_on_finite]) (auto simp: bounded_omega_finite)
  also have "\<dots> = \<Omega>"
    by blast
  finally show ?thesis .
qed

lemma summable_weierstrass_fun_aux: "(\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) summable_on \<Omega>"
  using norm_summable_weierstrass_fun_aux by (rule abs_summable_summable)

lemma weierstrass_summable: "(\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) summable_on \<Omega>*"
  by (rule summable_on_subset[OF summable_weierstrass_fun_aux]) (auto simp: omega_minus_zero_def)

lemma weierstrass_fun_aux_has_sum:
  "z \<notin> \<Omega>* \<Longrightarrow> ((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum weierstrass_fun_aux z) \<Omega>*"
  unfolding weierstrass_fun_aux_def by (simp add: weierstrass_summable)

lemma weierstrass_fun_aux_has_field_derivative:
  defines "F \<equiv> weierstrass_fun_aux"
  defines "F' \<equiv> (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (z - \<omega>) ^ 3)"
  assumes z: "z \<notin> \<Omega>*"
  shows   "(F has_field_derivative -2 * eisenstein_fun 3 z) (at z)"
proof -
  define R where "R = norm z + 1"
  have R: "R > 0" "norm z < R"
    by (auto simp: R_def add_nonneg_pos)
  have "finite (\<Omega> \<inter> cball 0 R)"
    by (simp add: bounded_omega_finite)
  moreover have "\<Omega>* \<inter> cball 0 R \<subseteq> \<Omega> \<inter> cball 0 R"
    unfolding omega_minus_zero_def by blast
  ultimately have fin: "finite (\<Omega>* \<inter> cball 0 R)"
    using finite_subset by blast

  define F1 where "F1 = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  define F'1 where "F'1 = (\<lambda>z. \<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>-disk R. 1 / (z - \<omega>) ^ 3)"
  define F2 where "F2 = (\<lambda>z. \<Sum>\<omega>\<in>\<Omega>*\<inter>disk R. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
  define F'2 where "F'2 = (\<lambda>z. \<Sum>\<omega>\<in>\<Omega>*\<inter>disk R. 1 / (z - \<omega>) ^ 3)"

  have "(F1 has_field_derivative -2 * F'1 z) (at z)"
    unfolding F1_def F'1_def
    by (rule weierstrass_fun_has_field_derivative_aux) (auto simp: R_def add_nonneg_pos)
  moreover have "(F2 has_field_derivative -2 * F'2 z) (at z)"
    unfolding F2_def F'2_def sum_distrib_left omega_minus_zero_def
    by (rule derivative_eq_intros refl sum.cong | use R z in \<open>force simp: omega_minus_zero_def\<close>)+
       (simp add: divide_simps power3_eq_cube power4_eq_xxxx)
  ultimately have "((\<lambda>z. F1 z + F2 z) has_field_derivative (-2 * F'1 z) + (-2 * F'2 z)) (at z)"
    by (intro derivative_intros)
  also have "?this \<longleftrightarrow> (F has_field_derivative (-2 * F'1 z) + (-2 * F'2 z)) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z'. z' \<in> -\<Omega>*) (nhds z)"
      using z by (intro eventually_nhds_in_open) (auto simp: closed_omega_minus_zero)
    thus "\<forall>\<^sub>F x in nhds z. x \<in> UNIV \<longrightarrow> F1 x + F2 x = F x"
    proof eventually_elim
      case (elim z)
      have "((\<lambda>\<omega>. 1 / (z - \<omega>)^2 - 1 / \<omega>^2) has_sum (F1 z + F2 z)) ((\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R))"
        unfolding F1_def F2_def using R fin
        by (intro has_sum_Un_disjoint[OF has_sum_infsum has_sum_finite]
                  summable_on_subset_banach[OF summable_weierstrass_fun_aux]) auto
      also have "(\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R) = \<Omega>*"
        using R unfolding omega_minus_zero_def by auto
      finally show ?case using elim
        unfolding F1_def F2_def F_def weierstrass_fun_aux_def by (simp add: infsumI)
    qed
  qed auto
  also have "(-2 * F'1 z) + (-2 * F'2 z) = -2 * (F'1 z + F'2 z)"
    by (simp add: algebra_simps)
  also have "F'1 z + F'2 z = F' z"
  proof -
    have "((\<lambda>\<omega>. 1 / (z - \<omega>)^3) has_sum (F'1 z + F'2 z)) ((\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R))"
      unfolding F'1_def F'2_def using R fin
      by (intro has_sum_Un_disjoint [OF has_sum_infsum has_sum_finite] converges') auto
    also have "(\<Omega> - cball 0 R) \<union> (\<Omega>* \<inter> cball 0 R) = \<Omega>*"
      using R unfolding omega_minus_zero_def by auto
    finally show "F'1 z + F'2 z = F' z"
      unfolding F'1_def F'2_def F'_def by (simp add: infsumI)
  qed
  finally show ?thesis
    using assms by (simp add: eisenstein_fun_def)
qed

lemmas weierstrass_fun_aux_has_field_derivative' [derivative_intros] =
  weierstrass_fun_aux_has_field_derivative [THEN DERIV_chain2]

lemma weierstrass_fun_aux_holomorphic: "weierstrass_fun_aux holomorphic_on -\<Omega>*"
  by (subst holomorphic_on_open)
     (auto intro!: weierstrass_fun_aux_has_field_derivative simp: closed_omega_minus_zero)

lemma weierstrass_fun_aux_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*"
  shows   "(\<lambda>z. weierstrass_fun_aux (f z)) holomorphic_on A"
proof -
  have "weierstrass_fun_aux \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms weierstrass_fun_aux_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_aux_continuous_on: "continuous_on (-\<Omega>*) weierstrass_fun_aux"
  using holomorphic_on_imp_continuous_on weierstrass_fun_aux_holomorphic by blast

lemma weierstrass_fun_aux_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*"
  shows   "continuous_on A (\<lambda>z. weierstrass_fun_aux (f z))"
  by (rule continuous_on_compose2[OF weierstrass_fun_aux_continuous_on assms(1)]) (use assms in auto)

lemma weierstrass_fun_aux_analytic: "weierstrass_fun_aux analytic_on -\<Omega>*"
  by (simp add: analytic_on_open closed_omega_minus_zero open_Compl weierstrass_fun_aux_holomorphic)  

lemma weierstrass_fun_aux_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>*"
  shows   "(\<lambda>z. weierstrass_fun_aux (f z)) analytic_on A"
proof -
  have "weierstrass_fun_aux \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms weierstrass_fun_aux_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma deriv_weierstrass_fun_aux: "z \<notin> \<Omega>* \<Longrightarrow> deriv weierstrass_fun_aux z = -2 * eisenstein_fun 3 z"
  by (rule DERIV_imp_deriv derivative_eq_intros refl | assumption)+ simp



lemma weierstrass_fun_has_field_derivative:
  fixes R :: real
  assumes z: "z \<notin> \<Omega>"
  shows   "(\<wp> has_field_derivative \<wp>' z) (at z)"
proof -
  note [derivative_intros] = weierstrass_fun_aux_has_field_derivative
  from z have [simp]: "z \<noteq> 0" "z \<notin> \<Omega>*"
    by (auto simp: omega_minus_zero_def)
  define D where "D = -2 / z ^ 3 - 2 * eisenstein_fun 3 z"

  have "((\<lambda>z. 1 / z\<^sup>2 + weierstrass_fun_aux z) has_field_derivative D) (at z)" unfolding D_def
    by (rule derivative_eq_intros refl | simp)+ (simp add: divide_simps power3_eq_cube power4_eq_xxxx)
  also have "?this \<longleftrightarrow> (weierstrass_fun has_field_derivative D) (at z)"
  proof (intro has_field_derivative_cong_ev refl)
    have "eventually (\<lambda>z. z \<in> -\<Omega>) (nhds z)"
      using closed_omega z by (intro eventually_nhds_in_open) auto
    thus "eventually (\<lambda>z. z \<in> UNIV \<longrightarrow> 1 / z ^ 2 + weierstrass_fun_aux z = \<wp> z) (nhds z)"
      by eventually_elim (simp add: weierstrass_fun_def)
  qed auto
  also have "D = -2 * eisenstein_fun' 3 z"
    using z by (simp add: eisenstein_fun'_conv_eisenstein_fun D_def)
  finally show ?thesis by (simp add: weierstrass_fun_deriv_def)
qed

lemmas weierstrass_fun_has_field_derivative' [derivative_intros] =
  weierstrass_fun_has_field_derivative [THEN DERIV_chain2]

lemma weierstrass_fun_holomorphic: "weierstrass_fun holomorphic_on -\<Omega>"
  by (subst holomorphic_on_open)
     (auto intro!: weierstrass_fun_has_field_derivative simp: closed_omega)

lemma weierstrass_fun_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "(\<lambda>z. weierstrass_fun (f z)) holomorphic_on A"
proof -
  have "weierstrass_fun \<circ> f holomorphic_on A"
    by (rule holomorphic_on_compose_gen assms weierstrass_fun_holomorphic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_analytic: "weierstrass_fun analytic_on -\<Omega>"
  by (simp add: analytic_on_open closed_omega open_Compl weierstrass_fun_holomorphic)  

lemma weierstrass_fun_analytic' [analytic_intros]: 
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "(\<lambda>z. weierstrass_fun (f z)) analytic_on A"
proof -
  have "weierstrass_fun \<circ> f analytic_on A"
    by (rule analytic_on_compose_gen assms weierstrass_fun_analytic)+ (use assms in auto)
  thus ?thesis by (simp add: o_def)
qed

lemma weierstrass_fun_continuous_on: "continuous_on (-\<Omega>) weierstrass_fun"
  using holomorphic_on_imp_continuous_on weierstrass_fun_holomorphic by blast

lemma weierstrass_fun_continuous_on' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<Omega>"
  shows   "continuous_on A (\<lambda>z. weierstrass_fun (f z))"
  by (rule continuous_on_compose2[OF weierstrass_fun_continuous_on assms(1)]) (use assms in auto)

lemma deriv_weierstrass_fun:
  assumes "z \<notin> \<Omega>"
  shows   "deriv \<wp> z = \<wp>' z"
  by (rule DERIV_imp_deriv weierstrass_fun_has_field_derivative refl assms)+

(* Using division by zero: would probably simplify the remaining proofs (?) *)
lemma weierstrass_fun_eq: 
  assumes "z \<notin> \<Omega>"
  shows   "\<wp> z = (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Omega>. (1/(z - \<omega>)^2) - 1/\<omega>\<^sup>2)"
proof -
  have \<section>: "((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum \<wp> z - 1 / z^2) \<Omega>*"
    using has_sum_infsum [OF weierstrass_summable, of z] assms
    by (simp add: weierstrass_fun_def weierstrass_fun_aux_def omega_minus_zero_def)
  have "((\<lambda>\<omega>. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) has_sum \<wp> z - 1 / z^2 + 1 / z^2) \<Omega>"
    using has_sum_insert [OF zero_notin_omega_mz \<section>]
    by (simp add: omega_omega_minus_zero)
  then show ?thesis
    by (simp add: infsumI)
qed

(* Theorem 1.10 (4) *)
theorem weierstrass_fun_minus: "\<wp> (-z) = \<wp> z"  
proof (cases "z \<in> \<Omega>")
  case False
  have "(\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Omega>*. 1 / (- z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) = (\<Sum>\<^sub>\<infinity> \<omega> \<in> uminus ` \<Omega>*. 1 / (- z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
    by (simp add: minus_omegamz_eq)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity> \<omega> \<in> \<Omega>*. 1 / (- z - (-\<omega>))\<^sup>2 - 1 / (-\<omega>)\<^sup>2)"
    by (simp add: inj_on_def o_def infsum_reindex)
  also have "\<dots> = (\<Sum>\<^sub>\<infinity> \<omega>\<in>\<Omega>*. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)"
    by (simp add: power2_commute)
  finally have "(\<Sum>\<^sub>\<infinity> \<omega>\<in>\<Omega>*. 1 / (- z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2) = (\<Sum>\<^sub>\<infinity> \<omega>\<in>\<Omega>*. 1 / (z - \<omega>)\<^sup>2 - 1 / \<omega>\<^sup>2)" .
  then show ?thesis using False
    by (simp add: weierstrass_fun_def weierstrass_fun_aux_def
                  omega_minus_iff omega_minus_zero_minus_iff)
qed (simp add: omega_minus_iff weierstrass_fun_at_pole)

(* Theorem 1.10 (1) *)
theorem weierstrass_fun_is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 \<wp>"
proof -
  have period: "is_periodic \<omega> \<wp>" if \<omega>: "\<omega> \<in> {\<omega>1, \<omega>2}" for \<omega>
    unfolding is_periodic_def
  proof
    fix z :: complex
    define f where "f = (\<lambda>z. \<wp> (z + \<omega>) - \<wp> z)"
    have "\<omega> \<in> \<Omega>"
      using that by (auto intro: omegaI1 omegaI2)
    have [simp]: "z + \<omega> \<in> \<Omega> \<longleftrightarrow> z \<in> \<Omega>" for z
      using \<open>\<omega> \<in> \<Omega>\<close> by (metis add_diff_cancel_right' omega_add omega_diff)

    have "(1 / 2 :: real) \<notin> \<int>"
      using fraction_not_in_ints[of 2 1, where ?'a = real] by simp
    with that have "\<omega> / 2 \<notin> \<Omega>"
      by (elim insertE) (simp_all add: in_omega_conv_\<omega>12_coords)

    show "\<wp> (z + \<omega>) = \<wp> z"
    proof (cases "z \<in> \<Omega>")
      case z: True
      thus ?thesis by (simp add: weierstrass_fun_at_pole omega_minus_iff)
    next
      case z: False
      with \<open>z \<notin> \<Omega>\<close> have "(f has_field_derivative 0) (at z)" if "z \<notin> \<Omega>" for z
      proof -
        interpret elliptic_fun' "\<wp>'" \<omega>1 \<omega>2 
          by (intro elliptic_fun_intros)
        from that have "(f has_field_derivative (\<wp>' (z + \<omega>) - \<wp>' z)) (at z)"
          unfolding f_def by (auto intro!: derivative_eq_intros)
        also have "is_periodic \<omega> \<wp>'"
          using \<open>\<omega> \<in> \<Omega>\<close> is_doubly_periodic omega_is_periodic  by blast
        hence "\<wp>' (z + \<omega>) = \<wp>' z"
          by (simp add: is_periodic_def)
        finally show ?thesis
          by simp
      qed
      hence deriv: "\<forall>x\<in>UNIV - \<Omega> - {}. (f has_field_derivative 0) (at x)"
        by blast
      have cont: "continuous_on (UNIV - \<Omega>) f"
        by (auto simp: f_def intro!: continuous_intros)
  
      have *: "connected (UNIV - \<Omega>)" "open (UNIV - \<Omega>)" "finite ({} :: complex set)"
        by (auto simp: closed_omega countable_omega intro!: connected_open_diff_countable)
  
      obtain c where c: "\<And>z. z \<in> UNIV - \<Omega> \<Longrightarrow> f z = c"
        using DERIV_zero_connected_constant[OF * cont deriv] by blast
  
      have "f (-\<omega> / 2) = c"
        using \<open>\<omega> / 2 \<notin> \<Omega>\<close> by (intro c) (auto simp: omega_minus_iff)
      also have "f (-\<omega> / 2) = 0"
        by (simp add: f_def weierstrass_fun_minus)
      finally have "f z = 0"
        using c that z by auto
      thus ?thesis
        by (simp add: f_def)
    qed
  qed

  show ?thesis
    unfolding is_doubly_periodic_def using ratio_notin_real by (auto intro: period)
qed

theorem weierstrass_fun_is_periodic: "\<omega> \<in> \<Omega> \<Longrightarrow> is_periodic \<omega> \<wp>"
  by (simp add: omega_is_periodic weierstrass_fun_is_doubly_periodic)


(* Theorem 1.10 (3) *)
theorem weierstrass_has_double_pole_at_each_period:
  assumes "\<omega> \<in> \<Omega>"
  shows   "zorder \<wp> \<omega> = -2"
proof -
  define R where "R = Inf_para"
  have R: "R > 0"
    using Inf_para_positive by (auto simp: R_def)
  have R': "ball 0 R \<inter> \<Omega>* = {}"
    using Inf_para_le_norm by (force simp: R_def)

  have "zorder weierstrass_fun \<omega> = zorder (\<lambda>z. weierstrass_fun (z + \<omega>)) 0"
    by (rule zorder_shift)
  also have "(\<lambda>z. weierstrass_fun (z + \<omega>)) = weierstrass_fun"
    using weierstrass_fun_is_periodic[OF assms] unfolding is_periodic_def by simp
  also have "zorder weierstrass_fun 0 = -2"
  proof (rule zorder_eqI)
    show "open (ball 0 R :: complex set)" "(0 :: complex) \<in> ball 0 R"
      using R by auto
    show "(\<lambda>z. 1 + weierstrass_fun_aux z * z ^ 2) holomorphic_on ball 0 R" using R'
      by (intro holomorphic_intros holomorphic_on_subset[OF weierstrass_fun_aux_holomorphic]) auto
    show "\<And>w. \<lbrakk>w \<in> ball 0 R; w \<noteq> 0\<rbrakk>
         \<Longrightarrow> \<wp> w =
             (1 + weierstrass_fun_aux w * w\<^sup>2) *
             (w - 0) powi - 2"
      using R' 
      by (auto simp: weierstrass_fun_def field_simps power_numeral_reduce powi_minus_numeral_reduce
                              omega_minus_zero_def)
  qed auto
  finally show ?thesis .
qed

lemma is_pole_weierstrass_fun:
  assumes \<omega>:  "\<omega> \<in> \<Omega>"
  shows   "is_pole \<wp> \<omega>"
proof -
  have "is_pole \<wp> 0"
  proof -
    have "eventually (\<lambda>z. z \<in> -\<Omega>*) (nhds 0)"
      using closed_omega_minus_zero 
      by (intro eventually_nhds_in_open) (auto simp: zero_notin_omega_mz)
    hence ev: "eventually (\<lambda>z. z \<notin> \<Omega>) (at 0)"
      unfolding eventually_at_filter by eventually_elim (auto simp: omega_minus_zero_def)
    have "\<Omega> - \<Omega>* = {0}" "\<Omega>* \<subseteq> \<Omega>"
      by (auto simp: insert_Diff_if omega_omega_minus_zero zero_notin_omega_mz)
    hence "weierstrass_fun_aux holomorphic_on -\<Omega>*"
      by (auto intro!: holomorphic_intros)
    hence "continuous_on (-\<Omega>*) weierstrass_fun_aux"
      using holomorphic_on_imp_continuous_on by blast
    moreover have "0 \<in> -\<Omega>*"
      by (auto simp: omega_minus_zero_def)
    ultimately have "(weierstrass_fun_aux \<longlongrightarrow> weierstrass_fun_aux 0) (at 0)"
      using closed_omega_minus_zero by (metis at_within_open closed_open continuous_on_def)
    moreover have "filterlim (\<lambda>z::complex. 1 / z ^ 2) at_infinity (at 0)"
      using is_pole_inverse_power[of 2 0] by (simp add: is_pole_def)
    ultimately have "filterlim (\<lambda>z. weierstrass_fun_aux z + 1 / z ^ 2) at_infinity (at 0)"
      by (rule tendsto_add_filterlim_at_infinity)
    also have "?this \<longleftrightarrow> filterlim weierstrass_fun at_infinity (at 0)"
      by (intro filterlim_cong refl eventually_mono[OF ev]) (auto simp: weierstrass_fun_def)
    finally show ?thesis
      by (simp add: is_pole_def)
  qed
  thus "is_pole \<wp> \<omega>"
    using is_periodic_pole_minus[OF weierstrass_fun_is_periodic[of "-\<omega>"], of 0] \<omega>
    by (simp add: omega_minus_iff)
qed

lemma isolated_singularity_at_weierstrass_fun: "isolated_singularity_at \<wp> \<omega>"
proof -
  have "\<not>\<omega> islimpt \<Omega>"
    by (simp add: omega_not_limpt)
  then obtain r where r: "r > 0" "ball \<omega> r \<inter> \<Omega> - {\<omega>} = {}"
    by (subst (asm) islimpt_approachable) (auto simp: dist_commute ball_def)
  hence "\<wp> analytic_on ball \<omega> r - {\<omega>}"
    by (intro analytic_intros) auto
  thus "isolated_singularity_at \<wp> \<omega>"
    unfolding isolated_singularity_at_def using \<open>r > 0\<close> by blast
qed

lemma weierstrass_fun_meromorphic [meromorphic_intros]: "\<wp> meromorphic_on UNIV"
  by (meson Compl_iff analytic_on_imp_meromorphic_on 
      is_pole_imp_not_essential is_pole_weierstrass_fun 
      isolated_singularity_at_weierstrass_fun meromorphic_on_altdef weierstrass_fun_analytic)

theorem weierstrass_fun_elliptic [elliptic_fun_intros]: "elliptic_fun \<wp> \<omega>1 \<omega>2"
proof 
  show "is_doubly_periodic \<omega>1 \<omega>2 \<wp>"
    using weierstrass_fun_is_doubly_periodic .
  show "\<wp> meromorphic_on UNIV" 
    by (simp add: weierstrass_fun_meromorphic)
  show "\<forall>z. is_pole \<wp> z \<and> \<wp> z = 0 \<or> \<wp> \<midarrow>z\<rightarrow> \<wp> z"
    by (meson ComplI analytic_at_imp_isCont analytic_on_analytic_at 
        isCont_def is_pole_weierstrass_fun weierstrass_fun_analytic weierstrass_fun_at_pole)
qed

section \<open>The Laurent Expansion of \<open>\<wp>\<close> near the origin\<close>

(* TODO: this notation is too general for my taste. What about \<G>? *)
definition eisenstein_series :: "nat \<Rightarrow> complex" ("G _" [900] 900) where
  "G n = (if n = 0 then 1 else if n < 3 then 0 else (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / \<omega> ^ n))"

lemma eisenstein_series_odd_eq_0:
  assumes "odd n"
  shows   "G n = 0"
proof (cases "n \<ge> 3")
  case True
  have "G n = -(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (-\<omega>) ^ n)"
    using True assms by (simp add: eisenstein_series_def infsum_uminus)
  also have "(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / (-\<omega>) ^ n) = (\<Sum>\<^sub>\<infinity>\<omega>\<in>uminus ` \<Omega>*. 1 / \<omega> ^ n)"
    by (subst infsum_reindex) (auto simp: o_def inj_on_def)
  also have "uminus ` \<Omega>* = \<Omega>*"
    by (rule minus_omegamz_eq)
  also have "-(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / \<omega> ^ n) = -G n"
    using True by (simp add: eisenstein_series_def)
  finally show ?thesis
    by simp
qed (use assms in \<open>auto simp: eisenstein_series_def intro!: Nat.gr0I\<close>)

lemma eisenstein_series_norm_summable:
  assumes "n \<ge> 3"
  shows   "(\<lambda>\<omega>. 1 / norm \<omega> ^ n) summable_on \<Omega>*"
  using converges_absolutely_iff[of "of_nat n"] assms by (simp add: powr_realpow')

lemma eisenstein_series_summable:
  assumes "n \<ge> 3"
  shows   "(\<lambda>\<omega>. 1 / \<omega> ^ n) summable_on \<Omega>*"
  by (rule abs_summable_summable)
     (use eisenstein_series_norm_summable[OF assms] in \<open>simp add: norm_divide norm_power\<close>)

lemma eisenstein_series_has_sum:
  assumes "n \<ge> 3"
  shows   "((\<lambda>\<omega>. 1 / \<omega> ^ n) has_sum (G n)) \<Omega>*"
proof -
  have "G n = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / \<omega> ^ n)"
    using assms unfolding eisenstein_series_def by simp
  also have "((\<lambda>\<omega>. 1 / \<omega> ^ n) has_sum \<dots>) \<Omega>*"
    by (intro has_sum_infsum summable_on_subset[OF converges'] eisenstein_series_summable assms)
  finally show ?thesis .
qed

lemma eisenstein_fun_0 [simp]:
  "eisenstein_fun n 0 = eisenstein_series n"
proof (cases "n \<ge> 3")
  case gt3: True
  show ?thesis
  proof (cases "even n")
    case True
    show ?thesis
      using True gt3 zero_notin_omega_mz
      by (auto simp: eisenstein_fun_def eisenstein_series_def)
  next
    case False
    have "eisenstein_fun n 0 = -(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Omega>*. 1 / \<omega> ^ n)"
      using False gt3 zero_notin_omega_mz
      by (auto simp: eisenstein_fun_def eisenstein_series_def infsum_uminus)
    also have "\<dots> = -eisenstein_series n"
      using gt3 by (simp add: eisenstein_series_def)
    finally show ?thesis
      using False by (simp add: eisenstein_series_odd_eq_0)
  qed
qed (auto simp: eisenstein_fun_def eisenstein_series_def)

lemma higher_deriv_weierstrass_fun_aux_0:
  assumes "m > 0"
  shows   "(deriv ^^ m) weierstrass_fun_aux 0 = (- 1) ^ m * fact (Suc m) * G (m + 2)"
proof -
  define n where "n = m - 1"
  have "(deriv ^^ Suc n) weierstrass_fun_aux 0 = (deriv ^^ n) (\<lambda>w. -2 * eisenstein_fun 3 w) 0"
    unfolding funpow_Suc_right o_def
  proof (rule higher_deriv_cong_ev)
    have "eventually (\<lambda>z. z \<in> -\<Omega>*) (nhds 0)"
      using closed_omega_minus_zero zero_notin_omega_mz by (intro eventually_nhds_in_open) auto
    thus "\<forall>\<^sub>F x in nhds 0. deriv weierstrass_fun_aux x = -2 * eisenstein_fun 3 x"
      by eventually_elim (simp add: deriv_weierstrass_fun_aux)
  qed auto
  also have "\<dots> = -2 * (deriv ^^ n) (eisenstein_fun 3) 0"
    using zero_notin_omega_mz closed_omega_minus_zero 
    by (intro higher_deriv_cmult[where A = "-\<Omega>*"]) (auto intro!: holomorphic_intros)
  also have "\<dots> = (- 1) ^ Suc n * fact (n + 2) * G (n + 3)"
    using zero_notin_omega_mz
    by (subst higher_deriv_eisenstein_fun)
       (auto simp: algebra_simps pochhammer_rec pochhammer_fact)
  finally show ?thesis
    using assms by (simp add: n_def)
qed



(* Theorem 1.11 *)
text \<open>
  We choose a different approach for this Theorem than Apostol: Apostol argues converts the
  sum in question into a double sum and then interchanges the order of summation, claiming the
  double sum to be absolutely convergent. Since we were unable to see why that sum should be
  absolutely convergent, we were unable to replicate his argument. In any case, arguing about
  absolute convergence of double sums is always messy.

  Our approach instead simply uses the fact that \<^const>\<open>weierstrass_fun_aux\<close> (the Weierstrass
  function with its double pole removed) is analytic at 0 and thus has a power series expansion
  that is valid within any ball around 0 that does not contain any lattice points.

  The coefficients of this power series expansion can be determined simply by taking the \<open>n\<close>-th
  derivative of \<^const>\<open>weierstrass_fun_aux\<close> at 0, which is easy to do.

  Note that this series converges absolutely in this domain, since it is a power series, but
  we do not show this here.
\<close>
definition fps_weierstrass :: "complex fps"
  where "fps_weierstrass = Abs_fps (\<lambda>n. if n = 0 then 0 else of_nat (Suc n) * G (n + 2))"

lemma weierstrass_fun_aux_fps_expansion: "weierstrass_fun_aux has_fps_expansion fps_weierstrass"
proof -
  define c where "c = (\<lambda>n. if n = 0 then 0 else of_nat (Suc n) * G (n + 2))"
  have "(\<lambda>n. (deriv ^^ n) weierstrass_fun_aux 0 / fact n) = c"
          (is "?lhs = ?rhs")
  proof
    fix n :: nat
    show "?lhs n = ?rhs n" unfolding c_def
      by (cases "even n") (auto simp: higher_deriv_weierstrass_fun_aux_0 eisenstein_series_odd_eq_0)
  qed
  hence "fps_weierstrass = fps_expansion weierstrass_fun_aux 0"
    by (intro fps_ext) (auto simp: fps_expansion_def fps_weierstrass_def c_def fun_eq_iff)
  also have "weierstrass_fun_aux has_fps_expansion \<dots>"
    using closed_omega_minus_zero
    by (intro has_fps_expansion_fps_expansion[of "-\<Omega>*"] holomorphic_intros)
       (auto simp: zero_notin_omega_mz)
  finally show ?thesis .
qed

definition fls_weierstrass :: "complex fls"
  where "fls_weierstrass = fls_X_intpow (-2) + fps_to_fls fps_weierstrass"

lemma fls_subdegree_weierstrass: "fls_subdegree fls_weierstrass = -2"
  by (intro fls_subdegree_eqI) (auto simp: fls_weierstrass_def)

lemma fls_weierstrass_nz [simp]: "fls_weierstrass \<noteq> 0"
  using fls_subdegree_weierstrass by auto

theorem fls_weierstrass_laurent_expansion [laurent_expansion_intros]:
  "\<wp> has_laurent_expansion fls_weierstrass"
proof -
  have "(\<lambda>z. z powi (-2) + weierstrass_fun_aux z) has_laurent_expansion fls_weierstrass"
    unfolding fls_weierstrass_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps[OF weierstrass_fun_aux_fps_expansion])
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro has_laurent_expansion_cong refl)
    have "eventually (\<lambda>z. z \<in> -\<Omega>* - {0}) (at 0)"
      using closed_omega_minus_zero zero_notin_omega_mz by (intro eventually_at_in_open) auto
    thus "\<forall>\<^sub>F x in at 0. x powi - 2 + weierstrass_fun_aux x = \<wp> x"
      by eventually_elim
         (auto simp: weierstrass_fun_def power_int_minus field_simps omega_omega_minus_zero)
  qed
  finally show ?thesis .
qed

corollary fls_weierstrass_deriv_laurent_expansion [laurent_expansion_intros]:
  "\<wp>' has_laurent_expansion fls_deriv fls_weierstrass"
  by (rule has_laurent_expansion_deriv'[where A = "-\<Omega>*", OF fls_weierstrass_laurent_expansion])
     (use closed_omega_minus_zero zero_notin_omega_mz
      in  \<open>auto intro!: derivative_eq_intros simp: omega_omega_minus_zero\<close>)

lemma fls_nth_weierstrass:
  "fls_nth fls_weierstrass n =
     (if n = -2 then 1 else if n > 0 then of_int (n + 1) * G (nat n + 2) else 0)"
  unfolding fls_weierstrass_def fps_weierstrass_def by (auto simp: not_less)


section \<open>Differential Equation Satisfied by \<open>\<wp>\<close>\<close>

text \<open>Theorem 1.12\<close>
theorem weierstrass_fun_ODE1:
  assumes "z \<notin> \<Omega>"
  shows   "\<wp>' z ^ 2 = 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6"
proof -
  note [simp] = fls_subdegree_deriv fls_subdegree_weierstrass
  define f where "f = (\<lambda>z. \<wp>' z ^ 2 - 4 * \<wp> z ^ 3 + 60 * G 4 * \<wp> z)"
  interpret f: elliptic_fun' f \<omega>1 \<omega>2
    unfolding f_def
    
    by (intro elliptic_fun_intros omega_not_limpt elliptic_fun.axioms)
  let ?P = fls_weierstrass
  define F :: "complex fls" where "F = fls_deriv ?P ^ 2 - 4 * ?P ^ 3 + fls_const (60 * G 4) * ?P"
  define g where "g = (\<lambda>z. if z \<in> \<Omega> then -140 * G 6 else f z)"

  (* FIXME: Somewhat tedious computation. Could be automated – Manuel *)
  have unwind: "{m..n::int} = insert m {m+1..n}" if "m \<le> n" for m n
    using that by auto
  define fls_terms :: "complex fls \<Rightarrow> complex list"
    where "fls_terms = (\<lambda>F. map (\<lambda>k. fls_nth F k) [-6,-5,-4,-3,-2,-1,0])"
  have coeffs: "map (\<lambda>k. fls_nth F k) [-6,-5,-4,-3,-2,-1,0] = [0, 0, 0, 0, 0, 0, - (140 * G 6)]"
    by (simp add: power2_eq_square power3_eq_cube unwind fls_terms_def fls_times_nth(1) 
                  fls_nth_weierstrass F_def eisenstein_series_odd_eq_0 flip: One_nat_def)

  have F: "f has_laurent_expansion F"
    unfolding f_def F_def by (intro laurent_expansion_intros)

  have "fls_subdegree F \<ge> 0"
  proof (cases "F = 0")
    case False
    thus ?thesis
    proof (rule fls_subdegree_geI)
      show "fls_nth F k = 0" if "k < 0" for k
      proof (cases "k < -6")
        case True
        thus ?thesis
          by (simp add: power2_eq_square power3_eq_cube fls_times_nth(1) F_def)
      next
        case False
        with \<open>k < 0\<close> have "k \<in> {-6, -5, -4, -3, -2, -1}"
          by auto
        thus ?thesis using \<open>k < 0\<close>
          using coeffs by auto
      qed
    qed
  qed auto

  have per_g: "is_periodic \<omega> g" if "\<omega> \<in> \<Omega>" for \<omega>
    using that omega_is_periodic[OF that f.is_doubly_periodic]
    by (auto simp: g_def is_periodic_def)
  hence per_g': "is_doubly_periodic \<omega>1 \<omega>2 g"
    unfolding is_doubly_periodic_def by (intro conjI ratio_notin_real per_g omegaI1 omegaI2)

  have "f holomorphic_on -\<Omega>* - {0}"
    unfolding f_def by (intro holomorphic_intros) (auto simp: omega_omega_minus_zero)
  moreover have "open (-\<Omega>*)"
    using closed_omega_minus_zero by auto
  moreover have "f \<midarrow>0\<rightarrow> fls_nth F 0"
    using F \<open>fls_subdegree F \<ge> 0\<close> by (meson has_laurent_expansion_imp_tendsto_0)
  hence "f \<midarrow>0\<rightarrow> -140 * G 6"
    using coeffs by simp
  ultimately have "(\<lambda>z. if z = 0 then -140 * G 6 else f z) holomorphic_on -\<Omega>*"
    unfolding g_def by (rule removable_singularity)
  hence "(\<lambda>z. if z = 0 then -140 * G 6 else f z) analytic_on {0}"
    using closed_omega_minus_zero zero_notin_omega_mz unfolding analytic_on_holomorphic by blast
  also have "?this \<longleftrightarrow> g analytic_on {0}"
    using closed_omega_minus_zero zero_notin_omega_mz
    by (intro analytic_at_cong refl eventually_mono[OF eventually_nhds_in_open[of "-\<Omega>*"]])
       (auto simp: g_def f_def omega_omega_minus_zero)
  finally have "g analytic_on {0}" .

  have "g analytic_on (-\<Omega> \<union> (\<Union>\<omega>\<in>\<Omega>. {\<omega>}))"
    unfolding analytic_on_Un analytic_on_UN
  proof safe
    fix \<omega> :: complex
    assume \<omega>: "\<omega> \<in> \<Omega>"
    have "g \<circ> (\<lambda>z. z - \<omega>) analytic_on {\<omega>}"
      using \<open>g analytic_on {0}\<close>
      by (intro analytic_on_compose) (auto intro!: analytic_intros)
    also have "g \<circ> (\<lambda>z. z - \<omega>) = g"
      using per_g[of "-\<omega>"] \<omega> by (simp add: is_periodic_def o_def omega_minus_iff)
    finally show "g analytic_on {\<omega>}" .
  next
    have "f holomorphic_on (-\<Omega>)"
      unfolding f_def by (auto intro!: holomorphic_intros)
    also have "?this \<longleftrightarrow> g holomorphic_on (-\<Omega>)"
      by (intro holomorphic_cong refl) (auto simp: g_def)
    finally show "g analytic_on (-\<Omega>)"
      using closed_omega by (subst analytic_on_open) auto
  qed
  also have "\<dots> = UNIV"
    by blast
  finally have "g analytic_on UNIV" .

  have "is_constant g"
  proof (rule Liouville_theorem)
    have cont_g: "continuous_on (period_parallelogram \<omega>1 \<omega>2 0 0) g"
      using \<open>g analytic_on UNIV\<close>
      by (blast intro: holomorphic_on_imp_continuous_on holomorphic_on_subset analytic_imp_holomorphic)
    have "compact (g ` period_parallelogram \<omega>1 \<omega>2 0 0)"
      by (intro compact_continuous_image cont_g compact_parallelogram)
    also have "g ` period_parallelogram \<omega>1 \<omega>2 0 0 = range g"
      by (intro f_parallelogram per_g')
    finally show "bounded (range g)"
      using compact_imp_bounded by blast
  qed (use \<open>g analytic_on UNIV\<close> in \<open>auto simp: constant_on_def intro: analytic_imp_holomorphic\<close>)

  then obtain c where c: "g z = c" for z
    unfolding constant_on_def by blast
  from c[of 0] have "c = -140 * G 6"
    by (simp add: g_def)
  with c[of z] and assms show ?thesis
    by (simp add: g_def f_def algebra_simps)
qed

theorem fls_weierstrass_ODE1:
  defines "P \<equiv> fls_weierstrass"
  shows   "fls_deriv P ^ 2 = 4 * P ^ 3 - fls_const (60 * G 4) * P - fls_const (140 * G 6)"
  (is "?lhs = ?rhs")
proof -
  have ev: "eventually (\<lambda>z. z \<in> -\<Omega>* - {0}) (at 0)"
    using closed_omega_minus_zero zero_notin_omega_mz by (intro eventually_at_in_open) auto
  have "(\<lambda>z. \<wp>' z ^ 2) has_laurent_expansion ?lhs"
    unfolding P_def by (intro laurent_expansion_intros)
  also have "?this \<longleftrightarrow> (\<lambda>z. 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6) has_laurent_expansion ?lhs"
    by (intro has_laurent_expansion_cong refl eventually_mono[OF ev] weierstrass_fun_ODE1)
       (auto simp: omega_omega_minus_zero)
  finally have \<dots> .
  moreover have "(\<lambda>z. 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6) has_laurent_expansion ?rhs"
    unfolding P_def by (intro laurent_expansion_intros)
  ultimately show ?thesis
    using has_laurent_expansion_unique by blast
qed

theorem fls_weierstrass_ODE2:
  defines "P \<equiv> fls_weierstrass"
  shows   "fls_deriv (fls_deriv P) = 6 * P ^ 2 - fls_const (30 * G 4)"
proof -
  define d where "d = fls_deriv P"

  have "fls_subdegree d = -3"
    using fls_subdegree_weierstrass unfolding d_def
    by (subst fls_subdegree_deriv) (auto simp: P_def)
  hence nz: "d \<noteq> 0" by auto

  have "2 * d * fls_deriv d 
          = 2 * d * (6 * P\<^sup>2  - 30 * fls_const (G 4))"
    using arg_cong[OF fls_weierstrass_ODE1, of fls_deriv]
    unfolding P_def [symmetric] fls_const_mult_const [symmetric] d_def
    by (simp add: fls_deriv_power algebra_simps)
  then have "fls_deriv d = 6 * P\<^sup>2 - 30 * fls_const (G 4)"
    using nz by simp
  then show ?thesis unfolding d_def
    by (metis fls_const_mult_const fls_const_numeral)
qed

section \<open>The Eisenstein Series and the Invariants $g_2$ and $g_3$\<close>

text \<open>Definitions from Apostol, \S 1.9\<close>
definition invariant_g2:: "complex" ("\<g>\<^sub>2") where
  "\<g>\<^sub>2 \<equiv> 60 * eisenstein_series 4"

definition invariant_g3:: "complex" ("\<g>\<^sub>3") where
  "\<g>\<^sub>3 \<equiv> 140 * eisenstein_series 6"

theorem weierstrass_fun_ODE1':
  assumes "z \<notin> \<Omega>"
  shows   "\<wp>' z ^ 2 = 4 * \<wp> z ^ 3 - \<g>\<^sub>2 * \<wp> z - \<g>\<^sub>3"
  using weierstrass_fun_ODE1[OF assms] by (simp add: invariant_g2_def invariant_g3_def)

(* TODO: Move *)
lemma pointed_ball_nonempty:
  assumes "r > 0"
  shows   "ball x r - {x :: 'a :: {perfect_space, metric_space}} \<noteq> {}"
  using perfect_choose_dist[of r x] assms by (auto simp: ball_def dist_commute)  

text \<open>
  This is the ODE obtained by differentiating the first ODE. Some care is needed here
  because we need to cancel \<open>\<wp>'(z)\<close> from both sides of the equation, which is not possible when
  \<open>\<wp>'(z) = 0\<close>, so we prove the result first for all \<open>z\<close> such that \<open>\<wp>(z) \<noteq> 0\<close> and then extend
  the result using analytic continuation.

  With a better theory of Laurent expansions, one could also use the formal ODE on the Laurent
  series above to get a simpler proof.
\<close>
theorem weierstrass_fun_ODE':
  assumes "z \<notin> \<Omega>"
  shows   "deriv \<wp>' z = 6 * \<wp> z ^ 2 - \<g>\<^sub>2 / 2"
proof -
  define P where "P = fls_weierstrass"
  have "(\<lambda>z. deriv \<wp>' z - 6 * \<wp> z ^ 2 + \<g>\<^sub>2 / 2) has_laurent_expansion
        fls_deriv (fls_deriv P) - 6 * P ^ 2 + fls_const (\<g>\<^sub>2 / 2)" (is "?f has_laurent_expansion _")
    unfolding P_def by (intro laurent_expansion_intros)
  also have "\<dots> = 0"
    by (simp add: fls_weierstrass_ODE2 P_def invariant_g2_def)
  finally have "?f has_laurent_expansion 0" .
  hence "?f z = 0"
  proof (rule has_laurent_expansion_0_analytic_continuation)
    show "?f holomorphic_on UNIV - \<Omega>* - {0}"
      using closed_omega_minus_zero
      by (intro holomorphic_intros) (auto simp: omega_omega_minus_zero)
    show "connected (UNIV - \<Omega>*)"
      by (intro connected_open_diff_countable countable_subset[OF _ countable_omega])
         (auto simp: omega_omega_minus_zero)        
  qed (use assms closed_omega_minus_zero in \<open>auto simp: omega_omega_minus_zero zero_notin_omega_mz\<close>)
  thus ?thesis by (simp add: algebra_simps)
qed

text \<open>Theorem 1.13\<close>
theorem eisenstein_series_as_polynomials:
  defines "b \<equiv> \<lambda>n. (2*n + 1) * (G (2*n + 2))"
  shows "b 1 = \<g>\<^sub>2 / 20"
    and "b 2 = \<g>\<^sub>3 / 28"
    and "\<And>n. n \<ge> 3 \<Longrightarrow> (2 * of_nat n + 3) * (of_nat n - 2) * b n = 3 * (\<Sum>i=1..n-2. b i * b (n - i - 1))"
proof -
  show "b 1 = \<g>\<^sub>2 / 20" "b 2 = \<g>\<^sub>3 / 28"
    by (simp_all add: b_def invariant_g2_def invariant_g3_def)
next
  fix n :: nat assume n: "n \<ge> 3"

  define c where "c = fls_nth fls_weierstrass"
  have b_c: "b n = c (2 * n)" if "n > 0" for n
    using that by (simp add: c_def fls_nth_weierstrass nat_add_distrib b_def nat_mult_distrib)

  have "(2 * of_nat n) * (2 * of_nat n - 1) * b n =
        6 * fls_nth (fls_weierstrass\<^sup>2) (2 * int n - 2)"
    using arg_cong[OF fls_weierstrass_ODE2, of "\<lambda>F. fls_nth F (2 * (n - 1))"] n
    by (simp add: algebra_simps of_nat_diff nat_mult_distrib b_c c_def)
  also have "fls_nth (fls_weierstrass\<^sup>2) (2 * int n - 2) =
             (\<Sum>i=-2..2 * int n. c i * c (2 * int n - 2 - i))"
    by (simp add: power2_eq_square fls_times_nth(2) fls_subdegree_weierstrass flip: c_def)
  also have "\<dots> = (\<Sum>i\<in>{-2..2 * int n}-{n. odd n}. c i * c (2 * int n - 2 - i))"
    by (intro sum.mono_neutral_right)
       (auto simp: c_def fls_nth_weierstrass eisenstein_series_odd_eq_0 even_nat_iff)
  also have "\<dots> = (\<Sum>i\<in>{-1, int n} \<union> {0..<int n}. c (2 * i) * c (2 * (int n - i - 1)))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. 2 * k" "\<lambda>k. k div 2"]) (auto simp: algebra_simps)
  also have "\<dots> = 2 * b n + (\<Sum>i=0..<int n. c (2 * i) * c (2 * (int n - i - 1)))"
    using n by (subst sum.union_disjoint) (auto simp: c_def fls_nth_weierstrass b_c)
  also have "(\<Sum>i=0..<int n. c (2 * i) * c (2 * (int n - i - 1))) =
             (\<Sum>i=0..<n. c (2 * int i) * c (2 * (int n - int i - 1)))"
    by (intro sum.reindex_bij_witness[of _ int nat]) (auto simp: of_nat_diff)
  also have "\<dots> = (\<Sum>i=1..n-2. c (2 * int i) * c (2 * (int n - int i - 1)))"
    by (intro sum.mono_neutral_right) (auto simp: c_def fls_nth_weierstrass)
  also have "\<dots> = (\<Sum>i=1..n-2. b i * b (n - i - 1))"
    using n by (intro sum.cong) (auto simp: b_c of_nat_diff algebra_simps)
  finally show "(2 * of_nat n + 3) * (of_nat n - 2) * b n 
      = 3 * (\<Sum>i=1..n-2. b i * b (n - i - 1))"
    by Groebner_Basis.algebra
qed

section \<open>The Numbers $e_1, e_2, e_3$\<close>

(* Definition p.13 *)
definition number_e1:: "complex" ("\<e>\<^sub>1") where
"\<e>\<^sub>1 \<equiv> \<wp> (\<omega>1 / 2)"

definition number_e2:: "complex" ("\<e>\<^sub>2") where
"\<e>\<^sub>2 \<equiv> \<wp> (\<omega>2 / 2)"

definition number_e3:: "complex" ("\<e>\<^sub>3") where
"\<e>\<^sub>3 \<equiv> \<wp> ((\<omega>1 + \<omega>2) / 2)" 

lemma half_period_is_zero_of_odd_fun:
  assumes "f (-(\<omega> / 2)) = -f (\<omega> / 2)" "is_periodic \<omega> f"
  shows   "f (\<omega> / 2 :: complex) = (0 :: complex)"
  using is_periodicD[OF assms(2), of "-\<omega> / 2"] assms by simp

lemma half_periods_notin_omega [simp]:
  "\<omega>1 / 2 \<notin> \<Omega>" "\<omega>2 / 2 \<notin> \<Omega>" "(\<omega>1 + \<omega>2) / 2 \<notin> \<Omega>"
  using fraction_not_in_ints[of 2 1, where ?'a = real] by (auto simp: in_omega_conv_\<omega>12_coords)

lemma half_period_weierstrass_fun_is_root:
  assumes "\<omega> \<in> \<Omega>" "\<omega> / 2 \<notin> \<Omega>"
  defines "z \<equiv> \<wp> (\<omega> / 2)"
  shows   "4 * z ^ 3 - \<g>\<^sub>2 * z - \<g>\<^sub>3 = 0"
proof -
  have "\<wp>' (\<omega> / 2) = 0"
    using weierstrass_fun_deriv_minus[of "\<omega> / 2"] assms
    by (intro half_period_is_zero_of_odd_fun weierstrass_fun_deriv_is_periodic) auto
  hence "0 = \<wp>' (\<omega> / 2) ^ 2"
    by simp
  also have "\<dots> = 4 * \<wp> (\<omega> / 2) ^ 3 - \<g>\<^sub>2 * \<wp> (\<omega> / 2) - \<g>\<^sub>3"
    using assms by (subst weierstrass_fun_ODE1') auto
  finally show ?thesis
    by (simp add: z_def)
qed

lemma weierstass_fun_deriv_half_root_eq_0 [simp]:
  "\<wp>' (\<omega>1 / 2) = 0" "\<wp>' (\<omega>2 / 2) = 0" "\<wp>' ((\<omega>1 + \<omega>2) / 2) = 0"
  by (rule half_period_is_zero_of_odd_fun weierstrass_fun_deriv_minus
           weierstrass_fun_deriv_is_periodic omegaI1 omegaI2 omega_add)+

lemma depressed_cubic_discriminant:
  fixes a b :: "'a :: idom"
  assumes "[:b, a, 0, c:] = Polynomial.smult c ([:-x1, 1:] * [:-x2, 1:] * [:-x3, 1:])"
  shows   "c ^ 3 * (x1 - x2)\<^sup>2 * (x1 - x3)\<^sup>2 * (x2 - x3)\<^sup>2 = -4 * a ^ 3 - 27 * c * b ^ 2"
  using assms by (simp add: algebra_simps) Groebner_Basis.algebra

text \<open>Theorem 1.14\<close>

lemma is_zero_cong:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)" "a=b"
  shows "is_zero f a \<longleftrightarrow> is_zero g b"
proof -
  have "(f \<longlongrightarrow> 0) (nhds a) \<longleftrightarrow> (g \<longlongrightarrow> 0) (nhds b)" 
    using assms(1) assms(2) filterlim_cong by blast
  moreover have "(\<forall>\<^sub>F x in at a. f x \<noteq> 0) \<longleftrightarrow> (\<forall>\<^sub>F x in at b. g x \<noteq> 0)" 
    by (smt (verit, del_insts) assms(1) assms(2) eventually_elim2
        eventually_nhds_conv_at)
  ultimately show ?thesis
    unfolding is_zero_def by simp
qed

theorem distinct_e123: "distinct [\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3]"
proof -
  define X where "X = {\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2}"
  have empty: "X \<inter> \<Omega> = {}"
    by (auto simp: X_def)
  have roots: "\<forall>x\<in>X. \<wp>' x = 0"
    using weierstass_fun_deriv_half_root_eq_0 unfolding X_def by blast
  have X_subset: "X \<subseteq> period_parallelogram' \<omega>1 \<omega>2 0 0"
    unfolding period_parallelogram'_altdef of_\<omega>12_coords_image_eq
    by (auto simp: X_def)

  have *: "\<wp> w1 \<noteq> \<wp> w2" if w12: "{w1, w2} \<subseteq> X" and neq: "w1 \<noteq> w2" for w1 w2
  proof
    assume eq: "\<wp> w1 = \<wp> w2"
    have not_in_omega [simp]: "w1 \<notin> \<Omega>" "w2 \<notin> \<Omega>"
      using empty that(1) by blast+

    define f where "f = (\<lambda>z. \<wp> z - \<wp> w1)"

    have deriv_eq: "deriv f w = \<wp>' w" if "w \<notin> \<Omega>" for w
      unfolding f_def using that 
      by (auto intro!: derivative_eq_intros DERIV_imp_deriv)
    have "deriv f w1 = 0" "deriv f w2 = 0"
      using w12 roots not_in_omega deriv_eq by (metis insert_subset)+
    moreover have [simp]: "f w1 = 0" "f w2 = 0"
      using eq by (simp_all add: f_def)

    have "f has_laurent_expansion fls_weierstrass - fls_const (\<wp> w1)"
      unfolding f_def by (intro laurent_expansion_intros)
    moreover have "fls_subdegree (fls_weierstrass - fls_const (\<wp> w1)) = -2"
      by (simp add: fls_subdegree_weierstrass fls_subdegree_diff_eq1)
    ultimately have [simp]: "is_pole f 0" "zorder f 0 = -2"
      by (auto dest: has_laurent_expansion_imp_is_pole_0 has_laurent_expansion_zorder_0)
    have [simp]: "\<not>is_constant f"
      using pole_imp_not_constant[OF \<open>is_pole f 0\<close>, of UNIV UNIV] by auto

    have "\<not>(\<forall>x\<in>-\<Omega>. f x = 0)"
    proof
      assume *: "\<forall>x\<in>-\<Omega>. f x = 0"
      have "eventually (\<lambda>x. x \<in> -\<Omega>* - {0}) (at 0)"
        using closed_omega_minus_zero zero_notin_omega_mz
        by (intro eventually_at_in_open) auto
      hence "eventually (\<lambda>x. f x = 0) (at 0)"
        by eventually_elim (use * in \<open>auto simp: omega_omega_minus_zero\<close>)
      hence "f \<midarrow>0\<rightarrow> 0"
        by (simp add: tendsto_eventually)
      with \<open>is_pole f 0\<close> show False
        unfolding is_pole_def using not_tendsto_and_filterlim_at_infinity[of "at 0" f 0] by auto
    qed
    then obtain z0 where z0: "z0 \<notin> \<Omega>" "f z0 \<noteq> 0"
      by auto
    then have nconst:"\<not> f constant_on (UNIV-\<Omega>)"
      by (metis (mono_tags, lifting) Diff_iff UNIV_I \<open>f w1 = 0\<close>
          constant_on_def not_in_omega(1))
    have zorder_ge: "zorder f w \<ge> int 2" if "w \<in> {w1, w2}" for w
    proof (rule zorder_geI)
      show "f analytic_on {w}" "f holomorphic_on UNIV - \<Omega>"
        unfolding f_def using that w12 empty
        by (auto intro!: analytic_intros holomorphic_intros)
      show "connected (UNIV - \<Omega>)"
        using countable_omega by (intro connected_open_diff_countable) auto
      show "z0 \<in> UNIV - \<Omega>" "f z0 \<noteq> 0"
        using z0 by auto
    next
      fix k :: nat
      assume "k < 2"
      hence "k = 0 \<or> k = 1"
        by auto
      thus "(deriv ^^ k) f w = 0"
        using that w12 empty deriv_eq[of w] roots by auto
    qed (use closed_omega that w12 empty in auto)

    have not_pole: "\<not>is_pole f w" if "w \<in> {w1, w2}" for w
    proof -
      have "f holomorphic_on -\<Omega>"
        unfolding f_def by (intro holomorphic_intros) auto
      moreover have "open (-\<Omega>)" "w \<in> -\<Omega>"
        using that empty w12 closed_omega by auto
      ultimately show ?thesis
        using not_is_pole_holomorphic by blast
    qed

    have no_further_poles: "\<not>is_pole f z" if "z \<in> period_parallelogram' \<omega>1 \<omega>2 0 0 - {0}" for z
    proof -
      have "f holomorphic_on -\<Omega>"
        unfolding f_def by (intro holomorphic_intros) auto
      moreover have "z \<notin> \<Omega>"
      proof
        assume "z \<in> \<Omega>"
        then obtain m n where z_eq: "z = of_\<omega>12_coords (of_int m, of_int n)"
          by (auto simp: omega_def of_\<omega>12_coords_def)
        from that have "m = 0" "n = 0"
          unfolding period_parallelogram'_altdef of_\<omega>12_coords_image_eq
          by (simp_all add: z_eq)
        with that show False
          by (auto simp: z_eq)
      qed
      ultimately show "\<not>is_pole f z"
        using closed_omega not_is_pole_holomorphic[of "-\<Omega>" z f] by auto
    qed

    define g where "g = (\<lambda>z. (if z\<in>\<Omega> then 0 else \<wp> z - \<wp> w1))"
    
    have event_gf:"\<forall>\<^sub>F x in at w. g x = f x" for w
    proof -
      have "\<forall>\<^sub>F x in at w. x\<notin>\<Omega>"
        using islimpt_iff_eventually not_islimpt_omega by blast
      then show "\<forall>\<^sub>F x in at w. g x = f x"
        unfolding g_def f_def by (auto elim:eventually_mono)
    qed

    interpret g: elliptic_fun g \<omega>1 \<omega>2 
    proof -
      have g_pole:"is_pole g z" if "z \<in> \<Omega>" for z
      proof -
        have "is_pole \<wp> z"
          using that is_pole_weierstrass_fun by auto
        then have "is_pole f z" 
          unfolding f_def using is_pole_plus_const_iff[where c="- \<wp> w1"]
          by auto
        then show "is_pole g z" 
          using event_gf is_pole_cong by blast
      qed

      have "g meromorphic_on UNIV" 
      proof (rule meromorphic_onI_open)
        have "f holomorphic_on (UNIV - \<Omega>)" 
          unfolding f_def by (auto intro!: holomorphic_intros)
        then have "g holomorphic_on (UNIV - \<Omega>)" 
          apply (elim holomorphic_transform)
          unfolding g_def f_def by auto
        moreover have "open (UNIV - \<Omega>)" 
          by (simp add: closed_omega open_Diff)
        ultimately show "g analytic_on UNIV - \<Omega>" 
          using analytic_on_open by auto
        show "not_essential g z" if "z \<in> \<Omega>" for z
          using g_pole[OF that] unfolding not_essential_def by simp
        show "\<And>z. \<not> z islimpt \<Omega> \<inter> UNIV"
          using not_islimpt_omega by auto
      qed simp
      moreover have "is_doubly_periodic \<omega>1 \<omega>2 g" 
      proof -
        have "is_periodic \<omega>1 g"
          unfolding g_def
          by (smt (verit) is_periodic_def omegaI1 
              omega_plus_right_cancel weierstrass_fun_is_periodic)
        moreover have "is_periodic \<omega>2 g"
          unfolding g_def
          by (smt (verit) is_periodic_def omegaI2 
              omega_plus_right_cancel weierstrass_fun_is_periodic)
        ultimately show ?thesis
          unfolding is_doubly_periodic_def using ratio_notin_real
          by auto
      qed
      moreover have "is_pole g z \<and> g z = 0 \<or> g \<midarrow>z\<rightarrow> g z" for z 
      proof (cases "z\<in>\<Omega>")
        case True
        then show ?thesis 
          using g_pole unfolding g_def by auto
      next
        case False 
        moreover have "f analytic_on UNIV - \<Omega>"
          unfolding f_def by (intro analytic_intros) blast
        ultimately have "f analytic_on {z}"
          by (simp add: analytic_on_subset)
        then have "f \<midarrow>z\<rightarrow> f z"
          by (simp add: analytic_at_imp_isCont isContD)
        moreover have "\<forall>\<^sub>F x in nhds w. g x = f x" if "w\<notin>\<Omega>" for w
        proof -
          have "g w=f w"
            unfolding f_def g_def using that by auto
          then show ?thesis 
            using event_gf eventually_nhds_conv_at by auto
        qed
        ultimately have "g \<midarrow>z\<rightarrow> g z"
          using False event_gf eventually_nhds_x_imp_x tendsto_cong 
          by fastforce
        then show ?thesis by simp
      qed
      ultimately show "elliptic_fun g \<omega>1 \<omega>2"
        using elliptic_fun'.intro elliptic_fun_axioms.intro 
          elliptic_fun_def 
        by presburger
    qed
    
    have fg_zorder:"zorder f w = zorder g w" for w
      using event_gf zorder_cong by metis

    have "4 = (\<Sum>z\<in>{w1, w2}. 2 :: nat)"
      using neq by simp
    also have "\<dots> \<le> (\<Sum>z\<in>{w1, w2}. nat (zorder f z))"
      using zorder_ge[of w1] zorder_ge[of w2] by (intro sum_mono) auto
    also have "\<dots> \<le> (\<Sum>z\<in>g.zeros_in_period_parallelogram 0. nat (zorder f z))"
    proof (intro sum_mono2 g.finite_zeros_in_pp)
      have "w1\<in>g.shifted_period_parallelogram' 0"
          "w2\<in>g.shifted_period_parallelogram' 0"
        using X_subset g.shifted_period_parallelogram'_def w12 
        by fastforce+
      moreover have "is_zero g w" if "w\<in>{w1,w2}" for w
      proof -
        have "\<not> is_pole f w"
          using not_pole that by blast
        then have "\<not> is_pole g w" 
          using event_gf is_pole_cong by blast
        moreover have "g w = 0" 
          using \<open>f w2 = 0\<close> f_def g_def that by fastforce
        moreover have "g z0 \<noteq> 0" 
          using f_def g_def z0(1) z0(2) by presburger
        ultimately show ?thesis 
          using g.zero_or_pole_iff by fast
      qed
      ultimately show "{w1, w2} \<subseteq> g.zeros_in_period_parallelogram 0"
        unfolding g.zeros_in_period_parallelogram_def
        by simp
    qed simp
    also have "\<dots> = g.order" 
    proof -
      have "g z0 \<noteq> 0" 
        using f_def g_def z0(1) z0(2) by presburger
      then show ?thesis
        using g.order_zeros' fg_zorder by simp
    qed
    also have "g.order = (\<Sum>z\<in>g.poles_in_period_parallelogram 0. nat (-zorder g z))"
      by (rule g.order_poles' [symmetric])
    also have "... = (\<Sum>z\<in>g.poles_in_period_parallelogram 0. nat (-zorder f z))"
      using fg_zorder by simp
    also have "\<dots> \<le> (\<Sum>z\<in>{0}. nat (-zorder f z))" 
    proof (rule sum_mono2) 
      have "\<not> is_pole g w" 
        if "w \<in> period_parallelogram' \<omega>1 \<omega>2 0 0 - {0}" for w
        using no_further_poles[OF that] event_gf is_pole_cong by blast
      then show "g.poles_in_period_parallelogram 0 \<subseteq> {0}"
        unfolding g.poles_in_period_parallelogram_def
          g.shifted_period_parallelogram'_def
        by auto
    qed simp_all
    also have "\<dots> = 2" by simp
    finally show False by simp
  qed
  show ?thesis
    by (simp add: number_e1_def number_e2_def number_e3_def; intro conjI *) (auto simp: X_def)
qed

theorem
  fixes z:: "complex"
  defines "P \<equiv> [:-\<g>\<^sub>3, -\<g>\<^sub>2, 0, 4:]"
  shows discr_nonzero_aux1: "P = 4 * [:-\<e>\<^sub>1, 1:] * [:-\<e>\<^sub>2, 1:] * [:-\<e>\<^sub>3, 1:]"
  and   discr_nonzero_aux2: "4 * (\<wp> z)^3 - \<g>\<^sub>2 * (\<wp> z) - \<g>\<^sub>3 = 4 * (\<wp> z - \<e>\<^sub>1) * (\<wp> z - \<e>\<^sub>2) * (\<wp> z - \<e>\<^sub>3)" 
  and   discr_nonzero: "\<g>\<^sub>2^3 - 27 * \<g>\<^sub>3^2 \<noteq> 0"
proof -
  have zeroI: "poly P (\<wp> (\<omega> / 2)) = 0" if "\<omega> \<in> \<Omega>" "\<omega> / 2 \<notin> \<Omega>" for \<omega>
    using half_period_weierstrass_fun_is_root[OF that]
    by (simp add: P_def power3_eq_cube algebra_simps)

  obtain xs where "length xs = 3" and "Polynomial.smult 4 (\<Prod>x\<leftarrow>xs. [:-x, 1:]) = P"
    using fundamental_theorem_algebra_factorized[of P] 
    by (auto simp: P_def numeral_3_eq_3)
  hence P_eq: "P = Polynomial.smult 4 (\<Prod>x\<leftarrow>xs. [:-x, 1:])"
    by simp
  from \<open>length xs = 3\<close> obtain x1 x2 x3 where xs: "xs = [x1, x2, x3]"
    by (auto simp: numeral_3_eq_3 length_Suc_conv)
  have poly_P_eq: "poly P x = 4 * (x - x1) * (x - x2) * (x - x3)" for x
    by (simp add: algebra_simps P_eq xs)

  have "\<forall>x\<in>{\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}. poly P x = 0"
    by (auto simp: number_e1_def number_e2_def number_e3_def intro!: zeroI omega_add omegaI1 omegaI2)
  hence set_xs: "set xs = {\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}" and distinct: "distinct xs"
    using distinct_e123 by (auto simp: poly_P_eq xs)
  have "P = Polynomial.smult 4 (\<Prod>x\<in>set xs. [:-x, 1:])"
    using distinct P_eq by (subst prod.distinct_set_conv_list) auto
  thus P_eq': "P = 4 * [:-\<e>\<^sub>1, 1:] * [:-\<e>\<^sub>2, 1:] * [:-\<e>\<^sub>3, 1:]"
    unfolding set_xs using distinct_e123  by (simp add: xs numeral_poly algebra_simps)

  from arg_cong[OF this, of "\<lambda>P. poly P (\<wp> z)"]
    show "4 * (\<wp> z)^3 - \<g>\<^sub>2 * (\<wp> z) - \<g>\<^sub>3 = 4 * (\<wp> z - \<e>\<^sub>1) * (\<wp> z - \<e>\<^sub>2) * (\<wp> z - \<e>\<^sub>3)" 
    by (simp add: P_def numeral_poly algebra_simps power3_eq_cube)

  have "-4 * (-\<g>\<^sub>2) ^ 3 - 27 * 4 * (-\<g>\<^sub>3) ^ 2 = 4 ^ 3 * (\<e>\<^sub>1 - \<e>\<^sub>2)\<^sup>2 * (\<e>\<^sub>1 - \<e>\<^sub>3)\<^sup>2 * (\<e>\<^sub>2 - \<e>\<^sub>3)\<^sup>2"
    by (rule sym, rule depressed_cubic_discriminant, fold P_def) (simp add: P_eq' numeral_poly)
  also have "\<dots> \<noteq> 0"
    using distinct_e123 by simp
  finally show "\<g>\<^sub>2^3 - 27 * \<g>\<^sub>3^2 \<noteq> 0"
    by simp
qed

end (* gen_lattice *)


context std_lattice
begin

lemma eisenstein_series_norm_summable':
  "k \<ge> 3 \<Longrightarrow> (\<lambda>(m,n). norm (1 / (of_int m + of_int n * \<tau>) ^ k)) summable_on (-{(0,0)})"
  using eisenstein_series_norm_summable[of k]
        summable_on_reindex_bij_betw[OF bij_betw_omega_minus_zero, where f = "\<lambda>\<omega>. norm (1 / \<omega> ^ k)"]
  by (auto simp: eisenstein_series_def map_prod_def of_\<omega>12_coords_def
                 case_prod_unfold norm_divide norm_power)

lemma eisenstein_series_altdef:
  "eisenstein_series k =
     (if k = 0 then 1 else if k < 3 then 0 else \<Sum>\<^sub>\<infinity>(m,n)\<in>-{(0,0)}. 1 / (of_int m + of_int n * \<tau>) ^ k)"
  using infsum_reindex_bij_betw[OF bij_betw_omega_minus_zero, where f = "\<lambda>\<omega>. 1 / \<omega> ^ k"]
  by (auto simp: eisenstein_series_def map_prod_def of_\<omega>12_coords_def case_prod_unfold)

end

section \<open>Transforming lattices\<close>

locale gen_lattice_cnj = gen_lattice
begin

sublocale cnj: gen_lattice "cnj \<omega>1" "cnj \<omega>2"
  by unfold_locales (auto simp: ratio_notin_real simp flip: complex_cnj_divide)

lemma bij_betw_omega_cnj: "bij_betw cnj omega cnj.omega"
  by (rule bij_betwI[of _ _ _ cnj]) (force simp: cnj.omega_def omega_def)+

lemma bij_betw_omega_minus_zero_cnj: "bij_betw cnj omega_minus_zero cnj.omega_minus_zero"
  unfolding omega_minus_zero_def cnj.omega_minus_zero_def
  by (intro bij_betw_DiffI bij_betw_omega_cnj) auto

lemma eisenstein_series_cnj [simp]: "cnj.eisenstein_series n = cnj (eisenstein_series n)"
  unfolding eisenstein_series_def cnj.eisenstein_series_def
  by (subst infsum_reindex_bij_betw[OF bij_betw_omega_minus_zero_cnj, symmetric])
     (simp flip: infsum_cnj)

lemma omega_cnj_eq: "cnj.omega = cnj ` omega"
  using bij_betw_omega_cnj by (auto simp: bij_betw_def)

lemma omega_minus_zero_cnj_eq: "cnj.omega_minus_zero = cnj ` omega_minus_zero"
  using bij_betw_omega_minus_zero_cnj by (auto simp: bij_betw_def)

lemma eisenstein_fun_cnj: "cnj.eisenstein_fun n z = cnj (eisenstein_fun n (cnj z))"
  unfolding eisenstein_fun_def cnj.eisenstein_fun_def
  by (subst infsum_reindex_bij_betw[OF bij_betw_omega_minus_zero_cnj, symmetric])
     (auto simp flip: infsum_cnj simp: omega_minus_zero_cnj_eq in_image_cnj_iff)

lemma weierstrass_fun_aux_cnj: "cnj.weierstrass_fun_aux z = cnj (weierstrass_fun_aux (cnj z))"
  unfolding weierstrass_fun_aux_def cnj.weierstrass_fun_aux_def
  by (subst infsum_reindex_bij_betw[OF bij_betw_omega_minus_zero_cnj, symmetric])
     (auto simp flip: infsum_cnj simp: omega_minus_zero_cnj_eq in_image_cnj_iff)

lemma weierstrass_fun_cnj: "cnj.weierstrass_fun z = cnj (weierstrass_fun (cnj z))"
  unfolding weierstrass_fun_def cnj.weierstrass_fun_def
  by (auto simp: omega_cnj_eq in_image_cnj_iff weierstrass_fun_aux_cnj)
  
lemma invariant_g2_cnj [simp]: "cnj.invariant_g2 = cnj invariant_g2"
  and invariant_g3_cnj [simp]: "cnj.invariant_g3 = cnj invariant_g3"
  by (simp_all add: cnj.invariant_g2_def invariant_g2_def cnj.invariant_g3_def invariant_g3_def)

lemma number_e1_cnj [simp]: "cnj.number_e1 = cnj number_e1"
  and number_e2_cnj [simp]: "cnj.number_e2 = cnj number_e2"
  and number_e3_cnj [simp]: "cnj.number_e3 = cnj number_e3"
  by (simp_all add: number_e1_def cnj.number_e1_def number_e2_def 
                    cnj.number_e2_def number_e3_def cnj.number_e3_def weierstrass_fun_cnj)

end


locale gen_lattice_swap = gen_lattice
begin

sublocale swap: gen_lattice \<omega>2 \<omega>1
  by unfold_locales (use ratio_notin_real Im_divide_zero_iff in blast)

lemma omega_swap [simp]: "swap.omega = omega"
  by (auto simp: omega_def swap.omega_def algebra_simps)

lemma omega_minus_zero_swap [simp]: "swap.omega_minus_zero = omega_minus_zero"
  by (auto simp: omega_minus_zero_def swap.omega_minus_zero_def algebra_simps)

lemma eisenstein_series_swap [simp]: "swap.eisenstein_series = eisenstein_series"
  unfolding eisenstein_series_def [abs_def] swap.eisenstein_series_def [abs_def] by auto

lemma eisenstein_fun_swap [simp]: "swap.eisenstein_fun = eisenstein_fun"
  unfolding eisenstein_fun_def [abs_def] swap.eisenstein_fun_def [abs_def] by (auto cong: if_cong)

lemma invariant_g2_swap [simp]: "swap.invariant_g2 = invariant_g2"
  and invariant_g3_swap [simp]: "swap.invariant_g3 = invariant_g3"
  unfolding invariant_g2_def [abs_def] swap.invariant_g2_def [abs_def]
            invariant_g3_def [abs_def] swap.invariant_g3_def [abs_def] by auto

lemma weierstrass_fun_aux_swap [simp]: "swap.weierstrass_fun_aux = weierstrass_fun_aux"
  unfolding weierstrass_fun_aux_def [abs_def] swap.weierstrass_fun_aux_def [abs_def] by auto

lemma weierstrass_fun_swap [simp]: "swap.weierstrass_fun = weierstrass_fun"
  unfolding weierstrass_fun_def [abs_def] swap.weierstrass_fun_def [abs_def] by auto

lemma number_e1_swap [simp]: "swap.number_e1 = number_e2"
  and number_e2_swap [simp]: "swap.number_e2 = number_e1"
  and number_e3_swap [simp]: "swap.number_e3 = number_e3"
  unfolding number_e2_def swap.number_e1_def number_e1_def swap.number_e2_def
            number_e3_def swap.number_e3_def by (simp_all add: add_ac)

end


locale gen_lattice_stretch = gen_lattice +
  fixes c :: complex
  assumes stretch_nonzero: "c \<noteq> 0"
begin

sublocale stretched: gen_lattice "c * \<omega>1" "c * \<omega>2"
  by unfold_locales (auto simp: stretch_nonzero ratio_notin_real)

lemma mult_into_stretched_omega: "(*) c \<in> \<Omega> \<rightarrow> stretched.omega"
  by (auto simp: omega_def stretched.omega_def) (auto simp: algebra_simps)

lemma mult_into_stretched_omega': "(*) (inverse c) \<in> stretched.omega \<rightarrow> \<Omega>"
proof -
  interpret inv: gen_lattice_stretch "c * \<omega>1" "c * \<omega>2" "inverse c"
    by unfold_locales (use stretch_nonzero in auto)
  from inv.mult_into_stretched_omega show ?thesis
    by (simp add: inv.stretched.omega_def stretched.omega_def field_simps stretch_nonzero)
qed

lemma bij_betw_stretch_omega: "bij_betw ((*) c) omega stretched.omega"
proof (rule bij_betwI[of _ _ _ "(*) (inverse c)"])
  show "(*) c \<in> \<Omega> \<rightarrow> stretched.omega"
    by (rule mult_into_stretched_omega)
  show "(*) (inverse c) \<in> stretched.omega \<rightarrow> \<Omega>"
    by (rule mult_into_stretched_omega')
qed (auto simp: stretch_nonzero)

lemma bij_betw_stretch_omega_minus_zero:
  "bij_betw ((*) c) omega_minus_zero stretched.omega_minus_zero"
  unfolding omega_minus_zero_def stretched.omega_minus_zero_def
  by (intro bij_betw_DiffI bij_betw_stretch_omega) auto

lemma eisenstein_series_stretch:
  "stretched.eisenstein_series n = c powi (-n) * eisenstein_series n"
proof (cases "n \<ge> 3")
  case True
  have "stretched.eisenstein_series n = (\<Sum>\<^sub>\<infinity>x\<in>\<Omega>*. c powi (-n) * (1 / x ^ n))"
    using infsum_reindex_bij_betw[OF bij_betw_stretch_omega_minus_zero, where f = "\<lambda>\<omega>. 1 / \<omega> ^ n"] True
    unfolding stretched.eisenstein_series_def by (simp add: power_int_minus field_simps)
  also have "\<dots> = c powi (-n) * eisenstein_series n"
    using True by (subst infsum_cmult_right') (auto simp: eisenstein_series_def)
  finally show ?thesis .
qed (auto simp: stretched.eisenstein_series_def eisenstein_series_def)

lemma invariant_g2_stretch [simp]: "stretched.invariant_g2 = invariant_g2 / c ^ 4"
  and invariant_g3_stretch [simp]: "stretched.invariant_g3 = invariant_g3 / c ^ 6"
  unfolding invariant_g2_def stretched.invariant_g2_def 
            invariant_g3_def stretched.invariant_g3_def eisenstein_series_stretch
  by (simp_all add: power_int_minus field_simps)
     
end


locale unimodular_transform_lattice = gen_lattice + unimodular_transform
begin

definition \<omega>1' where "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
definition \<omega>2' where "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"

sublocale transformed: gen_lattice \<omega>1' \<omega>2'
proof unfold_locales
  define \<tau> where "\<tau> = \<omega>2 / \<omega>1"
  have "Im (\<phi> \<tau>) \<noteq> 0"
    using ratio_notin_real Im_transform_zero_iff[of \<tau>] unfolding \<tau>_def by auto
  also have "\<phi> \<tau> = \<omega>2' / \<omega>1'"
    by (simp add: \<phi>_def \<omega>1'_def \<omega>2'_def moebius_def \<tau>_def divide_simps)
  finally show "Im (\<omega>2' / \<omega>1') \<noteq> 0"
    by (simp add: \<phi>_def \<omega>1'_def \<omega>2'_def moebius_def \<tau>_def field_simps)
qed

lemma transformed_omega_subset: "transformed.omega \<subseteq> omega"
proof safe
  fix z assume "z \<in> transformed.omega"
  then obtain m n where mn: "z = of_int m * \<omega>1' + of_int n * \<omega>2'"
    by (auto simp: transformed.omega_def)
  also have "of_int m * \<omega>1' + of_int n * \<omega>2' =
             of_int (d * m + b * n) * \<omega>1 + of_int (c * m + a * n) * \<omega>2"
    by (simp add: algebra_simps \<omega>1'_def \<omega>2'_def)
  finally show "z \<in> omega"
    unfolding omega_def by blast
qed

lemma transformed_omega_eq: "transformed.omega = omega"
proof -
  interpret inverse_unimodular_transform a b c d ..
  interpret inv: unimodular_transform_lattice \<omega>1' \<omega>2' d "-b" "-c" a ..
  have [simp]: "inv.\<omega>1' = \<omega>1" "inv.\<omega>2' = \<omega>2"
    unfolding inv.\<omega>1'_def inv.\<omega>2'_def unfolding \<omega>1'_def \<omega>2'_def of_int_minus using unimodular
    by (simp_all add: algebra_simps flip: of_int_mult)
    
  have "inv.transformed.omega \<subseteq> transformed.omega"
    by (rule inv.transformed_omega_subset)
  also have "inv.transformed.omega = omega"
    unfolding inv.transformed.omega_def unfolding omega_def by simp
  finally show ?thesis
    using transformed_omega_subset by blast
qed  

lemma transformed_omega_minus_zero_eq: "transformed.omega_minus_zero = omega_minus_zero"
  by (simp add: transformed.omega_minus_zero_def omega_minus_zero_def transformed_omega_eq)

lemma eisenstein_fun_transformed [simp]: "transformed.eisenstein_fun = eisenstein_fun"
  by (intro ext) (simp add: transformed.eisenstein_fun_def eisenstein_fun_def
                            transformed_omega_minus_zero_eq)

lemma eisenstein_series_transformed [simp]: "transformed.eisenstein_series = eisenstein_series"
  by (intro ext) (simp add: transformed.eisenstein_series_def eisenstein_series_def
                            transformed_omega_minus_zero_eq)

lemma invariant_g2_transformed [simp]: "transformed.invariant_g2 = invariant_g2"
  and invariant_g3_transformed [simp]: "transformed.invariant_g3 = invariant_g3"
  and weierstrass_fun_aux_transformed [simp]: "transformed.weierstrass_fun_aux = weierstrass_fun_aux"
     by ((intro ext)?, unfold invariant_g2_def invariant_g3_def number_e1_def weierstrass_fun_aux_def
          transformed.invariant_g2_def transformed.invariant_g3_def
          transformed.weierstrass_fun_aux_def transformed_omega_minus_zero_eq) simp_all

lemma weierstrass_fun_transformed [simp]: "transformed.weierstrass_fun = weierstrass_fun"
  by (intro ext, simp add: weierstrass_fun_def transformed.weierstrass_fun_def transformed_omega_eq)

end


subsection \<open>Concrete expressions for some Eisenstein series\<close>

named_theorems eisenstein_series_reduce

lemma eisenstein_series_collect:
  "y * (y * x) = y ^ 2 * (x :: 'a :: comm_ring_1)"
  "y * (y ^ a * x) = y ^ (a + 1) * x"
  by (simp_all add: power_add power2_eq_square)

lemma atLeastAtMost_numeral_nat_reduce [eisenstein_series_reduce]:
  "(a::nat) \<le> numeral b \<Longrightarrow> {a..numeral b} = insert (numeral b) ({a..pred_numeral b})"
  by (simp add: atLeastAtMostSuc_conv numeral_eq_Suc)

method eisenstein_series_reduce =
  (simp add: eisenstein_series_reduce,
   (simp add: field_simps)?,
   (simp add: field_simps Suc_numeral power_Suc [symmetric] 
      power_Suc2 [symmetric] eisenstein_series_collect power2_eq_square [symmetric])?)

context gen_lattice
begin

lemma eisenstein_series_reduce_aux:
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * complex_of_nat n + 1) * (complex_of_nat n - 3) * (2 * complex_of_nat n - 1)"
  shows "G (2*n) = 3 / C * (\<Sum>i=1..n-3. complex_of_nat (2 * i + 1) * G (2 * i + 2) *
                               (complex_of_nat (2 * n - 2 * i - 3) * G (2 * n - 2 * i - 2)))"
proof -
  from assms have "3 \<le> n - 1"
    by simp
  have [simp]: "C \<noteq> 0"
    unfolding C_def mult_eq_0_iff using assms by (auto simp: complex_eq_iff)
  hence "(2 * of_nat (n - 1) + 3) * (of_nat n - 3) * (2 * of_nat (n - 1) + 1) * G (2 * n) =
         3 * (\<Sum>i = 1..n - 1 - 2. (2 * complex_of_nat i + 1) *
            G (2 * i + 2) * ((2 * complex_of_nat (n - 1 - i - 1) + 1) * G (2 * (n - 1 - i - 1) + 2)))"
    using eisenstein_series_as_polynomials(3)[of "n-1"] assms
    by (simp add: algebra_simps of_nat_diff Suc_diff_Suc)
  also have "(2 * complex_of_nat (n - 1) + 3) = (2 * of_nat n + 1)"
    using assms by (simp add: of_nat_diff)
  also have "(2 * complex_of_nat (n - 1) + 1) = 2 * of_nat n - 1"
    using assms by (simp add: of_nat_diff)
  also have "(2 * complex_of_nat n + 1) * (complex_of_nat n - 3) * (2 * complex_of_nat n - 1) = C"
    unfolding C_def ..
  also have "n - 1 - 2 = n - 3"
    by simp
  also have "(\<lambda>i. n - 1 - i - 1) = (\<lambda>i. n - i - 2)"
    by auto
  finally have "G (2 * n) = 3 / C * (\<Sum>i=1..n-3.
                  (2 * of_nat i + 1) * G (2 * i + 2) *
                  ((2 * of_nat (n - i - 2) + 1) * G (2 * (n - i - 2) + 2)))" (is "_ = _ * ?S")
    by (simp add: field_simps)
  also have "?S = (\<Sum>i=1..n-3. (2 * i + 1) * G (2 * i + 2) * 
                    ((2*n-2*i-3) * G (2*n-2*i-2)))"
    by (intro sum.cong) (auto simp: of_nat_diff Suc_diff_Suc algebra_simps)
  finally show ?thesis .
qed

lemma eisenstein_series_reduce_Bit0 [eisenstein_series_reduce]:
  fixes n' :: num
  defines "n \<equiv> numeral n'"
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * complex_of_nat n + 1) * (complex_of_nat n - 3) * (2 * complex_of_nat n - 1)"
  shows "G (numeral (num.Bit0 n')) = 
           3 / C * (\<Sum>i=1..n-3. complex_of_nat (2 * i + 1) * G (2 * i + 2) *
                               (complex_of_nat (2 * n - 2 * i - 3) * G (2 * n - 2 * i - 2)))"
proof -
  have *: "numeral (num.Bit0 n') = 2 * n"
    by (simp add: n_def)
  show ?thesis
    unfolding * C_def
    by (rule eisenstein_series_reduce_aux) (use assms in auto)
qed

lemma eisenstein_series_reduce_Bit1 [simp]: "eisenstein_series (numeral (num.Bit1 n)) = 0"
  by (rule eisenstein_series_odd_eq_0) auto

lemma eisenstein_series_0 [simp]: "eisenstein_series 0 = 1"
  by (simp add: eisenstein_series_def)

lemma eisenstein_series_Suc_0 [simp]: "eisenstein_series (Suc 0) = 0"
  by (rule eisenstein_series_odd_eq_0) auto

lemma G8_eq: "G 8 = 3 / 7 * G 4 ^ 2"
  by eisenstein_series_reduce

lemma G10_eq: "G 10 = 5 / 11 * G 4 * G 6"
  by eisenstein_series_reduce

lemma G12_eq: "G 12 = 18 / 143 * G 4 ^ 3 + 25 / 143 * G 6 ^ 2"
  by eisenstein_series_reduce

lemma G14_eq: "G 14 = 30 / 143 * G 4 ^ 2 * G 6"
  by eisenstein_series_reduce

lemma G16_eq: "G 16 = 27225 / 668525 * G 4 ^ 4 + 300 / 2431 * G 4 * G 6 ^ 2"
  by eisenstein_series_reduce

lemma G18_eq: "G 18 = 3915 / 46189 * G 4 ^ 3 * G 6 + 2750 / 92378 * G 6 ^ 3"
  by eisenstein_series_reduce

end

end