chapter \<open>Klein's \<open>J\<close> function and related functions\<close>
theory Klein_J
  imports Elliptic_Functions
begin

section \<open>The Eisenstein series\<close>

definition Eisenstein_G :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "Eisenstein_G k \<tau> =
     (if k = 0 then 1 else if k < 3 \<or> \<tau> \<in> \<real> then 0
      else \<Sum>\<^sub>\<infinity>(m,n)\<in>-{(0,0)}. 1 / (of_int m + of_int n * \<tau>) ^ k)"

lemma Eisenstein_G_0 [simp]: "Eisenstein_G 0 = (\<lambda>_. 1)"
  by (auto simp: Eisenstein_G_def fun_eq_iff)

lemma Eisenstein_G_real [simp]: "n > 0 \<Longrightarrow> \<tau> \<in> \<real> \<Longrightarrow> Eisenstein_G n \<tau> = 0"
  by (simp add: Eisenstein_G_def)

lemma Eisenstein_G_altdef:
  assumes "k \<ge> 3" "(\<tau> :: complex) \<notin> \<real>"
  shows "Eisenstein_G k \<tau> = gen_lattice.eisenstein_series 1 \<tau> k"
proof -
  interpret std_lattice \<tau>
    by unfold_locales fact+
  show ?thesis
    using infsum_reindex_bij_betw[OF bij_betw_omega_minus_zero, where f = "\<lambda>\<omega>. 1 / \<omega> ^ k"]
          eisenstein_series_summable[of k] assms
    by (simp add: of_\<omega>12_coords_def map_prod_def case_prod_unfold
                  Eisenstein_G_def eisenstein_series_def)
qed

lemma Eisenstein_G_cnj: "Eisenstein_G n (cnj z) = cnj (Eisenstein_G n z)"
  by (simp add: Eisenstein_G_def case_prod_unfold flip: infsum_cnj)

lemma summable_Eisenstein_G:
  assumes "k \<ge> 3" "(\<tau> :: complex) \<notin> \<real>"
  shows   "(\<lambda>(m,n). 1 / (of_int m + of_int n * \<tau>) ^ k) summable_on (-{(0,0)})"
proof -
  interpret std_lattice \<tau>
    by unfold_locales fact+
  show ?thesis
    using summable_on_reindex_bij_betw[OF bij_betw_omega_minus_zero, where f = "\<lambda>\<omega>. 1 / \<omega> ^ k"]
          eisenstein_series_summable[of k] assms
    by (simp add: of_\<omega>12_coords_def map_prod_def case_prod_unfold)
qed

lemma has_sum_Eisenstein_G:
  assumes "k \<ge> 3" "\<tau> \<notin> \<real>"
  shows   "((\<lambda>(m,n). 1 / (of_int m + of_int n * \<tau>) ^ k) has_sum Eisenstein_G k \<tau>) (-{(0,0)})"
  using summable_Eisenstein_G[OF assms] assms by (simp add: Eisenstein_G_def)

lemma Eisenstein_G_odd_eq_0 [simp]:
  assumes "odd k" "k \<noteq> 1"
  shows   "Eisenstein_G k \<tau> = 0"
proof (cases "k = 2")
  case False
  with assms have k: "k \<ge> 3"
    by presburger
  show ?thesis
  proof (cases "\<tau> \<in> \<real>")
    case False
    have [simp]: "(-x - y) ^ k = -((x + y) ^ k)" for x y :: complex
      using \<open>odd k\<close> by (metis more_arith_simps(9) power_minus_odd pth_2)
    have "((\<lambda>(m,n). -(1 / (of_int m + of_int n * \<tau>) ^ k)) has_sum (-Eisenstein_G k \<tau>)) (-{(0,0)})"
      unfolding case_prod_unfold using has_sum_Eisenstein_G[of k \<tau>] k False
      by (subst has_sum_uminus) (auto simp: case_prod_unfold)
    also have "?this \<longleftrightarrow> ((\<lambda>(m,n). 1 / (of_int m + of_int n * \<tau>) ^ k) has_sum (-Eisenstein_G k \<tau>)) (-{(0,0)})"
      by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(m,n). (-m,-n)" "\<lambda>(m,n). (-m,-n)"]) auto
    finally have "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<tau>) ^ k) has_sum -Eisenstein_G k \<tau>) (- {(0, 0)})" .
    moreover have "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<tau>) ^ k) has_sum Eisenstein_G k \<tau>) (- {(0, 0)})"
      using k False by (intro has_sum_Eisenstein_G) auto
    ultimately have "- Eisenstein_G k \<tau> = Eisenstein_G k \<tau>"
      using has_sum_unique by blast
    thus ?thesis
      by simp
  qed (use k in \<open>auto simp: Eisenstein_G_real\<close>)
qed (auto simp: Eisenstein_G_def)

lemma x_over_one_plus_x_mono:
  fixes x y :: real
  assumes xy: "0 < x" "x \<le> y"
  shows "x / (1 + x) \<le> y / (1 + y)"
proof (rule deriv_nonneg_imp_mono[of _ _ "\<lambda>x. x / (1 + x)"])
  fix t assume t: "t \<in> {x..y}"
  thus "((\<lambda>x. x / (1 + x)) has_real_derivative inverse (1 + t) ^ 2) (at t)"
    using xy by (auto intro!: derivative_eq_intros simp: field_simps power2_eq_square)
qed (use xy in auto)

lemma uniform_limit_Eisenstein_G:
  fixes k :: nat and A \<delta> :: real
  assumes "k \<ge> 3"
  assumes "A \<ge> 0" and "\<delta> > 0"
  shows   "uniform_limit {z. abs (Re z) \<le> A \<and> Im z \<ge> \<delta>}
             (\<lambda>X \<tau>. \<Sum>(m,n)\<in>X. 1 / (of_int m + of_int n * \<tau>) ^ k) (Eisenstein_G k)
             (finite_subsets_at_top (-{(0,0)}))"
proof -
  define K where "K = \<delta>\<^sup>2 / (1 + (A + \<delta>)\<^sup>2)"
  have "K > 0"
    using assms by (auto simp: K_def intro!: divide_pos_pos add_pos_nonneg)
  have "K < 1"
    using assms by (auto simp: K_def field_simps add_nonneg_pos add_pos_nonneg power2_eq_square)
  define M where "M = 1 / sqrt K ^ k"
  have "M > 0"
    using \<open>K > 0\<close> by (auto simp: M_def)

  have "uniform_limit {z. abs (Re z) \<le> A \<and> Im z \<ge> \<delta>}
             (\<lambda>X \<tau>. \<Sum>(m,n)\<in>X. 1 / (of_int m + of_int n * \<tau>) ^ k)
             (\<lambda>\<tau>. \<Sum>\<^sub>\<infinity>(m,n)\<in>-{(0,0)}. 1 / (of_int m + of_int n * \<tau>) ^ k)
             (finite_subsets_at_top (-{(0,0)}))"
  proof (rule Weierstrass_m_test_general)
    interpret std_lattice \<i>
      by unfold_locales (auto simp: complex_is_Real_iff)

    have "(\<lambda>\<omega>. 1 / cmod \<omega> ^ k) summable_on omega_minus_zero"
      by (rule eisenstein_series_norm_summable) fact
    also have "?this \<longleftrightarrow> (\<lambda>(m,n). 1 / cmod (of_int m * 1 + of_int n * \<i>) ^ k)
                 summable_on (-{(0,0)})"
      using summable_on_reindex_bij_betw[OF bij_betw_omega_minus_zero, where f = "\<lambda>\<omega>. 1 / norm \<omega> ^ k"]
      by (simp add: of_\<omega>12_coords_def case_prod_unfold)
    finally have "(\<lambda>(m,n). M * norm (1 / (of_int m + of_int n * \<i>) ^ k)) summable_on -{(0, 0)}"
      unfolding case_prod_unfold by (intro summable_on_cmult_right) (simp add: norm_divide norm_power)
    thus "(\<lambda>(m,n). M / norm (of_int m + of_int n * \<i>) ^ k) summable_on -{(0, 0)}"
      by (simp add: norm_divide norm_power)
  next
    fix mn :: "int \<times> int" and \<tau> :: complex
    assume "mn \<in> -{(0, 0)}" and \<tau>: "\<tau> \<in> {z. abs (Re z) \<le> A \<and> Im z \<ge> \<delta>}"
    obtain m n where [simp]: "mn = (m, n)"
      by (cases mn)
    have mn: "m \<noteq> 0 \<or> n \<noteq> 0"
      using \<open>mn \<in> _\<close> by auto
    have nz1: "of_int m + of_int n * \<tau> \<noteq> 0"
      using mn \<tau> \<open>\<delta> > 0\<close> by (auto simp: complex_eq_iff)
    have nz2: "of_int m + of_int n * \<i> \<noteq> 0"
      using mn by (auto simp: complex_eq_iff)

    have "K * norm (of_int m + of_int n * \<i>) ^ 2 \<le> norm (of_int m + of_int n * \<tau>) ^ 2"
    proof (cases "n = 0")
      case [simp]: True
      have "K * of_int m ^ 2 \<le> 1 * of_int m ^ 2"
        using \<open>K < 1\<close> by (intro mult_right_mono) auto
      thus ?thesis by simp
    next
      case False
      define q :: real where "q = of_int m / of_int n"
      have ineq8: "((q + Re \<tau>) ^ 2 + Im \<tau> ^ 2) \<ge> K * (1 + q ^ 2)"
      proof (cases "\<bar>q\<bar> \<le> A + \<delta>")
        case True
        have "(0 + \<delta> ^ 2) / (1 + (A + \<delta>) ^ 2) \<le> ((q + Re \<tau>) ^ 2 + Im \<tau> ^ 2) / (1 + q ^ 2)"
          using True \<open>\<delta> > 0\<close> \<tau>
          by (intro frac_le add_mono)
             (auto simp: add_pos_nonneg simp flip: abs_le_square_iff)
        thus ?thesis
          by (simp add: K_def field_simps add_pos_nonneg add_nonneg_pos)
      next
        case False
        hence "q \<noteq> 0"
          using \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by auto

        from False have "\<bar>Re \<tau> / q\<bar> \<le> \<bar>Re \<tau>\<bar> / (A + \<delta>)"
          unfolding abs_divide using \<tau> \<open>\<delta> > 0\<close> by (intro divide_left_mono) auto
        also have "\<dots> \<le> A / (A + \<delta>)"
          using \<tau> \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by (intro divide_right_mono) auto
        finally have "\<bar>Re \<tau> / q\<bar> \<le> A / (A + \<delta>)" .

        have "\<delta> / (A + \<delta>) = 1 - A / (A + \<delta>)"
          using \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by (simp add: field_simps)
        also have "\<dots> \<le> 1 - \<bar>Re \<tau> / q\<bar>"
          using \<open>\<bar>Re \<tau> / q\<bar> \<le> A / (A + \<delta>)\<close> by (intro diff_left_mono) auto
        also have "\<dots> \<le> \<bar>1 + Re \<tau> / q\<bar>"
          by linarith
        finally have "\<bar>q\<bar> * (\<delta> / (A + \<delta>)) \<le> \<bar>q\<bar> * \<bar>1 + Re \<tau> / q\<bar>"
          using \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by (intro mult_left_mono) auto
        also have "\<dots> = \<bar>q + Re \<tau>\<bar>"
          using \<open>q \<noteq> 0\<close> by (simp flip: abs_mult add: field_simps)
        finally have "(\<bar>q\<bar> * \<delta>) / (A + \<delta>) \<le> \<bar>q + Re \<tau>\<bar>"
          by (simp add: algebra_simps)

        hence "((\<bar>q\<bar> * \<delta>) / (A + \<delta>)) ^ 2 \<le> \<bar>q + Re \<tau>\<bar> ^ 2"
          using \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by (intro power_mono) auto
        hence "q ^ 2 * \<delta> ^ 2 / (A + \<delta>) ^ 2 \<le> (q + Re \<tau>) ^ 2"
          by (simp add: algebra_simps power_divide)
        also have "\<dots> \<le> (q + Re \<tau>) ^ 2 + Im \<tau> ^ 2"
          by simp
        finally have "(q\<^sup>2 * \<delta>\<^sup>2 / (A + \<delta>)\<^sup>2) / (1 + q\<^sup>2) \<le> ((q + Re \<tau>)\<^sup>2 + (Im \<tau>)\<^sup>2) / (1 + q\<^sup>2)"
          by (intro divide_right_mono) auto
        also have "(q\<^sup>2 * \<delta>\<^sup>2 / (A + \<delta>)\<^sup>2) / (1 + q\<^sup>2) = \<delta>\<^sup>2 / (A + \<delta>)\<^sup>2 * (q\<^sup>2 / (1 + q\<^sup>2))"
          by (simp add: algebra_simps)
        finally have ineq9: "\<delta>\<^sup>2 / (A + \<delta>)\<^sup>2 * (q\<^sup>2 / (1 + q\<^sup>2)) \<le> ((q + Re \<tau>)\<^sup>2 + (Im \<tau>)\<^sup>2) / (1 + q\<^sup>2)" .

        
        have "K = \<delta>\<^sup>2 / (A + \<delta>)\<^sup>2 * ((A + \<delta>)\<^sup>2 / (1 + (A + \<delta>)\<^sup>2))"
          using \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close> by (simp add: field_simps K_def)
        also have "\<dots> \<le> \<delta>\<^sup>2 / (A + \<delta>)\<^sup>2 * (q\<^sup>2 / (1 + q\<^sup>2))"
          using False \<open>A \<ge> 0\<close> \<open>\<delta> > 0\<close>
          by (intro mult_left_mono x_over_one_plus_x_mono) (auto simp flip: abs_le_square_iff)
        also have "\<dots> \<le> ((q + Re \<tau>)\<^sup>2 + (Im \<tau>)\<^sup>2) / (1 + q\<^sup>2)"
          by (fact ineq9)
        finally show ?thesis
          by (simp add: field_simps add_nonneg_pos add_pos_nonneg)
      qed

      from ineq8 have "K * (1 + q\<^sup>2) * of_int n ^ 2 \<le> ((q + Re \<tau>)\<^sup>2 + (Im \<tau>)\<^sup>2) * of_int n ^ 2"
        by (intro mult_right_mono) auto
      also have "\<dots> = norm (of_int m + of_int n * \<tau>) ^ 2"
        using \<open>n \<noteq> 0\<close> by (simp add: norm_complex_def q_def field_simps)
      also have "K * (1 + q\<^sup>2) * of_int n ^ 2 = K * norm (of_int m + of_int n * \<i>) ^ 2"
        using \<open>n \<noteq> 0\<close> by (simp add: norm_complex_def q_def field_simps)
      finally show ?thesis .
    qed

    hence "(sqrt K * norm (of_int m + of_int n * \<i>)) ^ 2 \<le> norm (of_int m + of_int n * \<tau>) ^ 2"
      using \<open>K > 0\<close> unfolding power_mult_distrib by simp
    hence "sqrt K * norm (of_int m + of_int n * \<i>) \<le> norm (of_int m + of_int n * \<tau>)"
      by (rule power2_le_imp_le) (use \<open>K > 0\<close> in auto)
    hence "(sqrt K * norm (of_int m + of_int n * \<i>)) ^ k \<le> norm (of_int m + of_int n * \<tau>) ^ k"
      by (rule power_mono) (use \<open>K > 0\<close> in auto)
    hence "norm (of_int m + of_int n * \<i>) ^ k / M \<le> norm (of_int m + of_int n * \<tau>) ^ k"
      using \<open>K > 0\<close> by (simp add: M_def field_simps)
    hence "norm (1 / (of_int m + of_int n * \<tau>) ^ k) \<le> M / norm (of_int m + of_int n * \<i>) ^ k"
      using nz1 nz2 \<open>M > 0\<close> by (simp add: field_simps norm_divide norm_power)
    thus "norm (case mn of (m, n) \<Rightarrow> 1 / (of_int m + of_int n * \<tau>) ^ k)
           \<le> (case mn of (m, n) \<Rightarrow> M / cmod (of_int m + of_int n * \<i>) ^ k)"
      by (simp add: field_simps)
  qed
  also have "?this \<longleftrightarrow> ?thesis"
    using \<open>\<delta> > 0\<close> \<open>k \<ge> 3\<close>
    by (intro uniform_limit_cong) (auto simp: Eisenstein_G_def complex_is_Real_iff)
  finally show ?thesis .
qed


text \<open>Theorem 1.15 \<close>

theorem Eisenstein_G_analytic_aux: "Eisenstein_G k analytic_on {z. Im z > 0}"
proof (cases "k \<ge> 3")
  case True
  have "Eisenstein_G k analytic_on {z}" if "Im z > 0" for z
  proof -
    define A \<delta> where "A = \<bar>Re z\<bar> + 1" and "\<delta> = \<bar>Im z\<bar> / 2"
    define h where "h = (\<lambda>z m n. of_int m + of_int n * z :: complex)"
    define f where "f = (\<lambda>X (z::complex). \<Sum>(m,n)\<in>X. 1 / h z m n ^ k)"
    define F where "F = finite_subsets_at_top (-{(0 :: int, 0 :: int)})"
    define strip where "strip = {w. \<bar>Re w\<bar> \<le> A \<and> Im w \<ge> \<delta>}"
    define strip' where "strip' = Re -` {-A<..<A} \<inter> Im -` {\<delta><..}"
    have [continuous_intros]: "continuous_on A (\<lambda>z. h z m n)" for m n A
      by (auto intro!: continuous_intros simp: h_def)
    have [holomorphic_intros]: "(\<lambda>z. h z m n) holomorphic_on A" for m n A
      by (auto intro!: holomorphic_intros simp: h_def)

    have "open strip'"
      unfolding strip'_def by (intro open_Int open_vimage) (auto intro!: continuous_intros)
    moreover have "z \<in> strip'"
      using \<open>Im z > 0\<close> by (auto simp: strip'_def A_def \<delta>_def)
    ultimately obtain r where r: "r > 0" "cball z r \<subseteq> strip'"
      using open_contains_cball by blast

    have h_eq_0_iff: "h w m n = 0 \<longleftrightarrow> m = 0 \<and> n = 0" if "w \<in> cball z r" for w m n
    proof -
      from that have "w \<in> strip'"
        using r by auto
      hence "Im w > 0"
        using \<open>Im z > 0\<close> by (auto simp: strip'_def \<delta>_def)
      then interpret std_lattice w
        using that by unfold_locales (auto simp: complex_is_Real_iff)
      show ?thesis unfolding h_def
        using of_\<omega>12_coords_eq_0_iff[of "(m, n)"] by (simp add: of_\<omega>12_coords_def prod_eq_iff)
    qed

    have "eventually (\<lambda>X. X \<subseteq> -{(0,0)}) F"
      unfolding F_def by blast
    hence 1: "\<forall>\<^sub>F n in F. continuous_on (cball z r) (f n) \<and> f n holomorphic_on ball z r"
      by eventually_elim
         (use r in \<open>auto simp: f_def strip'_def h_eq_0_iff
                         intro!: continuous_intros holomorphic_intros\<close>)
    have 2: "uniform_limit (cball z r) f (Eisenstein_G k) F"
    proof (rule uniform_limit_on_subset)
      show "uniform_limit strip f (Eisenstein_G k) F"
        unfolding strip_def f_def F_def h_def
        by (rule uniform_limit_Eisenstein_G) (use \<open>Im z > 0\<close> \<open>k \<ge> 3\<close> in \<open>auto simp: A_def \<delta>_def\<close>)
    next
      have "cball z r \<subseteq> strip'"
        by fact
      also have "strip' \<subseteq> strip"
        by (auto simp: strip_def strip'_def)
      finally show "cball z r \<subseteq> strip" .
    qed
    have 3: "F \<noteq> bot"
      by (auto simp: F_def)

    have "Eisenstein_G k holomorphic_on ball z r"
      using holomorphic_uniform_limit[OF 1 2 3] by blast
    thus ?thesis
      using \<open>r > 0\<close> analytic_at_ball by blast
  qed
  thus ?thesis
    by (subst analytic_on_analytic_at) auto
next
  case False
  thus ?thesis
    by (cases "k = 0") (auto simp: Eisenstein_G_def [abs_def])
qed

lemma Eisenstein_G_analytic: "Eisenstein_G n analytic_on -\<real>"
proof -
  have "cnj ` {\<tau>. Im \<tau> < 0} = {\<tau>. Im \<tau> > 0}"
    by (auto simp: in_image_cnj_iff)
  hence "(cnj \<circ> Eisenstein_G n \<circ> cnj) holomorphic_on {\<tau>. Im \<tau> < 0}"
    using Eisenstein_G_analytic_aux[of n]
    by (intro holomorphic_on_compose_cnj_cnj)
       (auto simp: open_halfspace_Im_lt open_halfspace_Im_gt analytic_on_open)
  also have "cnj \<circ> Eisenstein_G n \<circ> cnj = Eisenstein_G n"
    by (auto simp: fun_eq_iff Eisenstein_G_cnj)
  finally have "Eisenstein_G n analytic_on {\<tau>. Im \<tau> < 0}"
    by (simp add: analytic_on_open open_halfspace_Im_lt)
  hence "Eisenstein_G n analytic_on {\<tau>. Im \<tau> < 0} \<union> {\<tau>. Im \<tau> > 0}"
    using Eisenstein_G_analytic_aux analytic_on_Un by blast
  also have "{\<tau>. Im \<tau> < 0} \<union> {\<tau>. Im \<tau> > 0} = -\<real>"
    by (auto simp: complex_is_Real_iff)
  finally show ?thesis .
qed

lemma Eisenstein_G_analytic' [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_G k (f z)) analytic_on A"
proof -
  have "Eisenstein_G k \<circ> f analytic_on A"
    by (intro analytic_on_compose assms analytic_on_subset[OF Eisenstein_G_analytic])
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma Eisenstein_G_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_G k (f z)) holomorphic_on A"
proof -
  have "Eisenstein_G k \<circ> f holomorphic_on A"
    by (intro holomorphic_on_compose assms
              holomorphic_on_subset[OF analytic_imp_holomorphic[OF Eisenstein_G_analytic]])
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma Eisenstein_G_meromorphic [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_G k (f z)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma Eisenstein_G_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. Eisenstein_G k (f z))"
proof -
  have "continuous_on A (Eisenstein_G k \<circ> f)"
    by (intro continuous_on_compose[OF assms(1)] holomorphic_on_imp_continuous_on holomorphic_intros)
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma eisenstein_series_conv_Eisenstein_G_aux:
  assumes "Im (\<omega>2 / \<omega>1) \<noteq> 0" "n \<ge> 3"
  shows   "gen_lattice.eisenstein_series \<omega>1 \<omega>2 n = \<omega>1 powi (-n) * Eisenstein_G n (\<omega>2 / \<omega>1)"
proof -
  interpret gen_lattice_stretch 1 "\<omega>2 / \<omega>1" "\<omega>1"
    by unfold_locales (use assms in auto)
  have "stretched.eisenstein_series n = \<omega>1 powi (-n) * eisenstein_series n"
    by (rule eisenstein_series_stretch)
  also have "eisenstein_series n = Eisenstein_G n (\<omega>2 / \<omega>1)"
    using assms by (intro Eisenstein_G_altdef [symmetric]) (auto simp: complex_is_Real_iff)
  also have "stretched.eisenstein_series n = gen_lattice.eisenstein_series \<omega>1 \<omega>2 n"
    using assms by auto
  finally show ?thesis .
qed

lemma (in gen_lattice) eisenstein_series_conv_Eisenstein_G:
  "eisenstein_series n = \<omega>1 powi (-n) * Eisenstein_G n (\<omega>2 / \<omega>1)"
proof (cases "n \<ge> 3")
  case True
  thus ?thesis using eisenstein_series_conv_Eisenstein_G_aux[OF ratio_notin_real, of n]
    by simp
qed (auto simp: eisenstein_series_def Eisenstein_G_def)

lemma (in gen_lattice) Eisenstein_G_conv_eisenstein_series:
   "Eisenstein_G n (\<omega>2 / \<omega>1) = \<omega>1 ^ n * eisenstein_series n"
  using eisenstein_series_conv_Eisenstein_G[of n]
  by (auto simp: power_int_minus divide_simps mult_ac split: if_splits)

lemma Eisenstein_G_odd [simp]:
  assumes "odd k"
  shows   "Eisenstein_G k = (\<lambda>_. 0)"
proof
  fix \<tau> :: complex
  show "Eisenstein_G k \<tau> = 0"
  proof (cases "Im \<tau> = 0")
    case True
    thus ?thesis
      using assms by (auto simp: Eisenstein_G_def complex_is_Real_iff intro!: Nat.gr0I)
  next
    case False
    interpret gen_lattice 1 \<tau>
      by standard (use False in auto)
    have "Eisenstein_G k \<tau> = eisenstein_series k"
      using Eisenstein_G_conv_eisenstein_series[of k] by simp
    also have "\<dots> = 0"
      using assms by (simp add: eisenstein_series_odd_eq_0)
    finally show ?thesis .
  qed
qed

interpretation Eisenstein_G: periodic_fun_simple' "Eisenstein_G k"
proof
  fix \<tau> :: complex
  show "Eisenstein_G k (\<tau> + 1) = Eisenstein_G k \<tau>"
  proof (cases "\<tau> \<in> \<real>")
    case False
    interpret std_lattice \<tau> by unfold_locales fact
    interpret unimodular_transform_lattice 1 \<tau> 1 1 0 1
      by unfold_locales auto
    have "Eisenstein_G k (\<tau> + 1) = Eisenstein_G k (\<omega>2' / \<omega>1')"
      by (simp add: \<omega>2'_def \<omega>1'_def)
    also have "\<dots> = transformed.eisenstein_series k"
      by (subst transformed.eisenstein_series_conv_Eisenstein_G) (auto simp: \<omega>1'_def)
    also have "\<dots> = eisenstein_series k"
      by simp
    also have "\<dots> = Eisenstein_G k \<tau>"
      by (subst eisenstein_series_conv_Eisenstein_G) auto
    finally show ?thesis .
  qed (auto simp: Eisenstein_G_def)
qed


subsection \<open>A recurrence for Eisenstein's $G$ function\<close>

lemma Eisenstein_G_reduce_aux:
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * complex_of_nat n + 1) * (complex_of_nat n - 3) * (2 * complex_of_nat n - 1)"
  shows "Eisenstein_G (2*n) z = 3 / C * (\<Sum>i=1..n-3. complex_of_nat (2 * i + 1) * Eisenstein_G (2 * i + 2) z *
                               (complex_of_nat (2 * n - 2 * i - 3) * Eisenstein_G (2 * n - 2 * i - 2) z))"
    (is "?lhs z = ?rhs z")
proof (cases "z \<in> \<real>")
  case False
  interpret std_lattice z
    by standard (use False in auto)
  have [simp]: "Eisenstein_G n z = eisenstein_series n" for n
    using Eisenstein_G_conv_eisenstein_series[of n] by simp
  show ?thesis
    using eisenstein_series_reduce_aux[OF assms(1)] unfolding C_def by simp
qed (use assms in \<open>auto simp: Eisenstein_G_real\<close>)

lemma Eisenstein_G_reduce_Bit0 [eisenstein_series_reduce]:
  fixes n' :: num and z :: complex
  defines "n \<equiv> numeral n'"
  assumes "n \<ge> 4"
  defines "C \<equiv> (2 * complex_of_nat n + 1) * (complex_of_nat n - 3) * (2 * complex_of_nat n - 1)"
  defines "G \<equiv> (\<lambda>n. Eisenstein_G n z)"
  shows "G (numeral (num.Bit0 n')) = 
           3 / C * (\<Sum>i=1..n-3. complex_of_nat (2 * i + 1) * G (2 * i + 2) *
                               (complex_of_nat (2 * n - 2 * i - 3) * G (2 * n - 2 * i - 2)))"
proof -
  have *: "numeral (num.Bit0 n') = 2 * n"
    by (simp add: n_def)
  show ?thesis
    unfolding * C_def G_def
    by (rule Eisenstein_G_reduce_aux) (use assms in auto)
qed

lemma Eisenstein_G_reduce_Bit1 [simp]: "Eisenstein_G (numeral (num.Bit1 n)) z = 0"
  by (rule Eisenstein_G_odd_eq_0) auto

context
  fixes z :: complex and G
  defines "G \<equiv> (\<lambda>n. Eisenstein_G n z)"
begin

lemma G8_eq: "G 8 = 3 / 7 * G 4 ^ 2"
  unfolding G_def by eisenstein_series_reduce

lemma G10_eq: "G 10 = 5 / 11 * G 4 * G 6"
  unfolding G_def by eisenstein_series_reduce

lemma G12_eq: "G 12 = 18 / 143 * G 4 ^ 3 + 25 / 143 * G 6 ^ 2"
  unfolding G_def by eisenstein_series_reduce

lemma G14_eq: "G 14 = 30 / 143 * G 4 ^ 2 * G 6"
  unfolding G_def by eisenstein_series_reduce

lemma G16_eq: "G 16 = 27225 / 668525 * G 4 ^ 4 + 300 / 2431 * G 4 * G 6 ^ 2"
  unfolding G_def by eisenstein_series_reduce

lemma G18_eq: "G 18 = 3915 / 46189 * G 4 ^ 3 * G 6 + 2750 / 92378 * G 6 ^ 3"
  unfolding G_def by eisenstein_series_reduce

end



section \<open>The invariants \<open>g\<^sub>2\<close> and \<open>g\<^sub>3\<close>\<close>

definition Eisenstein_g2 :: "complex \<Rightarrow> complex"
  where "Eisenstein_g2 = (\<lambda>\<tau>. 60 * Eisenstein_G 4 \<tau>)"

lemma Eisenstein_g2_real [simp]: "\<tau> \<in> \<real> \<Longrightarrow> Eisenstein_g2 \<tau> = 0"
  by (simp add: Eisenstein_g2_def)

lemma Eisenstein_g2_cnj: "Eisenstein_g2 (cnj z) = cnj (Eisenstein_g2 z)"
  by (simp add: Eisenstein_g2_def Eisenstein_G_cnj)

lemma Eisenstein_g2_analytic [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g2 (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: Eisenstein_g2_def)

lemma Eisenstein_g2_holomorphic [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g2 (f z)) holomorphic_on A"
  using assms(2) by (auto intro!: holomorphic_intros simp: Eisenstein_g2_def)

lemma meromorphic_on_Eisenstein_g2 [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g2 (f z)) meromorphic_on A"
  using assms unfolding Eisenstein_g2_def by (auto intro!: meromorphic_intros)

lemma Eisenstein_g2_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. Eisenstein_g2 (f z))"
  using assms(2) by (auto intro!: continuous_intros simp: Eisenstein_g2_def)

interpretation Eisenstein_g2: periodic_fun_simple' "Eisenstein_g2"
  by standard (simp_all add: Eisenstein_g2_def Eisenstein_G.plus_1)

lemma (in gen_lattice) invariant_g2_conv_Eisenstein_g2:
  "invariant_g2 = Eisenstein_g2 (\<omega>2 / \<omega>1) / \<omega>1 ^ 4"
  by (simp add: invariant_g2_def eisenstein_series_conv_Eisenstein_G Eisenstein_g2_def
                power_int_minus field_simps)


definition Eisenstein_g3 :: "complex \<Rightarrow> complex"
  where "Eisenstein_g3 = (\<lambda>\<tau>. 140 * Eisenstein_G 6 \<tau>)"

lemma Eisenstein_g3_real [simp]: "\<tau> \<in> \<real> \<Longrightarrow> Eisenstein_g3 \<tau> = 0"
  by (simp add: Eisenstein_g3_def)

lemma Eisenstein_g3_cnj: "Eisenstein_g3 (cnj z) = cnj (Eisenstein_g3 z)"
  by (simp add: Eisenstein_g3_def Eisenstein_G_cnj)

lemma Eisenstein_g3_analytic [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g3 (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: Eisenstein_g3_def)

lemma Eisenstein_g3_holomorphic [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g3 (f z)) holomorphic_on A"
  using assms(2) by (auto intro!: holomorphic_intros simp: Eisenstein_g3_def)

lemma meromorphic_on_Eisenstein_g3 [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Eisenstein_g3 (f z)) meromorphic_on A"
  using assms unfolding Eisenstein_g3_def by (auto intro!: meromorphic_intros)

lemma Eisenstein_g3_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. Eisenstein_g3 (f z))"
  using assms(2) by (auto intro!: continuous_intros simp: Eisenstein_g3_def)

interpretation Eisenstein_g3: periodic_fun_simple' "Eisenstein_g3"
  by standard (simp_all add: Eisenstein_g3_def Eisenstein_G.plus_1)

lemma (in gen_lattice) invariant_g3_conv_Eisenstein_g3:
  "invariant_g3 = Eisenstein_g3 (\<omega>2 / \<omega>1) / \<omega>1 ^ 6"
  by (simp add: invariant_g3_def eisenstein_series_conv_Eisenstein_G Eisenstein_g3_def
                power_int_minus field_simps)


section \<open>The discriminant \<open>\<Delta>\<close>\<close>

definition modular_discr :: "complex \<Rightarrow> complex"
  where "modular_discr = (\<lambda>\<tau>. Eisenstein_g2 \<tau> ^ 3 - 27 * Eisenstein_g3 \<tau> ^ 2)"

lemma modular_discr_real [simp]: "\<tau> \<in> \<real> \<Longrightarrow> modular_discr \<tau> = 0"
  by (simp add: modular_discr_def)

lemma modular_discr_cnj: "modular_discr (cnj z) = cnj (modular_discr z)"
  by (simp add: modular_discr_def Eisenstein_g2_cnj Eisenstein_g3_cnj)

lemma modular_discr_analytic [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. modular_discr (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: modular_discr_def)

lemma meromorphic_on_modular_discr [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. modular_discr (f z)) meromorphic_on A"
  using assms unfolding modular_discr_def by (auto intro!: meromorphic_intros)

lemma modular_discr_holomorphic [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. modular_discr (f z)) holomorphic_on A"
  using assms(2) by (auto intro!: holomorphic_intros simp: modular_discr_def)

lemma modular_discr_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. modular_discr (f z))"
  using assms(2) by (auto intro!: continuous_intros simp: modular_discr_def)

lemma modular_discr_nonzero [simp]:
  assumes "\<tau> \<notin> \<real>"
  shows   "modular_discr \<tau> \<noteq> 0"
proof -
  interpret std_lattice \<tau>
    using assms by unfold_locales auto
  from discr_nonzero and assms show ?thesis
    by (simp add: modular_discr_def Eisenstein_g2_def Eisenstein_g3_def Eisenstein_G_def
                  invariant_g2_def invariant_g3_def eisenstein_series_altdef)
qed

lemma (in gen_lattice) modular_discr:
  "modular_discr (\<omega>2 / \<omega>1) = \<omega>1 ^ 12 * (invariant_g2 ^ 3 - 27 * invariant_g3 ^ 2)"
proof -
  interpret gen_lattice_swap ..
  have "modular_discr (\<omega>2 / \<omega>1) =
          Eisenstein_G 4 (\<omega>2 / \<omega>1) ^ 3 * 216000 - (Eisenstein_G 6 (\<omega>2 / \<omega>1))\<^sup>2 * 529200"
    unfolding modular_discr_def Eisenstein_g2_def Eisenstein_g3_def
    by (auto simp: algebra_simps)
  also have "\<dots> = \<omega>1 ^ 12 * (invariant_g2 ^ 3 - 27 * invariant_g3 ^ 2)"
    by (simp add: Eisenstein_G_conv_eisenstein_series invariant_g2_def invariant_g3_def algebra_simps)
  finally show ?thesis .
qed

interpretation modular_discr: periodic_fun_simple' "modular_discr"
  by standard (simp_all add: modular_discr_def Eisenstein_g2.plus_1 Eisenstein_g3.plus_1)


section \<open>Klein's \<open>J\<close> function\<close>

definition Klein_J :: "complex \<Rightarrow> complex"
  where "Klein_J \<tau> = Eisenstein_g2 \<tau> ^ 3 / modular_discr \<tau>"

lemma Klein_J_real [simp]: "\<tau> \<in> \<real> \<Longrightarrow> Klein_J \<tau> = 0"
  by (simp add: Klein_J_def)

lemma Klein_J_cnj: "Klein_J (cnj z) = cnj (Klein_J z)"
  by (simp add: Klein_J_def Eisenstein_g2_cnj modular_discr_cnj)

lemma Klein_J_analytic [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_J (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: Klein_J_def)

lemma Klein_J_holomorphic [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_J (f z)) holomorphic_on A"
  using assms(2) by (auto intro!: holomorphic_intros simp: Klein_J_def)

lemma Klein_J_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. Klein_J (f z))"
  using assms(2) by (auto intro!: continuous_intros simp: Klein_J_def)

lemma meromorphic_on_Klein_J [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_J (f z)) meromorphic_on A"
  using assms unfolding Klein_J_def by (auto intro!: meromorphic_intros)

lemma no_pole_Klein_J [simp]: "z \<notin> \<real> \<Longrightarrow> \<not>is_pole Klein_J z"
  by (intro analytic_at_imp_no_pole analytic_intros) auto

lemma no_pole_Klein_J' [simp]: "Im z > 0 \<Longrightarrow> \<not>is_pole Klein_J z"
  by (intro analytic_at_imp_no_pole analytic_intros) (auto simp: complex_is_Real_iff)

lemma (in gen_lattice) Klein_J:
  "Klein_J (\<omega>2 / \<omega>1) = invariant_g2 ^ 3 / (invariant_g2 ^ 3 - 27 * invariant_g3 ^ 2)"
  unfolding Klein_J_def modular_discr Eisenstein_g2_def Eisenstein_G_conv_eisenstein_series
  using discr_nonzero ratio_notin_real
  by (simp add: field_simps invariant_g2_def invariant_g3_def)

text \<open>Theorem 1.16\<close>
theorem (in unimodular_transform) Klein_J_transform: "Klein_J (\<phi> \<tau>) = Klein_J \<tau>"
proof (cases "\<tau> \<in> \<real>")
  case False
  interpret std_lattice \<tau>
    using False by unfold_locales (auto simp: complex_is_Real_iff)
  interpret unimodular_transform_lattice 1 \<tau> a b c d ..
  have "Klein_J (\<phi> \<tau>) = Klein_J (\<omega>2' / \<omega>1')"
    by (simp add: \<omega>2'_def \<omega>1'_def \<phi>_def moebius_def)
  also have "\<dots> = Klein_J (\<tau> / 1)"
    unfolding \<phi>_def moebius_def unfolding Klein_J transformed.Klein_J by simp
  finally show ?thesis by simp
qed (auto simp: Im_transform_zero_iff Klein_J_def)

interpretation Klein_J: periodic_fun_simple' Klein_J
proof
  fix \<tau> :: complex
  interpret unimodular_transform 1 1 0 1
    by unfold_locales auto
  show "Klein_J (\<tau> + 1) = Klein_J \<tau>"
    using Klein_J_transform by (simp add: \<phi>_def moebius_def)
qed

lemma Klein_J_neg_inverse: "Klein_J (-(1 / \<tau>)) = Klein_J \<tau>"
proof -
  interpret unimodular_transform 0 "-1" 1 0
    by unfold_locales auto
  show "Klein_J (-(1 / \<tau>)) = Klein_J \<tau>"
    using Klein_J_transform by (simp add: \<phi>_def moebius_def)
qed


section \<open>Klein's \<open>j\<close> function\<close>

definition Klein_j :: "complex \<Rightarrow> complex" where
  "Klein_j z = 12 ^ 3 * Klein_J z"

lemma Klein_J_conv_Klein_j: "Klein_J z = Klein_j z / 12 ^ 3"
  by (simp add: Klein_j_def)

lemma Klein_j_real [simp]: "\<tau> \<in> \<real> \<Longrightarrow> Klein_j \<tau> = 0"
  by (simp add: Klein_j_def)

lemma Klein_j_cnj: "Klein_j (cnj z) = cnj (Klein_j z)"
  by (simp add: Klein_j_def Klein_J_cnj)

lemma Klein_j_analytic [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_j (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: Klein_j_def)

lemma Klein_j_holomorphic [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "(\<lambda>z. Klein_j (f z)) holomorphic_on A"
  using assms(2) by (auto intro!: holomorphic_intros simp: Klein_j_def)

lemma Klein_j_continuous_on [continuous_intros]:
  assumes [continuous_intros]: "continuous_on A f" and "\<And>z. z \<in> A \<Longrightarrow> f z \<notin> \<real>"
  shows   "continuous_on A (\<lambda>z. Klein_j (f z))"
  using assms(2) by (auto intro!: continuous_intros simp: Klein_j_def)

lemma no_pole_Klein_j [simp]: "z \<notin> \<real> \<Longrightarrow> \<not>is_pole Klein_j z"
  by (intro analytic_at_imp_no_pole analytic_intros) auto

lemma no_pole_Klein_j' [simp]: "Im z > 0 \<Longrightarrow> \<not>is_pole Klein_j z"
  by (intro analytic_at_imp_no_pole analytic_intros) (auto simp: complex_is_Real_iff)

theorem (in unimodular_transform) Klein_j_transform: "Klein_j (\<phi> \<tau>) = Klein_j \<tau>"
  by (simp add: Klein_j_def Klein_J_transform)

interpretation Klein_j: periodic_fun_simple' Klein_j
proof
  fix \<tau> :: complex
  show "Klein_j (\<tau> + 1) = Klein_j \<tau>"
    by (simp add: Klein_j_def Klein_J.plus_1)
qed

lemma Klein_j_neg_inverse: "Klein_j (-(1 / \<tau>)) = Klein_j \<tau>"
  by (simp add: Klein_j_def Klein_J_neg_inverse)


subsection \<open>Special values of Klein's \<open>J\<close> function and related functions\<close>

text \<open>Theorem 2.7 (values only)\<close>

lemma Eisenstein_G_4_rho [simp]: "Eisenstein_G 4 \<^bold>\<rho> = 0"
proof -
  have *: "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4) has_sum Eisenstein_G 4 \<^bold>\<rho>) (- {(0, 0)})"
    by (rule has_sum_Eisenstein_G) auto
  also have "(\<lambda>(m, n). 1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4) =
             (\<lambda>(m, n). (1 / \<^bold>\<rho>) * (1 / (of_int (n - m) - of_int m * \<^bold>\<rho>) ^ 4))"
  proof (intro ext, clarify)
    fix m n :: int
    have "of_int m + of_int n * \<^bold>\<rho> = of_int m * \<^bold>\<rho> ^ 3 + of_int n * \<^bold>\<rho>"
      by simp
    also have "\<dots> = \<^bold>\<rho> * (of_int m * \<^bold>\<rho> ^ 2 + of_int n)"
      by (simp add: power2_eq_square power3_eq_cube algebra_simps)
    also have "\<dots> ^ 4 = \<^bold>\<rho> ^ 4 * (of_int m * \<^bold>\<rho> ^ 2 + of_int n) ^ 4"
      by (rule power_mult_distrib)
    also have "\<^bold>\<rho> ^ 4 = \<^bold>\<rho>"
      by simp
    also have "of_int m * \<^bold>\<rho> ^ 2 + of_int n = (of_int (n - m) - of_int m * \<^bold>\<rho>)"
      by (subst modfun_rho_square) (auto simp: algebra_simps)
    finally show "1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4 =
                    (1 / \<^bold>\<rho>) * (1 / (of_int (n - m) - of_int m * \<^bold>\<rho>) ^ 4)"
      by simp
  qed
  finally have "(((\<lambda>(m, n). 1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4) \<circ> (\<lambda>(m,n). (n - m, -m))) has_sum
                   Eisenstein_G 4 \<^bold>\<rho> * \<^bold>\<rho>) (- {(0, 0)})"
    unfolding case_prod_unfold o_def
    by (subst (asm) has_sum_cmult_right_iff) (auto simp: algebra_simps)
  also have "?this \<longleftrightarrow> ((\<lambda>(m, n). 1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4) has_sum
                   Eisenstein_G 4 \<^bold>\<rho> * \<^bold>\<rho>) (- {(0, 0)})"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(m,n). (-n, m - n)" "\<lambda>(m,n). (n - m, -m)"]) auto
  finally have "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<^bold>\<rho>) ^ 4) has_sum
                  Eisenstein_G 4 \<^bold>\<rho> * \<^bold>\<rho>) (- {(0, 0)})" .
  from this and * have "Eisenstein_G 4 \<^bold>\<rho> * \<^bold>\<rho> = Eisenstein_G 4 \<^bold>\<rho>"
    by (rule has_sum_unique)
  thus ?thesis
    by simp
qed

lemma Eisenstein_g2_rho [simp]: "Eisenstein_g2 \<^bold>\<rho> = 0"
  by (simp add: Eisenstein_g2_def)

lemma Eisenstein_G_6_i [simp]: "Eisenstein_G 6 \<i> = 0"
proof -
  have *: "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<i>) ^ 6) has_sum Eisenstein_G 6 \<i>) (- {(0, 0)})"
    by (rule has_sum_Eisenstein_G) (auto simp: complex_is_Real_iff)
  also have "(\<lambda>(m, n). 1 / (of_int m + of_int n * \<i>) ^ 6) =
             (\<lambda>(m, n). -(1 / (-of_int m * \<i> + of_int n) ^ 6))"
  proof (intro ext, clarify)
    fix m n :: int
    have "of_int m + of_int n * \<i> = \<i> * (-of_int m * \<i> + of_int n)"
      by (simp add: algebra_simps)
    also have "\<dots> ^ 6 = \<i> ^ 6 * (-of_int m * \<i> + of_int n) ^ 6"
      by (rule power_mult_distrib)
    also have "\<i> ^ 6 = -1"
      by simp
    finally show "1 / (of_int m + of_int n * \<i>) ^ 6 =
                    -(1 / (-of_int m * \<i> + of_int n) ^ 6)"
      by simp
  qed
  finally have "(((\<lambda>(m, n). 1 / (of_int m + of_int n * \<i>) ^ 6) \<circ> (\<lambda>(m,n). (n, -m))) has_sum
                   -Eisenstein_G 6 \<i>) (- {(0, 0)})"
    unfolding case_prod_unfold o_def
    by (subst (asm) has_sum_uminus) (auto simp: algebra_simps)
  also have "?this \<longleftrightarrow> ((\<lambda>(m, n). 1 / (of_int m + of_int n * \<i>) ^ 6) has_sum
                   -Eisenstein_G 6 \<i>) (- {(0, 0)})"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>(m,n). (-n, m)" "\<lambda>(m,n). (n, -m)"]) auto
  finally have "((\<lambda>(m, n). 1 / (of_int m + of_int n * \<i>) ^ 6) has_sum
                  -Eisenstein_G 6 \<i>) (- {(0, 0)})" .
  from this and * have "-Eisenstein_G 6 \<i> = Eisenstein_G 6 \<i>"
    by (rule has_sum_unique)
  thus ?thesis
    by simp
qed

lemma Eisenstein_g3_i [simp]: "Eisenstein_g3 \<i> = 0"
  by (simp add: Eisenstein_g3_def)

lemma Klein_J_rho [simp]: "Klein_J \<^bold>\<rho> = 0"
  by (simp add: Klein_J_def)

lemma Klein_j_rho [simp]: "Klein_j \<^bold>\<rho> = 0"
  by (simp add: Klein_j_def)

lemma Klein_J_i [simp]: "Klein_J \<i> = 1"
  using modular_discr_nonzero[of \<i>]
  by (simp add: Klein_J_def modular_discr_def complex_is_Real_iff)

lemma Klein_j_i [simp]: "Klein_j \<i> = 12 ^ 3"
  by (simp add: Klein_j_def)

lemma Eisenstein_g3_rho_nonzero: "Eisenstein_g3 \<^bold>\<rho> \<noteq> 0"
proof -
  have "modular_discr \<^bold>\<rho> \<noteq> 0"
    by (rule modular_discr_nonzero) auto
  thus ?thesis
    by (auto simp: modular_discr_def)
qed

lemma Eisenstein_g2_i_nonzero: "Eisenstein_g2 \<i> \<noteq> 0"
proof -
  have "modular_discr \<i> \<noteq> 0"
    by (rule modular_discr_nonzero) auto
  thus ?thesis
    by (auto simp: modular_discr_def)
qed

end