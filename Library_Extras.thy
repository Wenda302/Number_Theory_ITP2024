theory Library_Extras
  imports "HOL-Number_Theory.Number_Theory" "HOL-Complex_Analysis.Riemann_Mapping"
"HOL-Library.Landau_Symbols" "HOL-Complex_Analysis.Complex_Singularities"
begin

(* BEGIN big block of material from Manuel's private library; to be transferred to the distribution*)
lemmas [derivative_intros del] = DERIV_power_int

lemma DERIV_power_int [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative d) (at x within s)"
  and "n \<ge> 0 \<or> f x \<noteq> 0"
  shows   "((\<lambda>x. power_int (f x) n) has_field_derivative
             (of_int n * power_int (f x) (n - 1) * d)) (at x within s)"
proof (cases n rule: int_cases4)
  case (nonneg n)
  thus ?thesis 
    by (cases "n = 0"; cases "f x = 0")
       (auto intro!: derivative_eq_intros simp: field_simps power_int_diff 
                     power_diff power_int_0_left_If)
next
  case (neg n)
  thus ?thesis using assms(2)
    by (auto intro!: derivative_eq_intros simp: field_simps power_int_diff power_int_minus
             simp flip: power_Suc power_Suc2 power_add)
qed

lemma has_prod_imp_tendsto:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "f has_prod P"
  shows   "(\<lambda>n. \<Prod>k\<le>n. f k) \<longlonglongrightarrow> P"
proof -
  from assms have "convergent_prod f" "prodinf f = P"
    by (auto simp: has_prod_iff)
  thus ?thesis
    using convergent_prod_LIMSEQ by blast
qed

lemma has_prod_imp_tendsto':
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "f has_prod P"
  shows   "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
proof -
  have "(\<lambda>n. \<Prod>k<Suc n. f k) \<longlonglongrightarrow> P"
    using has_prod_imp_tendsto[OF assms] by (subst lessThan_Suc_atMost)
  thus ?thesis
    using filterlim_sequentially_Suc by blast
qed

lemma root_powr_inverse':
  assumes "n > 0" "x \<ge> 0"
  shows   "root n x = x powr (1 / real n)"
  by (rule real_root_pos_unique) (use assms in \<open>auto simp: powr_powr simp flip: powr_realpow'\<close>)

lemma root_test_convergence':
  fixes g :: "nat \<Rightarrow> 'a :: {banach}"
  assumes "(\<lambda>n. norm (g n) powr (1 / real n)) \<longlonglongrightarrow> c" "c < 1"
  shows   "summable g"
proof (rule root_test_convergence)
  have "eventually (\<lambda>n. norm (g n) powr (1 / real n) = root n (norm (g n))) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim (auto simp: root_powr_inverse')
  from Lim_transform_eventually[OF assms(1) this] show "(\<lambda>n. root n (norm (g n))) \<longlonglongrightarrow> c" .
qed fact

lemma prod_diff:
  fixes f :: "'a \<Rightarrow> 'b :: field"
  assumes "finite A" "B \<subseteq> A" "\<And>x. x \<in> B \<Longrightarrow> f x \<noteq> 0"
  shows   "prod f (A - B) = prod f A / prod f B"
proof -
  from assms have [intro, simp]: "finite B"
    using finite_subset by blast
  have "prod f A = prod f ((A - B) \<union> B)"
    using assms by (intro prod.cong) auto
  also have "\<dots> = prod f (A - B) * prod f B"
    using assms by (subst prod.union_disjoint) (auto intro: finite_subset)
  also have "\<dots> / prod f B = prod f (A - B)"
    using assms by simp
  finally show ?thesis ..
qed

lemma summable_norm_add:
  assumes "summable (\<lambda>n. norm (f n))" "summable (\<lambda>n. norm (g n))"
  shows   "summable (\<lambda>n. norm (f n + g n))"
proof (rule summable_comparison_test)
  show "summable (\<lambda>n. norm (f n) + norm (g n))"
    by (intro summable_add assms)
  show "\<exists>N. \<forall>n\<ge>N. norm (norm (f n + g n)) \<le> norm (f n) + norm (g n)"
    by (intro exI[of _ 0] allI impI) (auto simp: norm_triangle_ineq)
qed

lemma summable_norm_diff:
  assumes "summable (\<lambda>n. norm (f n))" "summable (\<lambda>n. norm (g n))"
  shows   "summable (\<lambda>n. norm (f n - g n))"
  using summable_norm_add[of f "\<lambda>n. -g n"] assms by simp

(* Note: this is more general than the version in the library *)
proposition swap_uniform_limit':
  assumes f: "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> g n) G"
  assumes g: "(g \<longlongrightarrow> l) F"
  assumes uc: "uniform_limit S f h F"
  assumes ev: "\<forall>\<^sub>F x in G. x \<in> S"
  assumes "\<not>trivial_limit F"
  shows "(h \<longlongrightarrow> l) G"
proof (rule tendstoI)
  fix e :: real
  define e' where "e' = e/3"
  assume "0 < e"
  then have "0 < e'" by (simp add: e'_def)
  from uniform_limitD[OF uc \<open>0 < e'\<close>]
  have "\<forall>\<^sub>F n in F. \<forall>x\<in>S. dist (h x) (f n x) < e'"
    by (simp add: dist_commute)
  moreover
  from f
  have "\<forall>\<^sub>F n in F. \<forall>\<^sub>F x in G. dist (g n) (f n x) < e'"
    by eventually_elim (auto dest!: tendstoD[OF _ \<open>0 < e'\<close>] simp: dist_commute)
  moreover
  from tendstoD[OF g \<open>0 < e'\<close>] have "\<forall>\<^sub>F x in F. dist l (g x) < e'"
    by (simp add: dist_commute)
  ultimately
  have "\<forall>\<^sub>F _ in F. \<forall>\<^sub>F x in G. dist (h x) l < e"
  proof eventually_elim
    case (elim n)
    note fh = elim(1)
    note gl = elim(3)
    show ?case
      using elim(2) ev
    proof eventually_elim
      case (elim x)
      from fh[rule_format, OF \<open>x \<in> S\<close>] elim(1)
      have "dist (h x) (g n) < e' + e'"
        by (rule dist_triangle_lt[OF add_strict_mono])
      from dist_triangle_lt[OF add_strict_mono, OF this gl]
      show ?case by (simp add: e'_def)
    qed
  qed
  thus "\<forall>\<^sub>F x in G. dist (h x) l < e"
    using eventually_happens by (metis \<open>\<not>trivial_limit F\<close>)
qed

(* reproved theorem in the library using the more general one above *)
proposition swap_uniform_limit:
  assumes f: "\<forall>\<^sub>F n in F. (f n \<longlongrightarrow> g n) (at x within S)"
  assumes g: "(g \<longlongrightarrow> l) F"
  assumes uc: "uniform_limit S f h F"
  assumes nt: "\<not>trivial_limit F"
  shows "(h \<longlongrightarrow> l) (at x within S)"
proof -
  have ev: "eventually (\<lambda>x. x \<in> S) (at x within S)"
    using eventually_at_topological by blast
  show ?thesis
    by (rule swap_uniform_limit'[OF f g uc ev nt])
qed

lemma eventually_eventually_prod_filter1:
  assumes "eventually P (F \<times>\<^sub>F G)"
  shows   "eventually (\<lambda>x. eventually (\<lambda>y. P (x, y)) G) F"
proof -
  from assms obtain Pf Pg where
    *: "eventually Pf F" "eventually Pg G" "\<And>x y. Pf x \<Longrightarrow> Pg y \<Longrightarrow> P (x, y)"
    unfolding eventually_prod_filter by auto
  show ?thesis
    using *(1)
  proof eventually_elim
    case x: (elim x)
    show ?case
      using *(2) by eventually_elim (use x *(3) in auto)
  qed
qed

lemma eventually_eventually_prod_filter2:
  assumes "eventually P (F \<times>\<^sub>F G)"
  shows   "eventually (\<lambda>y. eventually (\<lambda>x. P (x, y)) F) G"
proof -
  from assms obtain Pf Pg where
    *: "eventually Pf F" "eventually Pg G" "\<And>x y. Pf x \<Longrightarrow> Pg y \<Longrightarrow> P (x, y)"
    unfolding eventually_prod_filter by auto
  show ?thesis
    using *(2)
  proof eventually_elim
    case y: (elim y)
    show ?case
      using *(1) by eventually_elim (use y *(3) in auto)
  qed
qed



text \<open>
  Tannery's Theorem proves that, under certain boundedness conditions:
  \[ \lim_{x\to\bar x} \sum_{k=0}^\infty f(k,n) = \sum_{k=0}^\infty \lim_{x\to\bar x} f(k,n) \]
\<close>
lemma tannerys_theorem:
  fixes a :: "nat \<Rightarrow> _ \<Rightarrow> 'a :: {real_normed_algebra, banach}"
  assumes limit: "\<And>k. ((\<lambda>n. a k n) \<longlongrightarrow> b k) F"
  assumes bound: "eventually (\<lambda>(k,n). norm (a k n) \<le> M k) (at_top \<times>\<^sub>F F)"
  assumes "summable M"
  assumes [simp]: "F \<noteq> bot"
  shows   "eventually (\<lambda>n. summable (\<lambda>k. norm (a k n))) F \<and>
           summable (\<lambda>n. norm (b n)) \<and>
           ((\<lambda>n. suminf (\<lambda>k. a k n)) \<longlongrightarrow> suminf b) F"
proof (intro conjI allI)
  show "eventually (\<lambda>n. summable (\<lambda>k. norm (a k n))) F"
  proof -
    have "eventually (\<lambda>n. eventually (\<lambda>k. norm (a k n) \<le> M k) at_top) F"
      using eventually_eventually_prod_filter2[OF bound] by simp
    thus ?thesis
    proof eventually_elim
      case (elim n)
      show "summable (\<lambda>k. norm (a k n))"
      proof (rule summable_comparison_test_ev)
        show "eventually (\<lambda>k. norm (norm (a k n)) \<le> M k) at_top"
          using elim by auto
      qed fact
    qed
  qed

  have bound': "eventually (\<lambda>k. norm (b k) \<le> M k) at_top"
  proof -
    have "eventually (\<lambda>k. eventually (\<lambda>n. norm (a k n) \<le> M k) F) at_top"
      using eventually_eventually_prod_filter1[OF bound] by simp
    thus ?thesis
    proof eventually_elim
      case (elim k)
      show "norm (b k) \<le> M k"
      proof (rule tendsto_upperbound)
        show "((\<lambda>n. norm (a k n)) \<longlongrightarrow> norm (b k)) F"
          by (intro tendsto_intros limit)
      qed (use elim in auto)
    qed
  qed
  show "summable (\<lambda>n. norm (b n))"
    by (rule summable_comparison_test_ev[OF _ \<open>summable M\<close>]) (use bound' in auto)

  from bound obtain Pf Pg where
    *: "eventually Pf at_top" "eventually Pg F" "\<And>k n. Pf k \<Longrightarrow> Pg n \<Longrightarrow> norm (a k n) \<le> M k"
    unfolding eventually_prod_filter by auto

  show "((\<lambda>n. \<Sum>k. a k n) \<longlongrightarrow> (\<Sum>k. b k)) F"
  proof (rule swap_uniform_limit')
    show "(\<lambda>K. (\<Sum>k<K. b k)) \<longlonglongrightarrow> (\<Sum>k. b k)"
      using \<open>summable (\<lambda>n. norm (b n))\<close>
      by (intro summable_LIMSEQ) (auto dest: summable_norm_cancel)
    show "\<forall>\<^sub>F K in sequentially. ((\<lambda>n. \<Sum>k<K. a k n) \<longlongrightarrow> (\<Sum>k<K. b k)) F"
      by (intro tendsto_intros always_eventually allI limit)
    show "\<forall>\<^sub>F x in F. x \<in> {n. Pg n}"
      using *(2) by simp
    show "uniform_limit {n. Pg n} (\<lambda>K n. \<Sum>k<K. a k n) (\<lambda>n. \<Sum>k. a k n) sequentially"
    proof (rule Weierstrass_m_test_ev)
      show "\<forall>\<^sub>F k in at_top. \<forall>n\<in>{n. Pg n}. norm (a k n) \<le> M k"
        using *(1) by eventually_elim (use *(3) in auto)
      show "summable M"
        by fact
    qed
  qed auto
qed

lemma uniform_limit_singleton: "uniform_limit {x} f g F \<longleftrightarrow> ((\<lambda>n. f n x) \<longlongrightarrow> g x) F"
  by (simp add: uniform_limit_iff tendsto_iff)

lemma uniformly_convergent_on_singleton:
  "uniformly_convergent_on {x} f \<longleftrightarrow> convergent (\<lambda>n. f n x)"
  by (auto simp: uniformly_convergent_on_def uniform_limit_singleton convergent_def)

lemma uniformly_convergent_on_subset:
  assumes "uniformly_convergent_on A f" "B \<subseteq> A"
  shows   "uniformly_convergent_on B f"
  using assms by (meson uniform_limit_on_subset uniformly_convergent_on_def)

(* Note Manuel: generalised argument from complex to top. space *)
lemma uniformly_convergent_on_prod_aux:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> complex"
  assumes norm_f: "\<And>n x. x \<in> A \<Longrightarrow> norm (f n x) < 1"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes conv: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. ln (1 + f n x))"
  assumes A: "compact A"
  shows "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
proof -
  from conv obtain S where S: "uniform_limit A (\<lambda>N x. \<Sum>n<N. ln (1 + f n x)) S sequentially"
    by (auto simp: uniformly_convergent_on_def)
  have cont': "continuous_on A S"
  proof (rule uniform_limit_theorem[OF _ S])
    have "f n x + 1 \<notin> \<real>\<^sub>\<le>\<^sub>0" if "x \<in> A" for n x
    proof
      assume "f n x + 1 \<in> \<real>\<^sub>\<le>\<^sub>0"
      then obtain t where t: "t \<le> 0" "f n x = of_real (t - 1)"
        by (metis add_diff_cancel nonpos_Reals_cases of_real_1 of_real_diff)
      moreover have "norm \<dots> \<ge> 1"
        using t by (subst norm_of_real) auto
      ultimately show False
        using norm_f[of x n] that by auto
    qed
    thus "\<forall>\<^sub>F n in sequentially. continuous_on A (\<lambda>x. \<Sum>n<n. Ln (1 + f n x))"
      by (auto intro!: always_eventually continuous_intros cont simp: add_ac)
  qed auto

  define B where "B = {x + y |x y. x \<in> S ` A \<and> y \<in> cball 0 1}"
  have "compact B"
    unfolding B_def by (intro compact_sums compact_continuous_image cont' A) auto

  have "uniformly_convergent_on A (\<lambda>N x. exp ((\<Sum>n<N. ln (1 + f n x))))"
    using conv
  proof (rule uniformly_convergent_on_compose_uniformly_continuous_on)
    show "closed B"
      using \<open>compact B\<close> by (auto dest: compact_imp_closed)
    show "uniformly_continuous_on B exp"
      by (intro compact_uniformly_continuous continuous_intros \<open>compact B\<close>)

    have "eventually (\<lambda>N. \<forall>x\<in>A. dist (\<Sum>n<N. Ln (1 + f n x)) (S x) < 1) sequentially"
      using S unfolding uniform_limit_iff by simp
    thus "eventually (\<lambda>N. \<forall>x\<in>A. (\<Sum>n<N. Ln (1 + f n x)) \<in> B) sequentially"
    proof eventually_elim
      case (elim N)
      show "\<forall>x\<in>A. (\<Sum>n<N. Ln (1 + f n x)) \<in> B"
      proof safe
        fix x assume x: "x \<in> A"
        have "(\<Sum>n<N. Ln (1 + f n x)) = S x + ((\<Sum>n<N. Ln (1 + f n x)) - S x)"
          by auto
        moreover have "((\<Sum>n<N. Ln (1 + f n x)) - S x) \<in> ball 0 1"
          using elim x by (auto simp: dist_norm norm_minus_commute)
        ultimately show "(\<Sum>n<N. Ln (1 + f n x)) \<in> B"
          unfolding B_def using x by fastforce
      qed
    qed
  qed
  also have "?this \<longleftrightarrow> uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
  proof (intro uniformly_convergent_cong refl always_eventually allI ballI)
    fix N :: nat and x assume x: "x \<in> A"
    have "exp (\<Sum>n<N. ln (1 + f n x)) = (\<Prod>n<N. exp (ln (1 + f n x)))"
      by (simp add: exp_sum)
    also have "\<dots> = (\<Prod>n<N. 1 + f n x)"
      using norm_f[of x] x
      by (smt (verit, best) add.right_neutral add_diff_cancel exp_Ln norm_minus_commute norm_one prod.cong)
    finally show "exp (\<Sum>n<N. ln (1 + f n x)) = (\<Prod>n<N. 1 + f n x)" .
  qed
  finally show ?thesis .
qed

(*
text \<open>
  Cauchy's criterion for the convergence of infinite products, adapted to proving
  uniform convergence: let $f_k(x)$ be a sequence of functions such that

    \<^enum> $f_k(x)$ has uniformly bounded partial products, i.e.\ there exists a constant \<open>C\<close>
      such that $\prod_{k=0}^m f_k(x) \leq C$ for all $m$ and $x\in A$.

    \<^enum> For any $\varepsilon\<epsilon> > 0$ there exists a number $M \in \mathbb{N}$ such that, for any
      $m, n \geq M$ and all $x\in A$ we have $|(\prod_{k=m}^n f_k(x)) - 1| < \varepsilon$

  Then $\prod_{k=0}^n f_k(x)$ converges to $\prod_{k=0}^\infty f_k(x)$ uniformly for all
  $x \in A$.
\<close>
*)
lemma uniformly_convergent_prod_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes C: "\<And>x m. x \<in> A \<Longrightarrow> norm (\<Prod>k<m. f k x) \<le> C"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n\<ge>m. dist (\<Prod>k=m..n. f k x) 1 < e"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
proof (rule Cauchy_uniformly_convergent, rule uniformly_Cauchy_onI')
  fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
  define C' where "C' = max C 1"
  have C': "C' > 0"
    by (auto simp: C'_def)
  define \<delta> where "\<delta> = Min {2 / 3 * \<epsilon> / C', 1 / 2}"
  from \<epsilon> have "\<delta> > 0"
    using \<open>C' > 0\<close> by (auto simp: \<delta>_def)
  obtain M where M: "\<And>x m n. x \<in> A \<Longrightarrow> m \<ge> M \<Longrightarrow> n \<ge> m \<Longrightarrow> dist (\<Prod>k=m..n. f k x) 1 < \<delta>"
    using \<open>\<delta> > 0\<close> assms by fast

  show "\<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n>m. dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
  proof (rule exI, intro ballI allI impI)
    fix x m n
    assume x: "x \<in> A" and mn: "M + 1 \<le> m" "m < n"
    show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
    proof (cases "\<exists>k<m. f k x = 0")
      case True
      hence "(\<Prod>k<m. f k x) = 0" and "(\<Prod>k<n. f k x) = 0"
        using mn x by (auto intro!: prod_zero)
      thus ?thesis
        using \<epsilon> by simp
    next
      case False
      have *: "{..<n} = {..<m} \<union> {m..n-1}"
        using mn by auto
      have "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) = norm ((\<Prod>k<m. f k x) * ((\<Prod>k=m..n-1. f k x) - 1))"
        unfolding * by (subst prod.union_disjoint)
                       (use mn in \<open>auto simp: dist_norm algebra_simps norm_minus_commute\<close>)
      also have "\<dots> = (\<Prod>k<m. norm (f k x)) * dist (\<Prod>k=m..n-1. f k x) 1"
        by (simp add: norm_mult dist_norm prod_norm)
      also have "\<dots> < (\<Prod>k<m. norm (f k x)) * (2 / 3 * \<epsilon> / C')"
      proof (rule mult_strict_left_mono)
        show "dist (\<Prod>k = m..n - 1. f k x) 1 < 2 / 3 * \<epsilon> / C'"
          using M[of x m "n-1"] x mn unfolding \<delta>_def by fastforce
      qed (use False in \<open>auto intro!: prod_pos\<close>)
      also have "(\<Prod>k<m. norm (f k x)) = (\<Prod>k<M. norm (f k x)) * norm (\<Prod>k=M..<m. (f k x))"
      proof -
        have *: "{..<m} = {..<M} \<union> {M..<m}"
          using mn by auto
        show ?thesis
          unfolding * using mn by (subst prod.union_disjoint) (auto simp: prod_norm)
      qed
      also have "norm (\<Prod>k=M..<m. (f k x)) \<le> 3 / 2"
      proof -
        have "dist (\<Prod>k=M..m-1. f k x) 1 < \<delta>"
          using M[of x M "m-1"] x mn \<open>\<delta> > 0\<close> by auto
        also have "\<dots> \<le> 1 / 2"
          by (simp add: \<delta>_def)
        also have "{M..m-1} = {M..<m}"
          using mn by auto
        finally have "norm (\<Prod>k=M..<m. f k x) \<le> norm (1 :: 'b) + 1 / 2"
          by norm
        thus ?thesis
          by simp
      qed
      hence "(\<Prod>k<M. norm (f k x)) * norm (\<Prod>k = M..<m. f k x) * (2 / 3 * \<epsilon> / C') \<le>
             (\<Prod>k<M. norm (f k x)) * (3 / 2) * (2 / 3 * \<epsilon> / C')"
        using \<epsilon> C' by (intro mult_left_mono mult_right_mono prod_nonneg) auto
      also have "\<dots> \<le> C' * (3 / 2) * (2 / 3 * \<epsilon> / C')"
      proof (intro mult_right_mono)
        have "(\<Prod>k<M. norm (f k x)) \<le> C"
          using C[of x M] x by (simp add: prod_norm)
        also have "\<dots> \<le> C'"
          by (simp add: C'_def)
        finally show "(\<Prod>k<M. norm (f k x)) \<le> C'" .
      qed (use \<epsilon> C' in auto)
      finally show "dist (\<Prod>k<m. f k x) (\<Prod>k<n. f k x) < \<epsilon>"
        using \<open>C' > 0\<close> by (simp add: field_simps)
    qed
  qed
qed

text \<open>
  By instantiating the set $A$ in this result with a singleton set, we obtain the ``normal''
  Cauchy criterion for infinite products:
\<close>
lemma convergent_prod_Cauchy_sufficient:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
  shows   "convergent_prod f"
proof -
  obtain M where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> m \<Longrightarrow> dist (prod f {m..n}) 1 < 1 / 2"
    using assms(1)[of "1 / 2"] by auto
  have nz: "f m \<noteq> 0" if "m \<ge> M" for m
    using M[of m m] that by auto

  have M': "dist (prod (\<lambda>k. f (k + M)) {m..<n}) 1 < 1 / 2" for m n
  proof (cases "m < n")
    case True
    have "dist (prod f {m+M..n-1+M}) 1 < 1 / 2"
      by (rule M) (use True in auto)
    also have "prod f {m+M..n-1+M} = prod (\<lambda>k. f (k + M)) {m..<n}"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>k. k + M" "\<lambda>k. k - M"]) (use True in auto)
    finally show ?thesis .
  qed auto 

  have "uniformly_convergent_on {0::'b} (\<lambda>N x. \<Prod>n<N. f (n + M))"
  proof (rule uniformly_convergent_prod_Cauchy)
    fix m :: nat
    have "norm (\<Prod>k=0..<m. f (k + M)) < norm (1 :: 'b) + 1 / 2"
      using M'[of 0 m] by norm
    thus "norm (\<Prod>k<m. f (k + M)) \<le> 3 / 2"
      by (simp add: atLeast0LessThan)
  next
    fix e :: real assume e: "e > 0"
    obtain M' where M': "\<And>m n. M' \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
      using assms e by blast
    show "\<exists>M'. \<forall>x\<in>{0}. \<forall>m\<ge>M'. \<forall>n\<ge>m. dist (\<Prod>k=m..n. f (k + M)) 1 < e"
    proof (rule exI[of _ M'], intro ballI impI allI)
      fix m n :: nat assume "M' \<le> m" "m \<le> n"
      thus "dist (\<Prod>k=m..n. f (k + M)) 1 < e"
        using M' by (metis add.commute add_left_mono prod.shift_bounds_cl_nat_ivl trans_le_add1)
    qed
  qed
  hence "convergent (\<lambda>N. \<Prod>n<N. f (n + M))"
    by (rule uniformly_convergent_imp_convergent[of _ _ 0]) auto
  then obtain L where L: "(\<lambda>N. \<Prod>n<N. f (n + M)) \<longlonglongrightarrow> L"
    unfolding convergent_def by blast

  show ?thesis
    unfolding convergent_prod_altdef
  proof (rule exI[of _ M], rule exI[of _ L], intro conjI)
    show "\<forall>n\<ge>M. f n \<noteq> 0"
      using nz by auto
  next
    show "(\<lambda>n. \<Prod>i\<le>n. f (i + M)) \<longlonglongrightarrow> L"
      using LIMSEQ_Suc[OF L] by (subst (asm) lessThan_Suc_atMost)
  next
    have "norm L \<ge> 1 / 2"
    proof (rule tendsto_lowerbound)
      show "(\<lambda>n. norm (\<Prod>i<n. f (i + M))) \<longlonglongrightarrow> norm L"
        by (intro tendsto_intros L)
      show "\<forall>\<^sub>F n in sequentially. 1 / 2 \<le> norm (\<Prod>i<n. f (i + M))"
      proof (intro always_eventually allI)
        fix m :: nat
        have "norm (\<Prod>k=0..<m. f (k + M)) \<ge> norm (1 :: 'b) - 1 / 2"
          using M'[of 0 m] by norm
        thus "norm (\<Prod>k<m. f (k + M)) \<ge> 1 / 2"
          by (simp add: atLeast0LessThan)
      qed
    qed auto
    thus "L \<noteq> 0"
      by auto
  qed
qed

 
lemma convergent_prod_Cauchy_necessary:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_field, banach}"
  assumes "convergent_prod f" "e > 0"
  shows   "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
proof -
  have *: "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e"
    if f: "convergent_prod f" "0 \<notin> range f" and e: "e > 0"
    for f :: "nat \<Rightarrow> 'b" and e :: real
  proof -
    have *: "(\<lambda>n. norm (\<Prod>k<n. f k)) \<longlonglongrightarrow> norm (\<Prod>k. f k)"
      using has_prod_imp_tendsto' f(1) by (intro tendsto_norm) blast
    from f(1,2) have [simp]: "(\<Prod>k. f k) \<noteq> 0"
      using prodinf_nonzero by fastforce
    obtain M' where M': "norm (\<Prod>k<m. f k) > norm (\<Prod>k. f k) / 2" if "m \<ge> M'" for m
      using order_tendstoD(1)[OF *, of "norm (\<Prod>k. f k) / 2"]
      by (auto simp: eventually_at_top_linorder)
    define M where "M = Min (insert (norm (\<Prod>k. f k) / 2) ((\<lambda>m. norm (\<Prod>k<m. f k)) ` {..<M'}))"
    have "M > 0"
      unfolding M_def using f(2) by (subst Min_gr_iff) auto
    have norm_ge: "norm (\<Prod>k<m. f k) \<ge> M" for m
    proof (cases "m \<ge> M'")
      case True
      have "M \<le> norm (\<Prod>k. f k) / 2"
        unfolding M_def by (intro Min.coboundedI) auto
      also from True have "norm (\<Prod>k<m. f k) > norm (\<Prod>k. f k) / 2"
        by (intro M')
      finally show ?thesis by linarith
    next
      case False
      thus ?thesis
        unfolding M_def
        by (intro Min.coboundedI) auto
    qed

    have "convergent (\<lambda>n. \<Prod>k<n. f k)"
      using f(1) convergent_def has_prod_imp_tendsto' by blast
    hence "Cauchy (\<lambda>n. \<Prod>k<n. f k)"
      by (rule convergent_Cauchy)
    moreover have "e * M > 0"
      using e \<open>M > 0\<close> by auto
    ultimately obtain N where N: "dist (\<Prod>k<m. f k) (\<Prod>k<n. f k) < e * M" if "m \<ge> N" "n \<ge> N" for m n
      unfolding Cauchy_def by fast

    show "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (prod f {m..n}) 1 < e"
    proof (rule exI[of _ N], intro allI impI, goal_cases)
      case (1 m n)
      have "dist (\<Prod>k<m. f k) (\<Prod>k<Suc n. f k) < e * M"
        by (rule N) (use 1 in auto)
      also have "dist (\<Prod>k<m. f k) (\<Prod>k<Suc n. f k) = norm ((\<Prod>k<Suc n. f k) - (\<Prod>k<m. f k))"
        by (simp add: dist_norm norm_minus_commute)
      also have "(\<Prod>k<Suc n. f k) = (\<Prod>k\<in>{..<m}\<union>{m..n}. f k)"
        using 1 by (intro prod.cong) auto
      also have "\<dots> = (\<Prod>k\<in>{..<m}. f k) * (\<Prod>k\<in>{m..n}. f k)"
        by (subst prod.union_disjoint) auto
      also have "\<dots> - (\<Prod>k<m. f k) = (\<Prod>k<m. f k) * ((\<Prod>k\<in>{m..n}. f k) - 1)"
        by (simp add: algebra_simps)
      finally have "norm (prod f {m..n} - 1) < e * M / norm (prod f {..<m})"
        using f(2) by (auto simp add: norm_mult divide_simps mult_ac)
      also have "\<dots> \<le> e * M / M"
        using e \<open>M > 0\<close> f(2) by (intro divide_left_mono norm_ge mult_pos_pos) auto
      also have "\<dots> = e"
        using \<open>M > 0\<close> by simp
      finally show ?case
        by (simp add: dist_norm)
    qed
  qed

  obtain M where M: "f m \<noteq> 0" if "m \<ge> M" for m
    using convergent_prod_imp_ev_nonzero[OF assms(1)]
    by (auto simp: eventually_at_top_linorder)

  have "\<exists>M'. \<forall>m n. M' \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f (k + M)) 1 < e"
    by (rule *) (use assms M in auto)
  then obtain M' where M': "dist (\<Prod>k=m..n. f (k + M)) 1 < e" if "M' \<le> m" "m \<le> n" for m n
    by blast

  show "\<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (prod f {m..n}) 1 < e"
  proof (rule exI[of _ "M + M'"], safe, goal_cases)
    case (1 m n)
    have "dist (\<Prod>k=m-M..n-M. f (k + M)) 1 < e"
      by (rule M') (use 1 in auto)
    also have "(\<Prod>k=m-M..n-M. f (k + M)) = (\<Prod>k=m..n. f k)"
      using 1 by (intro prod.reindex_bij_witness[of _ "\<lambda>k. k - M" "\<lambda>k. k + M"]) auto
    finally show ?case .
  qed
qed

lemma convergent_prod_Cauchy_iff:
  fixes f :: "nat \<Rightarrow> 'b :: {real_normed_field, banach}"
  shows "convergent_prod f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m n. M \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>k=m..n. f k) 1 < e)"
  using convergent_prod_Cauchy_necessary[of f] convergent_prod_Cauchy_sufficient[of f]
  by blast

(* Note Manuel: generalised argument from 'b to 'a :: topological_space *)
lemma uniform_limit_suminf:
  fixes f:: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b::{metric_space, comm_monoid_add}"
  assumes "uniformly_convergent_on X (\<lambda>n x. \<Sum>k<n. f k x)" 
  shows "uniform_limit X (\<lambda>n x. \<Sum>k<n. f k x) (\<lambda>x. \<Sum>k. f k x) sequentially"
proof -
  obtain S where S: "uniform_limit X (\<lambda>n x. \<Sum>k<n. f k x) S sequentially"
    using assms uniformly_convergent_on_def by blast
  then have "(\<Sum>k. f k x) = S x" if "x \<in> X" for x
    using that sums_iff sums_def by (blast intro: tendsto_uniform_limitI [OF S])
  with S show ?thesis
    by (simp cong: uniform_limit_cong')
qed

text \<open>Theorem 17.6 by Bak and Newman, Complex Analysis [roughly]\<close>
lemma uniformly_convergent_on_prod:
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x))"
  shows   "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + f n x)"
proof -
  have lim: "uniform_limit A (\<lambda>n x. \<Sum>k<n. norm (f k x)) (\<lambda>x. \<Sum>k. norm (f k x)) sequentially"
    by (rule uniform_limit_suminf) fact
  have cont': "\<forall>\<^sub>F n in sequentially. continuous_on A (\<lambda>x. \<Sum>k<n. norm (f k x))"
    using cont by (auto intro!: continuous_intros always_eventually cont)
  have "continuous_on A (\<lambda>x. \<Sum>k. norm (f k x))"
    by (rule uniform_limit_theorem[OF cont' lim]) auto
  hence "compact ((\<lambda>x. \<Sum>k. norm (f k x)) ` A)"
    by (intro compact_continuous_image A)
  hence "bounded ((\<lambda>x. \<Sum>k. norm (f k x)) ` A)"
    by (rule compact_imp_bounded)
  then obtain C where C: "norm (\<Sum>k. norm (f k x)) \<le> C" if "x \<in> A" for x
    unfolding bounded_iff by blast
  show ?thesis
  proof (rule uniformly_convergent_prod_Cauchy)
    fix x :: 'a and m :: nat
    assume x: "x \<in> A"
    have "norm (\<Prod>k<m. 1 + f k x) = (\<Prod>k<m. norm (1 + f k x))"
      by (simp add: prod_norm)
    also have "\<dots> \<le> (\<Prod>k<m. norm (1 :: 'b) + norm (f k x))"
      by (intro prod_mono) norm
    also have "\<dots> = (\<Prod>k<m. 1 + norm (f k x))"
      by simp
    also have "\<dots> \<le> exp (\<Sum>k<m. norm (f k x))"
      by (rule prod_le_exp_sum) auto
    also have "(\<Sum>k<m. norm (f k x)) \<le> (\<Sum>k. norm (f k x))"
    proof (rule sum_le_suminf)
      have "(\<lambda>n. \<Sum>k<n. norm (f k x)) \<longlonglongrightarrow> (\<Sum>k. norm (f k x))"
        by (rule tendsto_uniform_limitI[OF lim]) fact
      thus "summable (\<lambda>k. norm (f k x))"
        using sums_def sums_iff by blast
    qed auto
    also have "exp (\<Sum>k. norm (f k x)) \<le> exp (norm (\<Sum>k. norm (f k x)))"
      by simp
    also have "norm (\<Sum>k. norm (f k x)) \<le> C"
      by (rule C) fact
    finally show "norm (\<Prod>k<m. 1 + f k x) \<le> exp C"
      by - simp_all
  next
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    have "uniformly_Cauchy_on A (\<lambda>N x. \<Sum>n<N. norm (f n x))"
      by (rule uniformly_convergent_Cauchy) fact
    moreover have "ln (1 + \<epsilon>) > 0"
      using \<epsilon> by simp
    ultimately obtain M where M: "\<And>m n x. x \<in> A \<Longrightarrow> M \<le> m \<Longrightarrow> M \<le> n \<Longrightarrow>
        dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<n. norm (f k x)) < ln (1 + \<epsilon>)"
      using \<epsilon> unfolding uniformly_Cauchy_on_def by metis
  
    show "\<exists>M. \<forall>x\<in>A. \<forall>m\<ge>M. \<forall>n\<ge>m. dist (\<Prod>k = m..n. 1 + f k x) 1 < \<epsilon>"
    proof (rule exI, intro ballI allI impI)
      fix x m n
      assume x: "x \<in> A" and mn: "M \<le> m" "m \<le> n"
      have "dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<Suc n. norm (f k x)) < ln (1 + \<epsilon>)"
        by (rule M) (use x mn in auto)
      also have "dist (\<Sum>k<m. norm (f k x)) (\<Sum>k<Suc n. norm (f k x)) =
                 \<bar>\<Sum>k\<in>{..<Suc n}-{..<m}. norm (f k x)\<bar>"
        using mn by (subst sum_diff) (auto simp: dist_norm)
      also have "{..<Suc n}-{..<m} = {m..n}"
        using mn by auto
      also have "\<bar>\<Sum>k=m..n. norm (f k x)\<bar> = (\<Sum>k=m..n. norm (f k x))"
        by (intro abs_of_nonneg sum_nonneg) auto
      finally have *: "(\<Sum>k=m..n. norm (f k x)) < ln (1 + \<epsilon>)" .
  
      have "dist (\<Prod>k=m..n. 1 + f k x) 1 = norm ((\<Prod>k=m..n. 1 + f k x) - 1)"
        by (simp add: dist_norm)
      also have "norm ((\<Prod>k=m..n. 1 + f k x) - 1) \<le> (\<Prod>n=m..n. 1 + norm (f n x)) - 1"
        by (rule norm_prod_minus1_le_prod_minus1)
      also have "(\<Prod>n=m..n. 1 + norm (f n x)) \<le> exp (\<Sum>k=m..n. norm (f k x))"
        by (rule prod_le_exp_sum) auto
      also note *
      finally show "dist (\<Prod>k = m..n. 1 + f k x) 1 < \<epsilon>"
        using \<epsilon> by - simp_all
    qed
  qed
qed

lemma uniformly_convergent_on_prod':
  fixes f :: "nat \<Rightarrow> 'a :: topological_space \<Rightarrow> 'b :: {real_normed_div_algebra, comm_ring_1, banach}"
  assumes cont: "\<And>n. continuous_on A (f n)"
  assumes A: "compact A"
  assumes conv_sum: "uniformly_convergent_on A (\<lambda>N x. \<Sum>n<N. norm (f n x - 1))"
  shows "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. f n x)"
proof -
  have "uniformly_convergent_on A (\<lambda>N x. \<Prod>n<N. 1 + (f n x - 1))"
    by (rule uniformly_convergent_on_prod) (use assms in \<open>auto intro!: continuous_intros\<close>)
  thus ?thesis
    by simp
qed
(* END MANUEL BLOCK *)

lemma ln_cis: "x \<in> {- pi<..pi} \<Longrightarrow> ln (cis x) = \<i> * x"
  by (simp add: Ln_Arg Arg_cis)

lemma tendsto_arcsin [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "L \<in> {-1..1}" "L \<in> {-1<..<1} \<or> (\<forall>\<^sub>F x in F. f x \<in> {- 1..1})"
  shows   "((\<lambda>x. arcsin (f x)) \<longlongrightarrow> arcsin L) F"
proof -
  have *: "\<forall>\<^sub>F x in F. f x \<in> {-1..1}"
    using assms(3)
  proof
    assume "L \<in> {-1<..<1}"
    hence "eventually (\<lambda>x. x \<in> {-1<..<1}) (nhds L)"
      by (intro eventually_nhds_in_open) auto
    moreover have "nhds L \<ge> filtermap f F"
      using assms(1) by (simp add: filterlim_def)
    ultimately have "eventually (\<lambda>x. x \<in> {-1<..<1}) (filtermap f F)"
      using filter_leD by blast
    thus "eventually (\<lambda>x. f x \<in> {-1..1}) F"
      unfolding eventually_filtermap by eventually_elim auto
  qed     
  show ?thesis
    using continuous_on_tendsto_compose [OF continuous_on_arcsin' assms(1,2) *] .
qed  

lemma tendsto_arccos [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "L \<in> {-1..1}" "L \<in> {-1<..<1} \<or> (\<forall>\<^sub>F x in F. f x \<in> {- 1..1})"
  shows   "((\<lambda>x. arccos (f x)) \<longlongrightarrow> arccos L) F"
proof -
  have *: "\<forall>\<^sub>F x in F. f x \<in> {-1..1}"
    using assms(3)
  proof
    assume "L \<in> {-1<..<1}"
    hence "eventually (\<lambda>x. x \<in> {-1<..<1}) (nhds L)"
      by (intro eventually_nhds_in_open) auto
    moreover have "nhds L \<ge> filtermap f F"
      using assms(1) by (simp add: filterlim_def)
    ultimately have "eventually (\<lambda>x. x \<in> {-1<..<1}) (filtermap f F)"
      using filter_leD by blast
    thus "eventually (\<lambda>x. f x \<in> {-1..1}) F"
      unfolding eventually_filtermap by eventually_elim auto
  qed     
  show ?thesis
    using continuous_on_tendsto_compose [OF continuous_on_arccos' assms(1,2) *] .
qed

lemma analytic_derivI:
  assumes "f analytic_on {x}"
  shows   "(f has_field_derivative deriv f x) (at x within T)"
proof -
  from assms obtain A where A: "open A" "{x} \<subseteq> A" "f holomorphic_on A"
    unfolding analytic_on_holomorphic by auto
  thus ?thesis
    by (intro holomorphic_derivI[of _ A]) auto
qed

(* TODO: Move *)
lemma cong_cmult_leftI: "[a = b] (mod m) \<Longrightarrow> [c * a = c * b] (mod (c * m))"
  by (simp add: Cong.cong_def)

lemma cong_cmult_rightI: "[a = b] (mod m) \<Longrightarrow> [a * c = b * c] (mod (m * c))"
  by (simp add: Cong.cong_def)

lemma gcd_prime_int:
  assumes "prime (p :: int)"
  shows   "gcd p k = (if p dvd k then p else 1)"
proof -
  have "p \<ge> 0"
    using assms prime_ge_0_int by auto
  show ?thesis
  proof (cases "p dvd k")
    case True
    thus ?thesis using assms \<open>p \<ge> 0\<close> by auto
  next
    case False
    hence "coprime p k"
      using assms by (simp add: prime_imp_coprime)
    with False show ?thesis
      by auto
  qed
qed

lemma dvd_diff_right_iff:
  fixes a b c :: "'a :: comm_ring_1"
  assumes "a dvd b"
  shows "a dvd b - c \<longleftrightarrow> a dvd c" (is "?P \<longleftrightarrow> ?Q")
  using dvd_add_right_iff[of a b "-c"] assms by auto

lemma dvd_diff_left_iff: 
  fixes a b c :: "'a :: comm_ring_1"
  shows "a dvd c \<Longrightarrow> a dvd b - c \<longleftrightarrow> a dvd b"
  using dvd_add_left_iff[of a "-c" b] by auto

lemma cong_uminus: "[(x :: 'a :: unique_euclidean_ring) = y] (mod m) \<Longrightarrow> [-x = -y] (mod m)"
  unfolding cong_minus_minus_iff .

lemma cong_dvd_mono_modulus:
  assumes "[a = b] (mod m)" "m' dvd m"
  shows   "[a = b] (mod m')"
  using assms by (metis Cong.cong_def mod_mod_cancel)
  
lemma coprime_cong_transfer_left:
  assumes "coprime a b" "[a = a'] (mod b)"
  shows   "coprime a' b"
  using assms by (metis cong_0 Cong.cong_def coprime_mod_left_iff)

lemma coprime_cong_cong_left:
  assumes "[a = a'] (mod b)"
  shows   "coprime a b \<longleftrightarrow> coprime a' b"
  using assms by (metis cong_0 Cong.cong_def coprime_mod_left_iff)



lemma cong_mod_leftI [simp]:
  "[b = c] (mod a) \<Longrightarrow> [b mod a = c] (mod a)"
  by (simp add: cong_def)  

lemma cong_mod_rightI [simp]:
  "[b = c] (mod a) \<Longrightarrow> [b = c mod a] (mod a)"
  by (simp add: cong_def)  


lemma add_in_Ints_iff_left [simp]: "x \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (metis Ints_add Ints_diff add_diff_cancel_left')

lemma add_in_Ints_iff_right [simp]: "y \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by (subst add.commute) auto

lemma diff_in_Ints_iff_left [simp]: "x \<in> \<int> \<Longrightarrow> x - y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (metis Ints_diff add_in_Ints_iff_left diff_add_cancel)

lemma diff_in_Ints_iff_right [simp]: "y \<in> \<int> \<Longrightarrow> x - y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by (metis Ints_minus diff_in_Ints_iff_left minus_diff_eq)

lemmas [simp] = minus_in_Ints_iff

lemma of_int_div_of_int_in_Ints_iff:
  "(of_int n / of_int m :: 'a :: field_char_0) \<in> \<int> \<longleftrightarrow> m = 0 \<or> m dvd n"
proof
  assume *: "(of_int n / of_int m :: 'a) \<in> \<int>"
  {
    assume "m \<noteq> 0"
    from * obtain k where k: "(of_int n / of_int m :: 'a) = of_int k"
      by (auto elim!: Ints_cases)
    hence "of_int n = (of_int k * of_int m :: 'a)"
      using \<open>m \<noteq> 0\<close> by (simp add: field_simps)
    also have "\<dots> = of_int (k * m)"
      by simp
    finally have "n = k * m"
      by (subst (asm) of_int_eq_iff)
    hence "m dvd n" by auto
  }
  thus "m = 0 \<or> m dvd n" by blast
qed auto



definition cong_inverse :: "'a :: euclidean_ring_gcd \<Rightarrow> 'a \<Rightarrow> 'a" where
  "cong_inverse m a = (if coprime a m then fst (bezout_coefficients a m) mod m else 0)"

lemma mult_cong_inverse_right:
  assumes "coprime a m"
  shows   "[a * cong_inverse m a = 1] (mod m)"
proof -
  define B where "B = bezout_coefficients a m"
  have "[(fst B mod m) * a + snd B * 0 = fst B * a + snd B * m] (mod m)"
    by (intro cong_add cong_mult cong_refl) (auto simp: Cong.cong_def)
  also have "fst B * a + snd B * m = 1"
    using bezout_coefficients[of a m] assms by (simp add: B_def)
  finally show ?thesis
    using assms by (simp add: B_def cong_inverse_def mult_ac)
qed

lemma mult_cong_inverse_left:
  assumes "coprime a m"
  shows   "[cong_inverse m a * a = 1] (mod m)"
  using mult_cong_inverse_right[OF assms] by (simp add: mult_ac)

lemma mult_cong_inverse_int_nonneg: "m > 0 \<Longrightarrow> cong_inverse m a \<ge> (0 :: int)"
  by (auto simp: cong_inverse_def pos_mod_sign)

lemma mult_cong_inverse_of_not_coprime [simp]: "\<not>coprime a m \<Longrightarrow> cong_inverse m a = 0"
  by (auto simp: cong_inverse_def)

lemma mult_cong_inverse_eq_0_iff:
  fixes a :: "'a :: {unique_euclidean_semiring, euclidean_ring_gcd}"
  shows "\<not>is_unit m \<Longrightarrow> cong_inverse m a = 0 \<longleftrightarrow> \<not>coprime a m"
  using mult_cong_inverse_right[of a m] by (cases "coprime a m") (auto simp: Cong.cong_def)

lemma mult_cong_inverse_int_pos: "m > 1 \<Longrightarrow> coprime a m \<Longrightarrow> cong_inverse m a > (0 :: int)"
  using mult_cong_inverse_eq_0_iff[of m a] mult_cong_inverse_int_nonneg[of m a] by auto

lemma abs_mult_cong_inverse_int_less: "m \<noteq> 0 \<Longrightarrow> \<bar>cong_inverse m a :: int\<bar> < \<bar>m\<bar>"
  by (auto simp: cong_inverse_def intro!: abs_mod_less)

lemma mult_cong_inverse_int_less: "m \<noteq> 0 \<Longrightarrow> (cong_inverse m a :: int) < \<bar>m\<bar>"
  using abs_mult_cong_inverse_int_less[of m a] by linarith

lemma mult_cong_inverse_int_less': "m > 0 \<Longrightarrow> (cong_inverse m a :: int) < m"
  using abs_mult_cong_inverse_int_less[of m a] by linarith


lemma bij_betw_mult_mod_int:
  assumes "coprime h (k :: int)"
  shows   "bij_betw (\<lambda>r. (h * r) mod k) {0..<k} {0..<k}"
proof (cases "k = 0")
  case True
  thus ?thesis by (auto simp: bij_betw_def)
next
  case k: False
  define h' where "h' = cong_inverse k h"
  show ?thesis
  proof (rule bij_betwI)
    show "(\<lambda>r. (h * r) mod k) \<in> {0..<k} \<rightarrow> {0..<k}"
      using k assms by auto
    show "(\<lambda>r. (h' * r) mod k) \<in> {0..<k} \<rightarrow> {0..<k}"
      using k assms by auto
  next
    fix x assume x: "x \<in> {0..<k}"
    have *: "a * (b * x mod k) mod k = x"
      if ab: "[a * b = 1] (mod k)" for a b
    proof -
      have "[a * (b * x mod k) mod k = a * (b * x)] (mod k)"
        by (intro cong_mult cong_mod_leftI cong_refl)
      also have "a * (b * x) = a * b * x"
        by (simp add: mult_ac)
      also have "[a * b * x = 1 * x] (mod k)"
        by (intro cong_mult ab cong_refl)
      finally show "a * (b * x mod k) mod k = x"
        using x by (auto simp: Cong.cong_def)
    qed
    show "h' * (h * x mod k) mod k = x"
      using assms unfolding h'_def by (intro * mult_cong_inverse_left)
    show "h * (h' * x mod k) mod k = x"
      using assms unfolding h'_def by (intro * mult_cong_inverse_right)
  qed
qed

lemma bij_betw_mult_mod_int':
  assumes "coprime h (k :: int)"
  shows   "bij_betw (\<lambda>r. (h * r) mod k) {1..<k} {1..<k}"
proof (cases "k > 0")
  case False
  thus ?thesis
    by (auto simp: bij_betw_def)
next
  case True
  hence "bij_betw (\<lambda>r. (h * r) mod k) ({0..<k} - {0}) ({0..<k} - {0})"
    by (intro bij_betw_DiffI bij_betw_mult_mod_int assms) auto
  also have "{0..<k} - {0} = {1..<k}"
    using True by auto
  finally show ?thesis .
qed


(*Migrated to the HOL distribution 23-09-2023*)
lemma powr_power: 
  fixes z:: "'a::{real_normed_field,ln}"
  shows "z \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> (z powr u) ^ n = z powr (of_nat n * u)"
  by (induction n) (auto simp: algebra_simps powr_add)

lemma zmult_eq_neg1_iff: "a * b = (-1 :: int) \<longleftrightarrow> a = 1 \<and> b = -1 \<or> a = -1 \<and> b = 1"
  using zmult_eq_1_iff[of a "-b"] by auto

lemma continuous_on_Complex [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. Complex (f x) (g x))"
  unfolding Complex_eq by (intro continuous_intros)

lemma continuous_image_closure_subset:
  assumes "continuous_on A f" "closure B \<subseteq> A"
  shows   "f ` closure B \<subseteq> closure (f ` B)"
  using assms by (meson closed_closure closure_subset continuous_on_subset image_closure_subset)

(*Migrated to the HOL distribution 27-09-2023*)
lemma analytic_imp_contour_integrable:
  assumes "f analytic_on path_image p" "valid_path p"
  shows   "f contour_integrable_on p"
  by (meson analytic_on_holomorphic assms contour_integrable_holomorphic_simple)

lemma filterlim_at_infinity_iff_eventually_norm_gt:
  "filterlim f at_infinity F \<longleftrightarrow> (\<forall>c. eventually (\<lambda>x. norm (f x) > c) F)"
  using filterlim_at_infinity_imp_norm_at_top filterlim_at_top_dense 
        filterlim_norm_at_top_imp_at_infinity by metis

lemma isolated_singularity_bounded_imp_convergent:
  assumes "f \<in> O[at z](\<lambda>_. 1)" "isolated_singularity_at f z"
  shows   "\<exists>c. f \<midarrow>z\<rightarrow> c"
proof -
  from assms(2) obtain A where A: "open A" "z \<in> A" "f analytic_on A - {z}"
    unfolding isolated_singularity_at_def using centre_in_ball by blast
  from assms(1) obtain C where C: "C > 0" "eventually (\<lambda>z. norm (f z) \<le> C) (at z)"
    by (elim landau_o.bigE) auto
  then obtain B where B: "open B" "z \<in> B" "\<And>w. w \<in> B - {z} \<Longrightarrow> norm (f w) \<le> C"
    unfolding eventually_at_topological by auto
  define C' where "C' = C + 1"
  have C': "C' > C"
    by (auto simp: C'_def)

  show ?thesis
  proof (rule great_Picard)
    show "open (A \<inter> B)" "z \<in> A \<inter> B" "of_real C' \<noteq> of_real C' * \<i>"
      using A B C C' by auto
    show "f holomorphic_on (A \<inter> B - {z})"
      by (rule analytic_imp_holomorphic, rule analytic_on_subset, rule A(3)) auto
    show "f w \<noteq> of_real C' \<and> f w \<noteq> of_real C' * \<i>" if w: "w \<in> A \<inter> B - {z}" for w
      using B(3)[of w] w C' by (auto simp: norm_mult)
    show "\<exists>c. f \<midarrow>z\<rightarrow> c" if "f \<midarrow>z\<rightarrow> l \<or> (inverse \<circ> f) \<midarrow>z\<rightarrow> l" for l
      using that
    proof
      assume lim: "(inverse \<circ> f) \<midarrow>z\<rightarrow> l"
      show ?thesis
      proof (cases "l = 0")
        case False
        have "(\<lambda>z. inverse ((inverse \<circ> f) z)) \<midarrow>z\<rightarrow> inverse l"
          by (rule tendsto_intros lim False)+
        also have "?this \<longleftrightarrow> f \<midarrow>z\<rightarrow> inverse l"
          by (intro tendsto_cong) auto
        finally show ?thesis by blast
      next
        case True
        with lim have "eventually (\<lambda>z. norm (inverse (f z)) < 1 / C') (at z)"
          using C C' by (simp add: tendsto_iff dist_norm)
        moreover have "eventually (\<lambda>w. w \<in> B - {z}) (at z)"
          using B(1,2) by (intro eventually_at_in_open) auto
        ultimately have "eventually (\<lambda>z. f z = 0) (at z)"
        proof eventually_elim
          case (elim w)
          thus ?case
            using B(3)[of w] C C' by (auto simp: norm_divide divide_simps split: if_splits)
        qed
        thus ?thesis
          using tendsto_eventually by blast
      qed
    qed auto
  qed
qed

lemma analytic_deriv' [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on (f ` A)"
  shows   "(\<lambda>z. deriv g (f z)) analytic_on A"
  by (rule analytic_on_compose[OF assms(1) analytic_deriv[OF assms(2)], unfolded o_def])

end
