section \<open>The infinite $q$-Pochhammer symbol\<close>
theory Q_Pochhammer_Infinite
  imports Library_Extras Lambert_Series.Lambert_Series_Library Meromorphic1
begin

subsection \<open>Definition and basic properties\<close>

definition qpochhammer_inf :: "'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "qpochhammer_inf a q = prodinf (\<lambda>k. 1 - a * q ^ k)"

lemma qpochhammer_inf_0_left [simp]: "qpochhammer_inf 0 q = 1"
  by (simp add: qpochhammer_inf_def)

lemma qpochhammer_inf_0_right [simp]: "qpochhammer_inf a 0 = 1 - a"
proof -
  have "qpochhammer_inf a 0 = (\<Prod>k\<le>0. 1 - a * 0 ^ k)"
    unfolding qpochhammer_inf_def by (rule prodinf_finite) auto
  also have "\<dots> = 1 - a"
    by simp
  finally show ?thesis .
qed

lemma abs_convergent_qpochhammer_inf:
  fixes a q :: "'a :: {real_normed_div_algebra, banach}"
  assumes "q \<in> ball 0 1"
  shows   "abs_convergent_prod (\<lambda>n. 1 - a * q ^ n)"
proof (rule summable_imp_abs_convergent_prod)
  show "summable (\<lambda>n. norm (1 - a * q ^ n - 1))"
    using assms by (auto simp: norm_power norm_mult)
qed

lemma convergent_qpochhammer_inf:
  fixes a q :: "'a :: {real_normed_field, banach}"
  assumes "q \<in> ball 0 1"
  shows   "convergent_prod (\<lambda>n. 1 - a * q ^ n)"
  using abs_convergent_qpochhammer_inf[OF assms] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod_qpochhammer_inf:
  "q \<in> ball 0 1 \<Longrightarrow> (\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
  using convergent_qpochhammer_inf unfolding qpochhammer_inf_def
  by (intro convergent_prod_has_prod)

lemma qpochhammer_inf_zero_iff:
  assumes q: "q \<in> ball 0 1"
  shows   "qpochhammer_inf a q = 0 \<longleftrightarrow> (\<exists>n. a * q ^ n = 1)"
proof -
  have "(\<lambda>n. 1 - a * q ^ n) has_prod qpochhammer_inf a q"
    using has_prod_qpochhammer_inf[OF q] by simp
  hence "qpochhammer_inf a q = 0 \<longleftrightarrow> (\<exists>n. a * q ^ n = 1)"
    by (subst has_prod_eq_0_iff) auto
  thus ?thesis .
qed

lemma qpochhammer_inf_nonzero:
  assumes "q \<in> ball 0 1" "norm a < 1"
  shows   "qpochhammer_inf a q \<noteq> 0"
proof
  assume "qpochhammer_inf a q = 0"
  then obtain n where n: "a * q ^ n = 1"
    using assms by (subst (asm) qpochhammer_inf_zero_iff) auto
  have "norm (q ^ n) * norm a \<le> 1 * norm a"
    unfolding norm_power using assms by (intro mult_right_mono power_le_one) auto
  also have "\<dots>  < 1"
    using assms by simp
  finally have "norm (a * q ^ n) < 1"
    by (simp add: norm_mult mult.commute)
  with n show False
    by auto
qed

context
  fixes P :: "nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a \<Rightarrow> 'a"
  defines "P \<equiv> (\<lambda>N a q. \<Prod>n<N. 1 - a * q ^ n)"
begin 

lemma uniformly_convergent_qpochhammer_inf_aux:
  assumes r: "0 \<le> ra" "0 \<le> rq" "rq < 1"
  shows   "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)"
  unfolding P_def case_prod_unfold
proof (rule uniformly_convergent_on_prod')
  show "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq)
          (\<lambda>N aq. \<Sum>n<N. norm (1 - fst aq * snd aq ^ n - 1 :: 'a))"
  proof (intro Weierstrass_m_test'_ev always_eventually allI ballI)
    show "summable (\<lambda>n. ra * rq ^ n)" using r
      by (intro summable_mult summable_geometric) auto
  next
    fix n :: nat and aq :: "'a \<times> 'a"
    assume "aq \<in> cball 0 ra \<times> cball 0 rq"
    then obtain a q where [simp]: "aq = (a, q)" and aq: "norm a \<le> ra" "norm q \<le> rq"
      by (cases aq) auto
    have "norm (norm (1 - a * q ^ n - 1)) = norm a * norm q ^ n"
      by (simp add: norm_mult norm_power)
    also have "\<dots> \<le> ra * rq ^ n"
      using aq r by (intro mult_mono power_mono) auto
    finally show "norm (norm (1 - fst aq * snd aq ^ n - 1)) \<le> ra * rq ^ n"
      by simp
  qed
qed (auto intro!: continuous_intros compact_Times) 

lemma uniformly_convergent_qpochhammer_inf:
  assumes "compact A" "A \<subseteq> UNIV \<times> ball 0 1"
  shows   "uniformly_convergent_on A (\<lambda>n (a,q). P n a q)"
proof (cases "A = {}")
  case False
  obtain rq where rq: "rq \<ge> 0" "rq < 1" "\<And>a q. (a, q) \<in> A \<Longrightarrow> norm q \<le> rq"
  proof -
    from \<open>compact A\<close> have "compact (norm ` snd ` A)"
      by (intro compact_continuous_image continuous_intros)
    hence "Sup (norm ` snd ` A) \<in> norm ` snd ` A"
      by (intro closed_contains_Sup bounded_imp_bdd_above compact_imp_bounded compact_imp_closed)
         (use \<open>A \<noteq> {}\<close> in auto)
    then obtain aq0 where aq0: "aq0 \<in> A" "norm (snd aq0) = Sup (norm ` snd ` A)"
      by auto
    show ?thesis
    proof (rule that[of "norm (snd aq0)"])
      show "norm (snd aq0) \<ge> 0" and "norm (snd aq0) < 1"
        using assms(2) aq0(1) by auto
    next
      fix a q assume "(a, q) \<in> A"
      hence "norm q \<le> Sup (norm ` snd ` A)"
        by (intro cSup_upper bounded_imp_bdd_above compact_imp_bounded assms
              compact_continuous_image continuous_intros) force
      with aq0 show "norm q \<le> norm (snd aq0)"
        by simp
    qed
  qed

  obtain ra where ra: "ra \<ge> 0" "\<And>a q. (a, q) \<in> A \<Longrightarrow> norm a \<le> ra"
  proof -
    have "bounded (fst ` A)"
      by (intro compact_imp_bounded compact_continuous_image continuous_intros assms)
    then obtain ra where ra: "norm a \<le> ra" if "a \<in> fst ` A" for a
      unfolding bounded_iff by blast
    from \<open>A \<noteq> {}\<close> obtain aq0 where "aq0 \<in> A"
      by blast
    have "0 \<le> norm (fst aq0)"
      by simp
    also have "fst aq0 \<in> fst ` A"
      using \<open>aq0 \<in> A\<close> by blast
    with ra[of "fst aq0"] and \<open>A \<noteq> {}\<close> have "norm (fst aq0) \<le> ra"
      by simp
    finally show ?thesis
      using that[of ra] ra by fastforce
  qed

  have "uniformly_convergent_on (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)"
    by (intro uniformly_convergent_qpochhammer_inf_aux) (use ra rq in auto)
  thus ?thesis
    by (rule uniformly_convergent_on_subset) (use ra rq in auto)
qed auto

lemma uniform_limit_qpochhammer_inf:
  assumes "compact A" "A \<subseteq> UNIV \<times> ball 0 1"
  shows   "uniform_limit A (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
proof -
  obtain g where g: "uniform_limit A (\<lambda>n (a,q). P n a q) g at_top"
    using uniformly_convergent_qpochhammer_inf[OF assms(1,2)]
    by (auto simp: uniformly_convergent_on_def)
  also have "?this \<longleftrightarrow> uniform_limit A (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
  proof (intro uniform_limit_cong)
    fix aq :: "'a \<times> 'a"
    assume "aq \<in> A"
    then obtain a q where [simp]: "aq = (a, q)" and aq: "(a, q) \<in> A"
      by (cases aq) auto
    from aq and assms have q: "norm q < 1"
      by auto
    have "(\<lambda>n. case aq of (a, q) \<Rightarrow> P n a q) \<longlonglongrightarrow> g aq"
      by (rule tendsto_uniform_limitI[OF g]) fact
    hence "(\<lambda>n. case aq of (a, q) \<Rightarrow> P (Suc n) a q) \<longlonglongrightarrow> g aq"
      by (rule filterlim_compose) (rule filterlim_Suc)
    moreover have "(\<lambda>n. case aq of (a, q) \<Rightarrow> P (Suc n) a q) \<longlonglongrightarrow> qpochhammer_inf a q"
      using convergent_prod_LIMSEQ[OF convergent_qpochhammer_inf[of q a]] aq q
      unfolding P_def lessThan_Suc_atMost
      by (simp add: qpochhammer_inf_def)
    ultimately show "g aq = (case aq of (a, q) \<Rightarrow> qpochhammer_inf a q)"
      using tendsto_unique by force
  qed auto
  finally show ?thesis .
qed

lemma continuous_on_qpochhammer_inf [continuous_intros]:
  fixes a q :: "'b :: topological_space \<Rightarrow> 'a"
  assumes [continuous_intros]: "continuous_on A a" "continuous_on A q"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "continuous_on A (\<lambda>x. qpochhammer_inf (a x) (q x))"
proof -
  have *: "continuous_on (cball 0 ra \<times> cball 0 rq) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
    if r: "0 \<le> ra" "0 \<le> rq" "rq < 1" for ra rq :: real
  proof (rule uniform_limit_theorem)
    show "uniform_limit (cball 0 ra \<times> cball 0 rq) (\<lambda>n (a,q). P n a q)
            (\<lambda>(a,q). qpochhammer_inf a q) at_top"
      by (rule uniform_limit_qpochhammer_inf) (use r in \<open>auto simp: compact_Times\<close>)
  qed (auto intro!: always_eventually intro!: continuous_intros simp: P_def case_prod_unfold)

  have **: "isCont (\<lambda>(a,q). qpochhammer_inf a q) (a, q)" if q: "norm q < 1" for a q :: 'a
  proof -
    obtain R where R: "norm q < R" "R < 1"
      using dense q by blast
    with norm_ge_zero[of q] have "R \<ge> 0"
      by linarith
    have "continuous_on (cball 0 (norm a + 1) \<times> cball 0 R) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
      by (rule *) (use R \<open>R \<ge> 0\<close> in auto)
    hence "continuous_on (ball 0 (norm a + 1) \<times> ball 0 R) (\<lambda>(a,q). qpochhammer_inf a q :: 'a)"
      by (rule continuous_on_subset) auto
    moreover have "(a, q) \<in> ball 0 (norm a + 1) \<times> ball 0 R"
      using q R by auto
    ultimately show ?thesis
      by (subst (asm) continuous_on_eq_continuous_at) (auto simp: open_Times)
  qed
  hence ***: "continuous_on ((\<lambda>x. (a x, q x)) ` A) (\<lambda>(a,q). qpochhammer_inf a q)"
    using assms(3) by (intro continuous_at_imp_continuous_on) auto
  have "continuous_on A ((\<lambda>(a,q). qpochhammer_inf a q) \<circ> (\<lambda>x. (a x, q x)))"
    by (rule continuous_on_compose[OF _ ***]) (intro continuous_intros)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_qpochhammer_inf [continuous_intros]:
  fixes a q :: "'b :: t2_space \<Rightarrow> 'a"
  assumes "continuous (at x within A) a" "continuous (at x within A) q" "norm (q x) < 1"
  shows   "continuous (at x within A) (\<lambda>x. qpochhammer_inf (a x) (q x))"
proof -
  have "continuous_on (UNIV \<times> ball 0 1) (\<lambda>x. qpochhammer_inf (fst x) (snd x) :: 'a)"
    by (intro continuous_intros) auto
  moreover have "(a x, q x) \<in> UNIV \<times> ball 0 1"
    using assms(3) by auto
  ultimately have "isCont (\<lambda>x. qpochhammer_inf (fst x) (snd x)) (a x, q x)"
    by (simp add: continuous_on_eq_continuous_at open_Times)
  hence "continuous (at (a x, q x) within (\<lambda>x. (a x, q x)) ` A) 
           (\<lambda>x. qpochhammer_inf (fst x) (snd x))"
    using continuous_at_imp_continuous_at_within by blast
  hence "continuous (at x within A) ((\<lambda>x. qpochhammer_inf (fst x) (snd x)) \<circ> (\<lambda>x. (a x, q x)))"
    by (intro continuous_intros assms)
  thus ?thesis
    by (simp add: o_def)
qed

lemma tendsto_qpochhammer_inf [tendsto_intros]:
  fixes a q :: "'b \<Rightarrow> 'a"
  assumes "(a \<longlongrightarrow> a0) F" "(q \<longlongrightarrow> q0) F" "norm q0 < 1"
  shows   "((\<lambda>x. qpochhammer_inf (a x) (q x)) \<longlongrightarrow> qpochhammer_inf a0 q0) F"
proof -
  define f where "f = (\<lambda>x. qpochhammer_inf (fst x) (snd x) :: 'a)"
  have "((\<lambda>x. f (a x, q x)) \<longlongrightarrow> f (a0, q0)) F"
  proof (rule isCont_tendsto_compose[of _ f])
    show "isCont f (a0, q0)"
      using assms(3) by (auto simp: f_def intro!: continuous_intros)
    show "((\<lambda>x. (a x, q x)) \<longlongrightarrow> (a0, q0)) F "
      by (intro tendsto_intros assms)
  qed
  thus ?thesis
    by (simp add: f_def)
qed

end


context
  fixes P :: "nat \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex"
  defines "P \<equiv> (\<lambda>N a q. \<Prod>n<N. 1 - a * q ^ n)"
begin

(* TODO: openness condition is a bit annoying *)
lemma holomorphic_qpochhammer_inf [holomorphic_intros]:
  assumes [holomorphic_intros]: "a holomorphic_on A" "q holomorphic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1" "open A"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) holomorphic_on A"
proof (rule holomorphic_uniform_sequence)
  fix x assume x: "x \<in> A"
  then obtain r where r: "r > 0" "cball x r \<subseteq> A"
    using \<open>open A\<close> unfolding open_contains_cball by blast
  have *: "compact ((\<lambda>x. (a x, q x)) ` cball x r)" using r
    by (intro compact_continuous_image continuous_intros)
       (auto intro!: holomorphic_on_imp_continuous_on[OF holomorphic_on_subset] holomorphic_intros)
  have "uniform_limit ((\<lambda>x. (a x, q x)) ` cball x r) (\<lambda>n (a,q). P n a q) (\<lambda>(a,q). qpochhammer_inf a q) at_top"
    unfolding P_def
    by (rule uniform_limit_qpochhammer_inf[OF *]) (use r assms(3) in \<open>auto simp: compact_Times\<close>)
  hence "uniform_limit (cball x r) (\<lambda>n x. case (a x, q x) of (a, q) \<Rightarrow> P n a q)
           (\<lambda>x. case (a x, q x) of (a, q) \<Rightarrow> qpochhammer_inf a q) at_top"
    by (rule uniform_limit_compose) auto
  thus "\<exists>d>0. cball x d \<subseteq> A \<and> uniform_limit (cball x d)
            (\<lambda>n x. case (a x, q x) of (a, q) \<Rightarrow> P n a q)
            (\<lambda>x. qpochhammer_inf (a x) (q x)) sequentially"
    using r by fast
qed (use \<open>open A\<close> in \<open>auto intro!: holomorphic_intros simp: P_def\<close>)

lemma analytic_qpochhammer_inf [analytic_intros]:
  assumes [analytic_intros]: "a analytic_on A" "q analytic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) analytic_on A"
proof -
  from assms(1) obtain A1 where A1: "open A1" "A \<subseteq> A1" "a holomorphic_on A1"
    by (auto simp: analytic_on_holomorphic)
  from assms(2) obtain A2 where A2: "open A2" "A \<subseteq> A2" "q holomorphic_on A2"
    by (auto simp: analytic_on_holomorphic)
  have "continuous_on A2 q"
    by (rule holomorphic_on_imp_continuous_on) fact
  hence "open (q -` ball 0 1 \<inter> A2)"
    using A2 by (subst (asm) continuous_on_open_vimage) auto
  define A' where "A' = (q -` ball 0 1 \<inter> A2) \<inter> A1"
  have "open A'"
    unfolding A'_def by (rule open_Int) fact+

  note [holomorphic_intros] = holomorphic_on_subset[OF A1(3)] holomorphic_on_subset[OF A2(3)]
  have "(\<lambda>x. qpochhammer_inf (a x) (q x)) holomorphic_on A'"
    using \<open>open A'\<close> by (intro holomorphic_intros) (auto simp: A'_def)
  moreover have "A \<subseteq> A'"
    using A1(2) A2(2) assms(3) unfolding A'_def by auto
  ultimately show ?thesis
    using analytic_on_holomorphic \<open>open A'\<close> by blast
qed  

lemma meromorphic_qpochhammer_inf [meromorphic_intros]:
  assumes [analytic_intros]: "a analytic_on A" "q analytic_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (q x) < 1"
  shows   "(\<lambda>x. qpochhammer_inf (a x) (q x)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) (use assms(3) in \<open>auto intro!: analytic_intros\<close>)

end


subsection \<open>Euler's function\<close>

definition euler_phi :: "'a :: {real_normed_field, banach, heine_borel} \<Rightarrow> 'a" where
  "euler_phi q = qpochhammer_inf q q"

lemma euler_phi_0 [simp]: "euler_phi 0 = 1"
  by (simp add: euler_phi_def)

lemma abs_convergent_euler_phi:
  assumes "(q :: 'a :: real_normed_div_algebra) \<in> ball 0 1"
  shows   "abs_convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
proof (rule summable_imp_abs_convergent_prod)
  show "summable (\<lambda>n. norm (1 - q ^ Suc n - 1))"
    using assms by (subst summable_Suc_iff) (auto simp: norm_power)
qed

lemma convergent_euler_phi:
  assumes "(q :: 'a :: {real_normed_field, banach}) \<in> ball 0 1"
  shows   "convergent_prod (\<lambda>n. 1 - q ^ Suc n)"
  using abs_convergent_euler_phi[OF assms] abs_convergent_prod_imp_convergent_prod by blast

lemma has_prod_euler_phi:
  "q \<in> ball 0 1 \<Longrightarrow> (\<lambda>n. 1 - q ^ Suc n) has_prod euler_phi q"
  using has_prod_qpochhammer_inf[of q q] by (simp add: euler_phi_def)

lemma euler_phi_nonzero [simp]:
  assumes x: "x \<in> ball 0 1"
  shows   "euler_phi x \<noteq> 0"
  using assms by (simp add: euler_phi_def qpochhammer_inf_nonzero)

lemma holomorphic_euler_phi [holomorphic_intros]:
  assumes [holomorphic_intros]: "f holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) holomorphic_on A"
proof -
  have *: "euler_phi holomorphic_on ball 0 1"
    unfolding euler_phi_def by (intro holomorphic_intros) auto
  show ?thesis
    by (rule holomorphic_on_compose_gen[OF assms(1) *, unfolded o_def]) (use assms(2) in auto)
qed

lemma analytic_euler_phi [analytic_intros]:
  assumes [analytic_intros]: "f analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. euler_phi (f z)) analytic_on A"
  using assms(2) by (auto intro!: analytic_intros simp: euler_phi_def)

lemma meromorphic_on_euler_phi [meromorphic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1) \<Longrightarrow> (\<lambda>z. euler_phi (f z)) meromorphic_on A"
  unfolding euler_phi_def by (intro meromorphic_intros)

lemma continuous_on_euler_phi [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "continuous_on A (\<lambda>z. euler_phi (f z))"
  using assms unfolding euler_phi_def by (intro continuous_intros) auto

lemma tendsto_euler_phi [tendsto_intros]:
  assumes [tendsto_intros]: "(f \<longlongrightarrow> c) F" and "norm c < 1"
  shows   "((\<lambda>x. euler_phi (f x)) \<longlongrightarrow> euler_phi c) F"
  unfolding euler_phi_def using assms by (auto intro!: tendsto_intros)

end