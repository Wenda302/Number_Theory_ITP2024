chapter \<open>Kronecker's Theorem with Applications\<close>

theory Kronecker_Theorem

imports Zeta_Function.Zeta_Function
        Library_Extras
        Elliptic_Functions (*Required for theorem 7.12 at the end*)

begin

section \<open>Dirichlet's Approximation Theorem\<close>

(*Installed in the distribution 25-09-23*)
lemma Rats_complex_of_real_iff [iff]: "complex_of_real x \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
proof -
  have "\<And>a b. \<lbrakk>0 < b; x = complex_of_int a / complex_of_int b\<rbrakk> \<Longrightarrow> x \<in> \<rat>"
    by (metis Rats_divide Rats_of_int Re_complex_of_real Re_divide_of_real of_real_of_int_eq)
  then show ?thesis
    by (auto simp: elim!: Rats_cases')
qed

(*Installed in the distribution 25-09-23*)
lemma uniform_limit_compose:
  assumes ul: "uniform_limit X g l F"  
    and cont: "uniformly_continuous_on U f"
    and g: "\<forall>\<^sub>F n in F. g n ` X \<subseteq> U" and l: "l ` X \<subseteq> U"
  shows "uniform_limit X (\<lambda>a b. f (g a b)) (f \<circ> l) F"
proof (rule uniform_limitI)
  fix \<epsilon>::real
  assume "0 < \<epsilon>" 
  then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>u v. \<lbrakk>u\<in>U; v\<in>U; dist u v < \<delta>\<rbrakk> \<Longrightarrow> dist (f u) (f v) < \<epsilon>"
    by (metis cont uniformly_continuous_on_def)
  show "\<forall>\<^sub>F n in F. \<forall>x\<in>X. dist (f (g n x)) ((f \<circ> l) x) < \<epsilon>"
    using uniform_limitD [OF ul \<open>\<delta>>0\<close>] g unfolding o_def
    by eventually_elim (use \<delta> l in blast)
qed

(*Installed in the distribution 25-09-23*)
lemma Sup_inverse_eq_inverse_Inf:
  fixes f::"'b \<Rightarrow> 'a::{conditionally_complete_linorder,linordered_field}"
  assumes "bdd_above (range f)" "L > 0" and geL: "\<And>x. f x \<ge> L"
  shows "(SUP x. 1 / f x) = 1 / (INF x. f x)"
proof (rule antisym)
  have bdd_f: "bdd_below (range f)"
    by (meson assms bdd_belowI2)
  have "Inf (range f) \<ge> L"
    by (simp add: cINF_greatest geL)
  have bdd_invf: "bdd_above (range (\<lambda>x. 1 / f x))"
  proof (rule bdd_aboveI2)
    show "\<And>x. 1 / f x \<le> 1/L"
      using assms by (auto simp: divide_simps)
  qed
  moreover have le_inverse_Inf: "1 / f x \<le> 1 / Inf (range f)" for x
  proof -
    have "Inf (range f) \<le> f x"
      by (simp add: bdd_f cInf_lower)
    then show ?thesis
      using assms \<open>L \<le> Inf (range f)\<close> by (auto simp: divide_simps)
  qed
  ultimately show *: "(SUP x. 1 / f x) \<le> 1 / Inf (range f)"
    by (auto simp: cSup_le_iff cINF_lower)
  have "1 / (SUP x. 1 / f x) \<le> f y" for y
  proof (cases "(SUP x. 1 / f x) < 0")
    case True
    with assms show ?thesis
      by (meson less_asym' order_trans linorder_not_le zero_le_divide_1_iff)
  next
    case False
    have "1 / f y \<le> (SUP x. 1 / f x)"
      by (simp add: bdd_invf cSup_upper)
    with False assms show ?thesis
    by (metis (no_types) div_by_1 divide_divide_eq_right dual_order.strict_trans1 inverse_eq_divide inverse_le_imp_le mult.left_neutral)
  qed
  then have "1 / (SUP x. 1 / f x) \<le> Inf (range f)"
    using bdd_f by (simp add: le_cInf_iff)
  moreover have "(SUP x. 1 / f x) > 0"
    using assms cSUP_upper [OF _ bdd_invf] by (meson UNIV_I less_le_trans zero_less_divide_1_iff)
  ultimately show "1 / Inf (range f) \<le> (SUP t. 1 / f t)"
    using \<open>L \<le> Inf (range f)\<close> \<open>L>0\<close> by (auto simp: field_simps)
qed 

(*Installed in the distribution 25-09-23*)
lemma Inf_inverse_eq_inverse_Sup:
  fixes f::"'b \<Rightarrow> 'a::{conditionally_complete_linorder,linordered_field}"
  assumes "bdd_above (range f)" "L > 0" and geL: "\<And>x. f x \<ge> L"
  shows  "(INF x. 1 / f x) = 1 / (SUP x. f x)"
proof -
  obtain M where "M>0" and M: "\<And>x. f x \<le> M"
    by (meson assms cSup_upper dual_order.strict_trans1 rangeI)
  have bdd: "bdd_above (range (inverse \<circ> f))"
    using assms le_imp_inverse_le by (auto simp: bdd_above_def)
  have "f x > 0" for x
    using \<open>L>0\<close> geL order_less_le_trans by blast
  then have [simp]: "1 / inverse(f x) = f x" "1 / M \<le> 1 / f x" for x
    using M \<open>M>0\<close> by (auto simp: divide_simps)
  show ?thesis
    using Sup_inverse_eq_inverse_Inf [OF bdd, of "inverse M"] \<open>M>0\<close>
    by (simp add: inverse_eq_divide)
qed


(*NOT USED*)
lemma prod_nonzero_limit_norm:
  fixes f :: "nat \<Rightarrow> 'a :: {idom, real_normed_div_algebra}"
  defines "\<pi> \<equiv> (\<lambda>n. \<Prod>i\<le>n. f i)"
  assumes lim: "\<pi> \<longlonglongrightarrow> L" and L: "L \<noteq> 0"
  obtains M where "M > 0" "\<And>n. norm (\<pi> n) > M"
proof -
  have nonzero: "f i \<noteq> 0" for i
    using assms unfolding \<pi>_def by (metis LIMSEQ_prod_0 LIMSEQ_unique)
  have nonzero': "\<pi> i \<noteq> 0" for i
    unfolding \<pi>_def by (auto simp: nonzero)

  show ?thesis
  proof -
    from lim have "(\<lambda>n. norm (\<pi> n)) \<longlonglongrightarrow> norm L"
      by (simp add: tendsto_norm)
    moreover from L have "norm L / 2 < norm L"
      by simp
    ultimately have "eventually (\<lambda>n. norm (\<pi> n) > norm L / 2) sequentially"
      by (rule order_tendstoD)
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> norm (\<pi> n) > norm L / 2"
      using eventually_sequentially by fastforce
    define M' where "M' = Min (insert (norm L) (norm ` \<pi> ` {..<N}))"
    have "M' / 2 > 0"
      using nonzero' N L by (auto simp: M'_def)
    moreover have "norm (\<pi> n) > M' / 2" for n
    proof (cases "n \<ge> N")
      case True
      have "M' / 2 \<le> norm L / 2"
        unfolding M'_def by auto
      also have "\<dots> < norm (\<pi> n)"
        using N[of n] True by auto
      finally show ?thesis .
    next
      case False
      have "M' / 2 < M'"
        using \<open>M' / 2 > 0\<close> by auto
      also have "M' \<le> norm (\<pi> n)"
        using False by (auto simp: M'_def)
      finally show ?thesis .
    qed
    thus ?thesis
      using that \<open>M' / 2 > 0\<close> by blast
  qed
qed

(*SIMILAR TO convergent_prod_imp_Cauchy, proved below. But neither "obviously" implies the other*)
(*NOT USED*)
lemma raw_convergent_prod_imp_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,complete_space}"
  defines "\<pi> \<equiv> (\<lambda>n. \<Prod>i\<le>n. f i)"
  assumes lim: "\<pi> \<longlonglongrightarrow> L" and L: "L \<noteq> 0" and \<epsilon>: "\<epsilon> > 0"
  obtains N where "\<And>m n. N \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> dist (\<Prod>i\<in>{m..n}. f i) 1 < \<epsilon>"
proof -
  have nonzero: "f i \<noteq> 0" for i
    using assms unfolding \<pi>_def by (metis LIMSEQ_prod_0 LIMSEQ_unique)
  have nonzero': "\<pi> i \<noteq> 0" for i
    unfolding \<pi>_def by (auto simp: nonzero)

  from lim obtain M where "M > 0" and M: "\<And>n. norm (\<pi> n) > M"
    using prod_nonzero_limit_norm assms by blast

  from lim have "convergent \<pi>"
    by (auto simp: convergent_def)
  hence "Cauchy \<pi>"
    by (rule convergent_Cauchy)
  moreover from \<open>M > 0\<close> and \<epsilon> have "\<epsilon> * M > 0"
    by simp
  ultimately obtain N
    where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> dist (\<pi> m) (\<pi> n) < \<epsilon> * M"
    unfolding Cauchy_def by fast

  show ?thesis
  proof 
    fix m n :: nat
    assume mn: "Suc N \<le> m" "m \<le> n"
    have "dist (\<pi> (m - 1)) (\<pi> n) < \<epsilon> * M"
      by (rule N) (use mn in auto)
    also have "\<pi> n = \<pi> (m - 1) * (\<Prod>i\<in>{m..n}. f i)"
    proof -
      have "{..n} = {..m-1} \<union> {m..n}"
        using mn by auto
      also have "(\<Prod>i\<in>\<dots>. f i) = \<pi> (m - 1) * (\<Prod>i\<in>{m..n}. f i)"
        unfolding \<pi>_def using mn by (subst prod.union_disjoint) auto
      finally show ?thesis
        by (simp add: \<pi>_def)
    qed
    also have "dist (\<pi> (m - 1)) (\<pi> (m - 1) * prod f {m..n}) =
               norm (\<pi> (m - 1)) * dist (prod f {m..n}) 1"
      by (simp add: dist_norm ring_distribs norm_minus_commute flip: norm_mult)
    finally have "dist (prod f {m..n}) 1 < \<epsilon> * (M / norm (\<pi> (m - 1)))"
      by (auto simp: field_simps nonzero')
    also have "\<dots> < \<epsilon> * 1"
      using M[of "m - 1"] \<epsilon>
      by (intro mult_strict_left_mono) (auto simp: field_simps nonzero')
    finally show "dist (\<Prod>i\<in>{m..n}. f i) 1 < \<epsilon>"
      by simp
  qed
qed

(*NOT USED*)
lemma Cauchy_imp_convergent:
  fixes f :: "nat \<Rightarrow> 'a :: {idom, real_normed_div_algebra, banach}"
  defines "\<pi> \<equiv> (\<lambda>n. \<Prod>i\<le>n. f i)"
  assumes N: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>m n. N \<le> m \<longrightarrow> m \<le> n \<longrightarrow> dist (\<Prod>i\<in>{m..n}. f i) 1 < \<epsilon>"
  shows "convergent \<pi>"
proof (cases "\<exists>i. f i = 0")
  case True
  thus ?thesis
    unfolding \<pi>_def using LIMSEQ_prod_0 convergent_def by blast
next
  case False
  hence nonzero: "f i \<noteq> 0" for i
    by auto
  hence nonzero': "\<pi> i \<noteq> 0" for i
    by (auto simp: \<pi>_def)

  have \<pi>_split: "\<pi> n = \<pi> m * (\<Prod>i=m+1..n. f i)" if "m \<le> n" for m n
  proof -
    have "\<pi> n = (\<Prod>i\<in>{..n}. f i)"
      by (simp add: \<pi>_def)
    also have "{..n} = {..m} \<union> {m+1..n}"
      using \<open>m \<le> n\<close> by auto
    also have "(\<Prod>i\<in>\<dots>. f i) = \<pi> m * (\<Prod>i=m+1..n. f i)"
      by (subst prod.union_disjoint) (auto simp: \<pi>_def)
    finally show ?thesis .
  qed

  obtain M where M: "M > 0" "\<And>n. norm (\<pi> n) \<le> M"
  proof -
    obtain N where N: "\<And>m n. N \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> dist (\<Prod>i=m..n. f i) 1 < 1 / 2"
      using N[of "1 / 2"] by auto
    define M where "M = Max (insert (3 / 2 * norm (\<pi> N)) (norm ` \<pi> ` {..N}))"
    have "0 < 3 / 2 * norm (\<pi> N)"
      by (simp add: nonzero')
    also have "\<dots> \<le> M"
      unfolding M_def by (intro Max.coboundedI) auto
    finally have "M > 0" .

    have "norm (\<pi> n) \<le> M" for n
    proof (cases "n > N")
      case False
      thus ?thesis
        unfolding M_def by (intro Max.coboundedI) (auto simp: not_less)
    next
      case True
      hence "\<pi> n = \<pi> N * (\<Prod>i=N+1..n. f i)"
        by (intro \<pi>_split) auto
      also have "norm \<dots> = norm (\<pi> N) * norm (\<Prod>i=N+1..n. f i)"
        by (simp add: norm_mult)
      also have "\<dots> \<le> norm (\<pi> N) * (3 / 2)"
      proof -
        have "dist (\<Prod>i=N+1..n. f i) 0 \<le> dist (\<Prod>i=N+1..n. f i) 1 + dist (0 :: 'a) 1"
          using dist_triangle2 by blast
        also have "\<dots> \<le> 3 / 2"
          using N[of "N+1" n] True by simp
        finally show ?thesis
          by (intro mult_left_mono) auto
      qed
      also have "\<dots> = 3 / 2 * norm (\<pi> N)"
        by simp
      also have "\<dots> \<le> M"
        unfolding M_def by (intro Max.coboundedI) auto
      finally show "norm (\<pi> n) \<le> M" .
    qed
    thus ?thesis
      using that \<open>M > 0\<close> by blast
  qed

  have "Cauchy \<pi>"
    unfolding Cauchy_altdef
  proof safe
    fix \<epsilon> :: real
    assume \<epsilon>: "\<epsilon> > 0"

    define \<epsilon>' where "\<epsilon>' = min (1 / 2) (\<epsilon> / M)"
    have \<epsilon>': "\<epsilon>' > 0"
      using \<epsilon> M by (auto simp: \<epsilon>'_def)
    then obtain N where N: "\<And>m n. N \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> dist (\<Prod>i=m..n. f i) 1 < \<epsilon>'"
      using N by blast    

    show "\<exists>N. \<forall>m\<ge>N. \<forall>n>m. dist (\<pi> m) (\<pi> n) < \<epsilon>"
    proof (rule exI[of _ N], safe)
      fix m n :: nat
      assume mn: "N \<le> m" "m < n"

      have "dist (f m) 1 < \<epsilon>'"
        using N[of m m] mn by auto
      also have "\<dots> \<le> 1 / 2"
        unfolding \<epsilon>'_def by linarith
      finally have fm_aux: "dist (f m) 1 < 1 / 2" .

      have [simp]: "f m \<noteq> 0"
        using fm_aux by auto

      have "dist (f m) 0 \<le> dist (f m) 1 + dist (0 :: 'a) 1"
        by (metis dist_triangle2)
      also have "\<dots> < 3 / 2"
        using fm_aux by simp
      finally have fm: "norm (f m) \<le> 3 / 2"
        by simp

      have "dist (\<Prod>i=m+1..n. f i) 1 < \<epsilon>'"
        by (rule N) (use mn in auto)
      also have "\<epsilon>' \<le> \<epsilon> / M"
        by (simp add: \<epsilon>'_def)
      also have "\<dots> \<le> \<epsilon> / norm (\<pi> m)"
        using \<epsilon> fm M(1) M(2)[of m] mn
        by (intro divide_left_mono) (auto intro!: mult_pos_pos simp: nonzero')
      finally have "norm (\<pi> m) * dist (prod f {m+1..n}) 1 < \<epsilon>"
        by (simp add: field_simps nonzero')
      also have "norm (\<pi> m) * dist (prod f {m+1..n}) 1 = dist (\<pi> m) (\<pi> m * prod f {m+1..n})"
        by (simp add: norm_minus_commute dist_norm ring_distribs flip: norm_mult)
      also have "\<pi> m * prod f {m+1..n} = \<pi> n"
        by (subst (2) \<pi>_split[of m]) (use mn in auto)
      finally show "dist (\<pi> m) (\<pi> n) < \<epsilon>" .
    qed
  qed
  thus ?thesis
    by (simp add: Cauchy_convergent_iff)
qed


(*NOT USED. Is it worth trying to replace that sort by {idom, real_normed_div_algebra, banach}?*)
lemma convergent_prod_imp_Cauchy:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,complete_space}"
  assumes f: "convergent_prod f" and nz: "\<And>n. f n \<noteq> 0" and "\<epsilon> > 0"
  obtains n0 where "\<And>n k. \<lbrakk>k>n; n \<ge> n0\<rbrakk> \<Longrightarrow> dist (prod f {n<..k}) 1 < \<epsilon>"
proof -
  define \<pi> where "\<pi> \<equiv> \<lambda>n. \<Prod>i\<le>n. f i"
  have \<pi>nz: "\<pi> n \<noteq> 0" for n
    by (simp add: \<pi>_def assms)
  obtain p where \<pi>: "\<pi> \<longlonglongrightarrow> p" and "p \<noteq> 0"
    unfolding \<pi>_def by (metis f nz convergent_prod_iff_nz_lim)
  then have Cau: "Cauchy \<pi>"
    using LIMSEQ_imp_Cauchy by blast
  have np: "(norm \<circ> \<pi>) \<longlonglongrightarrow> norm p"
    by (simp add: \<pi> o_def tendsto_norm)
  then obtain m where E: "\<And>n. n \<ge> m \<Longrightarrow> dist ((norm \<circ> \<pi>) n) (norm p) < norm p / 3"
    using \<open>p \<noteq> 0\<close> metric_LIMSEQ_D [OF np, of "norm p / 3"]
    by (meson divide_pos_pos zero_less_norm_iff zero_less_numeral)
  have "norm (\<pi> n) > norm p / 3" if "n \<ge> m" for n
    using E [OF that] by (simp only: dist_real_def o_def)
  then obtain M where "M>0" and M: "\<And>n. n \<ge> m \<Longrightarrow> norm (\<pi> n) > M"
    by (metis divide_pos_pos \<open>p \<noteq> 0\<close> zero_less_norm_iff zero_less_numeral)
  obtain m0 where m0: "\<And>n k. \<lbrakk>n \<ge> m0; k>n\<rbrakk> \<Longrightarrow> norm (\<pi> k - \<pi> n) < \<epsilon> * M"
    by (meson Cau Cauchy_iff \<open>0 < M\<close> \<open>0 < \<epsilon>\<close> nat_less_le order_trans zero_less_mult_iff)
  show thesis
  proof 
    fix n k
    assume n: "n \<ge> max m m0" "k > n"
    then have "norm (\<pi> k - \<pi> n) / norm (\<pi> n) < \<epsilon>"
      by (smt (verit, best) M m0 \<open>0 < M\<close> \<open>0 < \<epsilon>\<close> divide_less_eq mult_mono max.bounded_iff)
    moreover have "\<pi> k / \<pi> n = prod f {n<..k}"
      using \<open>k > n\<close>
      apply (simp add: \<pi>_def less_iff_Suc_add divide_simps assms flip: atLeast0AtMost atLeastSucAtMost_greaterThanAtMost)
      by (metis add_Suc_right  mult.commute  prod.ub_add_nat Suc_eq_plus1 zero_le)
    ultimately show "dist (prod f {n<..k}) 1 < \<epsilon>"
      by (metis \<pi>nz dist_divide_right dist_norm div_self)
  qed
qed



(*Added to DISTRIBUTION 26-10-2022*)
lemma map_equality_iff:
  "map f xs = map g ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i<length ys. f (xs!i) = g (ys!i))"
  by (fastforce simp: list_eq_iff_nth_eq)


section \<open>Dirichlet's Approximation Theorem\<close>

text \<open>Simultaneous version. From Hardy and Wright, An Introduction to the Theory of Numbers, page 170.\<close>
theorem Dirichlet_approx_simult:
  fixes \<theta> :: "nat \<Rightarrow> real" and N n :: nat
  assumes "N > 0" 
  obtains q p where "0<q" "q \<le> int (N^n)" 
    and "\<And>i. i<n \<Longrightarrow> \<bar>of_int q * \<theta> i - of_int(p i)\<bar> < 1/N"
proof -
  have lessN: "nat \<lfloor>x * real N\<rfloor> < N" if "0 \<le> x" "x < 1" for x
  proof -
    have "\<lfloor>x * real N\<rfloor> < N"
      using that by (simp add: assms floor_less_iff)
    with assms show ?thesis by linarith
  qed
  define interv where "interv \<equiv> \<lambda>k. {real k/N..< Suc k/N}"
  define fracs where "fracs \<equiv> \<lambda>k. map (\<lambda>i. frac (real k * \<theta> i)) [0..<n]"
  define X where "X \<equiv> fracs ` {..N^n}"
  define Y where "Y \<equiv> set (List.n_lists n (map interv [0..<N]))"
  have interv_iff: "interv k = interv k' \<longleftrightarrow> k=k'" for k k'
    using assms by (auto simp: interv_def Ico_eq_Ico divide_strict_right_mono)
  have in_interv: "x \<in> interv (nat \<lfloor>x * real N\<rfloor>)" if "x\<ge>0" for x
    using that assms by (simp add: interv_def divide_simps) linarith
  have False 
    if non: "\<forall>a b. b \<le> N^n \<longrightarrow> a < b \<longrightarrow> \<not>(\<forall>i<n. \<bar>frac (real b * \<theta> i) - frac (real a * \<theta> i)\<bar> < 1/N)"
  proof -
    have "inj_on (\<lambda>k. map (\<lambda>i. frac (k * \<theta> i)) [0..<n]) {..N^n}"
      using that assms by (intro linorder_inj_onI) fastforce+
    then have caX: "card X = Suc (N^n)"
      by (simp add: X_def fracs_def card_image)
    have caY: "card Y \<le> N^n"
      by (metis Y_def card_length diff_zero length_map length_n_lists length_upt)
    define f where "f \<equiv> \<lambda>l. map (\<lambda>x. interv (nat \<lfloor>x * real N\<rfloor>)) l"
    have "f ` X \<subseteq> Y"
      by (auto simp: f_def Y_def X_def fracs_def o_def set_n_lists frac_lt_1 lessN)
    then have "\<not> inj_on f X"
      using Y_def caX caY card_inj_on_le not_less_eq_eq by fastforce
    then obtain x x' where "x\<noteq>x'" "x \<in> X" "x' \<in> X" and eq: "f x = f x'"
      by (auto simp: inj_on_def)
    then obtain c c' where c: "c \<noteq> c'" "c \<le> N^n" "c' \<le> N^n" 
            and xeq: "x = fracs c" and xeq': "x' = fracs c'"
      unfolding X_def by (metis atMost_iff image_iff)
    have [simp]: "length x' = n"
      by (auto simp: xeq' fracs_def)
    have ge0: "x'!i \<ge> 0" if "i<n" for i
      using that \<open>x' \<in> X\<close> by (auto simp: X_def fracs_def)
    have "f x \<in> Y"
      using \<open>f ` X \<subseteq> Y\<close> \<open>x \<in> X\<close> by blast
    define k where "k \<equiv> map (\<lambda>r. nat \<lfloor>r * real N\<rfloor>) x"
    have "\<bar>frac (real c * \<theta> i) - frac (real c' * \<theta> i)\<bar> < 1/N" if "i < n" for i
    proof -
      have k: "x!i \<in> interv(k!i)" 
        using \<open>i<n\<close> assms by (auto simp: divide_simps k_def interv_def xeq fracs_def) linarith
      then have k': "x'!i \<in> interv(k!i)" 
        using \<open>i<n\<close> eq assms ge0[OF \<open>i<n\<close>]
        by (auto simp: k_def f_def divide_simps map_equality_iff in_interv interv_iff)
      with assms k show ?thesis
        using \<open>i<n\<close> by (auto simp add: xeq xeq' fracs_def interv_def add_divide_distrib)
    qed
    then show False
      by (metis c non nat_neq_iff abs_minus_commute)
  qed
  then obtain a b where "a<b" "b \<le> N^n" and *: "\<And>i. i<n \<Longrightarrow> \<bar>frac (real b * \<theta> i) - frac (real a * \<theta> i)\<bar> < 1/N"
    by blast
  let ?k = "b-a"
  let ?h = "\<lambda>i. \<lfloor>b * \<theta> i\<rfloor> - \<lfloor>a * \<theta> i\<rfloor>"
  show ?thesis
  proof
    fix i
    assume "i<n"
    have "frac (b * \<theta> i) - frac (a * \<theta> i) = ?k * \<theta> i - ?h i"
      using \<open>a < b\<close> by (simp add: frac_def left_diff_distrib' of_nat_diff)
    then show "\<bar>of_int ?k * \<theta> i - ?h i\<bar> < 1/N"
      by (metis "*" \<open>i < n\<close> of_int_of_nat_eq)
  qed (use \<open>a < b\<close> \<open>b \<le> N^n\<close> in auto)
qed


text \<open>Theorem 7.1\<close>
corollary Dirichlet_approx:
  fixes \<theta>:: real and N:: nat
  assumes "N > 0" 
  obtains h k where "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
  by (rule Dirichlet_approx_simult [OF assms, where n=1 and \<theta>="\<lambda>_. \<theta>"]) auto


text \<open>Theorem 7.2\<close>
corollary Dirichlet_approx_coprime:
  fixes \<theta>:: real and N:: nat
  assumes "N > 0" 
  obtains h k where "coprime h k" "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
proof -
  obtain h' k' where k': "0 < k'" "k' \<le> int N" and *: "\<bar>of_int k' * \<theta> - of_int h'\<bar> < 1/N"
    by (meson Dirichlet_approx assms)
  let ?d = "gcd h' k'"
  show thesis
  proof (cases "?d = 1")
    case True
    with k' * that show ?thesis by auto
  next
    case False
    then have 1: "?d > 1"
      by (smt (verit, ccfv_threshold) \<open>k'>0\<close> gcd_pos_int)
    let ?k = "k' div ?d"
    let ?h = "h' div ?d"
    show ?thesis
    proof
      show "coprime (?h::int) ?k"
        by (metis "1" div_gcd_coprime gcd_eq_0_iff not_one_less_zero)
      show k0: "0 < ?k"
        using \<open>k'>0\<close> pos_imp_zdiv_pos_iff by force
      show "?k \<le> int N"
        using k' "1" int_div_less_self by fastforce
      have "\<bar>\<theta> - of_int ?h / of_int ?k\<bar> = \<bar>\<theta> - of_int h' / of_int k'\<bar>"
        by (simp add: real_of_int_div)
      also have "\<dots> < 1 / of_int (N * k')"
        using k' * by (simp add: field_simps)
      also have "\<dots> < 1 / of_int (N * ?k)"
        using assms \<open>k'>0\<close> k0 1
        by (simp add: frac_less2 int_div_less_self)
      finally show "\<bar>of_int ?k * \<theta> - of_int ?h\<bar> < 1 / real N"
        using k0 k' by (simp add: field_simps)
    qed
  qed
qed

definition approx_set :: "real \<Rightarrow> (int \<times> int) set"
  where "approx_set \<theta> \<equiv> 
     {(h, k) | h k::int. k > 0 \<and> coprime h k \<and> \<bar>\<theta> - of_int h / of_int k\<bar> < 1/k\<^sup>2}" 
  for \<theta>::real

text \<open>Theorem 7.3\<close>
lemma approx_set_nonempty: "approx_set \<theta> \<noteq> {}"
proof -
  have "\<bar>\<theta> - of_int \<lfloor>\<theta>\<rfloor> / of_int 1\<bar> < 1 / (of_int 1)\<^sup>2"
    by simp linarith
  then have "(\<lfloor>\<theta>\<rfloor>, 1) \<in> approx_set \<theta>"
    by (auto simp: approx_set_def)
  then show ?thesis
    by blast
qed


text \<open>Theorem 7.4(c)\<close>
theorem infinite_approx_set:
  assumes "infinite (approx_set \<theta>)"
  shows  "\<exists>h k. (h,k) \<in> approx_set \<theta> \<and> k > K"
proof (rule ccontr, simp add: not_less)
  assume Kb [rule_format]: "\<forall>h k. (h, k) \<in> approx_set \<theta> \<longrightarrow> k \<le> K"
  define H where "H \<equiv> 1 + \<bar>K * \<theta>\<bar>"
  have k0:  "k > 0" if "(h,k) \<in> approx_set \<theta>" for h k
    using approx_set_def that by blast
  have Hb: "of_int \<bar>h\<bar> < H" if "(h,k) \<in> approx_set \<theta>" for h k
  proof -
    have *: "\<bar>k * \<theta> - h\<bar> < 1" 
    proof -
      have "\<bar>k * \<theta> - h\<bar> < 1 / k"
        using that by (auto simp: field_simps approx_set_def eval_nat_numeral)
      also have "\<dots> \<le> 1"
        using divide_le_eq_1 by fastforce
      finally show ?thesis .
    qed
    have "k > 0"
      using approx_set_def that by blast
    have "of_int \<bar>h\<bar> \<le> \<bar>k * \<theta> - h\<bar> + \<bar>k * \<theta>\<bar>"
      by force
    also have "\<dots> < 1 + \<bar>k * \<theta>\<bar>"
      using * that by simp
    also have "\<dots> \<le> H"
      using Kb [OF that] \<open>k>0\<close> by (auto simp add: H_def abs_if mult_right_mono mult_less_0_iff)
    finally show ?thesis .
  qed
  have "approx_set \<theta> \<subseteq> {-(ceiling H)..ceiling H} \<times> {0..K}"
    using Hb Kb k0 
    apply (simp add: subset_iff)
    by (smt (verit, best) ceiling_add_of_int less_ceiling_iff)
  then have "finite (approx_set \<theta>)"
    by (meson finite_SigmaI finite_atLeastAtMost_int finite_subset)
  then show False
    using assms by blast
qed

text \<open>Theorem 7.4(b,d)\<close>
theorem rational_iff_finite_approx_set:
  shows "\<theta> \<in> \<rat> \<longleftrightarrow> finite (approx_set \<theta>)"
proof
  assume "\<theta> \<in> \<rat>"
  then obtain a b where eq: "\<theta> = of_int a / of_int b" and "b>0" and "coprime a b"
    by (meson Rats_cases')
  then have ab: "(a,b) \<in> approx_set \<theta>"
    by (auto simp: approx_set_def)
  show "finite (approx_set \<theta>)"
  proof (rule ccontr)
    assume "infinite (approx_set \<theta>)"
    then obtain h k where "(h,k) \<in> approx_set \<theta>" "k > b" "k>0"
      using infinite_approx_set by (smt (verit, best))
    then have "coprime h k" and hk: "\<bar>a/b - h/k\<bar> < 1 / (of_int k)\<^sup>2"
      by (auto simp: approx_set_def eq)
    have False if "a * k = h * b"
    proof -
      have "b dvd k"
        using that \<open>coprime a b\<close>
        by (metis coprime_commute coprime_dvd_mult_right_iff dvd_triv_right)
      then obtain d where "k = b * d"
        by (metis dvd_def)
      then have "h = a * d"
        using \<open>0 < b\<close> that by force
      then show False
        using \<open>0 < b\<close> \<open>b < k\<close> \<open>coprime h k\<close> \<open>k = b * d\<close> by auto
    qed
    then have 0: "0 < \<bar>a*k - b*h\<bar>"
      by auto
    have "\<bar>a*k - b*h\<bar> < b/k"
      using \<open>k>0\<close> \<open>b>0\<close> hk by (simp add: field_simps eval_nat_numeral)
    also have "\<dots> < 1"
      by (simp add: \<open>0 < k\<close> \<open>b < k\<close>)
    finally show False
      using 0 by linarith
  qed
next
  assume fin: "finite (approx_set \<theta>)"
  show "\<theta> \<in> \<rat>"
  proof (rule ccontr)
    assume irr: "\<theta> \<notin> \<rat>"
    define A where "A \<equiv> ((\<lambda>(h,k). \<bar>\<theta> - h/k\<bar>) ` approx_set \<theta>)"
    let ?\<alpha> = "Min A"
    have "0 \<notin> A"
      using irr by (auto simp: A_def approx_set_def)
    moreover have "\<forall>x\<in>A. x\<ge>0" and A: "finite A" "A \<noteq> {}"
      using approx_set_nonempty by (auto simp: A_def fin)
    ultimately have \<alpha>: "?\<alpha> > 0"
      using Min_in by force 
    then obtain N where N: "real N > 1 / ?\<alpha>"
      using reals_Archimedean2 by blast
    have "0 < 1 / ?\<alpha>"
      using \<alpha> by auto
    also have "\<dots> < real N"
      by (fact N)
    finally have "N > 0"
      by simp
    from N have "1/N < ?\<alpha>"
      by (simp add: \<alpha> divide_less_eq mult.commute)
    then obtain h k where "coprime h k" "0 < k" "k \<le> int N" "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
      by (metis Dirichlet_approx_coprime \<alpha> N divide_less_0_1_iff less_le not_less_iff_gr_or_eq of_nat_0_le_iff of_nat_le_iff of_nat_0)
    then have \<section>: "\<bar>\<theta> - h/k\<bar> < 1 / (k*N)"
      by (simp add: field_simps)
    also have "\<dots> \<le> 1/k\<^sup>2"
      using \<open>k \<le> int N\<close> by (simp add: eval_nat_numeral divide_simps)
    finally have hk_in: "(h,k) \<in> approx_set \<theta>"
      using \<open>0 < k\<close> \<open>coprime h k\<close> by (auto simp: approx_set_def)
    then have "\<bar>\<theta> - h/k\<bar> \<in> A"
      by (auto simp: A_def)
    moreover have "1 / real_of_int (k * int N) < ?\<alpha>"
    proof -
      have "1 / real_of_int (k * int N) = 1 / real N / of_int k"
        by simp
      also have "\<dots> < ?\<alpha> / of_int k"
        using \<open>k > 0\<close> \<alpha> \<open>N > 0\<close> N by (intro divide_strict_right_mono) (auto simp: field_simps)
      also have "\<dots> \<le> ?\<alpha> / 1"
        using \<alpha> \<open>k > 0\<close> by (intro divide_left_mono) auto
      finally show ?thesis
        by simp
    qed
    ultimately show False using A \<section> by auto
  qed
qed


text \<open>No formalisation of Liouville's Approximation Theorem because this is already in the AFP
as Liouville\_Numbers. Apostol's Theorem 7.5 should be exactly the theorem
liouville\_irrational\_algebraic. There is a minor discrepancy in the definition 
of "Liouville number" between Apostol and Eberl: he requires the denominator to be 
positive, while Eberl require it to exceed 1.\<close>

section \<open>Kronecker's Approximation Theorem: the One-dimensional Case\<close>

lemma frac_int_mult: 
  assumes "m > 0" and le: "1-frac r \<le> 1/m"
  shows "1 - frac (of_int m * r) = m * (1 - frac r)" 
proof -
  have "frac (of_int m * r) = 1 - m * (1 - frac r)"
  proof (subst frac_unique_iff, intro conjI)
    show "of_int m * r - (1 - of_int m * (1 - frac r)) \<in> \<int>"
      by (simp add: algebra_simps frac_def)
  qed (use assms in \<open>auto simp: divide_simps mult_ac frac_lt_1\<close>)
  then show ?thesis
    by simp
qed

text \<open>Concrete statement of Theorem 7.7, and the real proof\<close>
theorem Kronecker_approx_1_explicit:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>" and \<alpha>: "0 \<le> \<alpha>" "\<alpha> \<le> 1" and "\<epsilon> > 0"
  obtains k where "k>0" "\<bar>frac(real k * \<theta>) - \<alpha>\<bar> < \<epsilon>"  
proof -
  obtain N::nat where "1/N < \<epsilon>" "N > 0"
    by (metis \<open>\<epsilon> > 0\<close> gr_zeroI inverse_eq_divide real_arch_inverse)
  then obtain h k where "0 < k" and hk: "\<bar>of_int k * \<theta> - of_int h\<bar> < \<epsilon>"
    using Dirichlet_approx that by (metis less_trans)
  have irrat: "of_int n * \<theta> \<in> \<rat> \<Longrightarrow> n = 0" for n
    by (metis Rats_divide Rats_of_int assms(1) nonzero_mult_div_cancel_left of_int_0_eq_iff)
  then consider "of_int k * \<theta> < of_int h" | "of_int k * \<theta> > of_int h"
    by (metis Rats_of_int \<open>0 < k\<close> less_irrefl linorder_neqE_linordered_idom)
  then show thesis
  proof cases
    case 1
    define \<xi> where "\<xi> \<equiv> 1 - frac (of_int k * \<theta>)"
    have pos: "\<xi> > 0"
      by (simp add: \<xi>_def frac_lt_1)
    define N where "N \<equiv> \<lfloor>1/\<xi>\<rfloor>"
    have "N > 0"
      by (simp add: N_def \<xi>_def frac_lt_1)
    have False if "1/\<xi> \<in> \<int>"
    proof -
      from that of_int_ceiling
      obtain r where r: "of_int r = 1/\<xi>" by blast
      then obtain s where s: "of_int k * \<theta> = of_int s + 1 - 1/r"
        by (simp add: \<xi>_def frac_def)
      from r pos s \<open>k > 0\<close> have "\<theta> = (of_int s + 1 - 1/r) / k"
        by (auto simp: field_simps)
      with assms show False
        by simp
    qed
    then have N0: "N < 1/\<xi>"
      unfolding N_def by (metis Ints_of_int floor_correct less_le)
    then have N2: "1/(N+1) < \<xi>"
      unfolding N_def by (smt (verit) divide_less_0_iff divide_less_eq floor_correct mult.commute pos)
    have "\<xi> * (N+1) > 1"
      by (smt (verit) N2 \<open>0 < N\<close> of_int_1_less_iff pos_divide_less_eq)
    then have ex: "\<exists>m. int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
      by (smt (verit, best) \<open>0 < N\<close> \<open>0 \<le> \<alpha>\<close> floor_of_int floor_of_nat mult.commute of_nat_nat)
    define m where "m \<equiv> LEAST m. int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
    have m: "int m \<le> N+1 \<and> 1-\<alpha> < m * \<xi>"
      using LeastI_ex [OF ex] unfolding m_def by blast
    have "m > 0"
      using m gr0I \<open>\<alpha> \<le> 1\<close> by force
    have k\<theta>: "\<xi> < \<epsilon>"
      using hk 1 by (smt (verit, best) floor_eq_iff frac_def \<xi>_def)
    show thesis
    proof (cases "m=1")
      case True
      then have "\<bar>frac (real (nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using m \<open>\<alpha> \<le> 1\<close> \<open>0 < k\<close> \<xi>_def k\<theta> by force
      with \<open>0 < k\<close> zero_less_nat_eq that show thesis by blast 
    next
      case False
      with \<open>0 < m\<close> have "m>1" by linarith
      have "\<xi> < 1 / N"
        by (metis N0 \<open>0 < N\<close> mult_of_int_commute of_int_pos pos pos_less_divide_eq)
      also have "\<dots> \<le> 1 / (real m - 1)"
        using \<open>m > 1\<close> m by (simp add: divide_simps)
      finally have "\<xi> < 1 / (real m - 1)" .
      then have m1_eq: "(int m - 1) * \<xi> = 1 - frac (of_int ((int m - 1) * k) * \<theta>)"
        using frac_int_mult [of "(int m - 1)" "k * \<theta>"] \<open>1 < m\<close>
        by (simp add: \<xi>_def mult.assoc)
      then
      have m1_eq': "frac (of_int ((int m - 1) * k) * \<theta>) = 1 - (int m - 1) * \<xi>"
        by simp
      moreover have "(m - Suc 0) * \<xi> \<le> 1-\<alpha>"
        using Least_le [where k="m-Suc 0"] m
        by (smt (verit, best) Suc_n_not_le_n Suc_pred \<open>0 < m\<close> m_def of_nat_le_iff)
      ultimately have le\<alpha>: " \<alpha> \<le> frac (of_int ((int m - 1) * k) * \<theta>)"
        by (simp add: Suc_leI \<open>0 < m\<close> of_nat_diff)
      moreover have "m * \<xi> + frac (of_int ((int m - 1) * k) * \<theta>) = \<xi> + 1"
        by (subst m1_eq') (simp add: \<xi>_def algebra_simps)
      ultimately have "\<bar>frac ((int (m - 1) * k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        by (smt (verit, best) One_nat_def Suc_leI \<open>0 < m\<close> int_ops(2) k\<theta> m of_nat_diff)
      with that show thesis
        by (metis \<open>0 < k\<close> \<open>1 < m\<close> mult_pos_pos of_int_of_nat_eq of_nat_mult pos_int_cases zero_less_diff)
    qed
  next
    case 2 
    define \<xi> where "\<xi> \<equiv> frac (of_int k * \<theta>)"
    have recip_frac: False if "1/\<xi> \<in> \<int>"
    proof -
      have "frac (of_int k * \<theta>) \<in> \<rat>"
        using that unfolding \<xi>_def
        by (metis Ints_cases Rats_1 Rats_divide Rats_of_int div_by_1 divide_divide_eq_right mult_cancel_right2)
      then show False
        using \<open>0 < k\<close> frac_in_Rats_iff irrat by blast
    qed
    have pos: "\<xi> > 0"
      by (metis \<xi>_def Ints_0 division_ring_divide_zero frac_unique_iff less_le recip_frac)
    define N where "N \<equiv> \<lfloor>1 / \<xi>\<rfloor>"
    have "N > 0"
      unfolding N_def
      by (smt (verit) \<xi>_def divide_less_eq_1_pos floor_less_one frac_lt_1 pos) 
    have N0: "N < 1 / \<xi>"
      unfolding N_def by (metis Ints_of_int floor_eq_iff less_le recip_frac)
    then have N2: "1/(N+1) < \<xi>"
      unfolding N_def
      by (smt (verit, best) divide_less_0_iff divide_less_eq floor_correct mult.commute pos)
    have "\<xi> * (N+1) > 1"
      by (smt (verit) N2 \<open>0 < N\<close> of_int_1_less_iff pos_divide_less_eq)
    then have ex: "\<exists>m. int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
      by (smt (verit, best) mult.commute \<open>\<alpha> \<le> 1\<close> \<open>0 < N\<close> of_int_of_nat_eq pos_int_cases)
    define m where "m \<equiv> LEAST m. int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
    have m: "int m \<le> N+1 \<and> \<alpha> < m * \<xi>"
      using LeastI_ex [OF ex] unfolding m_def by blast
    have "m > 0"
      using \<open>0 \<le> \<alpha>\<close> m gr0I by force
    have k\<theta>: "\<xi> < \<epsilon>"
      using hk 2 unfolding \<xi>_def by (smt (verit, best) floor_eq_iff frac_def)
    have mk_eq: "frac (of_int (m*k) * \<theta>) = m * frac (of_int k * \<theta>)"
      if "m>0" "frac (of_int k * \<theta>) < 1/m" for m k
    proof (subst frac_unique_iff , intro conjI)
      show "real_of_int (m * k) * \<theta> - real_of_int m * frac (real_of_int k * \<theta>) \<in> \<int>"
        by (simp add: algebra_simps frac_def)
    qed (use that in \<open>auto simp: divide_simps mult_ac\<close>)
    show thesis
    proof (cases "m=1")
      case True
      then have "\<bar>frac (real (nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using m \<alpha> \<open>0 < k\<close> \<xi>_def k\<theta> by force
      with \<open>0 < k\<close> zero_less_nat_eq that show ?thesis by blast 
    next
      case False
      with \<open>0 < m\<close> have "m>1" by linarith
      with \<open>0 < k\<close> have mk_pos:"(m - Suc 0) * nat k > 0" by force
      have "real_of_int (int m - 1) < 1 / frac (real_of_int k * \<theta>)"
        using N0 \<xi>_def m by force
      then
      have m1_eq: "(int m - 1) * \<xi> = frac (((int m - 1) * k) * \<theta>)"
        using m mk_eq [of "int m-1" k] pos \<open>m>1\<close> by (simp add: divide_simps mult_ac \<xi>_def)
      moreover have "(m - Suc 0) * \<xi> \<le> \<alpha>"
        using Least_le [where k="m-Suc 0"] m
        by (smt (verit, best) Suc_n_not_le_n Suc_pred \<open>0 < m\<close> m_def of_nat_le_iff)
      ultimately have le\<alpha>: "frac (of_int ((int m - 1) * k) * \<theta>) \<le> \<alpha>"
        by (simp add: Suc_leI \<open>0 < m\<close> of_nat_diff)
      moreover have "(m * \<xi> - frac (of_int ((int m - 1) * k) * \<theta>)) < \<epsilon>"
        by (metis m1_eq add_diff_cancel_left' diff_add_cancel k\<theta> left_diff_distrib' 
            mult_cancel_right2 of_int_1 of_int_diff of_int_of_nat_eq)
      ultimately have "\<bar>frac (real( (m - 1) * nat k) * \<theta>) - \<alpha>\<bar> < \<epsilon>"
        using \<open>0 < k\<close> \<open>0 < m\<close> by simp (smt (verit, best) One_nat_def Suc_leI m of_nat_1 of_nat_diff)
      with  \<open>m > 0\<close> that show thesis
        using mk_pos One_nat_def by presburger
    qed
  qed
qed


text \<open>Theorem 7.7 expressed more abstractly using @{term closure}\<close>
corollary Kronecker_approx_1:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>"
  shows "closure (range (\<lambda>n. frac (real n * \<theta>))) = {0..1}"  (is "?C = _")
proof -
  have "\<exists>k>0. \<bar>frac(real k * \<theta>) - \<alpha>\<bar> < \<epsilon>" if "0 \<le> \<alpha>" "\<alpha> \<le> 1" "\<epsilon> > 0" for \<alpha> \<epsilon>
    by (meson Kronecker_approx_1_explicit assms that)
  then have "x \<in> ?C" if "0 \<le> x" "x \<le> 1" for x :: real
    using that by (auto simp add: closure_approachable dist_real_def)
  moreover 
  have "(range (\<lambda>n. frac (real n * \<theta>))) \<subseteq> {0..1}"
    by (smt (verit) atLeastAtMost_iff frac_unique_iff image_subset_iff)
  then have "?C \<subseteq> {0..1}"
    by (simp add: closure_minimal)
  ultimately show ?thesis by auto
qed


text \<open>The next theorem removes the restriction $0 \leq \alpha \leq 1$.\<close>

text \<open>Theorem 7.8\<close>
corollary sequence_of_fractional_parts_is_dense:
  fixes \<theta> :: real
  assumes "\<theta> \<notin> \<rat>" "\<epsilon> > 0"
  obtains h k where "k > 0" "\<bar>of_int k * \<theta> - of_int h - \<alpha>\<bar> < \<epsilon>"
proof -
  obtain k where "k>0" "\<bar>frac(real k * \<theta>) - frac \<alpha>\<bar> < \<epsilon>"  
    by (metis Kronecker_approx_1_explicit assms frac_ge_0 frac_lt_1 less_le_not_le)
  then have "\<bar>real_of_int k * \<theta> - real_of_int (\<lfloor>k * \<theta>\<rfloor> - \<lfloor>\<alpha>\<rfloor>) - \<alpha>\<bar> < \<epsilon>"
    by (auto simp: frac_def)
  then show thesis
    by (meson \<open>0 < k\<close> of_nat_0_less_iff that)
qed

section \<open>Extension of Kronecker's Theorem to Simultaneous Approximation\<close>

subsection \<open>Towards Lemma 1\<close>

lemma integral_exp: 
  assumes  "T \<ge> 0" "a\<noteq>0"
  shows "integral {0..T} (\<lambda>t. exp(a * complex_of_real t)) = (exp(a * of_real T) - 1) / a"
proof -
  have "\<And>t. t \<in> {0..T} \<Longrightarrow> ((\<lambda>x. exp (a * x) / a) has_vector_derivative exp (a * t)) (at t within {0..T})"
    using assms
    by (intro derivative_eq_intros has_complex_derivative_imp_has_vector_derivative [unfolded o_def] | simp)+
  then have "((\<lambda>t. exp(a * of_real t)) has_integral exp(a * complex_of_real T)/a - exp(a * of_real 0)/a)  {0..T}"
    by (meson fundamental_theorem_of_calculus \<open>T \<ge> 0\<close>)
  then show ?thesis
    by (simp add: diff_divide_distrib integral_unique)
qed

lemma Kronecker_simult_aux1:
  fixes \<eta>:: "nat \<Rightarrow> real" and c:: "nat \<Rightarrow> complex" and N::nat
  assumes inj: "inj_on \<eta> {..N}" and "k \<le> N"
  defines "f \<equiv> \<lambda>t. \<Sum>r\<le>N. c r * exp(\<i> * of_real t * \<eta> r)"
  shows "((\<lambda>T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))) \<longlongrightarrow> c k) at_top"
proof -
  define F where "F \<equiv> \<lambda>k t. f t * exp(-\<i> * of_real t * \<eta> k)"
  have f: "F k = (\<lambda>t. \<Sum>r\<le>N. c r * exp(\<i> * (\<eta> r - \<eta> k) * of_real t))" 
    by (simp add: F_def f_def sum_distrib_left field_simps exp_diff exp_minus)
  have *: "integral {0..T} (F k)
      = c k * T + (\<Sum>r \<in> {..N}-{k}. c r * integral {0..T} (\<lambda>t. exp(\<i> * (\<eta> r - \<eta> k) * of_real t)))"
    if "T > 0" for T
    using \<open>k \<le> N\<close> that
    by (simp add: f integral_sum integrable_continuous_interval continuous_intros Groups_Big.sum_diff scaleR_conv_of_real)

  have **: "(1/T) * integral {0..T} (F k)
       = c k + (\<Sum>r \<in> {..N}-{k}. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / (\<i> * (\<eta> r - \<eta> k) * of_real T))"
    if "T > 0" for T
  proof -
    have I: "integral {0..T} (\<lambda>t. exp (\<i> * (complex_of_real t * \<eta> r) - \<i> * (complex_of_real t * \<eta> k))) 
           = (exp(\<i> * (\<eta> r - \<eta> k) * T) - 1) / (\<i> * (\<eta> r - \<eta> k))"
      if "r \<le> N" "r \<noteq> k" for r
      using that \<open>k \<le> N\<close> inj \<open>T > 0\<close> integral_exp [of T "\<i> * (\<eta> r - \<eta> k)"] 
      by (simp add: inj_on_eq_iff algebra_simps)
    show ?thesis
      using that by (subst *) (auto simp add: algebra_simps sum_divide_distrib I)
  qed
  have "((\<lambda>T. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / (\<i> * (\<eta> r - \<eta> k) * of_real T)) \<longlongrightarrow> 0) at_top"
    for r
  proof -
    have "((\<lambda>x. (cos ((\<eta> r - \<eta> k) * x) - 1) / x) \<longlongrightarrow> 0) at_top"
         "((\<lambda>x. sin ((\<eta> r - \<eta> k) * x) / x) \<longlongrightarrow> 0) at_top"
      by real_asymp+
    hence "((\<lambda>T. (exp (\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / of_real T) \<longlongrightarrow> 0) at_top"
      by (simp add: tendsto_complex_iff Re_exp Im_exp)
    from tendsto_mult[OF this tendsto_const[of "c r / (\<i> * (\<eta> r - \<eta> k))"]] show ?thesis
      by (simp add: field_simps)
  qed
  then have "((\<lambda>T. c k + (\<Sum>r \<in> {..N}-{k}. c r * (exp(\<i> * (\<eta> r - \<eta> k) * of_real T) - 1) / 
                  (\<i> * (\<eta> r - \<eta> k) * of_real T))) \<longlongrightarrow> c k + 0) at_top"
    by (intro tendsto_add tendsto_null_sum) auto
  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule filterlim_cong)
    show "\<forall>\<^sub>F x in at_top. c k + (\<Sum>r\<in>{..N} - {k}. c r * (exp (\<i> * of_real (\<eta> r - \<eta> k) * of_real x) - 1) /
            (\<i> * of_real (\<eta> r - \<eta> k) * of_real x)) = 
          1 / of_real x * integral {0..x} (\<lambda>t. f t * exp (- \<i> * of_real t * of_real (\<eta> k)))"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim T)
      show ?case
        using **[of T] elim by (simp add: F_def)
    qed
  qed auto
  finally show ?thesis .
qed

text \<open>the version of Lemma 1 that we actually need\<close>
lemma Kronecker_simult_aux1_strict:
  fixes \<eta>:: "nat \<Rightarrow> real" and c:: "nat \<Rightarrow> complex" and N::nat
  assumes \<eta>: "inj_on \<eta> {..<N}" "0 \<notin> \<eta> ` {..<N}" and "k < N"
  defines "f \<equiv> \<lambda>t. 1 + (\<Sum>r<N. c r * exp(\<i> * of_real t * \<eta> r))"
  shows "((\<lambda>T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))) \<longlongrightarrow> c k) at_top"
proof -
  define c' where "c' \<equiv> case_nat 1 c"
  define \<eta>' where "\<eta>' \<equiv> case_nat 0 \<eta>"
  define f' where "f' \<equiv> \<lambda>t. (\<Sum>r\<le>N. c' r * exp(\<i> * of_real t * \<eta>' r))"
  have "inj_on \<eta>' {..N}"
    using \<eta> by (auto simp: \<eta>'_def inj_on_def split: nat.split_asm)
  moreover have "Suc k \<le> N"
    using \<open>k < N\<close> by auto
  ultimately have "((\<lambda>T. 1 / T * integral {0..T} (\<lambda>t. (\<Sum>r\<le>N. c' r * exp (\<i> * of_real t * \<eta>' r)) *
                    exp (- \<i> * t * \<eta>' (Suc k)))) \<longlongrightarrow> c' (Suc k))
       at_top"
    by (intro Kronecker_simult_aux1)
  moreover have "(\<Sum>r\<le>N. c' r * exp (\<i> * of_real t * \<eta>' r)) = 1 + (\<Sum>r<N. c r * exp (\<i> * of_real t * \<eta> r))" for t
    by (simp add: c'_def \<eta>'_def sum.atMost_shift)
  ultimately show ?thesis
    by (simp add: f_def c'_def \<eta>'_def)
qed

subsection \<open>Towards Lemma 2\<close>

lemma cos_monotone_aux: "\<lbrakk>\<bar>2 * pi * of_int i + x\<bar> \<le> y; y \<le> pi\<rbrakk> \<Longrightarrow> cos y \<le> cos x"
  by (metis add.commute abs_ge_zero cos_abs_real cos_monotone_0_pi_le sin_cos_eq_iff)

lemma Figure7_1:
  assumes "0 \<le> \<epsilon>" "\<epsilon> \<le> \<bar>x\<bar>" "\<bar>x\<bar> \<le> pi"
  shows "cmod (1 + exp (\<i> * x)) \<le> cmod (1 + exp (\<i> * \<epsilon>))"
proof -
  have norm_eq: "sqrt (2 * (1 + cos t)) = cmod (1 + cis t)" for t
    by (simp add: norm_complex_def power2_eq_square algebra_simps)
  have "cos \<bar>x\<bar> \<le> cos \<epsilon>"
    by (rule cos_monotone_0_pi_le) (use assms in auto)
  hence "sqrt (2 * (1 + cos \<bar>x\<bar>)) \<le> sqrt (2 * (1 + cos \<epsilon>))"
    by simp
  also have "cos \<bar>x\<bar> = cos x"
    by simp
  finally show ?thesis
    unfolding norm_eq by (simp add: cis_conv_exp)
qed

lemma Kronecker_simult_aux2:
  fixes \<alpha>:: "nat \<Rightarrow> real" and \<theta>:: "nat \<Rightarrow> real" and n::nat
  defines "F \<equiv> \<lambda>t. 1 + (\<Sum>r<n. exp(\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r))))"
  defines "L \<equiv> Sup (range (norm \<circ> F))"
  shows "(\<forall>\<epsilon>>0. \<exists>t h. \<forall>r<n. \<bar>t * \<theta> r - \<alpha> r - of_int (h r)\<bar> < \<epsilon>) \<longleftrightarrow> L = Suc n" (is "?lhs = _")
proof
  assume ?lhs
  then have "\<And>k. \<exists>t h. \<forall>r<n. \<bar>t * \<theta> r - \<alpha> r - of_int (h r)\<bar> < 1 / (2 * pi * Suc k)"
    by simp
  then obtain t h where th: "\<And>k r. r<n \<Longrightarrow> \<bar>t k * \<theta> r - \<alpha> r - of_int (h k r)\<bar> < 1 / (2 * pi * Suc k)"
    by metis
  have Fle: "\<And>x. cmod (F x) \<le> real (Suc n)"
    by (force simp: F_def intro: order_trans [OF norm_triangle_ineq] order_trans [OF norm_sum])
  then have boundedF: "bounded (range F)"
    by (metis bounded_iff rangeE) 
  have leL: "1 + n * cos(1 / Suc k) \<le> L" for k
  proof -
    have *: "cos (1 / Suc k) \<le> cos (2 * pi * (t k * \<theta> r - \<alpha> r))" if "r<n" for r 
    proof (rule cos_monotone_aux)
      have "\<bar>2 * pi * (- h k r) + 2 * pi * (t k * \<theta> r - \<alpha> r)\<bar> \<le> \<bar>t k * \<theta> r - \<alpha> r - h k r\<bar> * 2 * pi"
        by (simp add: algebra_simps abs_mult_pos abs_mult_pos')
      also have "\<dots> \<le> 1 / real (Suc k)"
        using th [OF that, of k] by (simp add: divide_simps)
      finally show "\<bar>2 * pi * real_of_int (- h k r) + 2 * pi * (t k * \<theta> r - \<alpha> r)\<bar> \<le> 1 / real (Suc k)" .
      have "1 / real (Suc k) \<le> 1"
        by auto
      then show "1 / real (Suc k) \<le> pi"
        using pi_ge_two by linarith
    qed
    have "1 + n * cos(1 / Suc k) = 1 + (\<Sum>r<n. cos(1 / Suc k))"
      by simp
    also have "\<dots> \<le> 1 + (\<Sum>r<n. cos (2 * pi * (t k * \<theta> r - \<alpha> r)))"
      using * by (intro add_mono sum_mono) auto
    also have "\<dots> \<le> Re (F(t k))"
      by (simp add: F_def Re_exp)
    also have "\<dots> \<le> norm (F(t k))"
      by (simp add: complex_Re_le_cmod)
    also have "\<dots> \<le> L"
      by (simp add: L_def boundedF bounded_norm_le_SUP_norm)
    finally show ?thesis .
  qed
  show "L = Suc n"
  proof (rule antisym)
    show "L \<le> Suc n"
      using Fle by (auto simp add: L_def intro: cSup_least)
    have "((\<lambda>k. 1 + real n * cos (1 / real (Suc k))) \<longlongrightarrow> 1 + real n) at_top"
      by real_asymp
    with LIMSEQ_le_const2 leL show "Suc n \<le> L"
      by fastforce
  qed
next
  assume L: "L = Suc n"
  show ?lhs
  proof (rule ccontr)
    assume "\<not> ?lhs"
    then obtain e0 where "e0>0" and e0: "\<And>t h. \<exists>k<n. \<bar>t * \<theta> k - \<alpha> k - of_int (h k)\<bar> \<ge> e0"
      by (force simp: not_less)
    define \<epsilon> where "\<epsilon> \<equiv> min e0 (pi/4)"
    have \<epsilon>: "\<And>t h. \<exists>k<n. \<bar>t * \<theta> k - \<alpha> k - of_int (h k)\<bar> \<ge> \<epsilon>"
      unfolding \<epsilon>_def using e0 min.coboundedI1 by blast
    have \<epsilon>_bounds: "\<epsilon> > 0" "\<epsilon> < pi" "\<epsilon> \<le> pi/4"
      using \<open>e0 > 0\<close> by (auto simp: \<epsilon>_def min_def)
    with sin_gt_zero have "sin \<epsilon> > 0"
      by blast
    then have "\<not> collinear{0, 1, exp (\<i> * \<epsilon>)}"
      using collinear_iff_Reals cis.sel cis_conv_exp complex_is_Real_iff by force
    then have "norm (1 + exp (\<i> * \<epsilon>)) < 2"
      using norm_triangle_eq_imp_collinear
      by (smt (verit) linorder_not_le norm_exp_i_times norm_one norm_triangle_lt)
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "norm (1 + exp (\<i> * \<epsilon>)) = 2 - \<delta>"
      by (smt (verit, best))
    have "norm (F t) \<le> n+1-\<delta>" for t 
    proof -
      define h where "h \<equiv> \<lambda>r. round (t * \<theta> r - \<alpha> r)"
      define X where "X \<equiv> \<lambda>r. t * \<theta> r - \<alpha> r - h r"
      have "exp (\<i> * (of_int j * (of_real pi * 2))) = 1" for j
        by (metis add_0 exp_plus_2pin exp_zero)
      then have exp_X: "exp (\<i> * (2 * of_real pi * of_real (X r))) 
                 = exp (\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r)))" for r
        by (simp add: X_def right_diff_distrib exp_add exp_diff mult.commute)
      have norm_pr_12: "X r \<in> {-1/2..<1/2}" for r
        apply (simp add: X_def h_def)
        by (smt (verit, best) abs_of_nonneg half_bounded_equal of_int_round_abs_le of_int_round_gt)
      obtain k where "k<n" and 1: "\<bar>X k\<bar> \<ge> \<epsilon>"
        using X_def \<epsilon> [of t h] by auto
      have 2: "2*pi \<ge> 1"
        using pi_ge_two by auto
      have "\<bar>2 * pi * X k\<bar> \<ge> \<epsilon>"
        using mult_mono [OF 2 1] pi_ge_zero by linarith
      moreover
      have "\<bar>2 * pi * X k\<bar> \<le> pi"
        using norm_pr_12 [of k] apply (simp add: abs_if field_simps)
        by (smt (verit, best) divide_le_eq_1_pos divide_minus_left m2pi_less_pi nonzero_mult_div_cancel_left)
      ultimately
      have *: "norm (1 + exp (\<i> * of_real (2 * pi * X k))) \<le> norm (1 + exp (\<i> * \<epsilon>))"
        using Figure7_1[of \<epsilon> "2 * pi * X k"] \<epsilon>_bounds by linarith
      have "norm (F t) = norm (1 + (\<Sum>r<n. exp(\<i> * of_real (2 * pi * (X r)))))"
        by (auto simp: F_def exp_X)
      also have "\<dots> \<le> norm (1 + exp(\<i> * of_real (2 * pi * X k)) + (\<Sum>r \<in> {..<n}-{k}. exp(\<i> * of_real (2 * pi * X r))))"
        by (simp add: comm_monoid_add_class.sum.remove [where x=k] \<open>k < n\<close> algebra_simps)
      also have "\<dots> \<le> norm (1 + exp(\<i> * of_real (2 * pi * X k))) + (\<Sum>r \<in> {..<n}-{k}. norm (exp(\<i> * of_real (2 * pi * X r))))"
        by (intro norm_triangle_mono sum_norm_le order_refl)
      also have "\<dots> \<le> (2 - \<delta>) + (n - 1)"
        using \<open>k < n\<close> \<delta> 
        by simp (metis "*" mult_2 of_real_add of_real_mult)
      also have "\<dots> = n + 1 - \<delta>"
        using \<open>k < n\<close> by simp
      finally show ?thesis .
    qed
    then have "L \<le> 1 + real n - \<delta>"
      by (auto simp: L_def intro: cSup_least)
    with L \<open>\<delta> > 0\<close> show False
      by linarith
  qed
qed

subsection \<open>Towards lemma 3\<close>

text \<open>The text doesn't say so, but the generated polynomial needs to be "clean":
all coefficients nonzero, and with no exponent string mentioned more than once.
And no constant terms (with all exponents zero).\<close>

text \<open>Some tools for combining integer-indexed sequences or splitting them into parts\<close>

lemma less_sum_nat_iff:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>j<k. (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
proof (induction k arbitrary: b)
  case (Suc k)
  then show ?case
    by (simp add: less_Suc_eq) (metis not_less trans_less_add1)
qed auto

lemma less_sum_nat_iff_uniq:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>!j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
  unfolding less_sum_nat_iff by (meson leD less_sum_nat_iff nat_neq_iff)

definition part :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "part a k b \<equiv> (THE j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"

lemma part: 
  "b < (\<Sum>i<k. a i) \<longleftrightarrow> (let j = part a k b in j < k \<and> (\<Sum>i < j. a i) \<le> b \<and> b < (\<Sum>i < j. a i) + a j)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding less_sum_nat_iff_uniq part_def by (metis (no_types, lifting) theI')
qed (auto simp: less_sum_nat_iff Let_def)

lemma part_Suc: "part a (Suc k) b = (if sum a {..<k} \<le> b \<and> b < sum a {..<k} + a k then k else part a k b)"
  using leD 
  by (fastforce simp: part_def less_Suc_eq less_sum_nat_iff conj_disj_distribR cong: conj_cong)

text \<open>The polynomial expansions used in Lemma 3\<close>

definition gpoly :: "[nat, nat\<Rightarrow>complex, nat, nat\<Rightarrow>nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> complex"
  where "gpoly n x N a r \<equiv> (\<Sum>k<N. a k * (\<Prod>i<n. x i ^ r k i))"

lemma gpoly_cong:
  assumes "\<And>k. k < N \<Longrightarrow> a' k = a k" "\<And>k i. \<lbrakk>k < N; i<n\<rbrakk> \<Longrightarrow> r' k i = r k i"
  shows "gpoly n x N a r = gpoly n x N a' r'"
  using assms by (auto simp: gpoly_def)

lemma gpoly_inc: "gpoly n x N a r = gpoly (Suc n) x N a (\<lambda>k. (r k)(n:=0))"
  by (simp add: gpoly_def algebra_simps sum_distrib_left)

lemma monom_times_gpoly: "gpoly n x N a r * x n ^ q = gpoly (Suc n) x N a (\<lambda>k. (r k)(n:=q))"
  by (simp add: gpoly_def algebra_simps sum_distrib_left)

lemma const_times_gpoly: "e * gpoly n x N a r = gpoly n x N ((*)e \<circ> a) r"
  by (simp add: gpoly_def sum_distrib_left mult.assoc)

lemma one_plus_gpoly: "1 + gpoly n x N a r = gpoly n x (Suc N) (a(N:=1)) (r(N:=(\<lambda>_. 0)))"
  by (simp add: gpoly_def)

lemma gpoly_add:
  "gpoly n x N a r + gpoly n x N' a' r' 
 = gpoly n x (N+N') (\<lambda>k. if k<N then a k else a' (k-N)) (\<lambda>k. if k<N then r k else r' (k-N))"
proof -
  have "{..<N+N'} = {..<N} \<union> {N..<N+N'}" "{..<N} \<inter> {N..<N + N'} = {}"
    by auto
  then show ?thesis
    by (simp add: gpoly_def sum.union_disjoint sum.atLeastLessThan_shift_0[of _ N] atLeast0LessThan)
qed

lemma gpoly_sum:
  fixes n Nf af rf p
  defines "N \<equiv> sum Nf {..<p}"
  defines "a \<equiv> \<lambda>k. let q = (part Nf p k) in af q (k - sum Nf {..<q})"
  defines "r \<equiv> \<lambda>k. let q = (part Nf p k) in rf q (k - sum Nf {..<q})"
  shows "(\<Sum>q<p. gpoly n x (Nf q) (af q) (rf q)) = gpoly n x N a r"
  unfolding N_def a_def r_def
proof (induction p)
  case 0
  then show ?case
    by (simp add: gpoly_def)
next
  case (Suc p)
  then show ?case 
    by (auto simp: gpoly_add Let_def part_Suc intro: gpoly_cong)
qed

text \<open>For excluding constant terms: with all exponents zero\<close>
definition nontriv_exponents :: "[nat, nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> bool"
  where "nontriv_exponents n N r \<equiv> \<forall>k<N. \<exists>i<n. r k i \<noteq> 0"

lemma nontriv_exponents_add: 
  "\<lbrakk>nontriv_exponents n M r; nontriv_exponents (Suc n) N r'\<rbrakk> \<Longrightarrow> 
   nontriv_exponents (Suc n) (M + N) (\<lambda>k. if k<M then r k else r' (k-M))"
  by (force simp add: nontriv_exponents_def less_Suc_eq)

lemma nontriv_exponents_sum:
  assumes "\<And>q. q < p \<Longrightarrow> nontriv_exponents n (N q) (r q)"
  shows "nontriv_exponents n (sum N {..<p}) (\<lambda>k. let q = part N p k in r q (k - sum N {..<q}))"
  using assms by (simp add: nontriv_exponents_def less_diff_conv2 part Let_def)

definition uniq_exponents :: "[nat, nat, [nat,nat]\<Rightarrow>nat] \<Rightarrow> bool"
  where "uniq_exponents n N r \<equiv> \<forall>k<N. \<forall>k'<k. \<exists>i<n. r k i \<noteq> r k' i"

lemma uniq_exponents_inj: "uniq_exponents n N r \<Longrightarrow> inj_on r {..<N}"
  by (smt (verit, best) inj_on_def lessThan_iff linorder_cases uniq_exponents_def)

text \<open>All coefficients must be nonzero\<close>
definition nonzero_coeffs :: "[nat, nat\<Rightarrow>nat] \<Rightarrow> bool"
  where "nonzero_coeffs N a \<equiv> \<forall>k<N. a k \<noteq> 0"

text \<open>Any polynomial expansion can be cleaned up, removing zero coeffs, etc.\<close>
lemma gpoly_uniq_exponents:
  obtains N' a' r' 
  where "\<And>x. gpoly n x N a r = gpoly n x N' a' r'" 
        "uniq_exponents n N' r'" "nonzero_coeffs N' a'" "N' \<le> N" 
        "nontriv_exponents n N r \<Longrightarrow> nontriv_exponents n N' r'" 
proof (cases "\<forall>k<N. a k = 0")
  case True
  show thesis
  proof
    show "gpoly n x N a r = gpoly n x 0 a r" for x
      by (auto simp: gpoly_def True)
  qed (auto simp: uniq_exponents_def nonzero_coeffs_def nontriv_exponents_def)
next
  case False
  define cut where "cut f i \<equiv> if i<n then f i else (0::nat)" for f i
  define R where "R \<equiv> cut ` r ` ({..<N} \<inter> {k. a k > 0})"
  define N' where "N' \<equiv> card R"
  define r' where "r' \<equiv> from_nat_into R"
  define a' where "a' \<equiv> \<lambda>k'. \<Sum>k<N. if r' k' = cut (r k) then a k else 0"
  have "finite R"
    using R_def by blast
  then have bij: "bij_betw r' {..<N'} R"
    using bij_betw_from_nat_into_finite N'_def r'_def by blast
  have 1: "card {i. i < N' \<and> r' i = cut (r k)} = Suc 0"
    if "k < N" "a k > 0" for k
  proof -
    have "card {i. i < N' \<and> r' i = cut (r k)} \<le> Suc 0"
      using bij by (simp add: card_le_Suc0_iff_eq bij_betw_iff_bijections Ball_def) metis
    moreover have "card {i. i < N' \<and> r' i = cut (r k)} > 0" 
      using bij that by (auto simp: card_gt_0_iff bij_betw_iff_bijections R_def)
    ultimately show "card {i. i < N' \<and> r' i = cut (r k)} = Suc 0"
      using that by auto
  qed
  show thesis
  proof
    have "\<exists>i<n. r' k i \<noteq> r' k' i" if "k < N'" and "k' < k" for k k'
    proof -
      have "k' < N'"
        using order.strict_trans that by blast
      then have "r' k \<noteq> r' k'"
        by (metis bij bij_betw_iff_bijections lessThan_iff nat_neq_iff that)
      moreover obtain sk sk' where "r' k = cut sk" "r' k' = cut sk'"
        by (metis R_def \<open>k < N'\<close> \<open>k' < N'\<close> bij bij_betwE image_iff lessThan_iff)
      ultimately show ?thesis
        using local.cut_def by force
    qed
    then show "uniq_exponents n N' r'"
      by (auto simp: uniq_exponents_def R_def)
    have "R \<subseteq> (cut \<circ> r) ` {..<N}"
      by (auto simp: R_def)
    then show "N' \<le> N"
      unfolding N'_def by (metis card_lessThan finite_lessThan surj_card_le)
    show "gpoly n x N a r = gpoly n x N' a' r'" for x
    proof -
      have "a k * (\<Prod>i<n. x i ^ r k i) 
          = (\<Sum>i<N'. (if r' i = cut (r k) then of_nat (a k) else of_nat 0) * (\<Prod>j<n. x j ^ r' i j))" 
        if "k<N" for k
        using that
        by (cases"a k = 0")
           (simp_all add: if_distrib [of "\<lambda>v. v * _"] 1 cut_def flip: sum.inter_filter cong: if_cong)
      then show ?thesis
        by (simp add: gpoly_def a'_def sum_distrib_right sum.swap [where A="{..<N'}"] if_distrib [of of_nat])
    qed
    show "nontriv_exponents n N' r'" if ne: "nontriv_exponents n N r"
    proof -
      have "\<exists>i<n. 0 < r' k' i" if "k' < N'" for k'
      proof -
        have "r' k' \<in> R"
          using bij bij_betwE that by blast
        then obtain k where "k<N" and k: "r' k' = cut (r k)"
          using R_def by blast
        with ne obtain i where "i<n" "r k i > 0"
          by (auto simp: nontriv_exponents_def)
        then show ?thesis
          using k local.cut_def by auto
      qed
      then show ?thesis
        by (simp add: nontriv_exponents_def)
    qed
    have "0 < a' k'" if "k' < N'" for k'
    proof -
      have "r' k' \<in> R"
        using bij bij_betwE that by blast
      then obtain k where "k<N" "a k > 0" "r' k' = cut (r k)"
        using R_def by blast
      then have False if "a' k' = 0"
        using that by (force simp add: a'_def Ball_def )
      then show ?thesis
        by blast
    qed
    then show "nonzero_coeffs N' a'"
      by (auto simp: nonzero_coeffs_def)
  qed
qed


lemma Kronecker_simult_aux3: 
  "\<exists>N a r. (\<forall>x. (1 + (\<Sum>i<n. x i))^p = 1 + gpoly n x N a r) \<and> Suc N \<le> (p+1)^n
         \<and> nontriv_exponents n N r"
proof (induction n arbitrary: p)
  case 0
  then show ?case
    by (auto simp: gpoly_def nontriv_exponents_def nonzero_coeffs_def)
next
  case (Suc n)
  then obtain Nf af rf 
    where feq: "\<And>q x. (1 + (\<Sum>i<n. x i)) ^ q = 1 + gpoly n x (Nf q) (af q) (rf q)" 
      and Nle: "\<And>q. Suc (Nf q) \<le> (q+1)^n"
      and nontriv: "\<And>q. nontriv_exponents n (Nf q) (rf q)"
    by metis
  define N where "N \<equiv> Nf p + (\<Sum>q<p. Suc (Nf q))"
  define a where "a \<equiv> \<lambda>k. if k < Nf p then af p k
                           else let q = part (\<lambda>t. Suc (Nf t)) p (k - Nf p)
                                in (p choose q) *
                                   (if k - Nf p - (\<Sum>t<q. Suc (Nf t)) = Nf q then Suc 0
                                    else af q (k - Nf p - (\<Sum>t<q. Suc(Nf t))))"
  define r where "r \<equiv> \<lambda>k. if k < Nf p then (rf p k)(n := 0)
                                       else let q = part (\<lambda>t. Suc (Nf t)) p (k - Nf p)
                                          in (if k - Nf p - (\<Sum>t<q. Suc (Nf t)) = Nf q then \<lambda>_. 0
                                              else rf q (k - Nf p - (\<Sum>t<q. Suc(Nf t))))  (n := p-q)"
  have peq: "{..p} = insert p {..<p}"
    by auto
  have "nontriv_exponents n (Nf p) (\<lambda>i. (rf p i)(n := 0))"
       "\<And>q. q<p \<Longrightarrow> nontriv_exponents (Suc n) (Suc (Nf q)) (\<lambda>k. (if k = Nf q then \<lambda>_. 0 else rf q k) (n := p - q))"
    using nontriv by (fastforce simp: nontriv_exponents_def)+
  then have "nontriv_exponents (Suc n) N r"
    unfolding N_def r_def by (intro nontriv_exponents_add nontriv_exponents_sum)
  moreover
  { fix x :: "nat \<Rightarrow> complex"
    have "(1 + (\<Sum>i < Suc n. x i)) ^ p = (1 + (\<Sum>i<n. x i) + x n) ^ p"
      by (simp add: add_ac)
    also have "\<dots> = (\<Sum>q\<le>p. (p choose q) * (1 + (\<Sum>i<n. x i))^q * x n^(p-q))"
      by (simp add: binomial_ring)
    also have "\<dots> = (\<Sum>q\<le>p. (p choose q) * (1 + gpoly n x (Nf q) (af q) (rf q)) * x n^(p-q))"
      by (simp add: feq)
    also have "\<dots> = 1 + (gpoly n x (Nf p) (af p) (rf p) + (\<Sum>q<p. (p choose q) * (1 + gpoly n x (Nf q) (af q) (rf q)) * x n^(p-q)))"
      by (simp add: algebra_simps sum.distrib peq)
    also have "\<dots> = 1 + gpoly (Suc n) x N a r"
      apply (subst one_plus_gpoly)
      apply (simp add: const_times_gpoly monom_times_gpoly gpoly_sum)
      apply (simp add: gpoly_inc [where n=n] gpoly_add N_def a_def r_def)
      done
    finally have "(1 + sum x {..<Suc n}) ^ p = 1 + gpoly (Suc n) x N a r" . 
  }
  moreover have "Suc N \<le> (p + 1) ^ Suc n"
  proof -
    have "Suc N = (\<Sum>q\<le>p. Suc (Nf q))"
      by (simp add: N_def peq)
    also have "\<dots> \<le> (\<Sum>q\<le>p. (q+1)^n)"
      by (meson Nle sum_mono)
    also have "\<dots> \<le> (\<Sum>q\<le>p. (p+1)^n)"
      by (force intro!: sum_mono power_mono)
    also have "\<dots> \<le> (p + 1) ^ Suc n"
      by simp
    finally show "Suc N \<le> (p + 1) ^ Suc n" .
  qed
  ultimately show ?case
    by blast
qed

lemma Kronecker_simult_aux3_uniq_exponents:
  obtains N a r where "\<And>x. (1 + (\<Sum>i<n. x i))^p = 1 + gpoly n x N a r" "Suc N \<le> (p+1)^n" 
                      "nontriv_exponents n N r" "uniq_exponents n N r" "nonzero_coeffs N a"
proof -
  obtain N0 a0 r0 where "\<And>x. (1 + (\<Sum>r<n. x r)) ^ p = 1 + gpoly n x N0 a0 r0" 
    and "Suc N0 \<le> (p+1)^n" "nontriv_exponents n N0 r0" 
    using Kronecker_simult_aux3 by blast
  with le_trans Suc_le_mono gpoly_uniq_exponents [of n N0 a0 r0] that show thesis
    by (metis (no_types, lifting))
qed

subsection \<open>And finally Kroncker's theorem itself\<close>

text \<open>Statement of Theorem 7.9\<close>
theorem Kronecker_thm_1:
  fixes \<alpha> \<theta>:: "nat \<Rightarrow> real" and n:: nat
  assumes indp: "module.independent (\<lambda>r. (*) (real_of_int r)) (\<theta> ` {..<n})"
    and inj\<theta>: "inj_on \<theta> {..<n}" and "\<epsilon> > 0"
  obtains t h where "\<And>i. i < n \<Longrightarrow> \<bar>t * \<theta> i - of_int (h i) - \<alpha> i\<bar> < \<epsilon>"
proof (cases "n>0")
  case False then show ?thesis
    using that by blast
next
  case True
  interpret Modules.module "(\<lambda>r. (*) (real_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  define F where "F \<equiv> \<lambda>t. 1 + (\<Sum>i<n. exp(\<i> * of_real (2 * pi * (t * \<theta> i - \<alpha> i))))"
  define L where "L \<equiv> Sup (range (norm \<circ> F))"
  have [continuous_intros]: "0 < T \<Longrightarrow> continuous_on {0..T} F" for T
    unfolding F_def by (intro continuous_intros)
  have nft_Sucn: "norm (F t) \<le> Suc n" for t
    unfolding F_def by (rule norm_triangle_le order_trans [OF norm_sum] | simp)+
  then have L_le: "L \<le> Suc n"
    by (simp add: L_def cSUP_least)
  have nft_L: "norm (F t) \<le> L" for t
    by (metis L_def UNIV_I bdd_aboveI2 cSUP_upper nft_Sucn o_apply)
  have "L = Suc n"
  proof -
    { fix p::nat
      assume "p>0"      
      obtain N a r where 3: "\<And>x. (1 + (\<Sum>r<n. x r)) ^ p = 1 + gpoly n x N a r" 
             and SucN: "Suc N \<le> (p+1)^n"   
             and nontriv: "nontriv_exponents n N r" and uniq: "uniq_exponents n N r"
             and apos: "nonzero_coeffs N a"
        using Kronecker_simult_aux3_uniq_exponents by blast
      have "N \<noteq> 0"
      proof 
        assume "N = 0"
        have "2^p = (1::complex)"
          using 3 [of "(\<lambda>_. 0)(0:=1)"] True \<open>p>0\<close> \<open>N = 0\<close> by (simp add: gpoly_def)
        then have "2 ^ p = Suc 0"
          by (metis of_nat_1 One_nat_def of_nat_eq_iff of_nat_numeral of_nat_power)
        with \<open>0 < p\<close> show False by force
      qed
      define x where "x \<equiv> \<lambda>t r. exp(\<i> * of_real (2 * pi * (t * \<theta> r - \<alpha> r)))"
      define f where "f \<equiv> \<lambda>t. (F t) ^ p"
      have feq: "f t = 1 + gpoly n (x t) N a r" for t
        unfolding f_def F_def x_def by (simp flip: 3)
      define c where "c \<equiv> \<lambda>k. a k / cis (\<Sum>i<n. (pi * (2 * (\<alpha> i * real (r k i)))))"
      define \<eta> where "\<eta> \<equiv> \<lambda>k. 2 * pi * (\<Sum>i<n. r k i * \<theta> i)"
      define INTT where "INTT \<equiv> \<lambda>k T. (1/T) * integral {0..T} (\<lambda>t. f t * exp(-\<i> * of_real t * \<eta> k))"
      have "a k * (\<Prod>i<n. x t i ^ r k i) = c k * exp (\<i> * t * \<eta> k)" if "k<N" for k t
        apply (simp add: x_def \<eta>_def sum_distrib_left flip: exp_of_nat_mult exp_sum)
        apply (simp add: algebra_simps sum_subtractf exp_diff c_def sum_distrib_left cis_conv_exp)
        done
      then have fdef: "f t = 1 + (\<Sum>k<N. c k * exp(\<i> * of_real t * \<eta> k))" for t
        by (simp add: feq gpoly_def)
      have nzero: "\<theta> i \<noteq> 0" if "i<n" for i
        using indp that local.dependent_zero by force
      have ind_disj: "\<And>u. (\<forall>x<n. u (\<theta> x) = 0) \<or> (\<Sum>v \<in> \<theta>`{..<n}. of_int (u v) * v) \<noteq> 0"
        using indp by (auto simp: dependent_finite)
      have inj\<eta>: "inj_on \<eta> {..<N}"
      proof
        fix k k'
        assume k: "k \<in> {..<N}" "k' \<in> {..<N}" and "\<eta> k = \<eta> k'"
        then have eq: "(\<Sum>i<n. real (r k i) * \<theta> i) = (\<Sum>i<n. real (r k' i) * \<theta> i)"
          by (auto simp: \<eta>_def)
        define f where "f \<equiv> \<lambda>z. let i = inv_into {..<n} \<theta> z in int (r k i) - int (r k' i)"
        show "k = k'"
          using ind_disj [of f] inj\<theta> uniq eq k
          apply (simp add: f_def Let_def sum.reindex sum_subtractf algebra_simps uniq_exponents_def)
          by (metis not_less_iff_gr_or_eq)
      qed
      moreover have "0 \<notin> \<eta> ` {..<N}"
        unfolding \<eta>_def
      proof clarsimp
        fix k
        assume *: "(\<Sum>i<n. real (r k i) * \<theta> i) = 0" "k < N"
        define f where "f \<equiv> \<lambda>z. let i = inv_into {..<n} \<theta> z in int (r k i)"
        obtain i where "i<n" and "r k i > 0"
          by (meson \<open>k < N\<close> nontriv nontriv_exponents_def zero_less_iff_neq_zero)
        with * nzero show False
          using ind_disj [of f] inj\<theta> by (simp add: f_def sum.reindex)
      qed
      ultimately have 15: "(INTT k \<longlongrightarrow> c k) at_top" if "k<N" for k
        unfolding fdef INTT_def using Kronecker_simult_aux1_strict that by presburger
      have norm_c: "norm (c k) \<le> L^p" if "k<N" for k 
      proof (intro tendsto_le [of _ "\<lambda>_. L^p"])
        show "((norm \<circ> INTT k) \<longlongrightarrow> cmod (c k)) at_top"
          using that 15 by (simp add: o_def tendsto_norm)
        have "norm (INTT k T) \<le> L^p" if  "T \<ge> 0" for T::real
        proof -
          have "0 \<le> L ^ p"
            by (meson nft_L norm_ge_zero order_trans zero_le_power) 
          have "norm (integral {0..T} (\<lambda>t. f t * exp (- (\<i> *  t * \<eta> k)))) 
                \<le> integral {0..T} (\<lambda>t. L^p)" (is "?L \<le> ?R")  if "T>0"
          proof -
            have "?L \<le> integral {0..T} (\<lambda>t. norm (f t * exp (- (\<i> *  t * \<eta> k))))"
              unfolding f_def by (intro continuous_on_imp_absolutely_integrable_on continuous_intros that)
            also have "\<dots> \<le> ?R"
              unfolding f_def
              by (intro integral_le continuous_intros integrable_continuous_interval that
                  | simp add: nft_L norm_mult norm_power power_mono)+
            finally show ?thesis .
          qed
          with \<open>T \<ge> 0\<close> have "norm (INTT k T) \<le> (1/T) * integral {0..T} (\<lambda>t. L ^ p)"
            by (auto simp add: INTT_def norm_divide divide_simps simp del: integral_const_real)
          also have "\<dots> \<le> L ^ p"
            using \<open>T \<ge> 0\<close> \<open>0 \<le> L ^ p\<close> by simp
          finally show ?thesis .
        qed
        then show "\<forall>\<^sub>F x in at_top. (norm \<circ> INTT k) x \<le> L ^ p"
          using eventually_at_top_linorder that by fastforce
      qed auto
      then have "(\<Sum>k<N. cmod (c k)) \<le> N * L^p"
        by (metis sum_bounded_above card_lessThan lessThan_iff)
      moreover
      have "Re((1 + (\<Sum>r<n. 1)) ^ p) = Re (1 + gpoly n (\<lambda>_. 1) N a r)"
        using 3 [of "\<lambda>_. 1"] by metis
      then have 14: "1 + (\<Sum>k<N. norm (c k)) = (1 + real n) ^ p"
        by (simp add: c_def norm_divide gpoly_def)
      moreover 
      have "L^p \<ge> 1"
        using norm_c [of 0] \<open>N \<noteq> 0\<close> apos 
        by (force simp add: c_def norm_divide nonzero_coeffs_def)
      ultimately have *: "(1 + real n) ^ p \<le> Suc N * L^p"
        by (simp add: algebra_simps)
      have [simp]: "L>0"
        using \<open>1 \<le> L ^ p\<close> \<open>0 < p\<close> by (smt (verit, best) nft_L norm_ge_zero power_eq_0_iff)
      have "Suc n ^ p \<le> (p+1)^n * L^p" 
        by (smt (verit, best) * mult.commute \<open>1 \<le> L ^ p\<close> SucN mult_left_mono of_nat_1 of_nat_add of_nat_power_eq_of_nat_cancel_iff of_nat_power_le_of_nat_cancel_iff plus_1_eq_Suc)
      then have "(Suc n ^ p) powr (1/p) \<le> ((p+1)^n * L^p) powr (1/p)"
        by (simp add: powr_mono2)
      then have "(Suc n) \<le> ((p+1)^n) powr (1/p) * L"
        using \<open>p > 0\<close> \<open>0 < L\<close> by (simp add: powr_powr powr_mult flip: powr_realpow)
      also have "\<dots> = ((p+1) powr n) powr (1/p) * L"
        by (simp add: powr_realpow)
      also have "\<dots> = (p+1) powr (n/p) * L"
        by (simp add: powr_powr)
      finally have "(n + 1) / L \<le> (p+1) powr (n/p)"
        by (simp add: divide_simps)
      then have "ln ((n + 1) / L) \<le> ln (real (p + 1) powr (real n / real p))"
        by simp
      also have "\<dots> \<le> (n/p) * ln(p+1)"
        by (simp add: powr_def)
      finally have "ln ((n + 1) / L) \<le> (n/p) * ln(p+1) \<and> L > 0"
        by fastforce
    } note * = this
    then have [simp]: "L > 0"
      by blast
    have 0: "(\<lambda>p. (n/p) * ln(p+1)) \<longlonglongrightarrow> 0"
      by real_asymp
    have "ln (real (n + 1) / L) \<le> 0"
      using * eventually_at_top_dense by (intro tendsto_lowerbound [OF 0]) auto
    then have "n+1 \<le> L"
      by (simp add: ln_div)
    then show ?thesis
      using L_le by linarith
  qed
  with Kronecker_simult_aux2 [of n \<theta> \<alpha>] \<open>\<epsilon> > 0\<close> that show thesis
    by (auto simp: F_def L_def add.commute diff_diff_eq)
qed


text \<open>Theorem 7.10\<close>

corollary Kronecker_thm_2:
  fixes \<alpha> \<theta> :: "nat \<Rightarrow> real" and n :: nat
  assumes indp: "module.independent (\<lambda>r x. of_int r * x) (\<theta> ` {..n})"
    and inj\<theta>: "inj_on \<theta> {..n}" and [simp]: "\<theta> n = 1" and "\<epsilon> > 0"
  obtains k m where "\<And>i. i < n \<Longrightarrow> \<bar>of_int k * \<theta> i - of_int (m i) - \<alpha> i\<bar> < \<epsilon>"
proof -
  interpret Modules.module "(\<lambda>r. (*) (real_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  have one_in_\<theta>: "1 \<in> \<theta> ` {..n}"
    unfolding \<open>\<theta> n = 1\<close>[symmetric] by blast

  have not_in_Ints: "\<theta> i \<notin> \<int>" if i: "i < n" for i
  proof
    assume "\<theta> i \<in> \<int>"
    then obtain m where m: "\<theta> i = of_int m"
      by (auto elim!: Ints_cases)
    have not_one: "\<theta> i \<noteq> 1"
      using inj_onD[OF inj\<theta>, of i n] i by auto
    define u :: "real \<Rightarrow> int" where "u = (\<lambda>_. 0)(\<theta> i := 1, 1 := -m)"
    show False
      using independentD[OF indp, of "\<theta> ` {i, n}" u "\<theta> i"] \<open>i < n\<close> not_one one_in_\<theta>
      by (auto simp: u_def simp flip: m)
  qed

  have inj\<theta>': "inj_on (frac \<circ> \<theta>) {..n}"
  proof (rule linorder_inj_onI')
    fix i j assume ij: "i \<in> {..n}" "j \<in> {..n}" "i < j"
    show "(frac \<circ> \<theta>) i \<noteq> (frac \<circ> \<theta>) j"
    proof (cases "j = n")
      case True
      thus ?thesis
        using not_in_Ints[of i] ij by auto
    next
      case False
      hence "j < n"
        using ij by auto
      have "inj_on \<theta> (set [i, j, n])"
        using inj\<theta> by (rule inj_on_subset) (use ij in auto)
      moreover have "distinct [i, j, n]"
        using \<open>j < n\<close> ij by auto
      ultimately have "distinct (map \<theta> [i, j, n])"
        unfolding distinct_map by blast
      hence distinct: "distinct [\<theta> i, \<theta> j, 1]"
        by simp

      show "(frac \<circ> \<theta>) i \<noteq> (frac \<circ> \<theta>) j"
      proof
        assume eq: "(frac \<circ> \<theta>) i = (frac \<circ> \<theta>) j"
        define u :: "real \<Rightarrow> int" where "u = (\<lambda>_. 0)(\<theta> i := 1, \<theta> j := -1, 1 := \<lfloor>\<theta> j\<rfloor> - \<lfloor>\<theta> i\<rfloor>)"
        have "(\<Sum>v\<in>{\<theta> i, \<theta> j, 1}. real_of_int (u v) * v) = frac (\<theta> i) - frac (\<theta> j)"
          using distinct by (simp add: u_def frac_def)
        also have "\<dots> = 0"
          using eq by simp
        finally have eq0: "(\<Sum>v\<in>{\<theta> i, \<theta> j, 1}. real_of_int (u v) * v) = 0" .
        show False
          using independentD[OF indp _ _ eq0, of "\<theta> i"] one_in_\<theta> ij distinct
          by (auto simp: u_def)
      qed
    qed
  qed

  have "frac (\<theta> n) = 0"
    by auto
  then have \<theta>no_int: "of_int r \<notin> \<theta> ` {..<n}" for r
    using inj\<theta>' frac_of_int  
    apply (simp add: inj_on_def Ball_def)
    by (metis \<open>frac (\<theta> n) = 0\<close> frac_of_int imageE le_less lessThan_iff less_irrefl)
  define \<theta>' where "\<theta>' \<equiv> (frac \<circ> \<theta>)(n:=1)"
  have [simp]: "{..<Suc n} \<inter> {x. x \<noteq> n} = {..<n}"
    by auto
  have \<theta>image[simp]: "\<theta> ` {..n} = insert 1 (\<theta> ` {..<n})"
    using lessThan_Suc lessThan_Suc_atMost by force
  have "module.independent (\<lambda>r. (*) (of_int r)) (\<theta>' ` {..<Suc n})"
    unfolding dependent_explicit \<theta>'_def
  proof clarsimp
    fix T u v
    assume T: "T \<subseteq> insert 1 ((\<lambda>i. frac (\<theta> i)) ` {..<n})"
      and "finite T"
      and uv_eq0: "(\<Sum>v\<in>T. of_int (u v) * v) = 0"
      and "v \<in> T"
    define invf where "invf \<equiv> inv_into {..<n} (frac \<circ> \<theta>)"
    have "inj_on (\<lambda>x. frac (\<theta> x)) {..<n}"
      using inj\<theta>' by (auto simp: inj_on_def)
    then have invf [simp]: "invf (frac (\<theta> i)) = i" if "i<n" for i
      using frac_lt_1 [of "\<theta> i"] that by (auto simp: invf_def o_def inv_into_f_eq [where x=i])
    define N where "N \<equiv> invf ` (T - {1})"
    have Nsub: "N \<subseteq> {..n}" and "finite N"
      using T \<open>finite T\<close> by (auto simp: N_def subset_iff)
    have inj_invf: "inj_on invf (T - {1})"
      using \<theta>no_int [of 1] \<open>\<theta> n = 1\<close> inv_into_injective T
      by (fastforce simp: inj_on_def invf_def)
    have invf_iff: "invf t = i \<longleftrightarrow> (i<n \<and> t = frac (\<theta> i))" if "t \<in> T-{1}" for i t
      using that T by auto
    have sumN: "(\<Sum>i\<in>N. f i) = (\<Sum>x\<in>T - {1}. f (invf x))" for f :: "nat \<Rightarrow> int"
      using inj_invf T  by (simp add: N_def sum.reindex)
    define T' where "T' \<equiv> insert 1 (\<theta> ` N)"
    have [simp]: "finite T'" "1 \<in> T'"
      using T'_def N_def \<open>finite T\<close> by auto
    have T'sub: "T' \<subseteq> \<theta> ` {..n}"
      using Nsub T'_def \<theta>image by blast
    have in_N_not1: "x \<in> N \<Longrightarrow> \<theta> x \<noteq> 1" for x
      using \<theta>no_int [of 1] by (metis N_def image_iff invf_iff lessThan_iff of_int_1)
    define u' where "u' = (u \<circ> frac)(1:=(if 1\<in>T then u 1 else 0) + (\<Sum>i\<in>N. - \<lfloor>\<theta> i\<rfloor> * u (frac (\<theta> i))))"
    have "(\<Sum>v\<in>T'. real_of_int (u' v) * v) = u' 1 + (\<Sum>v \<in> \<theta> ` N. real_of_int (u' v) * v)"
      using \<open>finite N\<close> by (simp add: T'_def image_iff in_N_not1)
    also have "\<dots> = u' 1 + sum ((\<lambda>v. real_of_int (u' v) * v) \<circ> \<theta>) N"
      by (smt (verit) N_def \<open>finite N\<close> image_iff invf_iff sum.reindex_nontrivial)
    also have "\<dots> = u' 1 + (\<Sum>i\<in>N. of_int ((u \<circ> frac) (\<theta> i)) * \<theta> i)"
      by (auto simp add: u'_def in_N_not1)
    also have "\<dots> = u' 1 + (\<Sum>i\<in>N. of_int ((u \<circ> frac) (\<theta> i)) * (floor (\<theta> i) + frac(\<theta> i)))"
      by (simp add: frac_def cong: if_cong)
    also have "\<dots> = (\<Sum>v\<in>T. of_int (u v) * v)"
    proof (cases "1 \<in> T")
      case True
      then have T1: "(\<Sum>v\<in>T. real_of_int (u v) * v) = u 1 + (\<Sum>v\<in>T-{1}. real_of_int (u v) * v)"
        by (simp add: \<open>finite T\<close> sum.remove)
      show ?thesis
        using inj_invf True T unfolding N_def u'_def
        by (auto simp: add.assoc distrib_left sum.reindex T1 simp flip: sum.distrib intro!: sum.cong)
    next
      case False
      then show ?thesis
        using inj_invf T unfolding N_def u'_def
        by (auto simp: algebra_simps sum.reindex simp flip: sum.distrib intro!: sum.cong)
    qed
    also have "\<dots> = 0"
      using uv_eq0 by blast
    finally have 0: "(\<Sum>v\<in>T'. real_of_int (u' v) * v) = 0" .
    have "u v = 0" if T'0: "\<And>v. v\<in>T' \<Longrightarrow> u' v = 0"
    proof -
      have [simp]: "u t = 0" if "t \<in> T - {1}" for t
      proof -
        have "\<theta> (invf t) \<in> T'"
          using N_def T'_def that by blast
        then show ?thesis
          using that T'0 [of "\<theta> (invf t)"]
          by (smt (verit, best) in_N_not1 N_def fun_upd_other imageI invf_iff o_apply u'_def)
      qed
      show ?thesis
      proof (cases "v = 1")
        case True
        then have "1 \<in> T"
          using \<open>v \<in> T\<close> by blast
        have "(\<Sum>v\<in>T. real_of_int (u v) * v) = u 1 + (\<Sum>v\<in>T - {1}. real_of_int (u v) * v)"
          using True \<open>finite T\<close> \<open>v \<in> T\<close> mk_disjoint_insert by fastforce
        then have "0 = u 1"
          using uv_eq0 by auto
        with True show ?thesis by presburger
      next
        case False
        then have "\<theta> (invf v) \<in> \<theta> ` N"
          using N_def \<open>v \<in> T\<close> by blast
        then show ?thesis
          using that [of "\<theta> (invf v)"] False \<open>v \<in> T\<close> T by (force simp: T'_def in_N_not1 u'_def)
      qed
    qed
    with indp T'sub \<open>finite T'\<close> 0 show "u v = 0"
      unfolding dependent_explicit by blast
  qed
  moreover have "inj_on \<theta>' {..<Suc n}"
    using inj\<theta>' 
    unfolding \<theta>'_def inj_on_def 
    by (metis comp_def frac_lt_1 fun_upd_other fun_upd_same lessThan_Suc_atMost less_irrefl)
  ultimately obtain t h where th: "\<And>i. i < Suc n \<Longrightarrow> \<bar>t * \<theta>' i - of_int (h i) - (\<alpha>(n:=0)) i\<bar> < \<epsilon>/2"
    using Kronecker_thm_1 [of \<theta>' "Suc n" "\<epsilon>/2"] lessThan_Suc_atMost assms using half_gt_zero by blast
  define k where "k = h n"
  define m where "m \<equiv> \<lambda>i. h i + k * \<lfloor>\<theta> i\<rfloor>"
  show thesis
  proof
    fix i assume "i < n"
    have "\<bar>k * frac (\<theta> i) - h i - \<alpha> i\<bar> < \<epsilon>" 
    proof -
      have "\<bar>k * frac (\<theta> i) - h i - \<alpha> i\<bar> = \<bar>t * frac (\<theta> i) - h i - \<alpha> i + (k-t) * frac (\<theta> i)\<bar>"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> \<bar>t * frac (\<theta> i) - h i - \<alpha> i\<bar> + \<bar>(k-t) * frac (\<theta> i)\<bar>"
        by linarith
      also have "\<dots> \<le> \<bar>t * frac (\<theta> i) - h i - \<alpha> i\<bar> + \<bar>k-t\<bar>"
        using frac_lt_1 [of "\<theta> i"] le_less by (fastforce simp add: abs_mult)
      also have "\<dots> < \<epsilon>"
        using th[of i] th[of n] \<open>i<n\<close> 
        by (simp add: k_def \<theta>'_def) (smt (verit, best))
      finally show ?thesis .
    qed
    then show "\<bar>k * \<theta> i - m i - \<alpha> i\<bar> < \<epsilon>"
      by (simp add: algebra_simps frac_def m_def)
  qed
qed
(* TODO: use something like module.independent_family instead *)


section \<open>Applications to the Riemann Zeta Function\<close>

(*Use results from the theory Conditionally_Complete_Lattices here*)

lemma norm_zeta_same_Im_le:
  fixes \<sigma> t :: real
  assumes "\<sigma> > 1"
  shows   "norm (zeta (\<sigma> + \<i> * t)) \<le> Re (zeta \<sigma>)"
proof -
  have "norm (zeta (\<sigma> + \<i> * t)) = norm (\<Sum>n. of_nat (Suc n) powr (-\<sigma> - \<i> * t))"
    using assms by (subst zeta_conv_suminf) auto
  also have "\<dots> \<le> (\<Sum>n. norm (of_nat (Suc n) powr (-\<sigma> - \<i> * t)))"
  proof (rule summable_norm)
    show "summable (\<lambda>n. norm (of_nat (Suc n) powr (of_real (-\<sigma>) - \<i> * of_real t)))"
      using summable_zeta_real[of \<sigma>] assms by (simp add: norm_powr_real_powr)
  qed
  also have "\<dots> = (\<Sum>n. of_nat (Suc n) powr -\<sigma>)"
    by (simp add: norm_powr_real_powr)
  also have "\<dots> = (\<Sum>n. Re (of_nat (Suc n) powr -of_real \<sigma>))"
    by (simp add: powr_Reals_eq)
  also have "\<dots> = Re (\<Sum>n. of_nat (Suc n) powr -of_real \<sigma> :: complex)"
    by (intro Re_suminf [symmetric]) (use summable_zeta[of "of_real \<sigma>"] assms in auto)
  also have "(\<Sum>n. of_nat (Suc n) powr -of_real \<sigma>) = zeta \<sigma>"
    using assms by (subst zeta_conv_suminf) auto
  finally show "norm (zeta (\<sigma> + \<i> * t)) \<le> Re (zeta \<sigma>)" .
qed

lemma Euler_product_inverse_zeta:
  assumes "Re s > 1"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then 1 - 1 / of_nat p powr s else 1) \<longlonglongrightarrow> 1 / zeta s"
proof -
  have "(\<lambda>n. inverse (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1))
          \<longlonglongrightarrow> inverse (zeta s)"
    using assms by (intro tendsto_inverse euler_product_zeta) (auto simp: zeta_Re_gt_1_nonzero)
  also have "(\<lambda>n. inverse (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr s) else 1)) =
             (\<lambda>n. \<Prod>p\<le>n. if prime p then 1 - 1 / of_nat p powr s else 1)"
    by (subst prod_inversef [symmetric]) (auto intro!: ext prod.cong)
  finally show ?thesis
    by (simp add: field_simps)
qed


text \<open>First part of equation (17) on page 155\<close>
lemma prod_tendsto_zeta:
  fixes \<sigma> t :: real
  assumes "\<sigma> > 1"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then 1 + real p powr -\<sigma> else 1)
        \<longlonglongrightarrow> Re (zeta \<sigma> / zeta (2 * of_real \<sigma>))"
proof -
  have "(\<lambda>n. (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr (of_real \<sigma>)) else 1) /
             (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr (2 * of_real \<sigma>)) else 1))
          \<longlonglongrightarrow> (zeta (of_real \<sigma>) / zeta (2 * of_real \<sigma>))"
    using assms by (intro tendsto_divide euler_product_zeta) (auto simp: zeta_Re_gt_1_nonzero)
  also have "(\<lambda>n. (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr (of_real \<sigma>)) else 1) /
                  (\<Prod>p\<le>n. if prime p then inverse (1 - 1 / of_nat p powr (2 * complex_of_real \<sigma>)) else 1)) =
             (\<lambda>n. (\<Prod>p\<le>n. if prime p then 
               (1 - 1 / of_nat p powr (2 * of_real \<sigma>)) / (1 - 1 / of_nat p powr (of_real \<sigma>)) else 1))"
    by (auto simp: fun_eq_iff field_simps simp flip: prod_dividef intro!: prod.cong)
  also have "\<dots> = (\<lambda>n. (\<Prod>p\<le>n. if prime p then of_real (1 + real p powr -\<sigma>) else 1))"
  proof (intro ext prod.cong if_cong refl)
    fix n p :: nat
    assume p: "p \<in> {..n}" "prime p"
    have "p > 1"
      using p prime_gt_1_nat by simp
    define x where "x = 1 / of_nat p powr complex_of_real \<sigma>"
    define x' where "x' = 1 / real p powr \<sigma>"
    have x_x': "x = of_real x'"
      by (simp add: x'_def x_def powr_Reals_eq)
    have "x' \<noteq> 1"
      using \<open>p > 1\<close> assms by (simp add: x'_def)
    hence "x \<noteq> 1"
      by (simp add: x_x')

    have "of_nat p powr (2 * of_real \<sigma>) = (of_nat p powr complex_of_real \<sigma>) ^ 2"
      by (metis mult_2 power2_eq_square powr_add)
    hence "(1 - 1 / of_nat p powr (2 * of_real \<sigma>)) / (1 - 1 / of_nat p powr complex_of_real \<sigma>) =
           (1 - x ^ 2) / (1 - x)"
      by (simp add: x_def field_simps)
    also have "\<dots> = 1 + x"
      using \<open>x \<noteq> 1\<close> by (auto simp: field_simps power2_eq_square)
    also have "\<dots> = of_real (1 + x')"
      by (simp add: x_x')
    finally show "(1 - 1 / of_nat p powr (2 * of_real \<sigma>)) / (1 - 1 / of_nat p powr of_real \<sigma>) =
                  complex_of_real (1 + real p powr -\<sigma>)"
      by (simp add: x'_def powr_minus field_simps)
  qed
  finally have \<section>: "(\<lambda>n. \<Prod>p\<le>n. if prime p then of_real (1 + real p powr -\<sigma>) else 1)
  \<longlonglongrightarrow> zeta \<sigma> / zeta (2 * of_real \<sigma>)" .  
  show ?thesis
    using continuous_on_tendsto_compose [of UNIV Re, OF _ \<section>] 
          continuous_on_Re [where g=id]
    by (auto simp: Re_prod_Reals if_distrib cong: if_cong)
qed


text \<open>Second part of equation (17) on page 155\<close>
lemma norm_zeta_same_Im_ge:
  fixes \<sigma> t :: real
  assumes "\<sigma> > 1"
  shows   "norm (zeta (\<sigma> + \<i> * t)) \<ge> Re (zeta (2 * \<sigma>)) / Re (zeta \<sigma>)"
proof -
  define s where "s = \<sigma> + \<i> * t"
  have "zeta s \<noteq> 0"
    by (simp add: assms s_def zeta_Re_gt_1_nonzero)
  have "(\<lambda>n. \<Prod>p\<le>n. if prime p then 1 - 1 / of_nat p powr s else 1) \<longlonglongrightarrow> 1 / zeta s"
    by (rule Euler_product_inverse_zeta) (use assms in \<open>auto simp: s_def\<close>)
  hence "(\<lambda>n. norm (\<Prod>p\<le>n. if prime p then 1 - 1 / of_nat p powr s else 1)) \<longlonglongrightarrow> norm (1 / zeta s)"
    by (intro tendsto_norm)
  also have "(\<lambda>n. norm (\<Prod>p\<le>n. if prime p then 1 - 1 / of_nat p powr s else 1)) =
             (\<lambda>n. \<Prod>p\<le>n. norm (if prime p then 1 - 1 / of_nat p powr s else 1))"
    by (auto simp flip: prod_norm cong: if_cong)
  finally have lim1:
    "(\<lambda>n. \<Prod>p\<le>n. norm (if prime p then 1 - 1 / of_nat p powr s else 1)) \<longlonglongrightarrow> 1 / norm (zeta s)"
    by (simp add: norm_divide)
  have "cmod (1 - 1 / of_nat p powr s) \<le> 1 + real p powr -\<sigma>" if "p \<le> n" for n p
  proof -
    have "of_nat p powr s = of_real (of_nat p powr \<sigma>) * cis (t * ln (of_nat p))" 
      by (simp add: s_def exp_add cis_conv_exp powr_def mult_ac distrib_left flip: exp_of_real)
    then have *: "1 / of_nat p powr s = of_real (1 / (of_nat p powr \<sigma>)) * cis (- t * ln (of_nat p))"
      by (simp add: inverse_eq_divide flip: cis_inverse)
    have "cmod (1 - 1 / of_nat p powr s) \<le> cmod 1 + cmod (1 / (of_nat p powr s))" 
      using norm_triangle_ineq4 by blast
    also have "\<dots> = 1 + real p powr -\<sigma>"
      by (simp add: * norm_divide powr_minus_divide)
    finally show ?thesis by simp
  qed
  then have "(\<Prod>p\<le>n. norm (if prime p then 1 - 1 / of_nat p powr s else 1)) 
          \<le> (\<Prod>p\<le>n. if prime p then (1 + real p powr -\<sigma>) else 1)" for n
    by (intro prod_mono) auto
  then have *: "1 / norm (zeta s) \<le> Re (zeta \<sigma> / zeta (2 * of_real \<sigma>))"
    by (intro tendsto_le [OF _ prod_tendsto_zeta [OF assms] lim1] sequentially_bot) auto
  have "Re (zeta (2 * \<sigma>)) / Re (zeta \<sigma>) = 1 / Re (zeta \<sigma> / zeta (2 * of_real \<sigma>))"
    using zeta_real' by auto
  also have "\<dots> \<le> norm (zeta s)"
    using le_imp_inverse_le [OF *] by (simp add: \<open>zeta s \<noteq> 0\<close> inverse_eq_divide)
  finally show ?thesis
    unfolding s_def .
qed



text \<open>Theorem 7.11, the easy bit (for the supremum), first line of Apostol's proof\<close>
theorem Sup_7_11:
  fixes \<sigma>:: real
  assumes "\<sigma> > 1"
  shows "(SUP t. cmod (zeta(Complex \<sigma> t))) = Re (zeta \<sigma>)"
proof -
  have "cmod (zeta \<sigma>) = Re (zeta \<sigma>)"
    using norm_zeta_same_Im_le [OF assms] by (smt (verit) in_Reals_norm norm_ge_zero zeta_real)
  then show ?thesis
    by (metis (no_types, lifting) norm_zeta_same_Im_le [OF assms] cSup_eq_maximum Complex_eq 
        complex_of_real_def rangeE rangeI)
qed

text \<open>Arguably the natural form\<close>
corollary Sup_7_11b:
  fixes \<sigma>:: real
  assumes "\<sigma> > 1"
  shows "of_real(SUP t. cmod (zeta(Complex \<sigma> t))) = zeta \<sigma>"
  using zeta_real' by (simp add: Sup_7_11 assms)


text \<open>Theorem 7.11, the hard bit (for the infimum)\<close>
theorem Inf_7_11:
  fixes \<sigma>:: real
  assumes "\<sigma> > 1"
  shows "(INF t. cmod (zeta(Complex \<sigma> t))) = Re (zeta (2 * \<sigma>)) / Re (zeta \<sigma>)" (is "Inf ?F = ?rhs")
proof (intro antisym)
  show rhs_le_INFF: "?rhs \<le> Inf ?F"
    by (metis Complex_eq UNIV_I empty_iff norm_zeta_same_Im_ge [OF assms] cINF_greatest)
  interpret Modules.module "(\<lambda>r. (*) (real_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  define pr where "pr \<equiv> enumerate {p::nat. prime p}"
    \<comment> \<open>enumeration of the primes, starting from 0 (not 1 as in the text)\<close>
  have [simp]: "strict_mono pr"
    by (simp add: pr_def primes_infinite strict_mono_enumerate)
  have prime_iff: "prime n \<longleftrightarrow> (\<exists>k. n = pr k)" for n
    using enumerate_Ex enumerate_in_set pr_def primes_infinite by blast
  then have pnp: "prime (pr k)" for k
    using prime_iff by blast
  then have pr_gt1: "real (pr k) > 1" for k
    by (metis of_nat_1 of_nat_less_iff prime_gt_1_nat)
  have pr_gt: "n < pr n" for n
  proof (induction n)
    case 0
    then show ?case
      by (simp add: pnp prime_gt_0_nat) 
  next
    case (Suc n)
    then show ?case
      by (metis Suc.IH Suc_n_not_le_n \<open>strict_mono pr\<close> less_trans_Suc not_le strict_mono_less_eq)
  qed
  define \<theta> where "\<theta> \<equiv> \<lambda>k. - ln (pr k) / (2 * pi)"
  have "inj pr"
    by (simp add: strict_mono_imp_inj_on)
  then have inj\<theta>: "inj \<theta>"
    by (auto simp: inj_on_def \<theta>_def pnp prime_gt_0_nat)
  have [simp]: "pr 0 = 2"
    by (simp add: pr_def enumerate.simps Least_equality prime_ge_2_nat)
  have prod_if_prime_eq: "(\<Prod>p\<le>pr n. if prime p then w p else 1) = (\<Prod>k\<le>n. w (pr k))" (is "?L=?R")
    for w :: "nat \<Rightarrow> complex" and n
  proof -
    have "\<And>p. p \<le> pr n \<Longrightarrow> prime p \<Longrightarrow> \<exists>m\<le>n. p = pr m"
      by (metis \<open>strict_mono pr\<close> prime_iff strict_mono_less_eq)
    then have eq: "{k. k \<le> pr n \<and> prime k} = pr ` {..n}" 
      by (fastforce simp: image_iff Bex_def pnp strict_mono_less_eq)
    have "?L = prod w {x \<in> {..pr n}. prime x}"
      by (metis finite_atMost prod.inter_filter)
    also have "\<dots> = ?R"
      by (simp add: eq prod.reindex strict_mono_imp_inj_on)
    finally show ?thesis .
  qed
  have prod_if_prime_eq_real: "(\<Prod>p\<le>pr n. if prime p then w p else 1) = (\<Prod>k\<le>n. w (pr k))" 
    for w :: "nat \<Rightarrow> real" and n
  proof -
    have "complex_of_real(\<Prod>p\<le>pr n. if prime p then w p else 1) = (\<Prod>k\<le>n. w (pr k))"
      using prod_if_prime_eq [of "of_real \<circ> w" n] 
      by simp (smt (verit, best) o_apply of_real_1 prod.cong)
    then show ?thesis
      using of_real_eq_iff by blast
  qed
  have zeta_nz: "zeta (Complex \<sigma> t) \<noteq> 0" for t
    using assms complex.sel(1) zeta_Re_gt_1_nonzero by presburger
  then obtain zeta_pos: "Re (zeta \<sigma>) > 0" "Re (zeta (of_real \<sigma> * 2)) > 0"
    by (smt (verit) Complex_eq Re_complex_of_real assms complex_of_real_def mult_2_right 
            norm_zeta_same_Im_le of_real_add zero_less_norm_iff zeta_Re_gt_1_nonzero)
  then have rhs_pos: "?rhs > 0"
    by (auto simp: field_simps)
  with rhs_le_INFF have INFF_pos: "Inf ?F > 0"
    by linarith

  have get_t: "\<exists>t. \<forall>k<n. 1 + pr k powr -\<sigma> * cos \<epsilon> < norm (1 - pr k powr (- Complex \<sigma> t))"
    if \<epsilon>: "0 < \<epsilon>" "\<epsilon> < pi/2" and "n>0" for \<epsilon>::real and n::nat
        \<comment> \<open>(19) follows trivially from this\<close>
  proof -
    have "u (\<theta> k) = 0" if "k<n" "(\<Sum>k<n. of_int (u (\<theta> k)) * \<theta> k) = 0" for u k
    proof -
      define Pos where "Pos \<equiv> {k. u (\<theta> k) \<ge> 0}"
      define L where "L \<equiv> \<Prod>p \<in> pr ` ({..<n} \<inter> Pos). p ^ nat (u (\<theta> (inv_into UNIV pr p)))"
      define R where "R \<equiv> \<Prod>p \<in> pr ` ({..<n} - Pos). p ^ nat (- u (\<theta> (inv_into UNIV pr p)))"
      have "(\<Sum>k<n. u (\<theta> k) * ln (pr k)) = 0"
        using that by (simp add: \<theta>_def sum_negf flip: sum_divide_distrib)
      then have "ln (\<Prod>k<n. (pr k powr u (\<theta> k))) = 0"
        using prime_gt_0_nat [OF pnp] by (simp add: ln_prod ln_powr)
      then have 1: "(\<Prod>k<n. pr k powr u (\<theta> k)) = 1"
        by (simp add: pnp prime_gt_0_nat prod_pos)
      have "(\<Prod>k<n. pr k powr u (\<theta> k)) 
          = (\<Prod>k<n. if u (\<theta> k) \<ge> 0 then real (pr k) ^ nat (u (\<theta> k)) else 1 / real (pr k) ^ nat (- u (\<theta> k)))"
        by (smt (verit, best) prod.cong powr_int pr_gt1)
      also have "\<dots> = (\<Prod>k\<in>{..<n} \<inter> Pos. real (pr k) ^ nat (u (\<theta> k))) * (\<Prod>k\<in>{..<n} - Pos. 1 / (pr k) ^ nat (- u (\<theta> k)))"
        by (simp add: prod.If_cases Pos_def Diff_eq)
      also have "\<dots> = (\<Prod>k\<in>{..<n} \<inter> Pos. real (pr k) ^ nat (u (\<theta> k))) / (\<Prod>k\<in>{..<n} - Pos. (pr k) ^ nat (- u (\<theta> k)))"
        by (simp add: prod_dividef)
      finally have "(\<Prod>k\<in>{..<n} \<inter> Pos. real (pr k) ^ nat (u (\<theta> k))) = (\<Prod>k\<in>{..<n} - Pos. (pr k) ^ nat (- u (\<theta> k)))"
        using 1 by simp
      then have "(\<Prod>k\<in>{..<n} \<inter> Pos. pr k ^ nat (u (\<theta> k))) = (\<Prod>k\<in>{..<n} - Pos. pr k ^ nat (- u (\<theta> k)))"
        by (smt (verit) of_nat_eq_iff of_nat_power of_nat_prod prod.cong)
      then have "L = R"
        using \<open>inj pr\<close> by (simp add: L_def R_def prod.reindex inj_on_def)
      moreover have "multiplicity (pr k) L = (if k<n \<and> k \<in> Pos then nat (u (\<theta> k)) else 0)" for k
        unfolding L_def using \<open>inj pr\<close>
        by (subst multiplicity_prod_prime_powers) (auto simp: pnp inv_f_f inj_eq)
      moreover have "multiplicity (pr k) R = (if k<n \<and> k \<notin> Pos then nat (- u (\<theta> k)) else 0)" for k
        unfolding R_def using \<open>inj pr\<close>
        by (subst multiplicity_prod_prime_powers) (auto simp: pnp inv_f_f inj_eq)
      ultimately show ?thesis
        by (smt (verit, best) less_irrefl local.Pos_def mem_Collect_eq that zero_less_nat_eq)
    qed
    with inj\<theta> have ind\<theta>: "module.independent (\<lambda>r x. of_int r * x) (\<theta> ` {..<n})"
      by (auto simp: dependent_finite sum.reindex inj_on_def)
    obtain t h where "\<And>k. k < n \<Longrightarrow> \<bar>t * \<theta> k - of_int (h k) - 1/2\<bar> < \<epsilon> / (2*pi)"
      using Kronecker_thm_1 [OF ind\<theta>, of "\<epsilon> / (2*pi)" "\<lambda>_. 1/2"] \<epsilon> inj\<theta> 
      by (auto simp add: inj_on_def)
    then have th: "\<And>k. k < n \<Longrightarrow> \<bar>-t * ln (pr k) - pi - 2 * pi * h k\<bar> < \<epsilon>"
      using \<epsilon> by (fastforce simp add: \<theta>_def field_simps)
      \<comment> \<open>Equation (18), page 156\<close>
    show ?thesis
    proof (intro exI strip)
      fix k assume "k<n"
      let ?s = "Complex \<sigma> t"
      have "1 - pr k powr -?s = 1 - pr k powr -\<sigma> * exp (- \<i> * t * ln (pr k))"
        by (simp add: Complex_eq powr_def exp_diff exp_minus of_real_exp field_simps)
      also have "\<dots> = 1 + pr k powr -\<sigma> * exp (\<i> * (- t * ln (pr k) - pi))"
        by (simp add: algebra_simps exp_diff)
      also have "\<dots> = 1 + pr k powr -\<sigma> * cos (- t * ln (pr k) - pi) + \<i> * pr k powr -\<sigma> * sin (- t * ln (pr k) - pi)"
        unfolding exp_Euler sin_of_real cos_of_real by (simp add: complex_eq_iff)
      finally have *: "norm (1 - pr k powr -?s) \<ge> 1 + pr k powr -\<sigma> * cos (- t * ln (pr k) - pi)"
        by (metis Complex_eq complex.sel(1) mult.assoc of_real_mult complex_Re_le_cmod)
      have "cos \<epsilon> < cos \<bar>-t * ln (pr k) - pi - 2 * pi * h k\<bar>"
        by (smt (verit, best) \<epsilon> pi_ge_two pi_half_less_two \<open>k < n\<close> th cos_monotone_0_pi)
      also have "\<dots> = cos \<bar>-t * ln (pr k) - pi\<bar>"
        by (metis cos_abs_real cos_minus minus_diff_eq sin_cos_eq_iff uminus_add_conv_diff)
      finally have "(pr k powr -\<sigma>) * cos \<epsilon> < (pr k powr -\<sigma>) * - cos (t * ln (pr k))"
        using pr_gt1 [of k] mult_strict_left_mono by fastforce
      with * show "1 + pr k powr -\<sigma> * cos \<epsilon> < norm (1 - pr k powr -?s)"
        by simp
    qed
  qed

  define f where "f \<equiv> \<lambda>t k. 1 - pr k powr -(Complex \<sigma> t)"
  have norm_f_has_prod: "(\<lambda>k. norm (f t k)) has_prod (1 / norm (zeta (Complex \<sigma> t)))" for t::real
  proof -
    let ?s = "Complex \<sigma> t"
    have "(\<lambda>k. inverse (f t k)) has_prod zeta ?s"
      unfolding has_prod_def
    proof (rule disjI1)
      show "raw_has_prod (\<lambda>k. inverse (f t k)) 0 (zeta ?s)"
        unfolding raw_has_prod_def
      proof
        have "(\<lambda>n. \<Prod>p\<le>pr n. if prime p then inverse (1 - 1 / p powr ?s) else 1) \<longlonglongrightarrow> zeta ?s"
          using LIMSEQ_subseq_LIMSEQ [OF euler_product_zeta, of "?s" pr] assms by (simp add: o_def)
        then show "(\<lambda>n. \<Prod>i\<le>n. inverse (f t (i+0))) \<longlonglongrightarrow> zeta ?s"
          by (auto simp: prod_if_prime_eq powr_minus inverse_eq_divide f_def)
      qed (auto simp add: zeta_nz)
    qed
    then have "(\<lambda>k. norm (inverse (f t k))) has_prod norm (zeta ?s)"
      using has_prod_norm assms by blast
    moreover have "1 / cmod (inverse z) = cmod z" for z
      by (metis inverse_eq_divide inverse_inverse_eq norm_inverse)
    ultimately show ?thesis
      by (smt (verit, best) has_prod_cong has_prod_inverse inverse_eq_divide)
  qed
  then have conv_prod_nf: "convergent_prod (\<lambda>k. norm (f t k))" for t
    using has_prod_iff by blast
  have f_nonzero: "f t k \<noteq> 0" for k t
    using has_prod_nonzero norm_f_has_prod zeta_nz by fastforce

  define prod_f where "prod_f \<equiv> \<lambda>m m' t. \<Prod>k = m..m'. f t k"
  have norm_pr_12: "cmod (pr i powr -(Complex \<sigma> t)) < 1/2" for i t
  proof -
    have "cmod (pr i powr -(Complex \<sigma> t)) \<le> 2 powr -\<sigma>"
      using assms norm_powr_real_powr pnp powr_mono2' prime_ge_2_nat by auto
    also have "\<dots> < 1/2"
      by (smt (verit, del_insts) assms powr_less_mono powr_neg_one)
    finally show ?thesis .
  qed

  have summable_m\<sigma>: "summable (\<lambda>n. (Suc n) powr -\<sigma>)"
    using assms summable_zeta_real by force
  moreover have "(pr n) powr -\<sigma> \<le> (1 + real n) powr -\<sigma>" for n
    by (smt (verit, best) assms nat_less_real_le of_nat_0_le_iff powr_mono2' pr_gt)
  ultimately have summable_pr: "summable (\<lambda>i. real (pr i) powr -\<sigma>)" 
    by (force intro: summable_comparison_test')
  \<comment> \<open>remove the dependence upon t: Tip from Ofir Gorodetsky on MathOverflow\<close>
  have norm_Ln_f_le: "cmod (Ln (f t i)) \<le> 2 * real (pr i) powr -\<sigma>" for i t
  proof -
    have "cmod (Ln (f t i)) \<le> 2 * norm (pr i powr -(Complex \<sigma> t))" 
      by (metis norm_pr_12 add_uminus_conv_diff f_def norm_Ln_le norm_minus_cancel)
    also have "\<dots> \<le> 2 * real (pr i) powr -\<sigma>"
      by (simp add: norm_powr_real_powr)
    finally show ?thesis .
  qed
    \<comment> \<open>the conclusion holds for all $t$: not for one, as in Apostol's text \<close>
  have Cauchy: "\<exists>n0>0. \<forall>n k t. k\<ge>n \<longrightarrow> n \<ge> n0 \<longrightarrow> dist (prod (\<lambda>k. norm (f t k)) {n..k}) 1 < \<epsilon>"
    if \<epsilon>: "0 < \<epsilon>" for \<epsilon>::real
  proof -
    obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>z. z \<noteq> 0 \<Longrightarrow> cmod (Ln z) < \<delta> \<Longrightarrow> dist z 1 < \<epsilon>"
    proof -
      have "uniformly_continuous_on (cball (0::complex) 1) exp"
        by (intro compact_uniformly_continuous continuous_intros) auto
      with Ln_1 show ?thesis
        apply (simp add: uniformly_continuous_on_def Ball_def)
        by (smt (verit) \<epsilon> exp_gt_zero exp_Ln exp_zero norm_conv_dist norm_zero that)
    qed
    obtain N where N: "\<And>n k. k\<ge>n \<Longrightarrow> n \<ge> N \<Longrightarrow> (\<Sum>i = n..k. 2 * real (pr i) powr -\<sigma>) < \<delta>"
      using summable_mult [OF summable_pr, of 2] \<open>\<delta> > 0\<close>
      unfolding summable_Cauchy real_norm_def
      by (smt (verit, best) atLeastLessThanSuc_atLeastAtMost)
    define n0 where "n0 \<equiv> Suc N"
    have n0: "\<And>n k. k\<ge>n \<Longrightarrow> n \<ge> n0 \<Longrightarrow> (\<Sum>i = n..k. 2 * real (pr i) powr -\<sigma>) < \<delta>"
      using N by (force simp add: n0_def)
    show ?thesis
    proof (intro exI conjI strip)
      fix n k t
      assume "n0 \<le> n" "n \<le> k"
      have "cmod (Ln(prod_f n k t)) \<le> (\<Sum>i = n..k. cmod (Ln (f t i)))"
        unfolding prod_f_def by (metis f_nonzero norm_Ln_prod_le)
      also have "\<dots> \<le> (\<Sum>i = n..k. 2 * real (pr i) powr -\<sigma>)"
        by (meson norm_Ln_f_le sum_mono)
      finally have "cmod (Ln(prod_f n k t)) \<le> (\<Sum>i = n..k. 2 * real (pr i) powr -\<sigma>)" . 
      moreover
      have "(prod_f n k t) \<noteq> 0" for n k t
        by (simp add: prod_f_def f_nonzero)
      ultimately have "dist (prod_f n k t) 1 < \<epsilon>"
        using \<open>n \<le> k\<close> \<open>n0 \<le> n\<close> n0 \<delta> by (meson le_less_trans)
      then show "dist (\<Prod>k = n..k. cmod (f t k)) 1 < \<epsilon>"
        unfolding prod_f_def
        by (smt (verit) dist_commute dist_norm dist_real_def norm_one norm_triangle_ineq2 prod.cong prod_norm)
    qed (use n0_def in auto)
  qed

  \<comment> \<open>Now consider any partial product of the Euler product\<close>
  have eps_le: "(1-\<epsilon>) * (\<Prod>k. 1 + pr k powr -\<sigma> * cos \<epsilon>) \<le> 1 / Inf ?F" 
    if \<epsilon>: "0 < \<epsilon>" "\<epsilon> < 1" for \<epsilon>::real 
  proof -
    have \<epsilon>2: "\<epsilon>/2 > 0" "\<epsilon> < pi/2"
      using pi_ge_two \<epsilon> by auto
    with Cauchy obtain n0 where "n0>0" and n0: 
        "\<And>t n k. \<lbrakk>k\<ge>n; n \<ge> n0\<rbrakk> \<Longrightarrow> dist (prod (\<lambda>k. norm (f t k)) {n..k}) 1 < \<epsilon>/2"
      by metis
    define h where "h \<equiv> \<lambda>k. pr k powr -\<sigma> * cos \<epsilon>"
    have h_ge1: "1 + h k \<ge> 1" for k
      by (smt (verit, best) \<epsilon>(1) \<epsilon>2(2) cos_gt_zero_pi h_def mult_pos_pos powr_gt_zero pr_gt1)
    have prod_h_le: "(\<Prod>k<n. 1 + h k) \<le> 1 / ((1-\<epsilon>) * Inf ?F)" if "n\<ge>n0" for n
    proof -      
      have "n>0"
        using \<open>0 < n0\<close> that by linarith
      obtain t where t: "\<And>k. k<n \<Longrightarrow> 1 + h k < norm (f t k)"
        using get_t \<epsilon>(1) \<epsilon>2(2) \<open>n>0\<close> f_def h_def by blast
      let ?s = "Complex \<sigma> t"
      have Re_s: "1 < Re ?s"
        by (simp add: assms)
      have prod_h_less_nf: "(\<Prod>k<n. 1 + h k) < (\<Prod>k<n. norm (f t k))"
      proof (intro prod_mono_strict conjI)
        fix k :: nat
        assume i: "k \<in> {..<n}"
        show "0 \<le> 1 + h k"
          using \<epsilon>(1) \<epsilon>2(2) cos_ge_zero h_def by force
      qed (use \<open>n>0\<close> f_def t in auto)
      also have eq_cmod_prod_f: "\<dots> = norm (\<Prod>k<n. f t k)"
        using prod_norm by fastforce
      finally have 19: "(\<Prod>k<n. 1 + h k) < cmod (prod (f t) {..<n})" .

      define L where "L \<equiv> prodinf (\<lambda>i. norm (f t (i + n)))"
      have "\<And>k. k \<ge> n \<Longrightarrow> dist (\<Prod>i = n..k. cmod (f t i)) 1 < \<epsilon>/2"
        using n0 that by blast
      moreover have "(\<Prod>i = n..k. cmod (f t i)) 
                   = (if k < n then 1 else \<Prod>i\<le>k - n. cmod (f t (i + n)))" for k
      proof (cases "k < n")
        case False
        then have inj: "inj_on ((+)(n)) {..k - n}"
          by (simp add: inj_on_def)
        have "((+) (n) ` {..k - n}) = {n..k}"
          using False image_add_atLeastAtMost [of "n" 0] by (simp add: atLeast0AtMost)
        then show ?thesis
          using prod.reindex [OF inj, of "cmod \<circ> (f t)"] False by (simp add: add.commute)
      qed auto
      ultimately have dist_less: "\<And>k. dist (\<Prod>i\<le>k. cmod (f t (i + n))) 1 < \<epsilon>/2"
        by (metis diff_add_inverse le_add1 not_add_less1)
      have has_prod_L: "(\<lambda>i. cmod (f t (i + n))) has_prod L"
        using conv_prod_nf L_def convergent_prod_ignore_initial_segment by blast
      have "dist L 1 < \<epsilon>"
      proof -
        have "(\<lambda>k. \<Prod>i\<le>k. cmod (f t (i + n))) \<longlonglongrightarrow> L"
          unfolding L_def
          using conv_prod_nf convergent_prod_ignore_initial_segment convergent_prod_LIMSEQ by blast
        then obtain N where "dist (\<Prod>i\<le>N. cmod (f t (i + n))) L < \<epsilon>/2"
          unfolding LIMSEQ_def using \<epsilon>2 by blast
        with dist_less dist_triangle_half_r show ?thesis
          by blast
      qed
      then have L: "1-\<epsilon> < L \<and> L < 1+\<epsilon>"
        using dist_real_def by force
      moreover have "0 < (\<Prod>k<n. 1 + h k)"
        by (smt (verit, best) h_ge1 prod_pos)
      ultimately have "(1-\<epsilon>) * (\<Prod>k<n. 1 + h k) < L * (\<Prod>k<n. norm (f t k))"
        by (simp add: \<epsilon>(2) prod_h_less_nf mult_strict_mono' order_less_imp_le)
      also have "\<dots> = (1 / norm (zeta ?s))"
      proof (rule has_prod_unique2 [OF _ norm_f_has_prod])
        show "(\<lambda>k. cmod (f t k)) has_prod (L * (\<Prod>k<n. cmod (f t k)))"
          by (smt (verit) has_prod_L f_nonzero has_prod_cong has_prod_iff_shift norm_eq_zero)
      qed
      finally have "(1-\<epsilon>) * (\<Prod>k<n. 1 + h k) < 1 / norm (zeta ?s)" 
        by force 
      moreover have bdd: "bdd_above (range (\<lambda>t. 1 / cmod (zeta (Complex \<sigma> t))))"
      proof (intro bdd_aboveI2)
        fix t'
        show "1 / cmod (zeta (Complex \<sigma> t')) \<le> Re (zeta \<sigma>) / Re (zeta (2 * \<sigma>))"
          using norm_zeta_same_Im_ge [OF assms, of t'] zeta_nz zeta_pos
          by (auto simp add: mult_ac divide_simps Complex_eq split: if_split_asm)
      qed
      ultimately have "(1-\<epsilon>) * (\<Prod>k<n. 1 + h k) \<le> (SUP t. 1 / cmod (zeta(Complex \<sigma> t)))"
        by (meson cSup_upper dual_order.trans le_less rangeI)
      also have "\<dots> = 1 / Inf ?F"
      proof (rule Sup_inverse_eq_inverse_Inf)
        show "bdd_above (range (\<lambda>t. cmod (zeta (Complex \<sigma> t))))"
          by (rule bdd_aboveI2 [where M="Re (zeta \<sigma>)"]) (simp add: Complex_eq assms norm_zeta_same_Im_le)
        show "(0::real) < ?rhs"
          using rhs_pos by blast
        show "?rhs \<le> cmod (zeta (Complex \<sigma> t'))" for t'
          using Complex_eq assms norm_zeta_same_Im_ge by presburger
      qed
      finally show ?thesis
        by (smt (verit) \<epsilon> Groups.mult_ac(2) divide_divide_eq_left pos_le_divide_eq)
    qed
    have "(\<Prod>k. 1 + h k) \<le> 1 / ((1-\<epsilon>) * Inf ?F)"
    proof (rule prodinf_le_const)
      define M where "M \<equiv> max (\<Prod>k<n0. 1 + h k) (1 / ((1-\<epsilon>) * Inf ?F))"
      have M: "(\<Prod>k<n. 1 + h k) \<le> M" for n
      proof (cases "n < n0")
        case True
        have "1 \<le> (\<Prod>k=n..<n0. 1 + h k)"
          using h_ge1 by (simp add: prod_ge_1)
        then have "(\<Prod>k<n. 1 + h k) * 1 \<le> (\<Prod>k<n. 1 + h k) * (\<Prod>k=n..<n0. 1 + h k)"
          by (smt (verit, best) mult_le_cancel_left1 prod_nonneg h_ge1)
        also have "\<dots> = (\<Prod>k<n0. 1 + h k)"
          by (metis True lessThan_atLeast0 less_eq_nat.simps(1) order_le_less prod.atLeastLessThan_concat)
        finally show ?thesis
          by (simp add: M_def)
      next
        case False
        then show ?thesis
          by (simp add: prod_h_le M_def)
      qed
      show "convergent_prod (\<lambda>k. 1 + h k)"
        using M convergent_prodI_nonneg_bounded h_ge1 by meson
      fix n
      assume "n \<ge> n0"
      show "(\<Prod>k<n. 1 + h k) \<le> 1 / ((1 - \<epsilon>) * (INF t. cmod (zeta (Complex \<sigma> t))))"
        using prod_h_le \<open>n0 \<le> n\<close> by blast
    qed
    with \<epsilon> show ?thesis
      unfolding h_def
      by (smt (verit, best) mult_divide_mult_cancel_left mult_le_cancel_left_pos times_divide_eq_right)
  qed

  have uc: "uniformly_convergent_on {0..pi/2} (\<lambda>n x. \<Sum>k<n. \<bar>pr k powr -\<sigma> * cos x\<bar>)"
  proof (intro Weierstrass_m_test' [where M = "\<lambda>k. pr k powr -\<sigma>"])
    have "summable (\<lambda>p. if prime p then real p powr -\<sigma> else 0)"
      using summable_real_powr_iff [of "-\<sigma>"] assms
      by (force intro: summable_comparison_test')
    then show "summable (\<lambda>k. pr k powr -\<sigma>)"
      using summable_mono_reindex [of pr "\<lambda>p. if prime p then real p powr -\<sigma> else 0"]
      using pnp prime_iff by fastforce
  qed (auto simp: cos_ge_zero mult_le_cancel_left2)

  have pi_2_ge1: "1 \<le> pi/2"
    by (simp add: pi_ge_two)
  have cont_prod: "\<And>n. continuous_on {0..pi/2} (\<lambda>\<epsilon>. \<Prod>k<n. 1 + pr k powr -\<sigma> * cos \<epsilon>)"
    by (intro continuous_intros)
  have "continuous_on {0..pi/2} (\<lambda>\<epsilon>. \<Prod>k. 1 + pr k powr -\<sigma> * cos \<epsilon>)"
  proof (intro uniform_limit_theorem)
    have "uniformly_convergent_on {0..pi/2} (\<lambda>n x. \<Prod>k<n. 1 + pr k powr -\<sigma> * cos x)" 
      by (intro uc uniformly_convergent_on_prod_real [where K="{0..pi/2}"] continuous_intros) auto
    moreover have "\<And>x k. x \<in> {0..pi/2} \<Longrightarrow> 1 + real (pr k) powr -\<sigma> * cos x \<ge> 1"
      by (simp add: cos_ge_zero)
    ultimately show "uniform_limit {0..pi/2} (\<lambda>n x. \<Prod>k<n. 1 + pr k powr -\<sigma> * cos x) 
                      (\<lambda>x. prodinf (\<lambda>k. 1 + pr k powr -\<sigma> * cos x)) sequentially"
      by (intro uniform_limit_prodinf)
  qed (use cont_prod in auto)
  with pi_2_ge1 have "continuous_on {0..<1} (\<lambda>\<epsilon>. (1-\<epsilon>) * (\<Prod>k. 1 + pr k powr -\<sigma> * cos \<epsilon>))"
    by (force intro: continuous_intros elim!: continuous_on_subset)
  with pi_2_ge1 have tends: 
        "((\<lambda>\<epsilon>. (1-\<epsilon>) * (\<Prod>k. 1 + pr k powr -\<sigma> * cos \<epsilon>)) \<longlongrightarrow> (\<Prod>k. 1 + pr k powr -\<sigma>)) (at 0 within {0..<1})"
    by (force simp: continuous_on)
  have "(\<lambda>n. \<Prod>p\<le>pr n. if prime p then 1 + real p powr -\<sigma> else 1)
        \<longlonglongrightarrow> Re (zeta \<sigma> / zeta (2 * of_real \<sigma>))"
    using LIMSEQ_subseq_LIMSEQ [OF prod_tendsto_zeta [OF assms] \<open>strict_mono pr\<close>] by (simp add: o_def)
  with prod_if_prime_eq_real have "(\<lambda>n. \<Prod>k\<le>n. 1 + pr k powr -\<sigma>) \<longlonglongrightarrow> Re (zeta \<sigma>) / Re (zeta (2*\<sigma>))"
    by (simp add: zeta_real')
  with zeta_pos have prod_eq: "(\<Prod>k. 1 + pr k powr -\<sigma>) = Re (zeta \<sigma>) / Re (zeta (2*\<sigma>))"
    by (intro prodinf_eq_prod_lim) (auto simp: mult.commute)
  have "(\<Prod>k. 1 + pr k powr -\<sigma>) \<le> 1 / Inf ?F"
  proof (rule tendsto_le [OF _ tendsto_const tends])
    show "\<forall>\<^sub>F x in at 0 within {0..<1}. 
             (1 - x) * (\<Prod>k. 1 + pr k powr -\<sigma> * cos x) \<le> 1 / Inf ?F"
      using eps_le by (simp add: topological_space_class.eventually_at_filter)
  qed (simp add: trivial_limit_within islimpt_greaterThanLessThan1)
  then show "Inf ?F \<le> ?rhs"
    using zeta_pos assms INFF_pos
    by (auto simp add: prod_eq mult.commute divide_simps split: if_split_asm)
qed

text \<open>And the natural form\<close>
corollary Inf_7_11b:
  fixes \<sigma>:: real
  assumes "\<sigma> > 1"
  shows "of_real(INF t. cmod (zeta(Complex \<sigma> t))) = zeta (2 * \<sigma>) / zeta \<sigma>"
  using zeta_real' by (simp add: Inf_7_11 assms)

section \<open>Applications to Periodic Functions\<close>

text \<open>Theorem 7.12\<close>
theorem small_periods_real_irrational:
  fixes f:: "complex \<Rightarrow> complex" and \<omega>1 \<omega>2::complex and \<epsilon>::real
  assumes \<omega>: "is_periodic \<omega>1 f" "is_periodic \<omega>2 f" and real: "\<omega>2/\<omega>1 \<in> \<real>" and irrat: "\<omega>2/\<omega>1 \<notin> \<rat>"
    and "\<epsilon> > 0"
  obtains \<omega> where "is_periodic \<omega> f" "0 < cmod \<omega>" "cmod \<omega> < \<epsilon>"
proof -
  define N where "N \<equiv> ceiling (cmod \<omega>1 / \<epsilon>)"
  obtain \<theta> where \<theta>: "\<omega>2/\<omega>1 = of_real \<theta>" and "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0"
    using Reals_cases real
    by (metis Rats_0 irrat divide_eq_0_iff)
  with \<open>\<epsilon> > 0\<close> have "N>0"
    by (auto simp: N_def divide_simps)
  obtain h k where "0 < k" "k \<le> N" and hk: "\<bar>of_int k * \<theta> - of_int h\<bar> < 1/N"
    by (metis Dirichlet_approx zero_less_nat_eq \<open>0 < N\<close> int_nat_eq linorder_not_le of_nat_nat zero_less_nat_eq)
  moreover have "1/N \<le> \<epsilon> / cmod \<omega>1"
    using \<open>\<epsilon> > 0\<close> ceiling_divide_upper [of \<epsilon>] by (simp add: N_def divide_simps mult.commute)
  ultimately have *: "\<bar>of_int k * \<theta> - of_int h\<bar> < \<epsilon> / cmod \<omega>1"
    by linarith
  define \<omega> where "\<omega> \<equiv> of_int k * \<omega>2 - of_int h * \<omega>1"
  show thesis
  proof
    show "is_periodic \<omega> f"
      using \<omega> by (auto simp: \<omega>_def is_periodic_diff is_periodic_times_int) 
    have "k \<noteq> 0"
      using \<open>0 < k\<close> by blast
    then have "of_int k * \<omega>2 \<noteq> of_int h * \<omega>1"
      by (metis Rats_divide Rats_of_int \<open>\<omega>1 \<noteq> 0\<close> div_mult_mult2 irrat mult_of_int_commute of_int_0_eq_iff)
    then show "0 < cmod \<omega>"
      by (auto simp: \<omega>_def)
    have "cmod \<omega> = cmod (of_int k * \<theta> * \<omega>1 - of_int h * \<omega>1)"
      using \<open>\<omega>1 \<noteq> 0\<close> \<theta> by (simp add: \<omega>_def divide_simps mult_ac)
    also have "\<dots> = \<bar>of_int k * \<theta> - of_int h\<bar> * cmod \<omega>1"
      by (metis left_diff_distrib norm_mult norm_of_real of_real_diff of_real_of_int_eq)
    also have "\<dots> < \<epsilon>"
      using * \<open>\<omega>1 \<noteq> 0\<close> by (simp add: divide_simps)
    finally show "cmod \<omega> < \<epsilon>" .
  qed
qed


text \<open>Theorem 7.13\<close>
theorem
  fixes f:: "complex \<Rightarrow> complex" and \<omega>1 \<omega>2 \<omega>3::complex
  assumes \<omega>: "is_periodic \<omega>1 f" "is_periodic \<omega>2 f" "is_periodic \<omega>3 f" 
    and indp: "module.independent (\<lambda>r. (*) (complex_of_int r)) {\<omega>1,\<omega>2,\<omega>3}"
    and dist: "distinct [\<omega>1,\<omega>2,\<omega>3]"
    and "\<epsilon> > 0"
  obtains \<omega> where "is_periodic \<omega> f" "0 < cmod \<omega>" "cmod \<omega> < \<epsilon>"
proof -
  interpret C: Modules.module "(\<lambda>r. (*) (complex_of_int r))"
    by (simp add: Modules.module.intro distrib_left mult.commute)
  have nz: "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0" "\<omega>3 \<noteq> 0"
    using indp C.dependent_zero by force+
  show thesis
  proof (cases "\<omega>2/\<omega>1 \<in> \<real>")
    case True
    have "C.dependent {\<omega>1,\<omega>2}" if q: "\<omega>2/\<omega>1 = of_rat q" for q
    proof -
      obtain m n where mn: "\<omega>2/\<omega>1 = of_int m / of_int n"
        by (metis Rats_cases' Rats_of_rat q)
      with nz have "m * \<omega>1 + (-n) * \<omega>2 = 0" "m\<noteq>0" "n\<noteq>0"
        by (auto simp: field_simps split: if_split_asm)
      with mn dist show ?thesis
        apply (simp add: C.dependent_finite)
        apply (rule_tac x="\<lambda>z. if z=\<omega>1 then m else -n" in exI, auto)
        done
    qed
    with Rats_cases have "\<omega>2/\<omega>1 \<notin> \<rat>"
      by (metis C.dependent_mono indp insert_commute subset_insertI)
    then show ?thesis
      using True assms small_periods_real_irrational that by blast
  next
    case False
    then obtain \<alpha> \<beta> where \<alpha>\<beta>: "\<omega>3 = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2"
      using complex_is_Real_iff gen_lattice.\<omega>1\<omega>2_decompose gen_lattice.intro by blast
    have irrat: False if \<section>: "\<alpha> \<in> \<rat> \<and> \<beta> \<in> \<rat>" \<comment> \<open>A case analysis much simpler than Apostol's\<close>
    proof -
      obtain m1 n1 m2 n2 where mn1: "\<alpha> = of_int m1 / of_int n1" and "n1 > 0"
        and mn2: "\<beta> = of_int m2 / of_int n2" and "n2 > 0"
        by (meson Rats_cases' \<section>)
      have "of_int(m1*n2)*\<omega>1 + of_int(m2*n1)*\<omega>2 + of_int(-n1*n2)*\<omega>3 = 0"
        using \<alpha>\<beta> \<open>n1 > 0\<close> \<open>n2 > 0\<close> by (simp add: mn1 mn2 add_frac_eq)
      then have "C.dependent {\<omega>1,\<omega>2,\<omega>3}"
        using dist \<open>n1 > 0\<close> \<open>n2 > 0\<close>
        apply (simp add: C.dependent_finite)
        apply (rule_tac x="\<lambda>z. if z=\<omega>1 then (m1*n2) else if z=\<omega>2 then (m2*n1) else (-n1*n2)" in exI)
        apply (auto simp: add_diff_eq)
        done
      with indp show False
        by blast
    qed
    show ?thesis  
    proof -
      define \<theta> where "\<theta> \<equiv> case_nat \<alpha> (\<lambda>_. \<beta>)"
      define \<delta> where "\<delta> \<equiv> \<epsilon> / (1 + cmod \<omega>1 + cmod \<omega>2)"
      have "\<delta> > 0"
        by (smt (verit, best) \<delta>_def \<open>\<epsilon> > 0\<close> divide_pos_pos norm_not_less_zero) 
      obtain N where N: "1 / real N < \<delta>" and "N>0"
        by (meson \<open>0 < \<delta>\<close> nat_approx_posE zero_less_Suc)
      then obtain k q where kh: "\<And>i. i < 2 \<Longrightarrow> \<bar>of_int k * \<theta> i - of_int (q i)\<bar> < \<delta>" and "0 < k"
        by (metis Dirichlet_approx_simult[of N 2 \<theta>] less_trans)
      define h1 where "h1 \<equiv> q 0" define h2 where "h2 \<equiv> q 1"
      have "cmod (k * \<alpha> * \<omega>1 - h1 * \<omega>1) = cmod (k * \<alpha> - h1) * cmod \<omega>1"
        by (metis left_diff_distrib norm_mult of_real_diff of_real_of_int_eq)
      also have "\<dots> = abs (k * \<alpha> - h1) * cmod \<omega>1"
        by (metis norm_of_real)
      also have "\<dots> < \<delta> * cmod \<omega>1"
        using kh [of 0] by (simp add: \<theta>_def nz h1_def)
      finally have 1: "norm (k * \<alpha> * \<omega>1 - h1 * \<omega>1) < \<delta> * cmod \<omega>1" .
      have "cmod (k * \<beta> * \<omega>2 - h2 * \<omega>2) = cmod (k * \<beta> - h2) * cmod \<omega>2"
        by (metis left_diff_distrib norm_mult of_real_diff of_real_of_int_eq)
      also have "\<dots> = abs (k * \<beta> - h2) * cmod \<omega>2"
        by (metis norm_of_real)
      also have "\<dots> < \<delta> * cmod \<omega>2"
        using kh [of 1] by (simp add: \<theta>_def nz h2_def)
      finally have 2: "cmod (k * \<beta> * \<omega>2 - h2 * \<omega>2) < \<delta> * cmod \<omega>2" .
      define \<omega> where "\<omega> \<equiv> k * \<omega>3 - h1 * \<omega>1 - h2 * \<omega>2"
      have "\<omega> = (k * \<alpha> * \<omega>1 - h1 * \<omega>1) + (k * \<beta> * \<omega>2 - h2 * \<omega>2)"
        by (simp add: \<omega>_def \<alpha>\<beta> algebra_simps)
      then have "cmod \<omega> \<le> cmod(k * \<alpha> * \<omega>1 - h1 * \<omega>1) + cmod(k * \<beta> * \<omega>2 - h2 * \<omega>2)"
        using norm_triangle_ineq by blast
      also have "\<dots> <  \<delta> * cmod \<omega>1 +  \<delta> * cmod \<omega>2"
        using "1" "2" by linarith
      also have "\<dots> < \<epsilon>"
        using \<open>\<epsilon> > 0\<close> nz
        by (simp add: \<delta>_def divide_simps) (auto simp add: distrib_left pos_add_strict)
      finally have "cmod \<omega> < \<epsilon>" .
      have "is_periodic \<omega> f"
        by (simp add: \<omega> \<omega>_def is_periodic_diff is_periodic_times_int)
      moreover have "\<omega> \<noteq> 0"
      proof -
        have "(k * \<alpha> - h1) \<noteq> 0 \<or> (k * \<beta> - h2) \<noteq> 0"
          using irrat \<open>0 < k\<close> 
          by (smt (verit, best) Rats_divide Rats_of_int nonzero_mult_div_cancel_left of_int_pos)+
        then have "(k * \<alpha> - h1) * \<omega>1 + (k * \<beta> - h2) * \<omega>2 \<noteq> 0"
          using \<open>\<omega>2 / \<omega>1 \<notin> \<real>\<close> complex_is_Real_iff gen_lattice.eq_zero_iff gen_lattice.intro by blast
        then show ?thesis
          by (simp add: \<omega>_def \<alpha>\<beta> algebra_simps)
      qed
      ultimately show ?thesis
        by (simp add: \<open>cmod \<omega> < \<epsilon>\<close> that)
    qed
  qed
qed

end
