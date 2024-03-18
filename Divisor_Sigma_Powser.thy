theory Divisor_Sigma_Powser
imports
  FPS_Homomorphism
  Library_Extras
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Real_Asymp.Real_Asymp"
  "Dirichlet_Series.Divisor_Count"
  "Bernoulli.Bernoulli"
  "Landau_Symbols.Landau_Simprocs"
begin

(* TODO: this file is somewhat obsolete. It should be superseded by the 
Lambert Series in the AFP -- Manuel *)

lemma bernpoly_asymp_equiv [asymp_equiv_intros]: "bernpoly n \<sim>[at_top] (\<lambda>x::real. x ^ n)"
proof -
  have "(\<lambda>x::real. x ^ n + (\<Sum>k=1..n. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k)))
        \<sim>[at_top] (\<lambda>x. x ^ n)"
  proof (subst asymp_equiv_add_right)
    show "(\<lambda>x::real. \<Sum>k=1..n. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k)) \<in> o(\<lambda>x. x ^ n)"
    proof (rule big_sum_in_smallo)
      fix k assume k: "k \<in> {1..n}"
      show "(\<lambda>x::real. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k)) \<in> o(\<lambda>x. x ^ n)"
        using k by auto
    qed
  qed auto
  also have "(\<lambda>x::real. x ^ n + (\<Sum>k=1..n. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k))) =
             (\<lambda>x. \<Sum>k\<in>insert 0 {1..n}. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k))"
    by (subst sum.insert) auto
  also have "insert 0 {1..n} = {..n}"
    by auto
  also have "(\<lambda>x. \<Sum>k\<le>n. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k)) = bernpoly n"
    by (simp add: bernpoly_def)
  finally show ?thesis .
qed


subsection \<open>The power series $\sum_{n=0}^\infty \sigma_k(n) z^n$\<close>

definition divisor_sigma_powser :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "divisor_sigma_powser k z = (\<Sum>n. of_nat (divisor_sigma k n) * z ^ n)"

lemma divisor_sigma_powser_altdef:
  "divisor_sigma_powser k = eval_fps (of_nat.fps (Abs_fps (divisor_sigma k)))"
  by (simp add: divisor_sigma_powser_def [abs_def] eval_fps_def [abs_def])

lemma divisor_sigma_nat_le:
  "real (divisor_sigma k n) \<le> (bernpoly (Suc k) (real n + 1) - bernpoly (Suc k) 0) / (real k + 1)"
proof (cases "n = 0")
  case False
  have "divisor_sigma k n \<le> (\<Sum>i\<le>n. i ^ k)"
    unfolding divisor_sigma_def nat_power_nat_def
    using False by (intro sum_mono2) auto
  hence "real (divisor_sigma k n) \<le> real (\<Sum>i\<le>n. i ^ k)"
    by linarith
  also have "\<dots> = (bernpoly (Suc k) (real n + 1) - bernpoly (Suc k) 0) / (real k + 1)"
    unfolding of_nat_sum of_nat_power by (subst sum_of_powers) auto
  finally show ?thesis .
next
  case True
  thus ?thesis
    by (simp add: bernpoly_1' bernoulli'_def)
qed

lemma abs_summable_divisor_sigma_powser:
  assumes "norm (z :: complex) < 1"
  shows   "summable (\<lambda>n. norm (of_nat (divisor_sigma k n) * z ^ n))"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (simp add: summable_0_powser norm_mult norm_power)
next
  case False
  define f where "f = (\<lambda>n. (bernpoly (Suc k) (real n + 1) - bernpoly (Suc k) 0) / (real k + 1))"
    obtain C where C: "norm z < C" "C < 1"
      using assms dense by blast
    have "0 \<le> norm z"
      using False by simp
    also have "\<dots> < C"
      by fact
    finally have "C > 0" .

  show ?thesis
  proof (rule summable_comparison_test)
    show "\<exists>N. \<forall>n\<ge>N. norm (norm (of_nat (divisor_sigma k n) * z ^ n)) \<le> f n * norm z ^ n"
    proof (intro exI[of _ 0] allI impI)
      fix n :: nat
      have "real (divisor_sigma k n) * norm z ^ n \<le> f n * norm z ^ n"
        unfolding f_def by (intro mult_right_mono divisor_sigma_nat_le) auto
      thus "norm (norm (of_nat (divisor_sigma k n) * z ^ n)) \<le> f n * norm z ^ n"
        by (simp add: norm_mult norm_power)
    qed
  next
    show "summable (\<lambda>n. f n * norm z ^ n)"
    proof (rule summable_comparison_test_bigo)
      show "summable (\<lambda>n. norm (C ^ n))"
        using geometric_sums[of C] C \<open>C > 0\<close> by (simp add: sums_iff power_abs)
    next
      have "bernpoly (Suc k) \<in> O(\<lambda>x::real. x ^ Suc k)"
        by (intro asymp_equiv_imp_bigtheta bigthetaD1 asymp_equiv_intros)
      hence "(\<lambda>x. bernpoly (Suc k) (real x + 1)) \<in> O(\<lambda>x. (real x + 1) ^ Suc k)"
        by (rule landau_o.big.compose[of _ _ _ "\<lambda>x. real x + 1"]) real_asymp
      also have "(\<lambda>x. (real x + 1) ^ Suc k) \<in> O(\<lambda>x. real x ^ Suc k)"
        by real_asymp
      finally have "(\<lambda>n. f n * norm z ^ n) \<in> O(\<lambda>n. real n ^ Suc k * norm z ^ n)"
        unfolding f_def by (intro landau_o.big.mult landau_o.big_refl) (auto intro!: sum_in_bigo)
      also have "(\<lambda>n. real n ^ Suc k * norm z ^ n) \<in> O(\<lambda>n. C ^ n)"
        using C \<open>z \<noteq> 0\<close> \<open>C > 0\<close> by real_asymp
      finally show "(\<lambda>n. f n * norm z ^ n) \<in> O(\<lambda>n. C ^ n)" .
    qed
  qed
qed

lemma sums_divisor_sigma_powser:
  assumes "norm z < 1"
  shows   "(\<lambda>n. of_nat (divisor_sigma k n) * z ^ n) sums divisor_sigma_powser k z"
proof -
  have "summable (\<lambda>n. of_nat (divisor_sigma k n) * z ^ n)"
    using abs_summable_divisor_sigma_powser[OF assms, of k] summable_norm_cancel by fast
  thus ?thesis unfolding divisor_sigma_powser_def
    by (simp add: sums_iff)
qed

lemma fps_conv_radius_divisor_sigma:
  "fps_conv_radius (of_nat.fps (Abs_fps (divisor_sigma k)) :: complex fps) \<ge> 1"
proof -
  have "conv_radius (\<lambda>n. of_nat (divisor_sigma k n) :: complex) \<ge> 1"
  proof (rule conv_radius_geI_ex')
    fix r :: real
    assume r: "r > 0" "ereal r < 1"
    show "summable (\<lambda>n. of_nat (divisor_sigma k n) * complex_of_real r ^ n)"
      using summable_norm_cancel[OF abs_summable_divisor_sigma_powser[of "of_real r"]] r by simp
  qed
  thus ?thesis
    by (simp add: fps_conv_radius_def)
qed

lemma divisor_sigma_powser_holomorphic [holomorphic_intros]:
  "divisor_sigma_powser k holomorphic_on ball 0 1"
  unfolding divisor_sigma_powser_altdef
proof (rule holomorphic_on_eval_fps)
  have "1 \<le> fps_conv_radius (of_nat.fps (Abs_fps (divisor_sigma k)) :: complex fps)"
    using fps_conv_radius_divisor_sigma[of k] by simp
  thus "ball 0 1 \<le> eball 0 \<dots>"
    by (simp add: ball_eball_mono one_ereal_def)
qed

lemma divisor_sigma_powser_holomorphic' [holomorphic_intros]:
  assumes "f holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. divisor_sigma_powser k (f z)) holomorphic_on A"
proof -
  have "divisor_sigma_powser k \<circ> f holomorphic_on A"
    by (intro holomorphic_on_compose[OF assms(1)]
              holomorphic_on_subset[OF divisor_sigma_powser_holomorphic]) (use assms(2) in auto)
  thus ?thesis
    by (simp only: o_def)
qed

lemma has_fps_expansion_eval_fps [fps_expansion_intros]:
  assumes "fps_conv_radius F > 0"
  shows   "eval_fps F has_fps_expansion F"
  using assms by (simp add: has_fps_expansion_def)

lemma has_fps_expansion_divisor_sigma_powser [fps_expansion_intros]:
  "divisor_sigma_powser k has_fps_expansion of_nat.fps (Abs_fps (divisor_sigma k))"
  unfolding divisor_sigma_powser_altdef
proof (rule has_fps_expansion_eval_fps)
  have "0 < (1 :: ereal)"
    by simp
  also have "1 \<le> fps_conv_radius (of_nat.fps (Abs_fps (divisor_sigma k)) :: complex fps)"
    by (rule fps_conv_radius_divisor_sigma)
  finally show "\<dots> > 0" .
qed

(* TODO: analytic, continuous *)

end