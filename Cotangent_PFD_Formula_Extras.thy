(*
  File:     Cotangent_PFD_Formula.thy
  Author:   Manuel Eberl, University of Innsbruck

  A proof of the "partial fraction decomposition"-style sum formula for the contangent function.
*)
section \<open>The Partial-Fraction Formula for the Cotangent Function\<close>
theory Cotangent_PFD_Formula_Extras
  imports "Cotangent_PFD_Formula.Cotangent_PFD_Formula" 
begin

lemma cot_pfd_altdef_aux:
  fixes x :: "'a :: {banach, real_normed_field, field_char_0}"
  assumes "x \<notin> \<int> - {0}"
  shows   "2 * x / (x ^ 2 - of_nat (Suc n) ^ 2) =
           1 / (x + of_nat (Suc n)) + 1 / (x - of_nat (Suc n))"
proof -
  have neq1: "x + of_nat (Suc n) \<noteq> 0"
    using assms by (subst add_eq_0_iff2) (auto simp del: of_nat_Suc)
  have neq2: "x - of_nat (Suc n) \<noteq> 0"
    using assms by (auto simp del: of_nat_Suc)
  have neq3: "x ^ 2 - of_nat (Suc n) ^ 2 \<noteq> 0"
    using assms  by (auto simp del: of_nat_Suc simp: power2_eq_iff)
  show ?thesis using neq1 neq2 neq3
    by (simp add: divide_simps del: of_nat_Suc) (auto simp: power2_eq_square algebra_simps)
qed

lemma sums_cot_pfd_complex':
  fixes x :: complex
  assumes "x \<notin> \<int> - {0}"
  shows   "(\<lambda>n. 1 / (x + of_nat (Suc n)) + 1 / (x - of_nat (Suc n))) sums cot_pfd x"
  using sums_cot_pfd_complex[of x] cot_pfd_altdef_aux[OF assms] by simp

lemma has_field_derivative_cot_pfd:
  fixes z :: complex
  assumes z: "z \<in> -(\<int>-{0})"
  shows   "(cot_pfd has_field_derivative (-Polygamma 1 (1 + z) - Polygamma 1 (1 - z))) (at z)"
proof -
  define f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
    where "f = (\<lambda>N x. \<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))"
  define f' :: "nat \<Rightarrow> complex \<Rightarrow> complex"
    where "f' = (\<lambda>N x. \<Sum>n<N. -1/(x + of_nat (Suc n)) ^ 2 - 1/(x - of_nat (Suc n)) ^ 2)"

  have "\<exists>g'. \<forall>x\<in>- (\<int> - {0}). (cot_pfd has_field_derivative g' x) (at x) \<and> (\<lambda>n. f' n x) \<longlonglongrightarrow> g' x"
  proof (rule has_complex_derivative_uniform_sequence)
    show "open (-(\<int> - {0}) :: complex set)"
      by (intro open_Compl closed_subset_Ints) auto
  next
    fix n :: nat and x :: complex
    assume x: "x \<in> -(\<int> - {0})"
    have nz: "x\<^sup>2 - (of_nat (Suc n))\<^sup>2 \<noteq> 0" for n
    proof
      assume "x\<^sup>2 - (of_nat (Suc n))\<^sup>2 = 0"
      hence "(of_nat (Suc n))\<^sup>2 = x\<^sup>2"
        by algebra
      hence "x = of_nat (Suc n) \<or> x = -of_nat (Suc n)"
        by (subst (asm) eq_commute, subst (asm) power2_eq_iff) auto
      moreover have "(of_nat (Suc n) :: complex) \<in> \<int>" "(-of_nat (Suc n) :: complex) \<in> \<int>"
        by (intro Ints_minus Ints_of_nat)+
      ultimately show False using x
        by (auto simp del: of_nat_Suc)
    qed

    have nz1: "x + of_nat (Suc k) \<noteq> 0" for k
      using x by (subst add_eq_0_iff2) (auto simp del: of_nat_Suc)
    have nz2: "x - of_nat (Suc k) \<noteq> 0" for k
      using x by (auto simp del: of_nat_Suc)

    have "((\<lambda>x. 2 * x / (x\<^sup>2 - (of_nat (Suc k))\<^sup>2)) has_field_derivative
           - 1 / (x + of_nat (Suc k))\<^sup>2 - 1 / (x - of_nat (Suc k))\<^sup>2) (at x)" for k :: nat
    proof -
      have "((\<lambda>x. inverse (x + of_nat (Suc k)) + inverse (x - of_nat (Suc k))) has_field_derivative
             - inverse ((x + of_nat (Suc k)) ^ 2)- inverse ((x - of_nat (Suc k))) ^ 2) (at x)"
        by (rule derivative_eq_intros refl nz1 nz2)+ (simp add: power2_eq_square)
      also have "?this \<longleftrightarrow> ?thesis"
      proof (intro DERIV_cong_ev)
        have "eventually (\<lambda>t. t \<in> -(\<int>-{0})) (nhds x)" using x
          by (intro eventually_nhds_in_open open_Compl closed_subset_Ints) auto
        thus "eventually (\<lambda>t. inverse (t + of_nat (Suc k)) + inverse (t - of_nat (Suc k)) =
                              2 * t / (t\<^sup>2 - (of_nat (Suc k))\<^sup>2)) (nhds x)"
        proof eventually_elim
          case (elim t)
          thus ?case
            using cot_pfd_altdef_aux[of t k] by (auto simp add: field_simps)
        qed
      qed (auto simp: field_simps)
      finally show ?thesis .
    qed
    thus "(f n has_field_derivative f' n x) (at x)"
      unfolding f_def f'_def by (intro DERIV_sum)
  next
    fix x :: complex assume x: "x \<in> -(\<int>-{0})"
    have "open (-(\<int>-{0}) :: complex set)"
      by (intro open_Compl closed_subset_Ints) auto
    then obtain r where r: "r > 0" "cball x r \<subseteq> -(\<int>-{0})"
      using x open_contains_cball by blast

    have "uniform_limit (cball x r) f cot_pfd sequentially"
      using uniform_limit_cot_pfd_complex[of "norm x + r"] unfolding f_def
    proof (rule uniform_limit_on_subset)
      show "cball x r \<subseteq> cball 0 (cmod x + r)"
        by (subst cball_subset_cball_iff) auto
    qed (use \<open>r > 0\<close> in auto)
    thus "\<exists>d>0. cball x d \<subseteq> - (\<int> - {0}) \<and> uniform_limit (cball x d) f cot_pfd sequentially"
      using r by (intro exI[of _ r]) auto
  qed
  then obtain g' where g': "\<And>x. x\<in>-(\<int> - {0}) \<Longrightarrow> (cot_pfd has_field_derivative g' x) (at x)"
                           "\<And>x. x\<in>-(\<int> - {0}) \<Longrightarrow> (\<lambda>n. f' n x) \<longlonglongrightarrow> g' x" by blast

  have "(\<lambda>n. f' n z) \<longlonglongrightarrow> -Polygamma 1 (1 + z) - Polygamma 1 (1 - z)"
  proof -
    have "(\<lambda>n. -inverse (((1 + z) + of_nat n) ^ Suc 1) - 
               inverse (((1 - z) + of_nat n) ^ Suc 1)) sums
            (-((-1) ^ Suc 1 * Polygamma 1 (1 + z) / fact 1) - 
            (-1) ^ Suc 1 * Polygamma 1 (1 - z) / fact 1)"
      using z by (intro sums_diff sums_minus Polygamma_LIMSEQ) (auto simp: add_eq_0_iff)
    also have "\<dots> = -Polygamma 1 (1 + z) - Polygamma 1 (1 - z)"
      by simp
    also have "(\<lambda>n. -inverse (((1 + z) + of_nat n) ^ Suc 1) -  inverse (((1 - z) + of_nat n) ^ Suc 1)) =
               (\<lambda>n. -1/(z + of_nat (Suc n)) ^ 2 - 1/(z - of_nat (Suc n)) ^ 2)"
      by (simp add: f'_def field_simps power2_eq_square)
    finally show ?thesis
      unfolding sums_def f'_def .
  qed
  with g'(2)[OF z] have "g' z = -Polygamma 1 (1 + z) - Polygamma 1 (1 - z)"
    using LIMSEQ_unique by blast
  with g'(1)[OF z] show ?thesis
    by simp
qed

lemmas has_field_derivative_cot_pfd' [derivative_intros] =
  DERIV_chain2[OF has_field_derivative_cot_pfd]

lemma holomorphic_on_cot_pfd [holomorphic_intros]:
  assumes "A \<subseteq> -(\<int>-{0})"
  shows   "cot_pfd holomorphic_on A"
proof -
  have "cot_pfd holomorphic_on (-(\<int>-{0}))"
    unfolding holomorphic_on_def
    using has_field_derivative_cot_pfd field_differentiable_at_within
         field_differentiable_def by fast
  thus ?thesis
    by (rule holomorphic_on_subset) (use assms in auto)
qed

end