theory Siegel_Dedekind_Eta
  imports Meromorphic_Extras Bernoulli.Bernoulli_FPS "HOL-Real_Asymp.Real_Asymp"
          "Winding_Number_Eval.Winding_Number_Eval" Path_Automation
           More_Topology More_Cotangent
begin

(* biggest part of Siegel's proof of Theorem 3.1 *)

lemma siegel_symmetric_sum_reduce:
  fixes g :: "int \<Rightarrow> 'a :: comm_semiring_1"
  assumes "\<And>k. k \<in> {1..n} \<Longrightarrow> g (-k) = g k"
  shows   "(\<Sum>k\<in>{-int n..int n}-{0}. g k) = 2 * (\<Sum>k=1..n. g (int k))"
proof -
  have *: "{-int n..int n} - {0} = {-int n..-1} \<union> {1..int n}"
    by auto
  have "(\<Sum>k\<in>{-int n..int n}-{0}. g k) = (\<Sum>k\<in>{-int n..-1}. g k) + (\<Sum>k\<in>{1..int n}. g k)"
    by (subst *, intro sum.union_disjoint) auto
  also have "(\<Sum>k\<in>{-int n..-1}. g k) = (\<Sum>k=1..n. g (int k))"
    by (rule sum.reindex_bij_witness[of _ "\<lambda>k. -int k" "\<lambda>k. nat (-k)"])
       (use assms[of "-k" for k] in auto)
  also have "(\<Sum>k\<in>{1..int n}. g k) = (\<Sum>k=1..n. g (int k))"
    by (rule sum.reindex_bij_witness[of _ "int" "nat"]) auto
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by (simp add: mult_2)
  finally show ?thesis by simp
qed

lemma summable_siegel'_aux:
  assumes "x > 1"
  shows   "summable (\<lambda>k. 1 / (real k * (x ^ k - 1)))"
proof (rule summable_comparison_test_bigo)
  show "(\<lambda>k. 1 / (real k * (x ^ k - 1))) \<in> O(\<lambda>k. 1 / real k ^ 2)"
    using assms by real_asymp
  show "summable (\<lambda>k. norm (1 / real k ^ 2))"
    using inverse_power_summable[of 2] by (simp add: field_simps)
qed

lemma summable_siegel':
  fixes x :: "'a :: {real_normed_field, banach}"
  assumes "norm x > 1"
  shows   "summable (\<lambda>k. norm (1 / (of_nat k * (1 - x ^ k))))"
proof (rule summable_comparison_test)
  have "norm (norm (1 / (of_nat k * (1 - x ^ k)))) \<le>  1 / (real k * (norm x ^ k - 1))"
    if k: "k \<ge> 1" for k
  proof -
    have *: "norm x ^ k > 1 ^ k"
      using k assms by (intro power_strict_mono) auto
    hence "norm (x ^ k) > 1"
      by (auto simp: norm_power)
    hence **: "x ^ k \<noteq> 1"
      by auto
    have ***: "norm x ^ k - 1 \<le> norm (1 - x ^ k)"
      by (metis norm_minus_commute norm_one norm_power norm_triangle_ineq2)
    have "norm (norm (1 / (of_nat k * (1 - x ^ k)))) = 1 / (real k * norm (1 - x ^ k))"
      by (simp add: norm_divide norm_mult)
    also have "\<dots> \<le> 1 / (real k * (norm x ^ k - 1))"
      using k * ** *** by (intro divide_left_mono mult_left_mono mult_pos_pos) auto
    finally show ?thesis .
  qed
  thus "\<exists>N. \<forall>k\<ge>N. norm (norm (1 / (of_nat k * (1 - x ^ k)))) \<le> 1 / (real k * (norm x ^ k - 1))"
    by blast
next
  show "summable (\<lambda>k. 1 / (real k * (norm x ^ k - 1)))"
    by (intro summable_siegel'_aux assms)
qed

lemma abs_summable_siegel:
  assumes "c > 0"
  shows   "summable (\<lambda>k. norm (1 / (real k * (1 - exp (2 * pi * real k * c)))))"
proof (rule summable_comparison_test_bigo)
  show "(\<lambda>k. norm (1 / (real k * (1 - exp (2 * pi * real k * c))))) \<in> O(\<lambda>k. 1 / k ^ 2)"
    unfolding real_norm_def using assms by real_asymp
  show "summable (\<lambda>n. norm (1 / (real n) ^ 2))"
    using inverse_power_summable[of 2] by (simp add: field_simps)
qed  

lemma summable_siegel:
  assumes "c > 0"
  shows   "summable (\<lambda>k. 1 / (real k * (1 - exp (2 * pi * real k * c))))"
  using summable_norm_cancel[OF abs_summable_siegel[OF assms]] .


locale siegel_dedekind_eta =
  fixes y :: real
  assumes y: "y > 0"
begin

definition C :: "real \<Rightarrow> complex" where
  "C = linepath (-of_real y) (-\<i>) +++ linepath (-\<i>) (of_real y) +++
       linepath (of_real y) \<i> +++ linepath \<i> (-of_real y)"

definition h1 :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  where "h1 = (\<lambda>n z. complex_of_real pi * \<i> * (of_nat n + 1 / 2) * z)"
definition h2 :: "nat \<Rightarrow> complex \<Rightarrow> complex"
  where "h2 = (\<lambda>n z. complex_of_real pi * (of_nat n + 1 / 2) / complex_of_real y * z)"

definition f :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "f n z = -1 / (8 * z) * cot (of_real pi * \<i> * (n + 1 / 2) * z) *
           cot (of_real pi * (n + 1 / 2) / of_real y * z)"

lemma in_C_iff: "complex_of_real x * \<i> \<in> path_image C \<longleftrightarrow> \<bar>x\<bar> = 1" for x
  using y by (auto simp: C_def path_image_join closed_segment_def complex_eq_iff)

lemma in_C_iff': "complex_of_real x \<in> path_image C \<longleftrightarrow> \<bar>x\<bar> = of_real y" for x
  using y by (auto simp: C_def path_image_join closed_segment_def complex_eq_iff)

lemma zero_not_in_C: "0 \<notin> path_image C"
  using in_C_iff'[of 0] y by auto

lemma sin_nz_in_C: 
  assumes "z \<in> path_image C"
  shows   "sin (pi * \<i> * (of_nat n + 1 / 2) * z) \<noteq> 0"
proof
  assume "sin (pi * \<i> * (of_nat n + 1 / 2) * z) = 0"
  then obtain k where k: "of_int k = \<i> * ((of_nat n + 1 / 2) * z)"
    by (auto simp: sin_eq_0)
  have "z = of_real (-of_int k / (of_nat n + 1 / 2)) * \<i>"
    by (auto simp: complex_eq_iff k)
  hence "of_real (-of_int k / (of_nat n + 1 / 2)) * \<i> \<in> path_image C"
    using assms by simp
  also have "?this \<longleftrightarrow> real n + 1 / 2 = \<bar>real_of_int k\<bar>"
    by (subst in_C_iff) auto
  finally have "real_of_int (2 * n + 1) = real_of_int (2 * \<bar>k\<bar>)"
    unfolding of_int_mult of_int_add by simp
  hence "2 * n + 1 = 2 * \<bar>k\<bar>"
    by linarith
  thus False
    by presburger
qed
    
lemma sin_nz_in_C':
  assumes "z \<in> path_image C"
  shows   "sin (complex_of_real pi * (of_nat n + 1 / 2) * z / complex_of_real y) \<noteq> 0"
proof
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  assume "sin (complex_of_real pi * (of_nat n + 1 / 2) * z / complex_of_real y) = 0"
  then obtain k where k: "complex_of_real pi * (of_nat n + 1 / 2) * z / complex_of_real y =
                          of_int k * complex_of_real pi"
    by (auto simp: sin_eq_0)
  also have "complex_of_real pi * (of_nat n + 1 / 2) * z / complex_of_real y =
             (of_nat n + 1 / 2) * z / complex_of_real y * complex_of_real pi"
    by (simp add: field_simps)
  finally have k: "of_int k = (of_nat n + 1 / 2) * z / complex_of_real y"
    by (subst (asm) mult_cancel_right) auto
  have "z = of_real (of_int k * y / (real n + 1 / 2))"
    using y by (auto simp: complex_eq_iff k)
  hence "of_real (of_int k * y / (real n + 1 / 2)) \<in> path_image C"
    using assms by simp
  also have "?this \<longleftrightarrow> \<bar>real_of_int k * y\<bar> / (real n + 1 / 2) = y"
    by (subst in_C_iff') auto
  finally have "\<bar>real_of_int k\<bar> * y = (real n + 1 / 2) * y"
    using y by (simp add: field_simps abs_mult)
  hence "\<bar>real_of_int k\<bar> = real n + 1 / 2"
    using y by (subst (asm) mult_cancel_right) auto
  hence "real_of_int (2 * \<bar>k\<bar>) = real_of_int (2 * int n + 1)"
    unfolding of_int_mult by simp
  hence "2 * \<bar>k\<bar> = 2 * int n + 1"
    by linarith
  thus False
    by presburger
qed

lemma 
  assumes "z \<in> path_image C"
  shows   abs_Re_C_conv_Im: "\<bar>Re z\<bar> = y * (1 - \<bar>Im z\<bar>)"
    and   Im_bounds_C: "Im z \<in> {-1..1}"
proof -
  from assms obtain a b
    where ab: "a \<in> {complex_of_real y, -complex_of_real y}" "b \<in> {\<i>, -\<i>}" "z \<in> closed_segment a b"
    by (force simp: C_def path_image_join closed_segment_commute)
  from ab(3) obtain t where t: "t \<in> {0..1}" "z = linepath a b t"
    by (metis imageE linepath_image_01)
  show "\<bar>Re z\<bar> = y * (1 - \<bar>Im z\<bar>)" and "Im z \<in> {-1..1}"
    using ab(1,2) y t by (auto simp: linepath_def abs_mult)
qed

lemma cosh_real_gt_1_iff [simp]: "cosh x > 1 \<longleftrightarrow> x \<noteq> (0 :: real)"
  by (metis cosh_0 cosh_real_one_iff cosh_real_ge_1 nle_le not_le)

lemma sin_of_int_pi [simp]: "sin (of_int n * pi) = 0"
  by (simp add: sin_zero_iff_int2)

lemma cos_of_int_pi [simp]: "cos (of_int n * pi) = (-1) powi n"
  by (subst mult.commute) auto

lemma cos_plus_of_int_times_pi: "cos (x + of_int n * pi) = (-1) powi n * cos x"
  by (simp add: cos_add)

lemma norm_cot_bound1:
  obtains B where "B \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (cot (h1 n z)) \<le> B"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define N where "N = (\<lambda>n. real n + 1 / 2)"
  define H1 where "H1 = (\<lambda>n x. pi * (1 - x) * N n)"
  define H2 where "H2 = (\<lambda>n x. pi * y * x * N n)"

  define H where
    "H = (\<lambda>n x. 2 * (cos (H1 n x) ^ 2 + sinh (H2 n x) ^ 2) / (cosh (2 * H2 n x) - cos (2 * H1 n x)))"
  define H' where
    "H' = (\<lambda>x. 2 * (cos (pi / 2 * (1 - x)) ^ 2 + sinh (pi / 2 * y * x) ^ 2) /
               (cosh (pi * y * x) - cos (pi * (1 - x))))"

  have "bounded (range H')"
  proof (rule continuous_bounded_at_infinity_imp_bounded)
    show "H' \<in> O[at_bot](\<lambda>_. 1)" "H' \<in> O[at_top](\<lambda>_. 1)"
      unfolding H'_def using y by real_asymp+
    have "cosh (pi * y * x) \<noteq> cos (pi * (1 - x))" for x
    proof
      assume *: "cosh (pi * y * x) = cos (pi * (1 - x))"
      hence "cosh (pi * y * x) = 1"
        using cosh_real_ge_1[of "pi * y * x"] cos_le_one[of "pi * (1 - x)"] by linarith
      hence "x = 0"
        using y by simp
      with * show False
        by simp
    qed
    thus "continuous_on UNIV H'"
      unfolding H'_def by (intro continuous_intros) auto
  qed
  then obtain B where B: "B \<ge> 0" "norm (H' x) \<le> B" for x
    by (meson bounded_pos order_le_less rangeI)

  show ?thesis
  proof (rule that)
    fix z :: complex and n :: nat
    assume z: "z \<in> path_image C"
    define a b where "a = \<bar>Re z\<bar>" and "b = \<bar>Im z\<bar>"
  
    have H_reduce: "H n x = H' (x * (2 * n + 1))" for x
    proof -
      fix x :: real
      define x' where "x' = x * (2 * n + 1)"
  
      have "H1 n x = (H1 0 x' + of_int (int n) * pi)"
        by (simp add: H1_def field_simps N_def x'_def)
      also have "cos \<dots> ^ 2 = cos (H1 0 x') ^ 2"
        by (subst cos_plus_of_int_times_pi) (auto simp: power2_eq_square)
      finally have 1: "cos (H1 n x) ^ 2 = cos (H1 0 x') ^2" .
  
      have "2 * H1 n x = (2 * H1 0 x' + of_int (2 * int n) * pi)"
        by (simp add: H1_def field_simps N_def x'_def)
      also have "cos \<dots> = cos (2 * H1 0 x')"
        by (subst cos_plus_of_int_times_pi) auto
      finally have 2: "cos (2 * H1 n x) = cos (2 * H1 0 x')" .
  
      have 3: "H2 n x = H2 0 x'"
        by (simp add: H2_def N_def ring_distribs x'_def field_simps)
  
      have "H n x = H 0 x'"
        unfolding H_def 1 2 3 ..
      also have "\<dots> = H' x'"
        by (simp add: H_def H'_def N_def H1_def H2_def field_simps)
      finally show "H n x = H' x'" .
    qed

    have "norm (cot (h1 n z)) ^ 2 =
            2 * (cos (pi * N n * b) ^ 2 + sinh (pi * N n * a) ^ 2) / (cosh (2 * pi * N n * a) - cos (2 * pi * N n * b))"
      by (auto simp: norm_cot_complex_square h1_def N_def a_def b_def abs_if mult_ac)
    also have "a = y * (1 - b)"
      using z by (simp add: a_def b_def abs_Re_C_conv_Im)
    finally have "norm (cot (h1 n z)) ^ 2 = H n (1 - b)"
      by (simp add: mult_ac H_def H1_def H2_def)
    also have "H n (1 - b) = H' ((1 - b) * (2 * n + 1))"
      by (rule H_reduce)
    also have "\<dots> \<le> norm (H' ((1 - b) * (2 * n + 1)))"
      by simp
    also have "\<dots> \<le> B"
      by (rule B)
    finally show "norm (cot (h1 n z)) \<le> sqrt B"
      by (intro real_le_rsqrt)
  qed (use \<open>B \<ge> 0\<close> in auto)
qed

lemma norm_cot_bound2:
  obtains B where "B \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (cot (h2 n z)) \<le> B"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define N where "N = (\<lambda>n. real n + 1 / 2)"
  define H1 where "H1 = (\<lambda>n x. pi * (1 - x) * N n)"
  define H2 where "H2 = (\<lambda>n x. pi / y * x * N n)"

  define H where
    "H = (\<lambda>n x. 2 * (cos (H1 n x) ^ 2 + sinh (H2 n x) ^ 2) / (cosh (2 * H2 n x) - cos (2 * H1 n x)))"
  define H' where
    "H' = (\<lambda>x. 2 * (cos (pi / 2 * (1 - x)) ^ 2 + sinh (pi / 2 / y * x) ^ 2) /
               (cosh (pi / y * x) - cos (pi * (1 - x))))"

  have "bounded (range H')"
  proof (rule continuous_bounded_at_infinity_imp_bounded)
    show "H' \<in> O[at_bot](\<lambda>_. 1)" "H' \<in> O[at_top](\<lambda>_. 1)"
      unfolding H'_def using y by real_asymp+
    have "cosh (pi / y * x) \<noteq> cos (pi * (1 - x))" for x
    proof
      assume *: "cosh (pi / y * x) = cos (pi * (1 - x))"
      hence "cosh (pi / y * x) = 1"
        using cosh_real_ge_1[of "pi / y * x"] cos_le_one[of "pi * (1 - x)"] by linarith
      hence "x = 0"
        using y by simp
      with * show False
        by simp
    qed
    thus "continuous_on UNIV H'"
      unfolding H'_def by (intro continuous_intros) auto
  qed
  then obtain B where B: "B \<ge> 0" "norm (H' x) \<le> B" for x
    by (meson bounded_pos order_le_less rangeI) 

  show ?thesis
  proof (rule that)
    fix z :: complex and n :: nat
    assume z: "z \<in> path_image C"
    define a b where "a = \<bar>Re z\<bar>" and "b = \<bar>Im z\<bar>"
  
    have H_reduce: "H n x = H' (x * (2 * n + 1))" for x
    proof -
      fix x :: real
      define x' where "x' = x * (2 * n + 1)"
  
      have "H1 n x = H1 0 x' + of_int (int n) * pi"
        using y by (simp add: H1_def field_simps N_def x'_def)
      also have "cos \<dots> ^ 2 = cos (H1 0 x') ^ 2"
        by (subst cos_plus_of_int_times_pi) (auto simp: power2_eq_square)
      finally have 1: "cos (H1 n x) ^ 2 = cos (H1 0 x') ^2" .
  
      have "2 * H1 n x = (2 * H1 0 x' + of_int (2 * int n) * pi)"
        by (simp add: H1_def field_simps N_def x'_def)
      also have "cos \<dots> = cos (2 * H1 0 x')"
        by (subst cos_plus_of_int_times_pi) auto
      finally have 2: "cos (2 * H1 n x) = cos (2 * H1 0 x')" .
  
      have 3: "H2 n x = H2 0 x'"
        using y by (simp add: H2_def N_def ring_distribs x'_def field_simps)
  
      have "H n x = H 0 x'"
        unfolding H_def 1 2 3 ..
      also have "\<dots> = H' x'"
        using y by (simp add: H_def H'_def N_def H1_def H2_def field_simps)
      finally show "H n x = H' x'" .
    qed

    have "norm (cot (h2 n z)) ^ 2 =
            2 * (cos (pi / y * N n * a) ^ 2 + sinh (pi / y * N n * b) ^ 2) /
            (cosh (2 * pi / y * N n * b) - cos (2 * pi / y * N n * a))"
      by (auto simp: norm_cot_complex_square h2_def N_def a_def b_def abs_if mult_ac)
    also have "a = y * (1 - b)"
      using z by (simp add: a_def b_def abs_Re_C_conv_Im)
    finally have "norm (cot (h2 n z)) ^ 2 = H n b"
      using y by (simp add: mult_ac H_def H1_def H2_def)
    also have "H n b = H' (b * (2 * n + 1))"
      by (rule H_reduce)
    also have "\<dots> \<le> norm (H' (b * (2 * n + 1)))"
      by simp
    also have "\<dots> \<le> B"
      by (rule B)
    finally show "norm (cot (h2 n z)) \<le> sqrt B"
      by (intro real_le_rsqrt)
  qed (use \<open>B \<ge> 0\<close> in auto)
qed

lemma norm_bound_C:
  obtains B where "B \<ge> 0" "\<And>z. z \<in> path_image C \<Longrightarrow> norm (1 / z) \<le> B"
proof -
  have "continuous_on (path_image C) (\<lambda>z. 1 / z)"
    using zero_not_in_C by (intro continuous_intros) auto
  hence "compact ((\<lambda>z. 1 / z) ` path_image C)"
    by (simp add: C_def compact_continuous_image compact_path_image)
  hence "bounded ((\<lambda>z. 1 / z) ` path_image C)"
    by (rule compact_imp_bounded)
  thus ?thesis
    by (metis bounded_iff imageI norm_ge_zero order.trans that)
qed

lemma f_bound:
  obtains B where "B \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (f n z) \<le> B"
proof -
  obtain B1 where B1: "B1 \<ge> 0" "\<And>z. z \<in> path_image C \<Longrightarrow> norm (1 / z) \<le> B1"
    using norm_bound_C by blast
  obtain B2 where B2: "B2 \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (cot (h1 n z)) \<le> B2"
    using norm_cot_bound1 by blast
  obtain B3 where B3: "B3 \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (cot (h2 n z)) \<le> B3"
    using norm_cot_bound2 by blast
  show ?thesis
  proof (rule that)
    fix n :: nat and z :: complex
    assume z: "z \<in> path_image C"
    have "norm (f n z) = 1 / 8 * norm (1 / z) * norm (cot (h1 n z)) * norm (cot (h2 n z))"
      unfolding f_def h1_def h2_def by (simp add: norm_mult norm_divide)
    also have "\<dots> \<le> 1 / 8 * B1 * B2 * B3"
      by (intro mult_mono B1 B2 B3 z) (use B1(1) B2(1) B3(1) in auto)
    finally show "norm (f n z) \<le> \<dots>" .
  next
    show "1 / 8 * B1 * B2 * B3 \<ge> 0"
      using B1 B2 B3 by auto
  qed
qed

end


locale siegel_dedekind_eta' =siegel_dedekind_eta +
  fixes n :: nat
begin

definition N :: complex where "N = of_nat n + 1 / 2"

lemma N_nonzero [simp]: "N \<noteq> 0"
proof
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  assume "N = 0"
  hence "2 * of_nat n + 1 = (0 :: complex)"
    by (auto simp: field_simps N_def add_eq_0_iff)
  also have "2 * of_nat n + 1 = (of_nat (2 * n + 1) :: complex)"
    by simp
  finally have "2 * n + 1 = 0"
    by (subst (asm) of_nat_eq_0_iff)
  thus False
    by presburger
qed

lemma f_eq: "f n = (\<lambda>z. -1 / (8 * z) * cot (of_real pi * \<i> * N * z) *
                           cot (of_real pi * N / of_real y * z))"
  by (simp add: f_def [abs_def] N_def)

definition pts1 where "pts1 = (\<lambda>k. \<i> * of_int k / N) ` ({-int n..int n} - {0})"
definition pts2 where "pts2 = (\<lambda>k. of_int k * of_real y / N) ` ({-int n..int n} - {0})"

definition pts1' where "pts1' = range (\<lambda>k. \<i> * of_int k / N)"
definition pts2' where "pts2' = range (\<lambda>k. of_int k * y / N)"

lemma discrete_pts1': "discrete pts1'"
  unfolding pts1'_def
  by (intro uniform_discrete_imp_discrete uniform_discreteI2[of "1 / norm N"])
     (auto simp: pts1'_def dist_mult_left dist_of_int dist_divide_right field_simps
                 simp flip: of_int_diff of_int_abs)

lemma discrete_pts2':  "discrete pts2'"
  unfolding pts2'_def using y
  by (intro uniform_discrete_imp_discrete uniform_discreteI2[of "y / norm N"])
     (auto simp: pts2'_def dist_mult_right dist_of_int dist_divide_right field_simps
           simp flip: of_int_diff of_int_abs)

lemma pts1'_eq: "pts1' = isolated_points_of ((*) (pi * \<i> * N) -` 
                           range (\<lambda>z. complex_of_real (pi * real_of_int z)))"
  (is "_ = isolated_points_of (?g -` ?A)")
proof -
  have *: "?g -` ?A = pts1'"
    unfolding pts1'_def
  proof safe
    fix k z assume "pi * \<i> * N * z = complex_of_real (pi * real_of_int k)"
    hence "N * z = - (\<i> * of_int k)"
      by (auto simp: i_times_eq_iff)
    thus "z \<in> range (\<lambda>k. \<i> * of_int k / N)"
      by (intro rev_image_eqI[of "-k"]) (auto simp: field_simps)
  next
    fix k 
    have "- (complex_of_real pi * of_int k) \<in> range (\<lambda>x. complex_of_real pi * of_int x)"
      by (intro rev_image_eqI[of "-k"]) auto
    thus "\<i> * of_int k / N \<in> (*) (complex_of_real pi * \<i> * N) -` ?A"
      by auto
  qed
  moreover have "isolated_points_of pts1' = pts1'"
    by (intro isolated_points_of_discrete) (fact discrete_pts1')
  ultimately show ?thesis 
    by metis
qed

lemma pts2'_eq: "pts2' = isolated_points_of ((\<lambda>z. of_real pi * N / of_real y * z) -` 
                           range (\<lambda>z. complex_of_real (pi * real_of_int z)))"
  (is "_ = isolated_points_of (?g -` ?A)")
proof -
  have *: "?g -` ?A = pts2'"
    unfolding pts2'_def
  proof safe
    fix k z
    assume "complex_of_real pi * N / complex_of_real y * z = complex_of_real (pi * real_of_int k)"
    thus "z \<in> range (\<lambda>k. complex_of_real (real_of_int k * y) / N)"
      using y by (intro rev_image_eqI[of k]) (auto simp: field_simps)
  next
    fix k show "complex_of_real (real_of_int k * y) / N \<in> ?g -` ?A"
      by auto
  qed
  moreover have "isolated_points_of pts2' = pts2'"
    by (intro isolated_points_of_discrete) (fact discrete_pts2')
  ultimately show ?thesis 
    by metis
qed

lemma ind_1: "winding_number C z = 1" if "z \<in> {0} \<union> pts1 \<union> pts2" for z
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  show ?thesis
  proof (cases "z \<in> pts1")
    case True
    then obtain k where k: "z = \<i> * of_int k / N" "\<bar>k\<bar> \<le> int n"
      unfolding pts1_def by force
    define x where "x = real_of_int k / (n + 1 / 2)"
    from k have "\<bar>x\<bar> < 1"
      by (auto simp: x_def)
    hence "winding_number C (x * \<i>) = 1"
      using in_C_iff[of x] unfolding C_def using y
      by eval_winding (auto simp: cindex_pathE_linepath path_image_join)
    thus ?thesis
      by (simp add: k x_def field_simps N_def)
  next
    case False
    with that have "z \<in> insert 0 pts2"
      by auto
    then obtain x where x: "z = of_real x" "\<bar>x\<bar> < y"
    proof
      assume "z = 0"
      thus ?thesis using that[of 0] y by auto
    next
      assume "z \<in> pts2"
      then obtain k where k: "z = of_int k * complex_of_real y / N" "\<bar>k\<bar> \<le> n"
        by (force simp: pts2_def)
      define x where "x = real_of_int k * y / (n + 1 / 2)"
      have "y * (\<bar>real_of_int k\<bar> / (n + 1 / 2)) < y * 1"
        using k y by (intro mult_strict_left_mono) auto
      hence "\<bar>x\<bar> < y"
        using y by (auto simp: x_def field_simps abs_mult)
      moreover have "z = of_real x"
        by (auto simp: k x_def field_simps N_def)
      ultimately show ?thesis using that[of x]
        by auto
    qed
    show "winding_number C z = 1"
      using x(2) in_C_iff'[of x] unfolding x(1) C_def
      by eval_winding (auto simp: cindex_pathE_linepath path_image_join Let_def)
  qed
qed

lemma ind_0: "winding_number C (of_real x * \<i>) = 0" if "\<bar>x\<bar> > 1" for x
  using in_C_iff[of x] unfolding C_def using that y
  by eval_winding (auto simp: cindex_pathE_linepath path_image_join)

lemma ind_0': "winding_number C (of_real x) = 0" if "\<bar>x\<bar> > y" for x
  using in_C_iff'[of x] unfolding C_def using that y
  by eval_winding (auto simp: cindex_pathE_linepath path_image_join Let_def)

lemma mero: "f n meromorphic_on UNIV (pts1' \<union> pts2')"
proof -
  have "f n meromorphic_on UNIV ({0} \<union> pts1' \<union> pts2')"
    unfolding f_eq using y pts1'_eq pts2'_eq
    by (intro meromorphic_on_mult' meromorphic_on_compose'[OF meromorphic_on_cot]
              meromorphic_intros holomorphic_intros)
       (auto simp: islimpt_insert)
  also have "{0} \<union> pts1' \<union> pts2' = pts1' \<union> pts2'"
    by (auto simp: pts1'_def)
  finally show "f n meromorphic_on UNIV (pts1' \<union> pts2')" .
qed

lemma path_image_C_disjoint_pts: "path_image C \<inter> (pts1' \<union> pts2') = {}"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have "z \<notin> path_image C" if "z \<in> pts1'" for z
  proof -
    from that obtain k where k: "z = \<i> * of_int k / N"
      by (auto simp: pts1'_def)
    have "2 * n + 1 \<noteq> 2 * \<bar>k\<bar>"
      by presburger
    hence "real_of_int (2 * n + 1) \<noteq> of_int (2 * \<bar>k\<bar>)"
      by linarith
    hence "of_real (of_int k / (n + 1 / 2)) * \<i> \<notin> path_image C"
      unfolding of_int_add by (subst in_C_iff) (auto simp: field_simps abs_mult)
    thus ?thesis
      by (simp add: k N_def mult_ac)
  qed
  moreover have "z \<notin> path_image C" if "z \<in> pts2'" for z
  proof -
    from that obtain k where k: "z = of_int k * y / N"
      by (auto simp: pts2'_def)
    have "2 * \<bar>k\<bar> \<noteq> 1 + 2 * n"
      by presburger
    hence "real_of_int (2 * \<bar>k\<bar>) \<noteq> real_of_int (1 + 2 * n)"
      by linarith
    hence "y * real_of_int (2 * \<bar>k\<bar>) \<noteq> y * real_of_int (1 + 2 * n)"
      using y unfolding of_int_mult of_int_add by simp
    hence "of_real (k * y / (n + 1 / 2)) \<notin> path_image C"
      unfolding of_int_add using y by (subst in_C_iff') (auto simp: field_simps abs_mult)
    thus ?thesis
      by (simp add: k N_def mult_ac)
  qed
  ultimately show ?thesis
    by auto
qed

lemma integrable: 
  assumes "p \<le>\<^sub>p C" "valid_path p"
  shows   "f n contour_integrable_on p"
proof (rule contour_integrable_holomorphic_simple)
  show "f n holomorphic_on UNIV - (pts1' \<union> pts2')"
    using mero by (auto simp: meromorphic_on_def)
  show "open (UNIV - (pts1' \<union> pts2'))"
    by (intro meromorphic_imp_open_diff[OF mero])
  have "path_image p \<subseteq> path_image C"
    using assms(1) by (rule is_subpath_imp_path_image_subset)
  also have "\<dots> \<subseteq> UNIV - (pts1' \<union> pts2')"
    using path_image_C_disjoint_pts by blast
  finally show "path_image p \<subseteq> \<dots>" .
qed fact+

lemma contour_integral_eq:
  "contour_integral C (f n) =
     -pi/12*(y-1/y) -
       (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k/y)))) +
       (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k*y))))"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1

  have res1: "residue (f n) (\<i> * of_int k / N) = cot (pi*\<i>*k/y) / (8*pi*k)" if "k \<noteq> 0" for k
  proof -
    define z where "z = \<i> * of_int k / N"
    have "residue (\<lambda>z. (-1/(8*z) * cos (pi*\<i>*N*z) * cot (pi*N*z/y)) / sin (pi*\<i>*N*z)) z =
            cot (pi*\<i>*k/y) / (8*pi*k)"
    proof (subst residue_simple_pole_deriv)
      show "(\<lambda>z. -1/(8*z) * cos (pi*\<i>*N*z) * cot (pi*N*z/y)) holomorphic_on (UNIV - pts2')"
        using y by (intro holomorphic_intros) (auto simp: pts2'_def field_simps)
      show "(\<lambda>z. sin (pi*\<i>*N*z)) holomorphic_on UNIV - pts2'"
        by (intro holomorphic_intros)
      show "open (UNIV - pts2')"
        by (intro meromorphic_imp_open_diff'[OF mero]) auto
      show "connected (UNIV - pts2')"
        by (intro meromorphic_imp_connected_diff'[OF mero]) auto
      show "z \<in> UNIV - pts2'"
        using y \<open>k \<noteq> 0\<close> by (auto simp: pts2'_def z_def)
      have "((\<lambda>z. sin (pi*\<i>*N*z)) has_field_derivative
               (cos (complex_of_real pi * of_int k) * (pi * \<i> * N))) (at z)"
        by (auto intro!: derivative_eq_intros simp: z_def)
      also have "cos (complex_of_real pi * of_int k) = (-1) powi k"
        by (simp add: cos_int_times_real mult.commute)
      finally show "((\<lambda>z. sin (of_real pi*\<i>*N*z)) has_field_derivative ((-1) powi k *pi*\<i>*N)) (at z)"
        by (simp add: mult_ac)
      show sin_0: "sin (pi*\<i>*N*z) = 0"
        by (auto simp: sin_eq_0 z_def)
      show "complex_of_real ((- 1) powi k * pi) * \<i> * N \<noteq> 0"
        by auto
      have "cos (pi*\<i>*N*z) \<noteq> 0"
        using sin_0 sin_cos_squared_add2[of "pi * \<i> * N * z"] by auto       
      moreover have "cot (pi*N*z/y) \<noteq> 0"
        using cot_eq_0_imp_Im_0[of "pi*N*z/y"] that y by (auto simp: z_def)
      ultimately show "-1/(8*z) * cos (pi*\<i>*N*z) * cot (pi*N*z/y) \<noteq> 0"
        using that y by (auto simp: cot_def z_def cos_eq_0 sin_eq_0)
    next
      show "-1/(8*z) * cos (pi*\<i>*N*z) * cot (pi*N*z/y) / (((-1) powi k * pi) * \<i> * N) =
               cot (pi*\<i>*k/y) / (8*pi*k)"
        by (simp add: z_def field_simps cos_int_times_real)
    qed
    also have "(\<lambda>z. (-1/(8*z) * cos (pi*\<i>*N*z) * cot (pi*N*z/y)) / sin (pi*\<i>*N*z)) = f n"
      by (simp add: f_eq field_simps cot_def)
    finally show ?thesis
      by (simp only: z_def)
  qed

  have res2: "residue (f n) (of_int k * of_real y / N) = -cot (pi*\<i>*k*y) / (8*pi*k)" if "k \<noteq> 0" for k
  proof -
    define z where "z = of_int k * y / N"
    have "residue (\<lambda>z. (-1/(8*z) * cot (pi*\<i>*N*z) * cos (pi*N*z/y)) / sin (pi*N*z/y)) z =
            -cot (pi*\<i>*k*y) / (8*pi*k)"
    proof (subst residue_simple_pole_deriv)
      have "w \<in> pts1'" if "w * (\<i> * N) = of_int l" for l :: int and w :: complex
        unfolding pts1'_def using that
        by (intro rev_image_eqI[of "-l"]) (auto simp: i_times_eq_iff field_simps)
      thus "(\<lambda>z. -1/(8*z) * cot (pi*\<i>*N*z) * cos (pi*N*z/y)) holomorphic_on (UNIV - pts1')"
        using y by (intro holomorphic_intros) (auto simp: field_simps)
      show "(\<lambda>z. sin (pi*N*z/y)) holomorphic_on UNIV - pts1'"
        by (intro holomorphic_intros) (use y in auto)
      show "open (UNIV - pts1')"
        by (intro meromorphic_imp_open_diff'[OF mero]) auto
      show "connected (UNIV - pts1')"
        by (intro meromorphic_imp_connected_diff'[OF mero]) auto
      show "z \<in> UNIV - pts1'"
        using y \<open>k \<noteq> 0\<close> by (auto simp: pts1'_def z_def)
      have "((\<lambda>z. sin (pi*N*z/y)) has_field_derivative
               cos (complex_of_real pi * of_int k) * (pi*N)/y) (at z)"
        using y by (auto intro!: derivative_eq_intros simp: z_def)
      also have "cos (complex_of_real pi * of_int k) = (-1) powi k"
        by (simp add: cos_int_times_real mult.commute)
      finally show "((\<lambda>z. sin (pi*N*z/y)) has_field_derivative ((-1) powi k *pi*N/y)) (at z)"
        by (simp add: mult_ac)
      show sin_0: "sin (pi*N*z/y) = 0"
        by (auto simp: sin_eq_0 z_def)
      show "(-1) powi k *pi*N/y \<noteq> 0"
        using y by auto
      have "cos (pi*N*z/y) \<noteq> 0"
        using sin_0 sin_cos_squared_add2[of "pi*N*z/y"] by auto       
      moreover have "cot (pi*\<i>*N*z) \<noteq> 0"
        using cot_eq_0_imp_Im_0[of "pi*\<i>*N*z"] that y by (auto simp: z_def)
      ultimately show "-1/(8*z) * cot (pi*\<i>*N*z) * cos (pi*N*z/y) \<noteq> 0"
        using that y by (auto simp: cot_def z_def cos_eq_0 sin_eq_0)
    next
      show "-1/(8*z) * cot (pi*\<i>*N*z) * cos (pi*N*z/y) / (((-1) powi k * pi) * N / y) =
               -cot (pi*\<i>*k*y) / (8*pi*k)"
        using y by (simp add: z_def field_simps cos_int_times_real)
    qed
    also have "(\<lambda>z. (-1/(8*z) * cot (pi*\<i>*N*z) * cos (pi*N*z/y)) / sin (pi*N*z/y)) = f n"
      by (simp add: f_eq field_simps cot_def)
    finally show ?thesis
      by (simp add: z_def)
  qed

  have res3: "residue (f n) 0 = \<i>/24 * (y - 1 / y)"
  proof -
    let ?F = "fls_const (-1/8) * fls_shift 1 (fls_cot (pi*\<i>*N) * fls_cot (pi*N/y))"
    have ivl_eq: "{- 2..(0::int)} = {-2, -1, 0}"
      by auto

    have "f n has_laurent_expansion ?F"
      unfolding f_eq
      apply (rule has_laurent_expansion_schematicI)
       apply (rule laurent_expansion_intros)+
      apply (auto simp flip: fls_const_divide_const)
      done
    hence "residue (f n) 0 = fls_residue ?F"
      using has_laurent_expansion_residue_0 by blast
    also have "\<dots> = \<i>/24 * (y - 1 / y)"
      using y
      apply (simp)
      apply (simp add: fls_times_nth ivl_eq eval_fps_nth_cot)
      apply (simp add: field_simps)
      done
    finally show ?thesis .
  qed

  have "contour_integral C (f n) =
          2 * pi * \<i> * (\<Sum>w\<in>{0}\<union>pts1\<union>pts2. winding_number C w * residue (f n) w)"
  proof (rule Residue_theorem' [OF mero])
    fix z assume z: "z \<in> pts1' \<union> pts2' - ({0} \<union> pts1 \<union> pts2)"
    hence "z \<in> (pts1' - pts1 - {0}) \<union> (pts2' - pts2 - {0})"
      by auto
    thus "winding_number C z = 0"
    proof
      assume z: "z \<in> pts1' - pts1 - {0}"
      then obtain k where k: "\<bar>k\<bar> > n" "z = \<i> * of_int k / N"
        by (force simp: pts1'_def pts1_def)
      have "winding_number C (of_real (of_int k / (real n + 1/2)) * \<i>) = 0"
        by (intro ind_0) (use k in auto)
      thus "winding_number C z = 0"
        using k by (simp add: N_def mult_ac)
    next
      assume z: "z \<in> pts2' - pts2 - {0}"
      then obtain k where k: "\<bar>k\<bar> > n" "z = of_int k * y / N"
        by (force simp: pts2'_def pts2_def)
      have "y * 1 < y * \<bar>real_of_int k / (real n + 1 / 2)\<bar>"
        using y k by (intro mult_strict_left_mono) auto
      hence "winding_number C (of_real (of_int k * (y / (real n + 1/2)))) = 0"
        using y by (intro ind_0') (auto simp: field_simps)
      thus "winding_number C z = 0"
        using k by (simp add: N_def mult_ac)
    qed
  next
    show "valid_path C" "pathfinish C = pathstart C"
      by (auto simp: C_def)
  next
    show "path_image C \<subseteq> UNIV - (pts1' \<union> pts2')"
      using path_image_C_disjoint_pts by blast
  qed (auto simp: pts1_def pts2_def convex_imp_simply_connected)

  also have "(\<Sum>w\<in>{0} \<union> pts1 \<union> pts2. winding_number C w * residue (f n) w) =
             (\<Sum>w\<in>{0} \<union> (pts1 \<union> pts2). residue (f n) w)"
    by (intro sum.cong) (auto simp: ind_1)
  also have "\<dots> = residue (f n) 0 + (\<Sum>w\<in>pts1\<union>pts2. residue (f n) w)"
    using y by (subst sum.union_disjoint) (auto simp: pts1_def pts2_def)
  also have "(\<Sum>w\<in>pts1\<union>pts2. residue (f n) w) =
               (\<Sum>w\<in>pts1. residue (f n) w) + (\<Sum>w\<in>pts2. residue (f n) w)"
    by (intro sum.union_disjoint) (auto simp: pts1_def pts2_def)
  also have "residue (f n) 0 = \<i>/24*(y-1/y)"
    by (simp add: res3)

  also have "(\<Sum>w\<in>pts1. residue (f n) w) = (\<Sum>k\<in>{-int n..int n}-{0}. residue (f n) (\<i> * of_int k / N))"
    unfolding pts1_def by (subst sum.reindex) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>k\<in>{-int n..int n}-{0}. cot (pi*\<i>*k/y) / (8*pi*k))"
    by (intro sum.cong) (auto simp: res1)
  also have "\<dots> = 2 * (\<Sum>k=1..n. cot (\<i> * (pi*k/y)) / (8*pi*k))"
    by (subst siegel_symmetric_sum_reduce) (auto simp: mult_ac)
  also have "(\<Sum>k=1..n. cot (\<i> * (pi*k/y)) / (8*pi*k)) =
               (\<Sum>k=1..n. (1 - 2 / (1 - exp (complex_of_real (2 * pi * k / y)))) / (8 * pi * \<i> * k))"
    by (intro sum.cong refl, subst cot_i_times) (use y in \<open>auto simp: field_simps\<close>)
  also have "\<dots> = (\<Sum>k=1..n. (1-2/(1-exp (2*pi*k/y)))/k) / (8 * pi * \<i>)"
    unfolding exp_of_real of_real_sum sum_divide_distrib by (simp add: field_simps)
  also have "(\<Sum>k=1..n. (1-2/(1-exp (2*pi*k/y)))/k) =
             (\<Sum>k=1..n. 1 / k) - 2 * (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k/y))))"
    unfolding sum_distrib_left
    by (subst sum_subtractf [symmetric]) (auto simp: diff_divide_distrib mult_ac)

  also have "(\<Sum>w\<in>pts2. residue (f n) w) = (\<Sum>k\<in>{-int n..int n}-{0}. residue (f n) (k * y / N))"
    unfolding pts2_def using y by (subst sum.reindex) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>k\<in>{-int n..int n}-{0}. -cot (pi*\<i>*k*y) / (8*pi*k))"
    by (intro sum.cong) (auto simp: res2)
  also have "\<dots> = 2 * (\<Sum>k=1..n. -(cot (pi*\<i>*k*y) / (8*pi*k)))"
    by (subst siegel_symmetric_sum_reduce) auto
  also have "\<dots> = -2 * (\<Sum>k=1..n. cot (\<i> *(pi*k*y)) / (8*pi*k))"
    by (subst sum_negf) (auto simp: mult_ac)
  also have "(\<Sum>k=1..n. cot (\<i> * (pi*k*y)) / (8*pi*k)) =
               (\<Sum>k=1..n. (1 - 2 / (1 - exp (complex_of_real (2*pi*k*y)))) / (8 * pi * \<i> * k))"
    by (intro sum.cong refl, subst cot_i_times) (use y in \<open>auto simp: field_simps\<close>)
  also have "\<dots> = (\<Sum>k=1..n. (1-2/(1-exp (2*pi*k*y)))/k) / (8 * pi * \<i>)"
    unfolding exp_of_real of_real_sum sum_divide_distrib by (simp add: field_simps)
  also have "(\<Sum>k=1..n. (1-2/(1-exp (2*pi*k*y)))/k) =
             (\<Sum>k=1..n. 1 / k) - 2 * (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k*y))))"
    unfolding sum_distrib_left
    by (subst sum_subtractf [symmetric]) (auto simp: diff_divide_distrib mult_ac)

  finally have "contour_integral C (f n) = 2 * pi * \<i> * (
                  \<i>/24*(y-1/y) +
                  2 * ((\<Sum>k=1..n. 1 / k) - 2 * (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k/y))))) / (8*pi*\<i>) -
                  2 * ((\<Sum>k=1..n. 1 / k) - 2 * (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k*y))))) / (8*pi*\<i>))"
    by (simp add: field_simps)
  also have "\<dots> = -pi/12*(y-1/y) - (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k/y)))) +
                  (\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k*y))))"
    by (simp add: field_simps)
  also have "(\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k/y)))) = (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k/y))))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>n. n + 1" "\<lambda>n. n - 1"]) auto
  also have "(\<Sum>k=1..n. 1/(k*(1-exp (2*pi*k*y)))) = (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k*y))))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>n. n + 1" "\<lambda>n. n - 1"]) auto

  finally show ?thesis .
qed

end


context siegel_dedekind_eta
begin

definition g :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "g n z = cot (of_real pi * \<i> * (n + 1 / 2) * z) * cot (of_real pi * (n + 1 / 2) / of_real y * z)"

lemma tendsto_g:
  fixes z :: complex
  assumes "Re z \<noteq> 0" "Im z \<noteq> 0"
  shows "(\<lambda>n. g n z) \<longlonglongrightarrow> of_real (-sgn (Re z) * sgn (Im z))"
proof -
  define F1 where "F1 = (if Re z > 0 then at_top else at_bot :: real filter)"
  define F2 where "F2 = (if Im z > 0 then at_top else at_bot :: real filter)"
  have lim: "filterlim (\<lambda>n. real n + 1 / 2) at_top sequentially"
    by real_asymp
  have "filterlim (\<lambda>n. Re z * pi * (real n + 1 / 2)) F1 sequentially"
    using assms by (intro filterlim_cmult_at_bot_at_top lim) (auto simp: F1_def zero_less_mult_iff)
  hence 1: "filterlim (\<lambda>n. of_real pi * \<i> * (n + 1 / 2) * z) (filtercomap Im F1) sequentially"
    by (auto simp: filterlim_filtercomap_iff o_def mult_ac)
  have 2: "(cot \<longlongrightarrow> -sgn (Re z) * \<i>) (filtercomap Im F1)"
    using tendsto_cot_Im_at_bot tendsto_cot_Im_at_top assms by (auto simp: F1_def)
  have 3: "(\<lambda>n. cot (of_real pi * \<i> * (n + 1 / 2) * z)) \<longlonglongrightarrow> -sgn (Re z) * \<i>"
    by (rule filterlim_compose[OF 2 1])

  have "filterlim (\<lambda>n. Im z * pi / of_real y * (real n + 1 / 2)) F2 sequentially"
    using assms y
    by (intro filterlim_cmult_at_bot_at_top lim)
       (auto simp: F2_def zero_less_mult_iff zero_less_divide_iff)
  hence 1: "filterlim (\<lambda>n. of_real pi * (n + 1 / 2) / of_real y * z) (filtercomap Im F2) sequentially"
    by (auto simp: filterlim_filtercomap_iff o_def mult_ac)
  have 2: "(cot \<longlongrightarrow> -sgn (Im z) * \<i>) (filtercomap Im F2)"
    using tendsto_cot_Im_at_bot tendsto_cot_Im_at_top assms by (auto simp: F2_def)
  have 4: "(\<lambda>n. cot (of_real pi * (n + 1 / 2) / of_real y * z)) \<longlonglongrightarrow> -sgn (Im z) * \<i>"
    by (rule filterlim_compose[OF 2 1])

  have "(\<lambda>n. g n z) \<longlonglongrightarrow> (-sgn (Re z) * \<i>) * (-sgn (Im z) * \<i>)"
    unfolding g_def using 3 4 by (intro tendsto_mult 3 4) auto
  also have "(-sgn (Re z) * \<i>) * (-sgn (Im z) * \<i>) = -sgn (Re z) * sgn (Im z)"
    by (simp add: algebra_simps)
  finally show ?thesis
    by simp
qed
    
lemma tendsto_contour_integral:
  "(\<lambda>n. contour_integral C (f n)) \<longlonglongrightarrow> -ln y / 2"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define I1 where "I1 = (\<lambda>n. integral {0<..<1} (\<lambda>x. f n (linepath y \<i> x)))"
  define I2 where "I2 = (\<lambda>n. integral {0<..<1} (\<lambda>x. f n (linepath (-\<i>) y x)))"

  obtain B where B: "B \<ge> 0" "\<And>n z. z \<in> path_image C \<Longrightarrow> norm (f n z) \<le> B"
    using f_bound by blast

  have integral_eq: "contour_integral C (f n) = 2 * (I1 n * (\<i> - y) + I2 n * (\<i> + y))" for n
  proof -
    interpret siegel_dedekind_eta' y n ..
    let ?int = "\<lambda>a b. contour_integral (linepath a b) (f n)"
    have "contour_integral C (f n) = ?int (-y) (-\<i>) + ?int (-\<i>) y + ?int y \<i> + ?int \<i> (-y)"
      unfolding C_def
    proof (path, fold C_def)
      show "f n holomorphic_on (UNIV - (pts1' \<union> pts2'))"
        using mero by (simp add: meromorphic_on_def)
      show "open (UNIV - (pts1' \<union> pts2'))"
        by (intro meromorphic_imp_open_diff[OF mero])
      show "path_image C \<subseteq> UNIV - (pts1' \<union> pts2')"
        using path_image_C_disjoint_pts by blast
    qed auto

    also have "?int (-y) (-\<i>) = contour_integral (uminus \<circ> linepath y \<i>) (f n)"
      by (simp add: o_def flip: linepath_minus)
    also have "\<dots> = -contour_integral (linepath y \<i>) (\<lambda>z. f n (-z))"
      by (simp add: contour_integral_reversepath contour_integral_negatepath)
    also have "contour_integral (linepath y \<i>) (\<lambda>z. f n (-z)) =
               contour_integral (linepath y \<i>) (\<lambda>z. -f n z)"
      by (intro contour_integral_cong) (simp_all add: f_eq)
    also have "\<dots> = -?int y \<i>"
      by (simp add: contour_integral_neg)
    also have "?int y \<i> = integral {0..1} (\<lambda>x. f n (linepath y \<i> x)) * (\<i> - y)"
      by (simp add: contour_integral_integral)
    also have "\<dots> = I1 n * (\<i> - y)"
      unfolding I1_def by (simp add: integral_open_interval_real)

    also have "?int \<i> (-y) = contour_integral (uminus \<circ> linepath (-\<i>) y) (f n)"
      by (simp add: o_def flip: linepath_minus)
    also have "\<dots> = -contour_integral (linepath (-\<i>) y) (\<lambda>z. f n (-z))"
      by (simp add: contour_integral_negatepath)
    also have "contour_integral (linepath (-\<i>) y) (\<lambda>z. f n (-z)) =
               contour_integral (linepath (-\<i>) y) (\<lambda>z. -f n z)"
      by (intro contour_integral_cong) (simp_all add: f_eq)
    also have "\<dots> = -?int (-\<i>) y"
      by (simp add: contour_integral_neg)
    also have "?int (-\<i>) y = integral {0..1} (\<lambda>x. f n (linepath (-\<i>) y x)) * (y - (-\<i>))"
      by (simp add: contour_integral_integral)
    also have "\<dots> = I2 n * (y - (-\<i>))"
      unfolding I2_def by (simp add: integral_open_interval_real)

    finally show "contour_integral C (f n) = 2 * (I1 n * (\<i> - y) + I2 n * (\<i> + y))"
      by simp
  qed

  have "I1 \<longlonglongrightarrow> integral {0<..<1} (\<lambda>x::real. 1 / (8 * linepath y \<i> x))"
    unfolding I1_def
  proof (rule dominated_convergence(2))
    fix n :: nat
    interpret siegel_dedekind_eta' y n ..
    have holo: "f n holomorphic_on (UNIV - (pts1' \<union> pts2'))"
      using mero by (auto simp: meromorphic_on_def)
    have "linepath y \<i> \<le>\<^sub>p C"
      unfolding C_def by path
    hence "f n contour_integrable_on (linepath y \<i>)"
      by (intro integrable) auto
    hence "(\<lambda>x. f n (linepath (complex_of_real y) \<i> x)) integrable_on {0..1}"
      by (simp add: contour_integrable_on complex_eq_iff)
    thus "(\<lambda>x. f n (linepath (complex_of_real y) \<i> x)) integrable_on {0<..<1}"
      by (simp add: integrable_on_open_interval_real)
  next
    show "(\<lambda>x. B) integrable_on {0<..<(1::real)}"
      by (intro integrable_on_const) auto
  next
    fix n :: nat and x :: real
    assume x: "x \<in> {0<..<1}"
    define z where "z = linepath y \<i> x"
    have "z \<in> path_image (linepath y \<i>)"
      using x unfolding z_def path_image_def by auto
    thus "norm (f n z) \<le> B"
      by (intro B) (auto simp: C_def path_image_join)
    have "(\<lambda>n. g n z / (-8 * z)) \<longlonglongrightarrow> of_real (-sgn (Re z) * sgn (Im z)) / (-8 * z)" using y
      by (intro tendsto_intros tendsto_g)
         (use x in \<open>auto simp: z_def linepath_def scaleR_conv_of_real field_simps complex_eq_iff\<close>)
    also have "(\<lambda>n. g n z / (-8 * z)) = (\<lambda>n. f n z)"
      by (auto simp: f_def g_def field_simps fun_eq_iff)
    also have "sgn (Re z) = 1"
      using x y by (auto simp: z_def linepath_def sgn_mult)
    also have "sgn (Im z) = 1"
      using x y by (auto simp: z_def linepath_def sgn_mult)
    finally show "(\<lambda>n. f n z) \<longlonglongrightarrow> 1 / (8 * z)"
      by simp
  qed
  hence "(\<lambda>n. I1 n * (\<i> - y)) \<longlonglongrightarrow>
           integral {0<..<1} (\<lambda>x::real. 1 / (8 * linepath y \<i> x)) * (\<i> - y)"
    by (intro tendsto_intros)
  also have "integral {0<..<1} (\<lambda>x::real. 1 / (8 * linepath y \<i> x)) =
             integral {0..1} (\<lambda>x::real. 1 / (8 * linepath y \<i> x))"
    by (simp add: integral_open_interval_real)
  also have "\<dots> * (\<i> - y) = contour_integral (linepath y \<i>) (\<lambda>z. 1 / (8 * z))"
    by (simp add: contour_integral_integral flip: integral_mult_left)
  also have "\<dots> = ln \<i> / 8 - ln y / 8"
  proof -
    let ?L = "linepath y \<i>"
    have "((\<lambda>z. 1/(8*z)) has_contour_integral (ln (pathfinish ?L) / 8 - ln (pathstart ?L) / 8)) ?L"
      using y
      by (intro contour_integral_primitive[where S = "-\<real>\<^sub>\<le>\<^sub>0"])
         (auto intro!: derivative_eq_intros simp: field_simps closed_segment_def complex_eq_iff
               elim!: nonpos_Reals_cases)
    from contour_integral_unique[OF this] show ?thesis
      using y by (simp add: Ln_of_real)
  qed
  finally have lim1: "(\<lambda>n. I1 n * (\<i> - y)) \<longlonglongrightarrow> ln \<i> / 8 - (ln y / 8)" .

  have "I2 \<longlonglongrightarrow> integral {0<..<1} (\<lambda>x::real. -1 / (8 * linepath (-\<i>) y x))"
    unfolding I2_def
  proof (rule dominated_convergence(2))
    fix n :: nat
    interpret siegel_dedekind_eta' y n ..
    have holo: "f n holomorphic_on (UNIV - (pts1' \<union> pts2'))"
      using mero by (auto simp: meromorphic_on_def)
    have "linepath (-\<i>) y \<le>\<^sub>p C"
      unfolding C_def by path
    hence "f n contour_integrable_on (linepath (-\<i>) y)"
      by (intro integrable) auto
    hence "(\<lambda>x. f n (linepath (-\<i>) y x)) integrable_on {0..1}"
      by (simp add: contour_integrable_on complex_eq_iff)
    thus "(\<lambda>x. f n (linepath (-\<i>) y x)) integrable_on {0<..<1}"
      by (simp add: integrable_on_open_interval_real)
  next
    show "(\<lambda>x. B) integrable_on {0<..<(1::real)}"
      by (intro integrable_on_const) auto
  next
    fix n :: nat and x :: real
    assume x: "x \<in> {0<..<1}"
    define z where "z = linepath (-\<i>) y x"
    have "z \<in> path_image (linepath (-\<i>) y)"
      using x unfolding z_def path_image_def by auto
    thus "norm (f n z) \<le> B"
      by (intro B) (auto simp: C_def path_image_join)
    have "(\<lambda>n. g n z / (-8 * z)) \<longlonglongrightarrow> of_real (-sgn (Re z) * sgn (Im z)) / (-8 * z)" using y
      by (intro tendsto_intros tendsto_g)
         (use x in \<open>auto simp: z_def linepath_def scaleR_conv_of_real field_simps complex_eq_iff\<close>)
    also have "(\<lambda>n. g n z / (-8 * z)) = (\<lambda>n. f n z)"
      by (auto simp: f_def g_def field_simps fun_eq_iff)
    also have "sgn (Re z) = 1"
      using x y by (auto simp: z_def linepath_def sgn_mult)
    also have "sgn (Im z) = -1"
      using x y by (auto simp: z_def linepath_def sgn_mult)
    finally show "(\<lambda>n. f n z) \<longlonglongrightarrow> -1 / (8 * z)"
      by simp
  qed
  hence "(\<lambda>n. I2 n * (\<i> + y)) \<longlonglongrightarrow>
           integral {0<..<1} (\<lambda>x::real. -1 / (8 * linepath (-\<i>) y x)) * (\<i> + y)"
    by (intro tendsto_intros)
  also have "integral {0<..<1} (\<lambda>x::real. -1 / (8 * linepath (-\<i>) y x)) =
             integral {0..1} (\<lambda>x::real. -1 / (8 * linepath (-\<i>) y x))"
    by (simp add: integral_open_interval_real)
  also have "\<dots> * (\<i> + y) = contour_integral (linepath (-\<i>) y) (\<lambda>z. -1 / (8 * z))"
    by (simp add: contour_integral_integral add.commute flip: integral_mult_left)
  also have "\<dots> = -ln y / 8 + ln (-\<i>) / 8"
  proof -
    let ?L = "linepath (-\<i>) y"
    have "((\<lambda>z. -1/(8*z)) has_contour_integral (-ln (pathfinish ?L) / 8 - (-ln (pathstart ?L) / 8))) ?L"
      using y
      by (intro contour_integral_primitive[where S = "-\<real>\<^sub>\<le>\<^sub>0"])
         (auto intro!: derivative_eq_intros simp: field_simps closed_segment_def complex_eq_iff
               elim!: nonpos_Reals_cases)
    from contour_integral_unique[OF this] show ?thesis
      using y by (simp add: Ln_of_real)
  qed
  finally have lim2: "(\<lambda>n. I2 n * (\<i> + y)) \<longlonglongrightarrow> -ln y / 8 + ln (-\<i>) / 8" .

  have "(\<lambda>n. 2 * (I1 n * (\<i> - y) + I2 n * (\<i> + y))) \<longlonglongrightarrow>
          2 * ((ln \<i> / 8 - (ln y / 8)) + (-ln y / 8 + ln (-\<i>) / 8))"
    by (intro tendsto_intros lim1 lim2)
  also have "(\<lambda>n. 2 * (I1 n * (\<i> - y) + I2 n * (\<i> + y))) = (\<lambda>n. contour_integral C (f n))"
    by (subst integral_eq) auto
  also have "2 * ((ln \<i> / 8 - (ln y / 8)) + (-ln y / 8 + ln (-\<i>) / 8)) = -ln y / 2"
    by simp
  finally show ?thesis .
qed

end

lemma siegel_dedekind_eta:
  fixes y :: real
  assumes "y > 0"
  shows "(\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k*y)))) - (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k/y)))) -
              pi / 12 * (y - 1 / y) = -ln y / 2"
proof -
  interpret siegel_dedekind_eta y
    by standard (fact assms)
  define S1 where "S1 = (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k/y))))"
  define S2 where "S2 = (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k*y))))"
  define g :: "nat \<Rightarrow> complex"
    where "g = (\<lambda>n. -pi/12*(y-1/y) - (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k/y)))) + 
                      (\<Sum>k<n. 1/(Suc k*(1-exp (2*pi*Suc k*y)))))"
  have 1: "summable (\<lambda>i. 1 / (real (Suc i) * (1 - exp (2 * pi * real (Suc i) / y))))"
    using summable_siegel[of "1/y"] y by (subst summable_Suc_iff) (auto simp: field_simps)
  have 2: "summable (\<lambda>i. 1 / (real (Suc i) * (1 - exp (2 * pi * real (Suc i) * y))))"
    using summable_siegel[of y] y by (subst summable_Suc_iff) (auto simp: field_simps)
  have "g \<longlonglongrightarrow> -pi/12*(y-1/y) - S1 + S2"
    unfolding g_def S1_def S2_def by (intro tendsto_intros summable_LIMSEQ 1 2)
  also have "g = (\<lambda>n. contour_integral C (f n))"
  proof
    fix n :: nat
    interpret siegel_dedekind_eta' y n ..
    show "g n = contour_integral C (f n)"
      using contour_integral_eq unfolding g_def by auto
  qed
  finally have 3: "(\<lambda>n. contour_integral C (f n)) \<longlonglongrightarrow> -pi/12*(y-1/y) - S1 + S2" .
  have "-pi/12*(y-1/y) - S1 + S2 = -1/2 * ln y"
    using tendsto_unique[OF _ 3 tendsto_contour_integral] unfolding of_real_eq_iff by simp
  thus ?thesis
    unfolding S1_def S2_def by simp
qed

lemma siegel_dedekind_eta':
  fixes y :: real
  assumes y: "y > 0"
  shows "(\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k*complex_of_real y)))) -
         (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k/complex_of_real y)))) -
              pi / 12 * (complex_of_real y - 1 / complex_of_real y) = -ln (complex_of_real y) / 2"
proof -
  define S where "S = (\<lambda>y. (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k*y)))))"
  define S' where "S' = (\<lambda>y. (\<Sum>k. 1/(Suc k*(1-exp (2*pi*Suc k*complex_of_real y)))))"
  have eq: "S' y = complex_of_real (S y)" if y: "y > 0" for y
  proof -
    have "summable (\<lambda>k. 1/(Suc k*(1-exp (2*pi*Suc k*y))))"
      by (subst summable_Suc_iff, rule summable_siegel) fact
    thus ?thesis
      unfolding S_def S'_def by (subst suminf_of_real) (auto simp flip: exp_of_real)
  qed
  have "S y - S (1 / y) - pi / 12 * (y - 1 / y) = -ln y / 2"
    using siegel_dedekind_eta[OF y] unfolding S_def by (simp add: field_simps)
  hence "complex_of_real (S y - S (1 / y) - pi / 12 * (y - 1 / y)) = complex_of_real (-ln y / 2)"
    by (simp only: )
  also have "complex_of_real (-ln y / 2) = -ln (complex_of_real y) / 2"
    using y by (simp add: Ln_of_real)
  also have "complex_of_real (S y - S (1 / y) - pi / 12 * (y - 1 / y)) =
             S' y - S' (1 / y) - pi / 12 * (y - 1 / y)"
    using y by (simp add: eq)
  finally show ?thesis
    unfolding S'_def by (simp add: field_simps)
qed

lemma siegel_dedekind_eta_sum1:
  fixes x :: complex
  assumes x: "norm x < 1" and [simp]: "x \<noteq> 0"
  shows   "((\<lambda>n. Ln (1 - x ^ n)) has_sum (\<Sum>m. 1 / (of_nat (Suc m) * (1 - inverse x ^ Suc m)))) {1..}"
proof -
  define S where "S = (\<Sum>m. 1/(Suc m*(1-inverse x^Suc m)))"
  have "summable (\<lambda>n. norm (1 / (of_nat (Suc n) * (1 - inverse x ^ Suc n))))"
    by (subst summable_Suc_iff, rule summable_siegel')
       (use x in \<open>auto simp: norm_inverse field_simps norm_divide\<close>)
  moreover from this have "summable (\<lambda>n. (1 / (of_nat (Suc n) * (1 - inverse x ^ Suc n))))"
    by (rule summable_norm_cancel)
  hence "(\<lambda>m. 1/(Suc m*(1-inverse x^Suc m))) sums S"
    by (simp add: sums_iff S_def)
  ultimately have "((\<lambda>m. 1/(Suc m*(1-inverse x^Suc m))) has_sum S) UNIV"
    by (intro norm_summable_imp_has_sum)
  also have "?this \<longleftrightarrow> ((\<lambda>m. 1/(m*(1-inverse x^m))) has_sum S) {1..}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>m. m-1" "\<lambda>m. m+1"]) auto
  finally have "((\<lambda>m. 1/(m*(1-inverse x^m))) has_sum S) {1..}" .

  have "((\<lambda>(m,n). -(x ^ (m * n) / m)) has_sum S) ({1..} \<times> {1..})"
  proof (rule has_sum_SigmaI)
    show "((\<lambda>m. 1/(m*(1-inverse x^m))) has_sum S) {1..}"
      by fact
    have "(\<lambda>mn. norm (case mn of (m, n) \<Rightarrow> -(x ^ (m * n) / of_nat m))) summable_on {1..} \<times> {1..}"
    proof (rule summable_on_SigmaI)
      fix m :: nat assume m: "m \<in> {1..}"
      have "((\<lambda>n. norm x ^ (m * n) / real m) has_sum (norm x ^ m / (1 - norm x ^ m) / real m)) {1..}"
      proof -
        have "norm x ^ m < 1 ^ m"
          using m x by (intro power_strict_mono) auto
        hence "((\<lambda>n. (norm x ^ m) ^ n / real m) has_sum (norm x ^ m / (1 - norm x ^ m) / real m)) {1..}"
          by (intro has_sum_divide_const has_sum_geometric_from_1) auto
        thus "((\<lambda>n. cmod x ^ (m * n) / real m) has_sum cmod x ^ m / (1 - cmod x ^ m) / real m) {1..}"
          by (simp add: power_mult)
      qed
      thus "((\<lambda>y. norm (case (m, y) of (m, n) \<Rightarrow> -(x ^ (m * n) / of_nat m))) has_sum
                (norm x ^ m / (1 - norm x ^ m) / real m)) {1..}"
        by (simp add: norm_power norm_mult norm_divide)
    next
      have "summable (\<lambda>k. norm ((norm x ^ k / (1 - norm x ^ k) / real k)))"
      proof (rule summable_comparison_test_bigo)
        show "summable (\<lambda>k. norm (norm x ^ k))"
          using x summable_geometric[of "norm x"] by simp
        have "(\<lambda>k. norm x ^ k / (1 - norm x ^ k) / real k) \<in> O(\<lambda>k. norm x ^ k)"
          using x by real_asymp
        also have "cmod x ^ k \<le> 1 ^ k" for k
          using x by (intro power_mono) auto
        hence "(\<lambda>k. norm x ^ k / (1 - norm x ^ k) / real k) =
               (\<lambda>k. norm ((norm x ^ k / (1 - norm x ^ k) / real k)))"
          by (auto simp: norm_power)
        finally show "(\<lambda>k. norm ((norm x ^ k / (1 - norm x ^ k) / real k))) \<in> O(\<lambda>k. norm x ^ k)" .
      qed
      hence "(\<lambda>k. (norm x ^ k / (1 - norm x ^ k) / real k)) summable_on UNIV"
        by (intro norm_summable_imp_summable_on)
      thus "(\<lambda>xa. (norm x ^ xa / (1 - cmod x ^ xa) / real xa)) summable_on {1..}"
        by (rule summable_on_subset) auto
    qed auto
    thus "(\<lambda>(m, n). - (x ^ (m * n) / of_nat m)) summable_on {1..} \<times> {1..}"
      using abs_summable_summable by blast
  next
    fix m :: nat assume m: "m \<in> {1..}"
    have "norm (x ^ m) < 1 ^ m"
      unfolding norm_power using x m by (intro power_strict_mono) auto
    hence "((\<lambda>n. -((x ^ m) ^ n / of_nat m)) has_sum -(x^m / (1 - x^m) / of_nat m)) {1..}"
      by (intro has_sum_divide_const has_sum_uminusI has_sum_geometric_from_1) auto
    
    also have "(\<lambda>n. -((x ^ m) ^ n / of_nat m)) = (\<lambda>n. -(x ^ (m * n) / of_nat m))"
      by (simp add: power_mult)
    also have "-(x^m / (1 - x^m) / of_nat m) = 1 / (of_nat m * (1 - inverse x ^ m))"
      by (simp add: divide_simps) (simp add: algebra_simps)?
    finally show "((\<lambda>y. case (m, y) of (m, n) \<Rightarrow> -(x ^ (m * n) / of_nat m)) has_sum
                     1 / (of_nat m * (1 - inverse x ^ m))) {1..}"
      by simp
  qed

  also have "?this \<longleftrightarrow> ((\<lambda>(n, m). -(x ^ (m * n) / of_nat m)) has_sum S) ({1..} \<times> {1..})"
    by (subst has_sum_swap) simp
  finally show "((\<lambda>n. ln (1 - x ^ n)) has_sum S) {1..}"
  proof (rule has_sum_Sigma')
    fix n :: nat
    assume n: "n \<in> {1..}"
    have "norm (x ^ n) < 1 ^ n"
      using n x unfolding norm_power by (intro power_strict_mono) auto
    hence "(\<lambda>m. -((x ^ n) ^ m) / m) sums ln (1 + (-(x ^ n)))"
      using Ln_series'[of "-(x ^ n)"] by simp
    moreover have "summable (\<lambda>m. norm (-((x ^ n) ^ m) / m))"
      using norm_summable_ln_series[of "x ^ n"] \<open>norm (x ^ n) < _\<close>
      by (simp add: norm_power norm_divide)
    ultimately have "((\<lambda>m. -((x ^ n) ^ m) / m) has_sum ln (1 + (-(x ^ n)))) UNIV"
      by (intro norm_summable_imp_has_sum)
    also have "?this \<longleftrightarrow> ((\<lambda>m. -((x ^ n) ^ m) / m) has_sum ln (1 + (-(x ^ n)))) {1..}"
      by (intro has_sum_cong_neutral) auto
    finally show "((\<lambda>m. case (n, m) of (n, m) \<Rightarrow> - (x ^ (m * n) / of_nat m)) has_sum (ln (1 - x ^ n))) {1..}"
      by (subst mult.commute) (simp add: power_mult)
  qed
qed

lemma siegel_dedekind_eta_sum2:
  fixes x :: complex
  assumes x: "norm x < 1" "x \<noteq> 0"
  shows   "(\<lambda>n. ln (1 - x ^ Suc n)) sums (\<Sum>m. 1 / (of_nat (Suc m) * (1 - inverse x ^ Suc m)))"
    (is "_ sums ?S")
proof -
  have "((\<lambda>n. ln (1 - x ^ n)) has_sum ?S) {1..}"
    by (rule siegel_dedekind_eta_sum1) fact+
  also have "?this \<longleftrightarrow> ((\<lambda>n. ln (1 - x ^ Suc n)) has_sum ?S) UNIV"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. n+1" "\<lambda>n. n-1"]) auto
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma siegel_dedekind_eta_sum3:
  assumes "y > 0"
  shows   "(\<lambda>n. ln (1 - exp (-2 * pi * complex_of_real y) ^ Suc n)) sums
           (\<Sum>m. 1 / (of_nat (Suc m) * (1 - exp (2 * pi * Suc m * complex_of_real y))))"
proof -
  define x where "x = exp (-2 * pi * complex_of_real y)"
  have "(\<lambda>n. ln (1 - x ^ Suc n)) sums (\<Sum>m. 1 / (of_nat (Suc m) * (1 - inverse x ^ Suc m)))"
    using assms by (intro siegel_dedekind_eta_sum2) (auto simp: x_def zero_less_mult_iff)
  also have "(\<Sum>m. 1 / (of_nat (Suc m) * (1 - inverse x ^ Suc m))) =
             (\<Sum>m. 1 / (of_nat (Suc m) * (1 - exp (2 * pi * Suc m * complex_of_real y))))"
    by (simp flip: exp_of_nat_mult add: mult_ac x_def exp_minus del: power_Suc)
  finally show ?thesis
    unfolding x_def .
qed

lemma siegel_dedekind_eta_sum4:
  assumes "y > 0"
  shows   "exp (\<Sum>m. 1 / (of_nat (Suc m) *
              (1 - exp (complex_of_real (2 * pi * real (Suc m)) * complex_of_real y)))) =
           (\<Prod>i. 1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i)"
proof -
  have *: "summable (\<lambda>n. ln (1 - exp (-2 * pi * complex_of_real y) ^ Suc n))"
    using siegel_dedekind_eta_sum3[OF assms] by (simp add: sums_iff)
  have "(\<Prod>i. exp (Ln (1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i))) =
         exp (\<Sum>n. Ln (1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc n))"
    using prodinf_exp[OF *] .
  also have "(\<lambda>i. exp (Ln (1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i))) =
             (\<lambda>i. 1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i)"
  proof (rule ext, goal_cases)
    case (1 i)
    have "norm (exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i) =
          exp (- (2 * pi * y)) ^ Suc i"
      unfolding norm_power by (auto simp del: power_Suc)
    also have "\<dots> = exp (-2*pi*y*Suc i)"
      by (subst exp_of_nat_mult [symmetric]) (auto simp: algebra_simps)
    also have "\<dots> < 1"
      using assms by simp
    finally have "exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc i \<noteq> 1"
      by auto
    thus ?case
      by (subst exp_Ln) auto
  qed
  also have "(\<Sum>n. Ln (1 - exp (complex_of_real (- 2 * pi) * complex_of_real y) ^ Suc n)) =
             (\<Sum>m. 1 / (of_nat (Suc m) * (1 - exp (2 * pi * Suc m * complex_of_real y))))"
    using siegel_dedekind_eta_sum3[OF assms] by (simp add: sums_iff)
  finally show ?thesis ..
qed

end
