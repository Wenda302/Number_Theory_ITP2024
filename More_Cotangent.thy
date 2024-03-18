theory More_Cotangent
  imports Meromorphic_Extras "Bernoulli.Bernoulli_FPS" "HOL-Real_Asymp.Real_Asymp" "Formal_Puiseux_Series.Formal_Puiseux_Series"
begin

lemma continuous_on_cot [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::{real_normed_field,banach}"
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> sin (f z) \<noteq> 0"
  shows   "continuous_on A (\<lambda>x. cot (f x))"
  unfolding cot_def by (intro continuous_intros assms) (use assms in auto)

lemma cot_eq_0_imp_Im_0: "cot z = 0 \<Longrightarrow> Im z = 0"
  by (auto simp: cot_def sin_eq_0 cos_eq_0)

lemma cot_conv_exp:
  assumes "Im z \<noteq> 0 \<or> Re (z / of_real pi) \<notin> \<int>"
  shows "cot z = -\<i> * (1 - 2 / (1 - exp (-(2 * (\<i> * z)))))"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have "exp (2 * (\<i> * z)) \<noteq> 1"
    using assms by (auto simp: exp_eq_1)
  thus ?thesis
    unfolding cot_def cos_exp_eq sin_exp_eq exp_double exp_minus
    apply (simp add: divide_simps)
    apply (auto simp add: exp_minus field_simps power2_eq_square)
    done
qed

lemma cot_i_times:
  assumes "Re z \<noteq> 0 \<or> Im (z / of_real pi) \<notin> \<int>"
  shows   "cot (\<i> * z) = (1 - 2 / (1 - exp (2*z))) / \<i>"
  using assms by (subst cot_conv_exp) (auto simp: minus_in_Ints_iff)

lemma holomorphic_on_cot [holomorphic_intros]:
  "A \<subseteq> -range (\<lambda>n. pi * of_int n) \<Longrightarrow> cot holomorphic_on A"
  unfolding cot_def by (intro holomorphic_intros) (auto simp: sin_eq_0)

lemma holomorphic_on_cot' [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> f z \<notin> range (\<lambda>n. complex_of_real pi * of_int n)) \<Longrightarrow>
   (\<lambda>z. cot (f z)) holomorphic_on A"
  unfolding cot_def by (intro holomorphic_intros; force simp: sin_eq_0)

lemma analytic_on_cot [analytic_intros]:
  "A \<subseteq> -range (\<lambda>n. pi * of_int n) \<Longrightarrow> cot analytic_on A"
  unfolding cot_def by (intro analytic_intros) (auto simp: sin_eq_0)

lemma analytic_on_cot' [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> f z \<notin> range (\<lambda>n. complex_of_real pi * of_int n)) \<Longrightarrow>
   (\<lambda>z. cot (f z)) analytic_on A"
  unfolding cot_def by (intro analytic_intros; force simp: sin_eq_0)

lemma meromorphic_on_cot [meromorphic_intros]:
  "cot meromorphic_on UNIV (range (\<lambda>n. pi * of_int n))"
proof -
  have "\<not>z islimpt range (\<lambda>x. complex_of_real pi * of_int x)" for z
    by (intro discrete_imp_not_islimpt[of pi]) (auto simp: dist_mult_left dist_of_int)
  thus ?thesis
    unfolding cot_def
    by (intro meromorphic_intros)
       (auto intro!: holomorphic_on_imp_meromorphic_on holomorphic_intros simp: sin_eq_0)
qed


definition fps_cot_coeff :: "nat \<Rightarrow> real" where
  "fps_cot_coeff m = (-1)^m * 2^(2*m) * bernoulli (2 * m) / fact (2 * m)"

definition fps_cot :: "'a \<Rightarrow> 'a :: real_normed_field fps" where
  "fps_cot c = Abs_fps (\<lambda>n. if even n then 0 else of_real (fps_cot_coeff ((n + 1) div 2)) * c ^ n)"

definition fls_cot :: "'a \<Rightarrow> 'a :: real_normed_field fls" where
  "fls_cot c = fls_const (inverse c) * fls_X_inv + fps_to_fls (fps_cot c)"

lemma fls_nth_cot_neg1 [simp]: "fls_nth (fls_cot c) (-1) = inverse c"
  by (simp add: fls_cot_def)

lemma fls_nth_cot_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> fls_nth (fls_cot c) n = fps_nth (fps_cot c) (nat n)"
  by (simp add: fls_cot_def)

lemma fps_nth_cot_even [simp]: "even n \<Longrightarrow> fps_nth (fps_cot c) n = 0"
  by (simp add: fps_cot_def)

lemma fps_nth_cot_odd:
  "odd n \<Longrightarrow> fps_nth (fps_cot c) n = c ^ n * of_real (fps_cot_coeff ((n+1) div 2))"
  by (simp add: fps_cot_def)

lemmas eval_fps_nth_cot = fps_nth_cot_odd fps_cot_coeff_def fact_numeral


lemma fls_subdegree_cot [simp]:
  assumes "c \<noteq> 0"
  shows   "fls_subdegree (fls_cot c) = -1"
  unfolding fls_cot_def
  using assms by (subst fls_subdegree_add_eq1) (auto simp: fls_subdegree_fls_to_fps)

lemma has_laurent_expansion_cot_aux:
  "(\<lambda>z. z * cot z - 1) has_laurent_expansion fps_to_fls (fps_X * fps_cot 1)"
proof -
  define h where "h = (\<lambda>z. 2 * \<i> * z)"
  define F where "F = fps_compose bernoulli_fps (fps_const (2 * \<i>) * fps_X)"

  have "eventually (\<lambda>z::complex. z \<in> ball 0 pi - {0}) (at 0)"
    by (intro eventually_at_in_open) auto
  hence "eventually (\<lambda>z. Im z \<noteq> 0 \<or> Re (z / of_real pi) \<notin> \<int>) (at 0)"
  proof eventually_elim
    case (elim z)
    have "Re z / pi \<notin> \<int>" if "Im z = 0"
    proof
      assume "Re z / pi \<in> \<int>"
      then obtain k where k: "of_int k = Re z / pi"
        by (elim Ints_cases) auto
      have "\<bar>of_int k\<bar> = \<bar>Re z\<bar> / pi"
        using k by simp
      also have "\<dots> = norm z / pi"
        by (simp add: \<open>Im z = 0\<close> norm_complex_def)
      also have "\<dots> < pi / pi"
        using elim by (intro divide_strict_right_mono) auto
      finally have "k = 0"
        by auto
      with elim and k show False
        using \<open>Im z = 0\<close> by (auto simp: complex_eq_iff)
    qed
    thus ?case
      by auto
  qed
  hence ev: "eventually (\<lambda>z. h z / (exp (h z) - 1) = z * (cot z - \<i>)) (at 0)"
  proof eventually_elim
    case (elim z)
    hence not_1: "exp (\<i> * (z * 2)) \<noteq> 1"
      by (auto simp: exp_eq_1)
    have "cot z = - \<i> * (1 - 2 / (1 - exp (- (2 * (\<i> * z)))))"
      using elim by (subst cot_conv_exp) auto
    also have "z * (\<dots> - \<i>) = h z / (exp (h z) - 1)"
      using not_1 by (auto simp: h_def field_simps exp_minus)
    finally show ?case ..
  qed

  have [simp]: "subdegree (1 - fps_exp 1 :: complex fps) = 1"
    by (intro subdegreeI) auto
  have "((\<lambda>z. z / (exp z - 1)) \<circ> h) has_laurent_expansion
          Laurent_Convergence.fls_compose_fps (fls_X / (fps_to_fls (fps_exp 1) - 1)) (fps_const (2 * \<i>) * fps_X)"
    unfolding h_def
    by (intro laurent_expansion_intros fps_expansion_intros has_laurent_expansion_fps) auto
  also have "fls_X / (fps_to_fls (fps_exp 1) - (1 :: complex fls)) =
             fps_to_fls bernoulli_fps"
    unfolding bernoulli_fps_def by (subst fls_divide_fps_to_fls [symmetric]) auto
  also have "Laurent_Convergence.fls_compose_fps \<dots> (fps_const (2 * \<i>) * fps_X) =
             fps_to_fls (fps_compose bernoulli_fps (fps_const (2 * \<i>) * fps_X))"
    by (rule fls_compose_fps_to_fls) auto
  finally have "((\<lambda>z. z / (exp z - 1)) \<circ> h) has_laurent_expansion fps_to_fls F"
    unfolding F_def .
  also have "?this \<longleftrightarrow> (\<lambda>z. z * (cot z - \<i>)) has_laurent_expansion fps_to_fls F"
    using ev by (intro has_laurent_expansion_cong) (auto simp: o_def)
  finally have "(\<lambda>z. z * (cot z - \<i>) + \<i> * z - 1) has_laurent_expansion
                   fps_to_fls F + fls_const \<i> * fls_X - 1"
    by (intro laurent_expansion_intros) auto
  also have "fps_to_fls F + fls_const \<i> * fls_X - 1 = fps_to_fls (F + fps_const \<i> * fps_X - 1)"
    by (simp add: fls_times_fps_to_fls)
  also have "F + fps_const \<i> * fps_X - 1 = fps_X * fps_cot 1"
    unfolding F_def
    by (auto simp add: fps_eq_iff fps_cot_def fps_compose_linear fps_cot_coeff_def
                       bernoulli_odd_eq_0 elim!: oddE)
  finally show "(\<lambda>z. z * cot z - 1) has_laurent_expansion fps_to_fls (fps_X * fps_cot 1)"
    by (simp add: algebra_simps)
qed

lemma has_laurent_expansion_cot' [laurent_expansion_intros]:
  "cot has_laurent_expansion fls_cot 1"
proof -
  have "(\<lambda>z. inverse z + (z * cot z - 1) / z) has_laurent_expansion fls_X_inv + fps_to_fls (fps_X * fps_cot 1) / fls_X"
    by (intro laurent_expansion_intros has_laurent_expansion_cot_aux)
  also have "fps_to_fls (fps_X * fps_cot 1) / fls_X = fps_to_fls (fps_cot 1)"
    by (simp add: fls_times_fps_to_fls fls_X_times_conv_shift)
  also have "fls_X_inv + fps_to_fls (fps_cot 1) = fls_cot 1"
    by (simp add: fls_cot_def)
  also have "(\<lambda>z. inverse z + (z * cot z - 1) / z) has_laurent_expansion \<dots> \<longleftrightarrow>
             cot has_laurent_expansion \<dots>"
    by (intro has_laurent_expansion_cong) (auto simp: eventually_at_filter field_simps)
  finally show ?thesis .
qed

lemma has_laurent_expansion_cot [laurent_expansion_intros]:
  "(\<lambda>z. cot (c * z)) has_laurent_expansion fls_cot c"
proof (cases "c = 0")
  case [simp]: False
  have "(cot \<circ> ((*) c)) has_laurent_expansion Laurent_Convergence.fls_compose_fps (fls_cot 1) (fps_const c * fps_X)"
    by (intro laurent_expansion_intros fps_expansion_intros has_laurent_expansion_fps) auto
  also have "Laurent_Convergence.fls_compose_fps (fls_cot 1) (fps_const c * fps_X) = fls_cot c"
    by (auto simp: expand_fls_eq fls_nth_fls_compose_fps_linear fls_cot_def fps_cot_def power_int_def)
  finally show ?thesis by simp
next
  case [simp]: True
  have "fls_cot c = 0"
    by (auto simp: fls_cot_def fps_cot_def fps_cot_coeff_def fps_eq_iff simp del: of_nat_Suc)
  thus ?thesis
    by auto
qed

lemma norm_cot_complex_square:
  "norm (cot z) ^ 2 = 2 * (cos (Re z) ^ 2 + sinh (Im z) ^ 2) / (cosh (2 * Im z) - cos (2 * Re z))"
proof -
  define x and y where "x = Re z" and "y = Im z"
  have "norm (cot z) ^ 2 = norm (cos z) ^ 2 / norm (sin z) ^ 2"
    by (simp add: cot_def norm_divide power_divide)
  also have "\<dots> = ((cos x) ^ 2 * 4 + (exp y - exp (-y)) ^ 2) /
                   (exp (2 * y) + exp (-2 * y) - 2 * cos (2 * x))"
    by (simp add: norm_cos_squared norm_sin_squared exp_minus x_def y_def)
  also have "(exp y - exp (-y)) ^ 2 = 4 * sinh y ^ 2"
    by (simp add: sinh_def power2_eq_square)
  also have "exp (2 * y) + exp (-2 * y) = 2 * cosh (2 * y)"
    by (simp add: cosh_def)
  also have "(cos x ^ 2 * 4 + 4 * sinh y ^ 2) = 2 * (2 * (cos x ^ 2 + sinh y ^ 2))"
    by (simp add: algebra_simps)
  also have "2 * cosh (2 * y) - 2 * cos (2 * x) = 2 * (cosh (2 * y) - cos (2 * x))"
    by (simp add: algebra_simps)
  also have "(2 * (2 * (cos x ^ 2 + sinh y ^ 2))) / \<dots> =
             2 * (cos x ^ 2 + sinh y ^ 2) / (cosh (2 * y) - cos (2 * x))"
    by (rule nonzero_mult_divide_mult_cancel_left) auto
  finally show ?thesis
    unfolding x_def y_def .
qed

lemma norm_cot_complex_square':
  fixes z :: complex
  defines "x \<equiv> Re z" and "y \<equiv> Im z"
  assumes nz: "cos (2 * x) \<noteq> 0" "cosh (2 * y) \<noteq> cos (2 * x)"
  shows   "norm (cot z) ^ 2 = 1 + 2 / (cosh (2 * y) / cos (2 * x) - 1)"
proof -   
  have "2 / (cosh (2 * y) / cos (2 * x) - 1) = 2 * cos (2 * x) / (cosh (2 * y) - cos (2 * x))"
    using nz by (simp add: field_simps)
  also have "1 + \<dots> = (cosh (2 * y) + cos (2 * x)) / (cosh (2 * y) - cos (2 * x))"
    using nz by (simp add: field_simps)
  also have "cosh (2 * y) + cos (2 * x) = 2 * (cos x ^ 2 + sinh y ^ 2)"
    by (simp add: cosh_double cos_double cos_squared_eq cosh_square_eq)
  also have "2 * ((cos x)\<^sup>2 + (sinh y)\<^sup>2) / (cosh (2 * y) - cos (2 * x)) = norm (cot z) ^ 2"
    unfolding x_def y_def by (rule norm_cot_complex_square [symmetric])
  finally show ?thesis ..
qed

lemma norm_cot_complex:
  "norm (cot z) = sqrt (2 * (cos (Re z) ^ 2 + sinh (Im z) ^ 2) / (cosh (2 * Im z) - cos (2 * Re z)))"
  by (intro real_sqrt_unique [symmetric] norm_cot_complex_square) auto
  
lemma tendsto_cot_Im_at_bot: "filterlim cot (nhds \<i>) (filtercomap Im at_bot)"
proof -
  have "filterlim ((*) (2 :: real)) at_bot at_bot"
    by real_asymp
  hence "filterlim (\<lambda>z. - (2 * (\<i> * z))) (filtercomap Re at_bot) (filtercomap Im at_bot)"
    by (auto simp: filterlim_filtercomap_iff o_def intro!: filterlim_filtercomapI)
  hence "filterlim (\<lambda>z. -\<i> * (1 - 2 / (1 - exp (-(2 * (\<i> * z))))))
          (nhds (-\<i> * (1 - 2 / (1 - 0)))) (filtercomap Im at_bot)"
    by (intro tendsto_intros filterlim_compose[OF tendsto_exp_0_Re_at_bot]) auto
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro filterlim_cong)
    have "eventually (\<lambda>x. Im x < 0) (filtercomap Im at_bot)"
      by (intro eventually_filtercomapI eventually_gt_at_bot)
    thus "eventually (\<lambda>z.  - \<i> * (1 - 2 / (1 - exp (- (2 * (\<i> * z))))) = cot z) (filtercomap Im at_bot)"
      by eventually_elim (auto simp: cot_conv_exp)
  qed auto
  finally show ?thesis .
qed

lemma tendsto_cot_Im_at_top: "filterlim cot (nhds (-\<i>)) (filtercomap Im at_top)"
proof -
  have "filterlim ((*) (2 :: real)) at_top at_top"
    by real_asymp
  hence "filterlim (\<lambda>z. - (2 * (\<i> * z))) (filtercomap Re at_top) (filtercomap Im at_top)"
    by (auto simp: filterlim_filtercomap_iff o_def intro!: filterlim_filtercomapI)
  hence "filterlim (\<lambda>z. -\<i> * (1 + 2 / (exp (-(2 * (\<i> * z))) + (-1))))
          (nhds (-\<i> * (1 + 0))) (filtercomap Im at_top)"
    by (intro tendsto_intros tendsto_divide_0[OF tendsto_const]
              tendsto_add_filterlim_at_infinity'[OF _ tendsto_const]
               filterlim_compose[OF filterlim_exp_at_infinity_Re_at_top])
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro filterlim_cong)
    have "eventually (\<lambda>x. Im x > 0) (filtercomap Im at_top)"
      by (intro eventually_filtercomapI eventually_gt_at_top)
    thus "eventually (\<lambda>z. - \<i> * (1 + 2 / (exp (- (2 * (\<i> * z))) + - 1)) = cot z) (filtercomap Im at_top)"
    proof eventually_elim
      case (elim z)
      have "cot z = - (\<i> * (1 + -2 / (1 - exp (- (2 * (\<i> * z))))))"
        using elim by (subst cot_conv_exp) auto
      also have "-2 / (1 - exp (- (2 * (\<i> * z)))) = 2 / (-(1 - exp (- (2 * (\<i> * z)))))"
        by (subst divide_minus_right) auto
      also have "-(1 - exp (- (2 * (\<i> * z)))) = exp (- (2 * (\<i> * z))) + (-1)"
        by simp
      finally show ?case by simp
    qed
  qed auto
  finally show ?thesis .
qed

end
