section \<open>The Dedekind \<open>\<eta>\<close> function\<close>
theory Dedekind_Eta_Function
imports Dirichlet_Series.Moebius_Mu
        Bernoulli.Bernoulli
        Modular_Forms_Valence_Formula
        Siegel_Dedekind_Eta
        Dedekind_Sums
        Q_Pochhammer_Infinite
begin

subsection \<open>Definition and basic properties of \<open>\<eta>\<close>\<close>

(* Definition in 3.1 p.47 *)
definition dedekind_eta:: "complex \<Rightarrow> complex" ("\<eta>") where
  "\<eta> z = exp (\<i> * of_real pi * z / 12) * euler_phi (cusp_q 1 z)"

lemma dedekind_eta_nonzero [simp]: "Im z > 0 \<Longrightarrow> \<eta> z \<noteq> 0"
  by (auto simp: dedekind_eta_def)

lemma holomorphic_dedekind_eta [holomorphic_intros]:
  assumes "A \<subseteq> {z. Im z > 0}"
  shows   "\<eta> holomorphic_on A"
  using assms unfolding dedekind_eta_def by (auto intro!: holomorphic_intros)

lemma holomorphic_dedekind_eta' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "(\<lambda>z. \<eta> (f z)) holomorphic_on A"
  using assms unfolding dedekind_eta_def by (auto intro!: holomorphic_intros)

lemma analytic_dedekind_eta [analytic_intros]:
  assumes "A \<subseteq> {z. Im z > 0}"
  shows   "\<eta> analytic_on A"
  using assms unfolding dedekind_eta_def by (auto intro!: analytic_intros)

lemma analytic_dedekind_eta' [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "(\<lambda>z. \<eta> (f z)) analytic_on A"
  using assms unfolding dedekind_eta_def by (auto intro!: analytic_intros)

lemma meromorphic_on_dedekind_eta [meromorphic_intros]:
  "f analytic_on A \<Longrightarrow> (\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0) \<Longrightarrow> (\<lambda>z. \<eta> (f z)) meromorphic_on A"
  by (rule analytic_on_imp_meromorphic_on) (auto intro!: analytic_intros)

lemma continuous_on_dedekind_eta [continuous_intros]:
  "A \<subseteq> {z. Im z > 0} \<Longrightarrow> continuous_on A \<eta>"
  unfolding dedekind_eta_def by (intro continuous_intros) auto

lemma continuous_on_dedekind_eta' [continuous_intros]:
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> Im (f z) > 0"
  shows   "continuous_on A (\<lambda>z. \<eta> (f z))"
  using assms unfolding dedekind_eta_def by (intro continuous_intros) auto

lemma tendsto_dedekind_eta [tendsto_intros]:
  assumes "(f \<longlongrightarrow> c) F" "Im c > 0"
  shows   "((\<lambda>x. \<eta> (f x)) \<longlongrightarrow> \<eta> c) F"
  unfolding dedekind_eta_def using assms by (intro tendsto_intros assms) auto

lemma tendsto_at_cusp_dedekind_eta [tendsto_intros]: "(\<eta> \<longlongrightarrow> 0) at_cusp"
proof -
  have "(cusp_q 1 \<longlongrightarrow> 0) at_cusp"
    by (simp add: filterlim_cusp_q_at_cusp')
  moreover have "filterlim (\<lambda>z. z / 24) at_cusp at_cusp"
    using filtermap_scaleR_at_cusp[of "1/24"]
    by (auto simp: scaleR_conv_of_real filterlim_def)
  ultimately have "((\<lambda>z. cusp_q 1 (z / 24)) \<longlongrightarrow> 0) at_cusp"
    by (rule filterlim_compose)
  hence *: "((\<lambda>x. exp (\<i> * complex_of_real pi * x / 12)) \<longlongrightarrow> 0) at_cusp"
    by (simp add: cusp_q_def field_simps)
  have "((\<lambda>z. exp (\<i>*pi*z/12) * euler_phi (cusp_q 1 z)) \<longlongrightarrow> 0 * euler_phi 0) at_cusp"
    by (intro tendsto_intros *) auto
  thus ?thesis
    by (simp add: dedekind_eta_def [abs_def])
qed

lemma dedekind_eta_plus1:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + 1) = cis (pi/12) * \<eta> z"
proof -
  have "\<eta> (z + 1) = exp (\<i> * pi * (z + 1) / 12) * euler_phi (cusp_q 1 (z + 1))"
    by (simp add: dedekind_eta_def)
  also have "cusp_q 1 (z + 1) = cusp_q 1 z"
    using cusp_q.plus_1[of 1 z] by simp
  also have "exp (\<i> * pi * (z + 1) / 12) = exp (\<i> * pi / 12) * exp (\<i> * pi * z / 12)"
    by (simp add: ring_distribs add_divide_distrib exp_add)
  also have "\<dots> * euler_phi (cusp_q 1 z) = exp (of_real pi * \<i> / 12) * \<eta> z"
    by (simp add: dedekind_eta_def mult_ac)
  finally show ?thesis by (simp add: cis_conv_exp mult_ac)
qed

lemma dedekind_eta_plus_nat:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + of_nat n) = cis (pi * n / 12) * \<eta> z"
proof (induction n)
  case (Suc n)
  have "\<eta> (z + of_nat (Suc n)) = \<eta> (z + of_nat n + 1)"
    by (simp add: add_ac)
  also have "\<dots> = cis (pi/12) * \<eta> (z + of_nat n)"
    using z by (intro dedekind_eta_plus1) auto
  also have "\<eta> (z + of_nat n) = cis (pi*n/12) * \<eta> z"
    by (rule Suc.IH)
  also have "cis (pi/12) * (cis (pi*n/12) * \<eta> z) = cis (pi*Suc n/12) * \<eta> z"
    by (simp add: ring_distribs add_divide_distrib exp_add mult_ac cis_mult)
  finally show ?case .
qed auto

lemma dedekind_eta_plus_int:
  assumes z: "Im z > 0"
  shows   "\<eta> (z + of_int n) = cis (pi*n/12) * \<eta> z"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis
    using dedekind_eta_plus_nat[OF assms, of "nat n"] by simp
next
  case False
  thus ?thesis
    using dedekind_eta_plus_nat[of "z + of_int n" "nat (-n)"] assms
    by (auto simp: cis_mult field_simps)
qed


subsection \<open>Functional equation for \<open>\<eta>(-1/z)\<close>\<close>

text \<open>
  Apostol's Theorem~3.1: the functional equation of $\eta$ with respect to the map
  $z\mapsto -\frac{1}{z}$.
\<close>
theorem dedekind_eta_minus_one_over:
  assumes "Im z > 0"
  shows   "\<eta> (-(1/z)) = csqrt (-\<i>*z) * \<eta> z"
proof -
  have eq: "\<eta> (-(1/z)) = csqrt (-\<i>*z) * \<eta> z" if z: "Re z = 0" "Im z > 0" for z :: complex
  proof -
    define y where "y = Im z"
    from z have y: "y > 0"
      by (auto simp: y_def)
    have z_eq: "z = \<i> * y"
      using z by (auto simp: y_def complex_eq_iff)
    define S where "S = (\<lambda>y. \<Sum>k. 1 / (Suc k * (1 - exp (2 * pi * Suc k * complex_of_real y))))"
    define S' where "S' = (\<lambda>y. (\<Sum>n. Ln (1 - exp (complex_of_real (-2*pi*y)) ^ Suc n)))"
    define x where "x = exp (complex_of_real (-2*pi*y))"
    define x' where "x' = exp (complex_of_real (-2*pi/y))"
    have "exp (- ln (complex_of_real y) / 2) = exp (S y - S (1 / y) - pi / 12 * (y - 1 / y))"
      unfolding siegel_dedekind_eta'[OF y, symmetric] using y by (simp add: S_def divide_simps)
    also have "exp (-ln (complex_of_real y) / 2) = 1 / csqrt (-\<i>*(\<i>*y))"
      using y by (subst csqrt_exp_Ln)
                 (auto simp flip: exp_of_real Ln_of_real simp: field_simps exp_minus)
    also have "\<dots> = 1 / sqrt y"
      using y by simp
    finally have "exp (S (1 / y)) / exp (pi / 12 / y) = exp (S y) / exp (pi / 12 * y) * sqrt y"
      using y unfolding exp_diff exp_minus ring_distribs diff_divide_distrib of_real_diff
      by (simp add: divide_simps mult_ac flip: exp_of_real)
    also have "exp (S (1 / y)) = euler_phi x'"
      unfolding S_def using y
      by (subst siegel_dedekind_eta_sum4) (auto simp: S'_def x'_def euler_phi_def qpochhammer_inf_def)
    also have "exp (S y) = euler_phi x"
      unfolding S_def using y
      by (subst siegel_dedekind_eta_sum4) (auto simp: S'_def x_def euler_phi_def qpochhammer_inf_def)
    also have "euler_phi x' / complex_of_real (exp (pi / 12 / y)) = \<eta> (-(1/(\<i>*y)))"
      by (auto simp: x'_def dedekind_eta_def exp_minus field_simps cusp_q_def simp flip: exp_of_real)
    also have "euler_phi x / complex_of_real (exp (pi / 12 * y)) = \<eta> (\<i>*y)"
      by (auto simp: x_def dedekind_eta_def exp_minus field_simps cusp_q_def simp flip: exp_of_real)
    finally show ?thesis
      using y by (simp add: z_eq)
  qed

  have "\<eta> (-(1/z)) - csqrt (-\<i>*z) * \<eta> z = 0" (is "?f z = 0")
  proof (rule analytic_continuation[where f = ?f])
    show "?f holomorphic_on {z. Im z > 0}"
      by (intro holomorphic_intros)  (auto simp: complex_nonpos_Reals_iff)
    show "open {z. Im z > 0}" "connected {z. Im z > 0}"
      by (auto intro: open_halfspace_Im_gt convex_connected convex_halfspace_Im_gt)
    show "?f z = 0" if "z \<in> (\<lambda>y. \<i> * complex_of_real y) ` {0<..}" for z
      using eq[of z] that by auto
    show "(\<lambda>y. \<i> * complex_of_real y) ` {0<..} \<subseteq> {z. 0 < Im z}"
      by auto
    have "(1 :: real) islimpt {0<..}"
      by (rule open_imp_islimpt) auto
    thus "\<i> * complex_of_real 1 islimpt (\<lambda>y. \<i> * complex_of_real y) ` {0<..}"
      by (intro islimpt_isCont_image) (auto simp: eventually_at_filter)
  qed (use assms in auto)
  thus ?thesis
    by simp
qed


subsection \<open>General functional equation\<close>

text \<open>
  From our results so far, it is easy to see that $\eta^{24}$ is a modular form of weight 12.
  Thus one might think that this means that $\eta$ is a modular form of weight $\frac{1}{2}$ --
  and in fact, it \<^emph>\<open>almost\<close> is: if $A = \begin{pmatrix}a&b\\c&d\end{pmatrix}\in\text{SL}(2)$ is a
  modular transformation, then $\eta(Az) = \epsilon(A)\sqrt{z}\eta(z)$, where $\epsilon(A)$ is
  a 24-th unit root that depends on $A$ but not on $z$.
\<close>
definition dedekind_eps :: "modgrp \<Rightarrow> complex" ("\<epsilon>") where
  "\<epsilon> f =
     (if is_singular_modgrp f then
        cis (pi * ((modgrp_a f + modgrp_d f) / (12 * modgrp_c f) -
          dedekind_sum (modgrp_d f) (modgrp_c f) - 1 / 4))
      else
        cis (pi * modgrp_b f / 12)
     )"

lemma dedekind_eps_1 [simp]: "dedekind_eps 1 = 1"
  by (simp add: dedekind_eps_def)

lemma dedekind_eps_shift [simp]: "\<epsilon> (shift_modgrp m) = cis (pi * m / 12)"
  by (simp add: dedekind_eps_def dedekind_sum_def)

lemma dedekind_eps_S [simp]: "dedekind_eps S_modgrp = cis (-pi / 4)"
  by (simp add: dedekind_eps_def dedekind_sum_def complex_eq_iff)

lemma dedekind_eps_shift_right [simp]: "\<epsilon> (f * shift_modgrp m) = cis (pi * m / 12) * \<epsilon> f"
proof (cases "is_singular_modgrp f")
  case True
  have [simp]: "modgrp_c f \<noteq> 0"
    using True by (simp add: is_singular_modgrp_altdef)
  have "dedekind_sum (modgrp_c f * m + modgrp_d f) (modgrp_c f) =
        dedekind_sum (modgrp_d f) (modgrp_c f)"
  proof (intro dedekind_sum_cong)
    have "[modgrp_c f * m + modgrp_d f = 0 + modgrp_d f] (mod modgrp_c f)"
      by (intro cong_add) (auto simp: Cong.cong_def)
    thus "[modgrp_c f * m + modgrp_d f = modgrp_d f] (mod modgrp_c f)"
      by simp
  qed (use coprime_modgrp_c_d[of f] in \<open>auto simp: coprime_commute\<close>)
  thus ?thesis using True
    by (simp add: dedekind_eps_def add_divide_distrib ring_distribs is_singular_modgrp_times_iff
             flip: cis_mult cis_divide)
next
  case False
  define n where "n = modgrp_b f"
  have f: "f = shift_modgrp n"
    unfolding n_def using False by (rule not_singular_modgrpD)
  have "f * shift_modgrp m = shift_modgrp (n + m)"
    by (simp add: shift_modgrp_add f)
  also have "\<epsilon> \<dots> = cis (pi * m / 12) * \<epsilon> f"
    by (simp add: f dedekind_eps_def cis_mult ring_distribs add_divide_distrib add_ac)
  finally show ?thesis .
qed

lemma dedekind_eps_shift_left [simp]: "\<epsilon> (shift_modgrp m * f) = cis (pi * m / 12) * \<epsilon> f"
proof (cases "is_singular_modgrp f")
  case True
  have [simp]: "modgrp_c f \<noteq> 0"
    using True by (simp add: is_singular_modgrp_altdef)
  have a: "modgrp_a (shift_modgrp m * f) = modgrp_a f + m * modgrp_c f"
    unfolding shift_modgrp_code using modgrp.unimodular[of f] modgrp_c_nonneg[of f]
    by (subst (3) modgrp_abcd [symmetric], subst times_modgrp_code) (auto simp: modgrp_a_code algebra_simps)
  show ?thesis using True
    by (auto simp: dedekind_eps_def a add_divide_distrib ring_distribs simp flip: cis_mult cis_divide)
next
  case False
  then obtain n where [simp]: "f = shift_modgrp n"
    using not_singular_modgrpD by blast
  show ?thesis
    by simp
qed

lemma dedekind_eps_S_right:
  assumes "is_singular_modgrp f" "modgrp_d f \<noteq> 0"
  shows   "\<epsilon> (f * S_modgrp) = cis (-sgn (modgrp_d f) * pi / 4) * \<epsilon> f"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have "c > 0"
    using assms modgrp_c_nonneg[of f] unfolding is_singular_modgrp_altdef a_b_c_d_def by auto
  from assms have [simp]: "d \<noteq> 0"
    by (auto simp: a_b_c_d_def)
  have "coprime c d"
    unfolding a_b_c_d_def by (intro coprime_modgrp_c_d)
  have det: "a * d - b * c = 1"
    unfolding a_b_c_d_def by (rule modgrp_abcd_det)
  hence det': "a * d = b * c + 1"
    by linarith

  have "pole_modgrp f \<noteq> (0 :: real)"
    using assms by transfer (auto simp: modgrp_rel_def split: if_splits)
  hence sing: "is_singular_modgrp (f * S_modgrp)"
    using assms by (auto simp: is_singular_modgrp_times_iff)

  show ?thesis
  proof (cases d "0 :: int" rule: linorder_cases)
    case greater
    have [simp]: "modgrp_a (f * S_modgrp) = b"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_b (f * S_modgrp) = -a"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_c (f * S_modgrp) = d"
      using greater unfolding a_b_c_d_def by transfer auto
    have [simp]: "modgrp_d (f * S_modgrp) = -c"
      using greater unfolding a_b_c_d_def by transfer (auto split: if_splits)

    have "dedekind_sum (-c) d = -dedekind_sum c d"
      using \<open>coprime c d\<close> by (simp add: dedekind_sum_negate)
    also have "\<dots> = dedekind_sum d c - c / d / 12 - d / c / 12 + 1 / 4 - 1 / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d > 0\<close> \<open>coprime c d\<close> by (subst dedekind_sum_reciprocity') simp_all
    finally have *: "dedekind_sum (-c) d = \<dots>" .
    have [simp]: "cnj (cis (pi / 4)) = 1 / cis (pi / 4)"
      by (subst divide_conv_cnj) auto

    have "\<epsilon> (f * S_modgrp) = cis (pi * ((b - c) / (12 * d) + c / (12*d) +
                                   d / (12*c) + 1 / (12 * c * d) - dedekind_sum d c - 1 / 2))"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d > 0\<close> sing assms
      by (simp add: * algebra_simps)
    also have "(b - c) / (12 * d) + c / (12*d) + d / (12*c) + 1 / (12 * c * d) =
               (b * c + 1 + d * d) / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d > 0\<close> by (simp add: field_simps)
    also have "b * c + 1 = a * d"
      using det by (simp add: algebra_simps)
    also have "(a * d + d * d) / (12 * c * d) = (a + d) / (12 * c)"
      using \<open>c > 0\<close> \<open>d > 0\<close> by (simp add: field_simps)
    also have "cis (pi * ((a + d) / (12 * c) - dedekind_sum d c - 1 / 2)) =
                cis (-pi / 4) * \<epsilon> f"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d > 0\<close> sing assms
      by (auto simp: cis_mult algebra_simps diff_divide_distrib add_divide_distrib)
    finally show ?thesis
      using \<open>d > 0\<close> by (simp add: a_b_c_d_def)

  next
    case less
    have [simp]: "modgrp_a (f * S_modgrp) = -b"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_b (f * S_modgrp) = a"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_c (f * S_modgrp) = -d"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)
    have [simp]: "modgrp_d (f * S_modgrp) = c"
      using less unfolding a_b_c_d_def by transfer (auto split: if_splits)

    have "dedekind_sum c (-d) = 
            -dedekind_sum (-d) c - c / d / 12 - d / c / 12 - 1 / 4 - 1 / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d < 0\<close> \<open>coprime c d\<close> by (subst dedekind_sum_reciprocity') simp_all
    also have "-dedekind_sum (-d) c = dedekind_sum d c"
      using \<open>coprime c d\<close> by (subst dedekind_sum_negate) (auto simp: coprime_commute)
    finally have *: "dedekind_sum c (-d) =
                      dedekind_sum d c - c / d / 12 - d / c / 12 - 1 / 4 - 1 / (12 * c * d)" .

    have "\<epsilon> (f * S_modgrp) =
            cis (pi * (c / (12 * d) + d / (12 * c) + 1 / (12 * c * d) - (c - b) / (12 * d) -
                       dedekind_sum d c))"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d < 0\<close> sing assms
      by (simp add: * algebra_simps)
    also have "c / (12 * d) + d / (12 * c) + 1 / (12 * c * d) - (c - b) / (12 * d) =
               (d * d + (1 + b * c)) / (12 * c * d)"
      using \<open>c > 0\<close> \<open>d < 0\<close> by (simp add: field_simps)
    also have "1 + b * c = a * d"
      using det by (simp add: algebra_simps)
    also have "(d * d + a * d) / (12 * c * d) = (a + d) / (12 * c)"
      using \<open>c > 0\<close> \<open>d < 0\<close> by (simp add: field_simps)
    also have "cis (pi * ((a + d) / (12 * c) - dedekind_sum d c)) = cis (pi / 4) * \<epsilon> f"
      unfolding dedekind_eps_def a_b_c_d_def [symmetric] using \<open>d < 0\<close> sing assms
      by (auto simp: cis_mult algebra_simps diff_divide_distrib add_divide_distrib)
    finally show ?thesis
      using \<open>d < 0\<close> by (simp add: a_b_c_d_def)
  qed auto
qed

lemma dedekind_eps_root_of_unity: "\<epsilon> f ^ 24 = 1"
proof -
  have not_sing: "\<epsilon> f ^ 24 = 1" if "\<not>is_singular_modgrp f" for f
  proof -
    have "\<epsilon> f ^ 24 = cis (2 * (pi * real_of_int (modgrp_b f)))"
      using that by (auto simp: dedekind_eps_def Complex.DeMoivre)
    also have "2 * (pi * real_of_int (modgrp_b f)) = 2 * pi * real_of_int (modgrp_b f)"
      by (simp add: mult_ac)
    also have "cis \<dots> = 1"
      by (rule cis_multiple_2pi) auto
    finally show ?thesis .
  qed

  show ?thesis
  proof (induction f rule: modgrp_induct_S_shift')
    case (S f)
    show ?case
    proof (cases "modgrp_d f = 0")
      case d: False
      show ?thesis
      proof (cases "is_singular_modgrp f")
        case sing: True
        have "\<epsilon> (f * S_modgrp) ^ 24 = cis (- (pi * (real_of_int (sgn (modgrp_d f)) * 6)))"
          using d sing by (simp add: dedekind_eps_S_right field_simps Complex.DeMoivre S)
        also have "- (pi * (real_of_int (sgn (modgrp_d f)) * 6)) = 2 * pi * of_int (-3 * sgn (modgrp_d f))"
          by simp
        also have "cis \<dots> = 1"
          by (rule cis_multiple_2pi) auto
        finally show ?thesis .
      next
        case False
        then obtain n where [simp]: "f = shift_modgrp n"
          using not_singular_modgrpD by blast
        show ?thesis using False S
          by (simp add: algebra_simps Complex.DeMoivre)
      qed
    qed (auto intro: not_sing)
  qed (auto simp: Complex.DeMoivre algebra_simps)
qed
      

text \<open>
  The following theorem is Apostol's Theorem~3.4: the general functional equation for
  Dedekind's $\eta$ function. 

  Our version is actually more general than Apostol's lemma since it also holds for modular groups
  with $c = 0$ (i.e.\ shifts, i.e.\ $T^n$). We also use a slightly different definition of \<open>\<epsilon>\<close> 
  though, namely the one from Wikipedia. This makes the functional equation look a bit nicer than
  Apostol's version.
\<close>
theorem dedekind_eta_apply_modgrp:
  assumes "Im z > 0"
  shows   "\<eta> (apply_modgrp f z) = \<epsilon> f * csqrt (modgrp_factor f z) * \<eta> z"
  using assms
proof (induction f arbitrary: z rule: modgrp_induct_S_shift')
  case id
  thus ?case by simp
next
  case (shift f n z)
  have "\<eta> (apply_modgrp (f * shift_modgrp n) z) = \<eta> (apply_modgrp f (z + of_int n))"
    using shift.prems by (subst apply_modgrp_mult) auto
  also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (z + of_int n)) * \<eta> (z + of_int n)"
    using shift.prems by (subst shift.IH) auto
  also have "\<eta> (z + of_int n) = cis (pi * n / 12) * \<eta> z"
    using shift.prems by (subst dedekind_eta_plus_int) auto
  also have "\<epsilon> f * csqrt (modgrp_factor f (z + of_int n)) * (cis (pi * n / 12) * \<eta> z) =
             \<epsilon> (f * shift_modgrp n) * csqrt (modgrp_factor (f * shift_modgrp n) z) * \<eta> z"
    by simp
  finally show ?case .
next
  case (S f z)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have det: "a * d - b * c = 1"
    using modgrp_abcd_det[of f] by (simp add: a_b_c_d_def)
  from S.prems have [simp]: "z \<noteq> 0"
    by auto
  show ?case
  proof (cases "is_singular_modgrp f")
    case False
    hence f: "f = shift_modgrp b"
      unfolding a_b_c_d_def by (rule not_singular_modgrpD)
    have *: "f * S_modgrp = modgrp b (-1) 1 0"
      unfolding f shift_modgrp_code S_modgrp_code times_modgrp_code by simp
    have [simp]: "modgrp_a (f * S_modgrp) = b"
                 "modgrp_b (f * S_modgrp) = -1"
                 "modgrp_c (f * S_modgrp) = 1"
                 "modgrp_d (f * S_modgrp) = 0"
      by (simp_all add: * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code)
    have eps: "\<epsilon> (f * S_modgrp) = cis (pi * (b / 12 - 1 / 4))"
      by (simp add: dedekind_eps_def dedekind_sum_def is_singular_modgrp_altdef)

    have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (-1 / z + of_int b)"
      using S.prems by (subst apply_modgrp_mult) (auto simp: f algebra_simps)
    also have "\<dots> = cis (pi * b / 12) * \<eta> (-(1 / z))"
      using S.prems by (subst dedekind_eta_plus_int) auto
    also have "\<dots> = cis (pi * b / 12) * csqrt (- \<i> * z) * \<eta> z"
      using S.prems by (subst dedekind_eta_minus_one_over) auto
    also have "\<dots> = cis (pi / 4) * csqrt (- \<i> * z) * \<epsilon> (shift_modgrp b * S_modgrp) * \<eta> z"
      using eps by (auto simp: f ring_distribs simp flip: cis_divide)
    also have "csqrt (-\<i> * z) = rcis (norm (csqrt (-\<i> * z))) (Arg (csqrt (-\<i> * z)))"
      by (rule rcis_cmod_Arg [symmetric])
    also have "\<dots> = rcis (sqrt (cmod z)) (Arg (- (\<i> * z)) / 2)"
      by (simp add: norm_mult)
    also have "cis (pi / 4) * \<dots> = rcis (sqrt (norm z)) ((Arg (-\<i>*z) + pi / 2) / 2)"
      by (simp add: rcis_def cis_mult add_divide_distrib algebra_simps)
    also have "Arg (-\<i>*z) + pi / 2 = Arg z"
    proof (rule cis_Arg_unique [symmetric])
      have "cis (Arg (-\<i> * z) + pi / 2) = - (sgn (\<i> * z) * \<i>)"
        by (simp flip: cis_mult add: cis_Arg)
      also have "\<dots> = sgn z"
        by (simp add: complex_sgn_def scaleR_conv_of_real field_simps norm_mult)
      finally show "sgn z = cis (Arg (-\<i> * z) + pi / 2)" ..
    next
      show "-pi < Arg (-\<i> * z) + pi / 2" "Arg (- \<i> * z) + pi / 2 \<le> pi"
        using Arg_Re_pos[of "-\<i> * z"] S.prems by auto
    qed
    also have "rcis (sqrt (norm z)) (Arg z / 2) = rcis (norm (csqrt z)) (Arg (csqrt z))"
      by simp
    also have "\<dots> = csqrt z"
      by (rule rcis_cmod_Arg)
    finally show ?thesis
      by (simp add: f)
  next
    case sing: True
    hence "c > 0"
      unfolding a_b_c_d_def by (meson is_singular_modgrp_altdef modgrp_cd_signs)
    have "Im (1 / z) < 0"
      using S.prems Im_one_over_neg_iff by blast
    have Arg_z: "Arg z \<in> {0<..<pi}"
      using S.prems by (simp add: Arg_lt_pi)
    have Arg_z': "Arg (-\<i> * z) = -pi/2 + Arg z"
      using Arg_z by (subst Arg_times) auto
    have [simp]: "Arg (-z) = Arg z - pi"
      using Arg_z by (subst Arg_minus) auto

    show ?thesis
    proof (cases d "0 :: int" rule: linorder_cases)
      case equal
      hence *: "\<not>is_singular_modgrp (f * S_modgrp)"
        unfolding a_b_c_d_def
        by transfer (auto simp: modgrp_rel_def split: if_splits)
      define n where "n = modgrp_b (f * S_modgrp)"
      have **: "f * S_modgrp = shift_modgrp n"
        unfolding n_def using * by (rule not_singular_modgrpD)
      show ?thesis using S.prems
        by (simp add: ** dedekind_eta_plus_int)
    next
      case greater
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = b" "modgrp_b (f * S_modgrp) = -a"
                   "modgrp_c (f * S_modgrp) = d" "modgrp_d (f * S_modgrp) = -c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using greater det by auto

      have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (- (1 / z))) * \<eta> (- (1 / z))"
        using S.prems by (subst S.IH) auto
      also have "modgrp_factor f (- (1 / z)) = d - c / z"
        unfolding modgrp_factor_def by (simp add: a_b_c_d_def)
      also have "\<eta> (- (1 / z)) = csqrt (-\<i> * z) * \<eta> z"
        using S.prems by (subst dedekind_eta_minus_one_over) auto
      also have "\<epsilon> f * csqrt (d - c / z) * (csqrt (-\<i> * z) * \<eta> z) =
                 (csqrt (d - c / z) * csqrt (-\<i> * z)) * \<epsilon> f * \<eta> z"
        by (simp add: mult_ac)
      also have "csqrt (d - c / z) * csqrt (-\<i> * z) = csqrt ((d - c / z) * (-\<i> * z))"
      proof (rule csqrt_mult [symmetric])
        have "Im (of_int d - of_int c / z) = -of_int c * Im (1 / z)"
          by (simp add: Im_divide)
        hence Im: "Im (of_int d - of_int c / z) > 0"
          using \<open>Im (1 / z) < 0\<close> \<open>c > 0\<close> by (auto simp: mult_less_0_iff)
        hence Arg_pos: "Arg (of_int d - of_int c / z) > 0"
          using Arg_pos_iff by blast

        have "Arg (of_int d - of_int c / z) + Arg z \<le> 3 / 2 * pi"
        proof (cases "Re z \<ge> 0")
          case True
          have "Arg (of_int d - of_int c / z) \<le> pi"
            by (rule Arg_le_pi)
          moreover have "Arg z \<le> pi / 2"
            using Arg_Re_nonneg[of z] True by auto
          ultimately show ?thesis by simp
        next
          case False
          have "Re (of_int d - of_int c / z) = of_int d - of_int c * Re z / norm z ^ 2"
            by (simp add: Re_divide norm_complex_def)
          also have "\<dots> \<ge> 0 - 0"
            using \<open>d > 0\<close> \<open>c > 0\<close> False
            by (intro diff_mono divide_nonpos_pos mult_nonneg_nonpos) auto
          finally have "Arg (of_int d - of_int c / z) \<le> pi / 2"
            using Arg_Re_nonneg[of "of_int d - of_int c / z"] by simp
          moreover have "Arg z \<le> pi"
            by (rule Arg_le_pi)
          ultimately show ?thesis by simp
        qed
        moreover have "Arg (of_int d - of_int c / z) + Arg z > 0 + 0"
          using Arg_z by (intro add_strict_mono Arg_pos) auto
        ultimately show "Arg (of_int d - of_int c / z) + Arg (- \<i> * z) \<in> {-pi<..pi}"
          using Arg_z' by auto
      qed
      also have "(d - c / z) * (-\<i> * z) = (-\<i>) * (d * z - c)"
        using S.prems by (auto simp: field_simps)
      also have "csqrt \<dots> = csqrt (-\<i>) * csqrt (d * z - c)"
      proof (intro csqrt_mult)
        have "Arg (of_int d * z - of_int c) > 0"
          using \<open>d > 0\<close> S.prems by (subst Arg_pos_iff) auto
        moreover have "Arg (of_int d * z - of_int c) \<le> pi"
          by (rule Arg_le_pi)
        ultimately show "Arg (-\<i>) + Arg (of_int d * z - of_int c) \<in> {-pi<..pi}"
          by auto
      qed
      also have "csqrt (-\<i>) = cis (-pi / 4)"
        by (simp add: csqrt_exp_Ln cis_conv_exp)
      also have "cis (-pi / 4) * csqrt (d * z - c) * \<epsilon> f * \<eta> z =
                 \<epsilon> (f * S_modgrp) * csqrt (d * z - c) * \<eta> z"
        using \<open>d > 0\<close> sing by (subst dedekind_eps_S_right) (auto simp: a_b_c_d_def)
      also have "\<dots> = \<epsilon> (f * S_modgrp) * csqrt (modgrp_factor (f * S_modgrp) z) * \<eta> z"
        unfolding modgrp_factor_def by simp
      finally show ?thesis .
    next
      case less
      have "modgrp a b c d * S_modgrp = modgrp b (-a) d (-c)"
        unfolding shift_modgrp_code S_modgrp_code times_modgrp_code det by simp
      hence *: "f * S_modgrp = modgrp b (-a) d (-c)"
        by (simp add: a_b_c_d_def)
      have [simp]: "modgrp_a (f * S_modgrp) = -b" "modgrp_b (f * S_modgrp) = a"
                   "modgrp_c (f * S_modgrp) = -d" "modgrp_d (f * S_modgrp) = c"
        unfolding * modgrp_a_code modgrp_b_code modgrp_c_code modgrp_d_code
        using less det by auto

      have "\<eta> (apply_modgrp (f * S_modgrp) z) = \<eta> (apply_modgrp f (- (1 / z)))"
        using S.prems by (subst apply_modgrp_mult) auto
      also have "\<dots> = \<epsilon> f * csqrt (modgrp_factor f (- (1 / z))) * \<eta> (- (1 / z))"
        using S.prems by (subst S.IH) auto
      also have "modgrp_factor f (- (1 / z)) = d - c / z"
        unfolding modgrp_factor_def by (simp add: a_b_c_d_def)
      also have "\<eta> (- (1 / z)) = csqrt (-\<i> * z) * \<eta> z"
        using S.prems by (subst dedekind_eta_minus_one_over) auto
      also have "\<epsilon> f * csqrt (d - c / z) * (csqrt (-\<i> * z) * \<eta> z) =
                 (csqrt (d - c / z) * csqrt (-\<i> * z)) * \<epsilon> f * \<eta> z"
        by (simp add: mult_ac)
      also have "csqrt (-\<i> * z) = csqrt (\<i> * -z)"
        by simp
      also have "\<dots> = csqrt \<i> * csqrt (-z)"
      proof (rule csqrt_mult)
        show "Arg \<i> + Arg (- z) \<in> {- pi<..pi}"
          using Arg_z by auto
      qed
      also have "csqrt (d - c / z) * \<dots> = csqrt \<i> * (csqrt (d - c / z) * csqrt (-z))"
        by (simp add: mult_ac)
      also have "csqrt (d - c / z) * csqrt (-z) = csqrt ((d - c / z) * (-z))"
      proof (rule csqrt_mult [symmetric])
        have "Im (of_int d - of_int c / z) = of_int c * Im z / norm z ^ 2"
          by (simp add: Im_divide norm_complex_def)
        also have "\<dots> > 0"
          using S.prems \<open>c > 0\<close> by (intro mult_pos_pos divide_pos_pos) auto
        finally have "Arg (of_int d - of_int c / z) \<in> {0<..<pi}"
          using Arg_lt_pi[of "of_int d - of_int c / z"] by auto
        thus "Arg (of_int d - of_int c / z) + Arg (- z) \<in> {- pi<..pi}"
          using Arg_z by auto
      qed
      also have "(d - c / z) * (-z) = c - d * z"
        using S.prems by (simp add: field_simps)
      also have "csqrt \<i> = cis (pi / 4)"
        by (simp add: csqrt_exp_Ln complex_eq_iff cos_45 sin_45 field_simps)
      also have "cis (pi / 4) * csqrt (c - d * z) * \<epsilon> f * \<eta> z =
                 \<epsilon> (f * S_modgrp) * csqrt (c - d * z) * \<eta> z"
        using \<open>d < 0\<close> sing by (subst dedekind_eps_S_right) (auto simp: a_b_c_d_def)
      also have "\<dots> = \<epsilon> (f * S_modgrp) * csqrt (modgrp_factor (f * S_modgrp) z) * \<eta> z"
        unfolding modgrp_factor_def by simp
      finally show ?thesis .
    qed
  qed
qed


subsection \<open>Relationship to the modular discriminant \<open>\<Delta>\<close>\<close>

(* Theorem 3.3 *)
theorem modular_discr_conv_dedekind_eta:
  assumes "Im z > 0"
  shows   "modular_discr z = (2 * pi) ^ 12 * \<eta> z ^ 24"
    and   "Abs_fps ramanujan_tau = fps_X * fps_expansion euler_phi 0 ^ 24"
proof -
  define eta where "eta = mero_uhp \<eta>"
  define f where "f = \<Delta> / eta ^ 24"
  have rel [mero_uhp_rel_intros]: "mero_uhp_rel eta \<eta>"
    unfolding eta_def by mero_uhp_rel (auto intro!: meromorphic_intros)
  have eval_eta [simp]: "eval_mero_uhp eta z = \<eta> z" if "Im z > 0" for z
    by (rule mero_uhp_rel_imp_eval_mero_uhp_eq, mero_uhp_rel)
       (use that in \<open>auto intro!: analytic_intros\<close>)
  have "eta \<i> \<noteq> eval_mero_uhp 0 \<i>"
    by auto
  hence [simp]: "eta \<noteq> 0"
    by blast    

  text \<open>
    The functional equations we proved earlier imply that $\eta^{24}$ satisfies the identities
    $\eta(z+1)^{24} = \eta(z)^{24}$ and $\eta(-1/z)^{24} = z^{12} \eta(z)^{24}$.
    Therefore, it is an weakly modular form of weight 12 on the full modular group.
  \<close>
  interpret eta24: weakly_modular_form "eta ^ 24" 12 UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
  proof (rule weakly_modular_formI_generators)
    show "mero_uhp_rel (eval_mero_uhp (eta ^ 24)) (\<lambda>z. \<eta> z ^ 24)"
      by mero_uhp_rel
    show "\<eta> (z + 1) ^ 24 = \<eta> z ^ 24" if "Im z > 0" for z
      using that by (simp add: dedekind_eta_plus1 power_mult_distrib Complex.DeMoivre)
    show "\<eta> (- (1 / z)) ^ 24 = z powi 12 * \<eta> z ^ 24" if "Im z > 0" for z
      using that by (simp add: dedekind_eta_minus_one_over power_mult_distrib csqrt_power_even)
  qed auto
  
  text \<open>
    The Fourier expansion of $\eta(z)^{24}$ at $i\infty$ is, basically by definition,
    $q \cdot \prod_{n\geq 1} (1 - q^n)^{24}$.
  \<close>
  have eta24_fourier: "eta24.fourier q = q * euler_phi q ^ 24" if q: "q \<in> ball 0 1 - {0}" for q
  proof -
    define z where "z = cusp_q_inv 1 q"
    have q_eq: "q = cusp_q 1 z"
      using q by (auto simp: z_def)
    have [simp]: "Im z > 0"
      using q by (auto simp: z_def intro!: Im_cusp_q_inv_gt)
    have "eta24.fourier q = eval_mero_uhp (eta ^ 24) z"
      unfolding q_eq by (simp add: q_eq)
    also have "\<dots> = \<eta> z ^ 24"
      by simp
    also have "\<eta> z ^ 24 = exp (2 * \<i> * pi * z) * euler_phi q ^ 24"
      by (simp add: dedekind_eta_def power_mult_distrib q_eq mult_ac flip: exp_of_nat_mult)
    also have "exp (2 * \<i> * pi * z) = q"
      by (simp add: q_eq cusp_q_def mult_ac)
    finally show ?thesis .
  qed
  have ev_eta24_fourier: "eventually (\<lambda>q. eta24.fourier q = q * euler_phi q ^ 24) (at 0)"
    by (intro eventually_mono[OF eventually_at_in_open[of "ball 0 1"]] eta24_fourier) auto

  text \<open>
    In particular, this means that $\eta^{24}$ has a limit at the cusp and is therefore
    an entire modular form. Since that limit is 0, it is also a cusp form.
  \<close>
  have eta24_lim: "eta24.fourier \<midarrow>0\<rightarrow> 0"
  proof (subst tendsto_cong)
    show "(\<lambda>q. q * euler_phi q ^ 24) \<midarrow>0\<rightarrow> 0"
      by (auto intro!: tendsto_eq_intros)
  qed (use ev_eta24_fourier in auto)
  hence [simp]: "eta24.fourier 0 = 0"
    using eta24.fourier_0_aux eta24.fourier_tendsto_0_iff by blast
  have ev_eta24_fourier': "eventually (\<lambda>q. eta24.fourier q = q * euler_phi q ^ 24) (nhds 0)"
    using ev_eta24_fourier unfolding eventually_nhds_conv_at by auto

  interpret eta24: modular_form "eta ^ 24" 12 UNIV
    rewrites "modgrp_subgroup_period UNIV = Suc 0"
  proof unfold_locales
    have "mero_uhp_rel (eta ^ 24) (\<lambda>z. \<eta> z ^ 24)"
      by mero_uhp_rel
    thus "holo_uhp (eta ^ 24)"
      by (rule holo_uhp_mero_uhp_rel_transfer) (auto intro!: analytic_intros)
  qed (use eta24_lim in auto)
  have eta: "eta ^ 24 \<in> MForms[12] - {0}"
    unfolding MForms_def using eta24.modular_form_axioms by auto

  text \<open>
    It is now easy to see that the power series expansion of $\eta$ at the cusp is of the form
    $q \cdot F(q)^{24}$, where $F$ is the power series expansion of the $q$-Pochhammer symbol
    $(q; q)_\infty = \prod{k\geq 1} (1 - q^k)$ at $q = 0$.
  \<close>
  define F where "F = fps_expansion euler_phi 0"
  have euler_phi_expansion [fps_expansion_intros]: "euler_phi has_fps_expansion F"
    unfolding F_def by (intro analytic_at_imp_has_fps_expansion_0 analytic_intros) auto
  have [simp]: "F \<noteq> 0" "subdegree F = 0"
    using euler_phi_expansion has_fps_expansion_to_laurent by fastforce+
  have eta24_expansion: "eta24.fourier has_fps_expansion fps_X * F ^ 24"
  proof (subst has_fps_expansion_cong)
    show "(\<lambda>q. q * euler_phi q ^ 24) has_fps_expansion fps_X * F ^ 24"
      by (intro fps_expansion_intros)
  qed (use ev_eta24_fourier' in \<open>simp_all add: eq_commute\<close>)

  text \<open>
    From this power series expansion, we can see that the zero of $\eta^{24}$ at the cusp is
    a simply zero.
  \<close>
  with eta24_expansion have "zorder eta24.fourier 0 = 1"
    by (simp add: has_fps_expansion_zorder_0)
  hence zorder: "zorder_at_cusp (Suc 0) (eta ^ 24) = 1"
    using eta24.zorder_at_cusp_conv_fourier by force

  text \<open>
    Hence $\eta^{24}$ and $\Delta$ both have no poles and no zeros except for a simple zero
    at the cusp. Therefore, $\eta^{24} / \Delta$ is an entire modular form of weight 0 and
    therefore constant.
  \<close>
  have "eta ^ 24 / \<Delta> \<in> MForms[0]"
  proof (rule mform_intros)
    show "eta ^ 24 \<in> MForms[12]"
      using eta by (auto simp: CForms_def)
    show "\<Delta> \<in> MForms[12 - 0]"
      by (rule mform_intros) auto
  qed (use zorder in \<open>auto simp: modular_discr_nonzero complex_is_Real_iff\<close>)
  then obtain c where "eta ^ 24 / \<Delta> = const_mero_uhp c"
    using MForms_0_eq_constant by blast
  hence eq: "eta ^ 24 = const_mero_uhp c * \<Delta>"
    by (simp add: field_simps)

  text \<open>
    This also means that the power series expansion of $\Delta$ at the cusp is a constant multiple 
    of $q (q; q)_\infty$. But we also know that the power series of $\Delta$ is equal to
    $\sum_{n=1}^\infty (2\pi)^{12} \tau(n)q^n$ where $\tau$ is Ramanujan's $\tau$ function.
  \<close>
  have eq': "fps_const c * fps_modular_discr = fps_X * F ^ 24"
  proof -
    have *: "modular_discr.fourier has_laurent_expansion fps_to_fls fps_modular_discr"
      using modular_discr.has_expansion_at_cusp has_laurent_expansion_fps by simp
    have "eta24.fourier has_laurent_expansion fls_const c * fps_to_fls fps_modular_discr"
      using modular_discr.has_laurent_expansion_at_cusp_cmult_left[OF *, of c] by (simp add: eq)
    also have "\<dots> = fps_to_fls (fps_const c * fps_modular_discr)"
      by (simp add: fls_times_fps_to_fls)
    finally have "eta24.fourier has_fps_expansion fps_const c * fps_modular_discr"
      using has_fps_expansion_to_laurent modular_discr.has_expansion_at_cusp by force
    with eta24_expansion show "fps_const c * fps_modular_discr = fps_X * F ^ 24"
      using fps_expansion_unique_complex by blast
  qed

  text \<open>
    We compare the coefficients of $q^1$ in these power series expansions, which gives us
    $c = (2\pi)^{-12}$ for the constant factor.
  \<close>
  have "c * ((2 * pi) ^ 12) = fps_nth (fps_const c * fps_modular_discr) 1"
    by (simp add: fps_modular_discr_def ramanujan_tau_1)
  also have "\<dots> = fps_nth F 0 ^ 24"
    by (subst eq') (auto simp: F_def fps_nth_power_0)
  also have "fps_nth F 0 = euler_phi 0"
    using euler_phi_expansion by (metis has_fps_expansion_imp_0_eq_fps_nth_0)
  also have "\<dots> = 1"
    by simp
  finally have [simp]: "c = 1 / (2 * pi) ^ 12"
    by (simp add: field_simps)

  text \<open>
    This concludes our proof.
  \<close>
  have "fps_modular_discr = fps_const ((2 * pi) ^ 12) * (fps_X * F ^ 24)"
    by (subst eq' [symmetric]) simp
  also have "fps_modular_discr = fps_const ((2 * pi) ^ 12) * Abs_fps ramanujan_tau"
    by (simp add: fps_modular_discr_def)
  finally show "Abs_fps ramanujan_tau = fps_X * F ^ 24"
    by simp

  have "c * modular_discr z = eval_mero_uhp (const_mero_uhp c * \<Delta>) z"
    using assms by simp
  also have "\<dots> = eval_mero_uhp (eta ^ 24) z"
    by (simp only: eq)
  also have "\<dots> = \<eta> z ^ 24"
    using assms by simp
  finally show "modular_discr z = complex_of_real ((2 * pi) ^ 12) * \<eta> z ^ 24"
    by (simp add: field_simps)
qed

end
