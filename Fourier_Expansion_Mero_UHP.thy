section \<open>Expanding complex functions in terms of $q = \exp(2i\pi z)$\<close>
theory Fourier_Expansion_Mero_UHP
imports
  "HOL-Complex_Analysis.Riemann_Mapping"
  "HOL-Real_Asymp.Real_Asymp"
  Library_Extras
  Meromorphic_Upper_Half_Plane
begin

lemma has_laurent_expansion_imp_bigtheta:
  assumes F: "f has_laurent_expansion F" "F \<noteq> 0"
  defines "n \<equiv> fls_subdegree F"
  shows   "f \<in> \<Theta>[at 0](\<lambda>z. z powi n)"
proof -
  have "f \<sim>[at 0] (\<lambda>z. fls_nth F n * z powi n)"
    unfolding n_def by (rule has_laurent_expansion_imp_asymp_equiv_0) fact+
  hence "f \<in> \<Theta>[at 0](\<lambda>z. fls_nth F n * z powi n)"
    by (rule asymp_equiv_imp_bigtheta)
  also have "(\<lambda>z. fls_nth F n * z powi n) \<in> \<Theta>[at 0](\<lambda>z. z powi n)"
    using \<open>F \<noteq> 0\<close> by (auto simp: n_def)
  finally show ?thesis .
qed

lemma ln_less_iff: "x > 0 \<Longrightarrow> ln x < (y :: real) \<longleftrightarrow> x < exp y"
  by (metis exp_less_cancel_iff exp_ln)

subsection \<open>Definition of \<open>q\<close> and the cusp \<open>i\<infinity>\<close>\<close>

definition at_cusp :: "complex filter" where
  "at_cusp = filtercomap Im at_top"

lemma eventually_at_cusp:
  "eventually (\<lambda>z. Im z > c) at_cusp"
  unfolding at_cusp_def using filterlim_at_top_dense by blast

lemma eventually_at_cusp_iff:
  "(\<forall>\<^sub>F z in at_cusp. P z) \<longleftrightarrow> (\<exists>c. \<forall>z. Im z > c \<longrightarrow> P z)"
  by (simp add: at_cusp_def eventually_filtercomap_at_top_dense)

lemma eventually_at_cusp_iff':
  "(\<forall>\<^sub>F z in at_cusp. P z) \<longleftrightarrow> (\<exists>c. \<forall>z. Im z \<ge> c \<longrightarrow> P z)"
  by (simp add: at_cusp_def eventually_filtercomap_at_top_linorder)

lemma filtermap_scaleR_at_cusp:
  assumes "c > 0"
  shows   "filtermap (\<lambda>z. c *\<^sub>R z) at_cusp = at_cusp"
proof (rule antisym)
  show "filtermap (\<lambda>z. c *\<^sub>R z) at_cusp \<le> at_cusp"
  proof (rule filter_leI)
    fix P
    assume "eventually P at_cusp"
    then obtain b where b: "\<And>z. Im z > b \<Longrightarrow> P z"
      by (auto simp: eventually_at_cusp_iff)
    have "eventually (\<lambda>z. Im z > b / c) at_cusp"
      by (intro eventually_at_cusp)
    thus "eventually P (filtermap (\<lambda>z. c *\<^sub>R z) at_cusp)"
      unfolding eventually_filtermap
      by eventually_elim (use assms in \<open>auto intro!: b simp: field_simps\<close>)
  qed
next
  show "filtermap (\<lambda>z. c *\<^sub>R z) at_cusp \<ge> at_cusp"
  proof (rule filter_leI)
    fix P
    assume "eventually P (filtermap (\<lambda>z. c *\<^sub>R z) at_cusp)"
    then obtain b where b: "\<And>z. Im z > b \<Longrightarrow> P (c *\<^sub>R z)"
      by (auto simp: eventually_at_cusp_iff eventually_filtermap)
    have b': "P z" if "Im z > b * c" for z
      using b[of "z /\<^sub>R c"] that assms by (auto simp: field_simps)
    have "eventually (\<lambda>z. Im z > b * c) at_cusp"
      by (intro eventually_at_cusp)
    thus "eventually P at_cusp"
      unfolding eventually_filtermap
      by eventually_elim (use assms in \<open>auto intro!: b' simp: field_simps\<close>)
  qed
qed

lemma at_cusp_neq_bot [simp]: "at_cusp \<noteq> bot"
  unfolding at_cusp_def by (intro filtercomap_neq_bot_surj surj_Im) auto

definition cusp_q :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "cusp_q n \<tau> = exp (2 * pi * \<i> * \<tau> / n)"

interpretation cusp_q: periodic_fun_simple "cusp_q n" "of_nat n"
proof
  show "cusp_q n (z + of_nat n) = cusp_q n z" for z
    by (cases "n = 0") (simp_all add: cusp_q_def ring_distribs exp_add add_divide_distrib)
qed

lemma Ln_cusp_q:
  assumes "x \<in> Re -` {n/2<..n/2}" "n > 0"
  shows "Ln (cusp_q n x) = 2 * pi * \<i> * x / n"
unfolding cusp_q_def 
proof (rule Ln_exp)
  have "-1/2 * pi < Re x / n * pi" "Re x / n * pi \<le> 1/2 * pi"
    using assms by (auto simp: field_simps)
  thus "-pi < Im (complex_of_real (2 * pi) * \<i> * x / n)" 
    using assms(2) by (auto simp: field_simps)
  show "Im (complex_of_real (2 * pi) * \<i> * x / n) \<le> pi"
    using \<open>Re x / n * pi \<le> 1/2 * pi\<close> using assms(2) by (auto simp: field_simps)
qed

lemma cusp_q_nonzero [simp]: "cusp_q n \<tau> \<noteq> 0"
  by (auto simp: cusp_q_def)

lemma norm_cusp_q [simp]: "norm (cusp_q n z) = exp (-2 * pi * Im z / n)"
  by (simp add: cusp_q_def)

lemma cusp_q_has_field_derivative [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative f') (at z)" and n: "n > 0"
  shows   "((\<lambda>z. cusp_q n (f z)) has_field_derivative (2 * pi * \<i> * f' / n * cusp_q n (f z))) (at z)"
  unfolding cusp_q_def by (rule derivative_eq_intros refl | (use n in simp; fail))+  

lemma deriv_cusp_q [simp]: "n > 0 \<Longrightarrow> deriv (cusp_q n) z = 2 * pi * \<i> / n * cusp_q n z"
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma cusp_q_holomorphic_on [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> n > 0 \<Longrightarrow> (\<lambda>z. cusp_q n (f z)) holomorphic_on A"
  unfolding cusp_q_def by (intro holomorphic_intros) auto

lemma cusp_q_analytic_on [analytic_intros]:
  "f analytic_on A \<Longrightarrow> n > 0 \<Longrightarrow> (\<lambda>z. cusp_q n (f z)) analytic_on A"
  unfolding cusp_q_def by (intro analytic_intros) auto

lemma cusp_q_continuous_on [continuous_intros]:
  "continuous_on A f \<Longrightarrow> n > 0 \<Longrightarrow> continuous_on A (\<lambda>z. cusp_q n (f z))"
  unfolding cusp_q_def by (intro continuous_intros) auto

lemma cusp_q_continuous [continuous_intros]:
  "continuous F f \<Longrightarrow> n > 0 \<Longrightarrow> continuous F (\<lambda>z. cusp_q n (f z))"
  unfolding cusp_q_def by (auto intro!: continuous_intros simp: divide_inverse)

lemma cusp_q_tendsto [tendsto_intros]:
  "(f \<longlongrightarrow> x) F \<Longrightarrow> n > 0 \<Longrightarrow> ((\<lambda>z. cusp_q n (f z)) \<longlongrightarrow> cusp_q n x) F"
  unfolding cusp_q_def by (intro tendsto_intros) auto

lemma cusp_q_eq_cusp_qE:
  assumes "cusp_q m \<tau> = cusp_q m \<tau>'" "m > 0"
  obtains n where "\<tau>' = \<tau> + of_int n * of_nat m"
proof -
  from assms obtain n where "2 * pi * \<i> * \<tau> / m = 2 * pi * \<i> * \<tau>' / m + real_of_int (2 * n) * pi * \<i>"
    using assms unfolding cusp_q_def exp_eq by blast
  also have "\<dots> = 2 * pi * \<i> * (\<tau>' / m + of_int n)"
    by (simp add: algebra_simps)
  also have "2 * pi * \<i> * \<tau> / m = 2 * pi * \<i> * (\<tau> / m)"
    by simp
  finally have "\<tau> / m = \<tau>' / m + of_int n"
    by (subst (asm) mult_cancel_left) auto
  hence "\<tau> = \<tau>' + of_int n * of_nat m"
    using \<open>m > 0\<close> by (metis divide_add_eq_iff divide_cancel_right of_nat_eq_0_iff rel_simps(70))
  thus ?thesis
    by (intro that[of "-n"]) auto
qed

lemma cusp_q_inj_on_standard:
  assumes n: "n > 0"
  shows "inj_on (cusp_q n) (Re -` {-n/2..<n/2})"
  unfolding inj_on_def
proof safe+
  fix x y::complex
  assume eq: "cusp_q n x = cusp_q n y" 
      and xRe: "Re x \<in> {- real n/2..<real n/2}" and yRe:"Re y \<in> {- real n/2..<real n/2}"
  obtain rx ix where x:"x=Complex rx ix" by (meson complex.exhaust_sel)
  obtain ry iy where y:"y=Complex ry iy" by (meson complex.exhaust_sel)
  define pp where "pp= 2*pi"
  have rxry:"rx/n\<in>{-1/2..<1/2}" "ry/n\<in>{-1/2..<1/2}" 
    using xRe yRe x y n by (auto simp: field_simps)

  define prx where "prx = pp*rx / n"
  define pry where "pry = pp*ry / n"

  have coseq:"exp (- (pp * ix / n)) * cos prx 
        = exp (- (pp * iy / n)) * cos pry"
  proof -
    have "Re (cusp_q n x) = Re (cusp_q n y)"
      using eq by simp
    then show ?thesis
      unfolding x y cusp_q_def Re_exp Im_exp pp_def prx_def pry_def using assms
      by simp 
  qed
  moreover have sineq:"exp (- (pp * ix / n)) * sin prx 
        = exp (- (pp * iy / n)) * sin pry"
  proof -
    have "Im (cusp_q n x) = Im (cusp_q n y)"
      using eq by simp
    then show ?thesis
      unfolding x y cusp_q_def Re_exp Im_exp pp_def prx_def pry_def
      by simp
  qed
  ultimately have "(exp (- (pp * ix / n)) * sin (prx))
    / (exp (- (pp * ix / n)) * cos (prx))
    = (exp (- (pp * iy / n)) * sin (pry))
    / (exp (- (pp * iy / n)) * cos (pry))"
    by auto
  then have teq:"tan prx  = tan pry"
    apply (subst (asm) (1 2) mult_divide_mult_cancel_left)
    unfolding tan_def by auto

  have sgn_eq_cos:"sgn (cos (prx)) = sgn (cos (pry))" 
  proof -
    have "sgn (exp (- (pp * ix / n)) * cos prx) 
        = sgn (exp (- (pp * iy / n)) * cos pry)"
      using coseq by simp
    then show ?thesis by (simp add:sgn_mult)
  qed
  have sgn_eq_sin:"sgn (sin (prx)) = sgn (sin (pry))" 
  proof -
    have "sgn (exp (- (pp * ix / n)) * sin prx) 
        = sgn (exp (- (pp * iy / n)) * sin pry)"
      using sineq by simp
    then show ?thesis by (simp add:sgn_mult)
  qed
  
  have "prx=pry" if "tan prx = 0"
  proof -
    define pi2 where "pi2 = pi /2"
    have [simp]: "cos pi2 = 0" "cos (-pi2) = 0"
      "sin pi2 = 1" "sin (-pi2) = -1"
      unfolding pi2_def by auto
    have "prx\<in>{-pi,-pi2,0,pi2}"
    proof -
      from tan_eq_0_Ex[OF that]
      obtain k0 where k0:"prx = real_of_int k0 / 2 * pi"
        by auto
      then have "rx / n = real_of_int k0 / 4" 
        unfolding pp_def prx_def using n by (auto simp: field_simps)
      with rxry have "k0\<in>{-2,-1,0,1}"
        by auto
      then show ?thesis using k0 pi2_def by auto
    qed
    moreover have "pry\<in>{-pi,-pi2,0,pi2}" 
    proof -
      from tan_eq_0_Ex that teq
      obtain k0 where k0:"pry = real_of_int k0 / 2 * pi"
        by auto
      then have "ry / n = real_of_int k0/4" 
        unfolding pp_def pry_def using n by (auto simp: field_simps)
      with rxry have "k0\<in>{-2,-1,0,1}"
        by auto
      then show ?thesis using k0 pi2_def by auto
    qed
    moreover note sgn_eq_cos sgn_eq_sin
    ultimately show "prx=pry" by auto
  qed
  moreover have "prx=pry" if "tan prx \<noteq> 0"
  proof -
    from tan_eq[OF teq that]
    obtain k0 where k0:"prx = pry + real_of_int k0 * pi"
      by auto
    then have "pi * (2 * rx / n) = pi* (2 * ry / n + real_of_int k0)"
      unfolding pp_def prx_def pry_def by (auto simp: algebra_simps)
    then have "real_of_int k0 = 2 * ((rx - ry) / n)" 
      by (subst diff_divide_distrib, subst (asm) mult_left_cancel) (use n in auto)
    also have "... \<in> {-2<..<2}"
      using rxry using n by (auto simp: field_simps)
    finally have "real_of_int k0 \<in> {- 2<..<2}" by simp
    then have "k0 \<in> {-1,0,1}" by auto
    then have "prx=pry-pi \<or> prx = pry \<or> prx = pry+pi"
      using k0 by auto
    moreover have False if "prx=pry-pi \<or> prx = pry+pi"
    proof -
      have "cos prx = - cos pry"
        using that by auto
      moreover note sgn_eq_cos
      ultimately have "cos prx = 0" 
        by (simp add: sgn_zero_iff)
      then have "tan prx = 0" unfolding tan_def by auto
      then show False 
        using \<open>tan prx \<noteq> 0\<close> unfolding prx_def by auto
    qed
    ultimately show "prx = pry" by auto
  qed
  ultimately have "prx=pry" by auto
  then have "rx = ry" unfolding prx_def pry_def pp_def using n by auto
  moreover have "ix = iy"
  proof - 
    have "cos prx \<noteq>0 \<or>  sin prx\<noteq>0"
      using sin_zero_norm_cos_one by force 
    then have "exp (- (pp * ix))  = exp (- (pp * iy))"
      using coseq sineq \<open>prx = pry\<close> n by auto
    then show "ix= iy" unfolding pp_def by auto
  qed
  ultimately show "x=y" unfolding x y by auto
qed

lemma filterlim_cusp_q_at_cusp' [tendsto_intros]:
  assumes n: "n > 0"
  shows   "filterlim (cusp_q n) (nhds 0) at_cusp"
proof -
  have "((\<lambda>z. exp (- (2 * pi * Im z) / n)) \<longlongrightarrow> 0) at_cusp"
    unfolding at_cusp_def 
    by (rule filterlim_compose[OF _ filterlim_filtercomap]) (use n in real_asymp)
  hence "filterlim (\<lambda>z. norm (cusp_q n z)) (nhds 0) at_cusp"
    by (simp add: cusp_q_def)
  thus ?thesis
    using tendsto_norm_zero_iff by blast
qed

lemma filterlim_cusp_q_at_cusp [tendsto_intros]: "n > 0 \<Longrightarrow> filterlim (cusp_q n) (at 0) at_cusp"
  using filterlim_cusp_q_at_cusp' by (auto simp: filterlim_at)  

lemma eventually_cusp_q_neq:
  assumes n: "n > 0"
  shows "eventually (\<lambda>w. cusp_q n w \<noteq> cusp_q n z) (at z)"
proof -
  have "eventually (\<lambda>w. w \<in> ball z 1 - {z}) (at z)"
    by (intro eventually_at_in_open) auto
  thus ?thesis
  proof eventually_elim
    case (elim w)
    show ?case
    proof
      assume "cusp_q n w = cusp_q n z"
      then obtain m where eq: "z = w + of_int m * of_nat n"
        using n by (elim cusp_q_eq_cusp_qE)
      with elim have "real_of_int (\<bar>m\<bar> * int n) < 1"
        by (simp add: dist_norm norm_mult)
      hence "\<bar>m\<bar> * int n < 1"
        by linarith
      with n have "m = 0"
        by (metis add_0 mult_pos_pos not_less of_nat_0_less_iff zero_less_abs_iff zless_imp_add1_zle)
      thus False
        using elim eq by simp
    qed
  qed
qed


lemma inj_on_cusp_q:
  assumes n: "n > 0"
  shows "inj_on (cusp_q n) (ball z (1/2))"
proof
  fix x y assume xy: "x \<in> ball z (1/2)" "y \<in> ball z (1/2)" "cusp_q n x = cusp_q n y"
  from xy have "dist x z < 1 / 2" "dist y z < 1 / 2"
    by (auto simp: dist_commute)
  hence "dist x y < 1 / 2 + 1 / 2"
    using dist_triangle_less_add by blast
  moreover obtain m where m: "y = x + of_int m * of_nat n"
    by (rule cusp_q_eq_cusp_qE[OF xy(3) n]) auto
  ultimately have "real_of_int (\<bar>m\<bar> * int n) < 1"
    by (auto simp: dist_norm norm_mult)
  hence "\<bar>m\<bar> * int n < 1"
    by linarith
  with n have "m = 0"
    by (metis add_0 mult_pos_pos not_less of_nat_0_less_iff zero_less_abs_iff zless_imp_add1_zle)
  thus "x = y"
    using m by simp
qed

lemma filtermap_cusp_q_nhds:
  assumes n: "n > 0"
  shows "filtermap (cusp_q n) (nhds z) = nhds (cusp_q n z)"
proof (rule filtermap_nhds_open_map')
  show "open (ball z (1 / 2))" "z \<in> ball z (1 / 2)" "isCont (cusp_q n) z"
    using n by (auto intro!: continuous_intros)
  show "open (cusp_q n ` S)" if "open S" "S \<subseteq> ball z (1 / 2)" for S
  proof (rule open_mapping_thm3)
    show "inj_on (cusp_q n) S"
      using that by (intro inj_on_subset[OF inj_on_cusp_q] n)
  qed (use that n in \<open>auto intro!: holomorphic_intros\<close>)
qed

lemma filtermap_cusp_q_at:
  assumes n: "n > 0"
  shows "filtermap (cusp_q n) (at z) = at (cusp_q n z)"
  using filtermap_cusp_q_nhds
proof (rule filtermap_nhds_eq_imp_filtermap_at_eq)
  show "eventually (\<lambda>x. cusp_q n x = cusp_q n z \<longrightarrow> x = z) (at z)"
    using eventually_cusp_q_neq[OF n, of z] by eventually_elim (use n in auto)
qed fact+

lemma is_pole_cusp_q_iff:
  assumes n: "n > 0"
  shows "is_pole f (cusp_q n x) \<longleftrightarrow> is_pole (f o cusp_q n) x"
proof -
  have "filtermap f (at (cusp_q n x)) 
          = filtermap f (filtermap (cusp_q n) (at x)) "
    unfolding filtermap_cusp_q_at[OF n] by simp
  also have "... = filtermap (f \<circ> cusp_q n) (at x)"
    unfolding filtermap_filtermap unfolding comp_def by simp
  finally show ?thesis unfolding is_pole_def filterlim_def by simp
qed

definition cusp_q_inv :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "cusp_q_inv n q = ln q / (2 * pi * \<i> / n)"

lemma Im_cusp_q_inv: "q \<noteq> 0 \<Longrightarrow> n > 0 \<Longrightarrow> Im (cusp_q_inv n q) = -n * ln (norm q) / (2 * pi)"
  by (simp add: cusp_q_inv_def Im_divide power2_eq_square)

lemma Im_cusp_q_inv_gt:
  assumes "norm q < exp (-2 * pi * c / n)" "q \<noteq> 0" "n > 0"
  shows   "Im (cusp_q_inv n q) > c"
proof -
  have "-Im (cusp_q_inv n q) = n * ln (norm q) / (2 * pi)"
    using assms by (subst Im_cusp_q_inv) auto
  also have "ln (norm q) < ln (exp (-2 * pi * c / n))"
    by (subst ln_less_cancel_iff) (use assms in auto)
  hence "n * ln (norm q) / (2 * pi) < n * ln (exp (-2 * pi * c / n)) / (2 * pi)"
    using \<open>n > 0\<close> by (intro mult_strict_left_mono divide_strict_right_mono) auto
  also have "\<dots> = -c"
    using \<open>n > 0\<close> by simp
  finally show ?thesis
    by simp
qed

lemma cusp_q_cusp_q_inv [simp]: "q \<noteq> 0 \<Longrightarrow> n > 0 \<Longrightarrow> cusp_q n (cusp_q_inv n q) = q"
  by (simp add: cusp_q_def cusp_q_inv_def)

lemma cusp_q_inv_cusp_q:
  assumes "m > 0"
  shows "\<exists>n. cusp_q_inv m (cusp_q m \<tau>) = \<tau> + of_int n * of_nat m"
proof
  show "cusp_q_inv m (cusp_q m \<tau>) =
          \<tau> + of_int (-unwinding (complex_of_real (2 * pi) * \<i> * \<tau> / m)) * of_nat m"
    using unwinding[of "2 * pi * \<i> * \<tau> / m"] assms
    by (simp add: cusp_q_inv_def cusp_q_def field_simps)
qed

lemma filterlim_norm_at_0: "filterlim norm (at_right 0) (at 0)"
  unfolding filterlim_at
  by (auto simp: eventually_at tendsto_norm_zero_iff intro: exI[of _ 1])

lemma filterlim_cusp_q_inv_at_0:
  assumes n: "n > 0"
  shows "filterlim (cusp_q_inv n) at_cusp (at 0)"
proof -
  have "filterlim (\<lambda>q. -n * ln (norm q) / (2 * pi)) at_top (at 0)"
    by (rule filterlim_compose[OF _ filterlim_norm_at_0]) (use n in real_asymp)
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. -n * ln (norm q) / (2 * pi) = Im (cusp_q_inv n q)) (at 0)"
    by eventually_elim (use n in \<open>simp add: Im_cusp_q_inv\<close>)
  hence "filterlim (\<lambda>q::complex. -n * ln (norm q) / (2 * pi)) at_top (at 0) \<longleftrightarrow>
         filterlim (\<lambda>q. Im (cusp_q_inv n q)) at_top (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    by (simp add: at_cusp_def filterlim_filtercomap_iff o_def)
qed

lemma at_cusp_filtermap:
  assumes "n > 0"
  shows   "filtermap (cusp_q n) at_cusp = at 0"
proof (rule filtermap_fun_inverse[OF  filterlim_cusp_q_inv_at_0 filterlim_cusp_q_at_cusp])
  have "eventually (\<lambda>x. x \<noteq> 0) (at (0 :: complex))"
    by (rule eventually_neq_at_within)
  thus "\<forall>\<^sub>F x in at 0. cusp_q n (cusp_q_inv n x) = x"
    by eventually_elim (use assms in auto)
qed fact+

lemma eventually_at_cusp_cusp_q:
  assumes n: "n > 0"
  shows "eventually P (at 0) = (\<forall>\<^sub>F x in at_cusp. P (cusp_q n x))"
proof -
  have "(\<forall>\<^sub>F x in at_cusp. P (cusp_q n x)) \<longleftrightarrow> (\<forall>\<^sub>F x in filtermap (cusp_q n) at_cusp. P x)"
    by (simp add: eventually_filtermap)
  also have "\<dots> \<longleftrightarrow> eventually P (at 0)"
    by (simp add: at_cusp_filtermap n)
  finally show ?thesis ..
qed

lemma cusp_q_inv_tendsto:
  assumes "x \<in> Re -` {real n / 2<..real n / 2}" "n > 0"
  shows "cusp_q_inv n \<midarrow>cusp_q n x\<rightarrow> x"
proof -
  obtain rx ix where x:"x = Complex rx ix" 
    using complex.exhaust_sel by blast
  have "Re (cusp_q n x) > 0" if "Im (cusp_q n x) = 0" 
  proof -
    have "sin (2 * pi * rx / n) = 0" 
      using that unfolding cusp_q_def x Im_exp Re_exp by simp
    then obtain k where "pi * (2 * rx / n) = pi * real_of_int k"
      unfolding sin_zero_iff_int2 by (auto simp: algebra_simps)
    hence k: "2 * rx / n = real_of_int k"
      using mult_cancel_left pi_neq_zero by blast
    moreover have "2*rx/n \<in> {-1<..<1}"
      using assms unfolding x by simp
    ultimately have "k=0" by auto
    then have "rx=0" using k \<open>n > 0\<close> by auto
    then show ?thesis unfolding cusp_q_def x
      using Re_exp by simp
  qed
  then have "cusp_q n x \<notin> \<real>\<^sub>\<le>\<^sub>0" 
    unfolding complex_nonpos_Reals_iff
    unfolding Im_exp Re_exp cusp_q_def
    by (auto simp add: complex_nonpos_Reals_iff)
  moreover have "Ln (cusp_q n x) / (2 * complex_of_real pi * \<i> / n) = x" 
    apply (subst Ln_cusp_q)
    using assms by (auto simp: field_simps)
  ultimately show "cusp_q_inv n \<midarrow>cusp_q n x\<rightarrow> x"
    unfolding cusp_q_inv_def by (auto intro!: tendsto_eq_intros )
qed

lemma cusp_q_inv_cusp_q_Re:
  assumes "x \<in> Re -` {real n / 2<..real n / 2}" "n > 0"
  shows "cusp_q_inv n (cusp_q n x) = x"
proof -
  have "- pi < Im (complex_of_real (2 * pi) * \<i> * x / n)"
  proof -
    have "pi* (-1/2) < pi * (Re x / n)" 
      apply (rule mult_strict_left_mono)
      using assms by auto
    then show ?thesis by auto
  qed
  moreover have "Im (complex_of_real (2 * pi) * \<i> * x / n) \<le> pi"
    using assms by auto
  ultimately show ?thesis using assms(2)
    unfolding cusp_q_def cusp_q_inv_def
    by (subst Ln_exp) auto
qed


definition eval_mero_uhp_at_cusp :: "mero_uhp \<Rightarrow> complex" where
  "eval_mero_uhp_at_cusp f = (if \<exists>L. (f \<longlongrightarrow> L) at_cusp then Lim at_cusp f else 0)"

definition zorder_at_cusp :: "nat \<Rightarrow> mero_uhp \<Rightarrow> int" where
  "zorder_at_cusp period f =
     (if period = 0 \<or> f = 0 then 0 else (THE n. eval_mero_uhp f \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q period z powi n)))"

lemma zorder_at_cusp_0 [simp]: "zorder_at_cusp period 0 = 0"
  by (auto simp: zorder_at_cusp_def)

lemma exp_power_int: "exp z powi n = exp (z * of_int n)"
  for z :: "'a::{real_normed_field,banach}"
  by (auto simp: power_int_def field_simps exp_minus simp flip: exp_of_nat_mult) 

lemma zorder_at_cusp_unique:
  assumes "k > 0"
  shows   "\<exists>\<^sub>\<le>\<^sub>1 n. f \<in> \<Theta>[at_cusp](\<lambda>x. cusp_q k x powi n)" (is "Uniq ?P")
proof
  fix m n assume mn: "?P m" "?P n"
  have lim: "filterlim (\<lambda>x. of_real x * \<i>) at_cusp at_top"
    by (simp add: at_cusp_def filterlim_filtercomap_iff o_def filterlim_ident)
  from mn have "(\<lambda>z. cusp_q k z powi m) \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q k z powi n)"
    using landau_theta.trans bigtheta_sym by metis
  hence "(\<lambda>x. cusp_q k (of_real x * \<i>) powi m) \<in> \<Theta>(\<lambda>x. cusp_q k (of_real x * \<i>) powi n)"
    using lim by (rule landau_theta.compose)
  hence "(\<lambda>x. exp (- (2 * pi * x * m / k))) \<in> \<Theta>(\<lambda>x. exp (- (2 * pi * x * n / k)))"
    by (subst (asm) landau_theta.norm_iff [symmetric], simp only: norm_power_int)
       (simp_all add: exp_power_int)
  thus "m = n"
  proof (induction m n rule: linorder_wlog)
    case (le m n)
    let ?f = "\<lambda>n z. exp ((2 * pi * z * n / k))"
    show "m = n"
    proof (rule ccontr)
      assume "m \<noteq> n"
      with le.hyps have "m < n"
        by auto
      have "(\<lambda>_. 1) \<in> o(\<lambda>x. exp (2 * pi * x / real k * real_of_int (n - m)))"
        using \<open>k > 0\<close> \<open>m < n\<close> by real_asymp
      also {
        have "(\<lambda>x. exp ((2 * pi * x * n / k) - (2 * pi * x * m / k))) \<in> \<Theta>(\<lambda>x. 1)"
          using landau_theta.mult[OF le.prems bigtheta_refl[of "?f n"]]
          by (simp add: exp_minus exp_diff field_simps)
        also have "(\<lambda>x. (2 * pi * x * n / k) - (2 * pi * x * m / k)) =
                   (\<lambda>x. 2 * pi * x / k * (n - m))"
          using \<open>k > 0\<close> by (auto simp: field_simps fun_eq_iff)
        finally have "(\<lambda>x. exp (2 * pi * x / real k * real_of_int (n - m))) \<in> \<Theta>(\<lambda>x. 1)" .
      }
      finally show False
        by (simp add: landau_o.small_refl_iff)
    qed
  qed (simp add: bigtheta_sym eq_commute)
qed 

lemma zorder_at_cusp_eqI:
  assumes "eval_mero_uhp f \<in> \<Theta>[at_cusp](\<lambda>x. cusp_q k x powi n)" "k > 0"
  shows   "zorder_at_cusp k f = n"
proof -
  have [simp]: "f \<noteq> 0"
    using assms by auto
  have "zorder_at_cusp k f = (THE n. eval_mero_uhp f \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q k z powi n))"
    using assms by (simp add: zorder_at_cusp_def)
  also have "(THE n. eval_mero_uhp f \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q k z powi n)) = n"
    using zorder_at_cusp_unique assms(1) by (rule the1_equality') fact
  finally show ?thesis .
qed  

abbreviation "zorder_mero_uhp f \<equiv> zorder (eval_mero_uhp f)"



subsection \<open>Expansion in terms of \<open>q\<close>\<close>

text \<open>
  Let \<open>f(\<tau>)\<close> be a holomorphic function on the halfplane $\{\tau \mid \text{Im}(\tau) > c\}$
  with period 1. The variable change \<open>q = 2\<pi>\<i>\<tau>\<close> gives us a function \<open>f(q)\<close> that is holomorphic
  on a punctured disc of radius $e^{-2\pi c}$ around 0. The point \<open>q = 0\<close> corresponds to \<open>\<tau> = \<i>\<infinity>\<close>.
  Thus, this function \<open>f(q)\<close> can be viewed as the expansion of \<open>f(\<tau>)\<close> at the point \<open>\<tau> = \<i>\<infinity>\<close> (also
  called the ``cusp'').
\<close>

locale fourier_expansion = 
  fixes f :: mero_uhp and period :: nat
  assumes period_pos [intro]: "period > 0"
  assumes invariant_compose_shift_period: "compose_modgrp_mero_uhp f (shift_modgrp period) = f"
begin

sublocale periodic_fun_simple "eval_mero_uhp f" "of_nat period"
proof
  fix z :: complex
  show "eval_mero_uhp f (z + of_nat period) = eval_mero_uhp f z"
  proof (cases "Im z > 0")
    case True
    have "eval_mero_uhp f (z + of_nat period) =
          eval_mero_uhp (compose_modgrp_mero_uhp f (shift_modgrp period)) z"
      using True by simp
    also have "compose_modgrp_mero_uhp f (shift_modgrp period) = f"
      by (rule invariant_compose_shift_period)
    finally show ?thesis .
  qed (auto simp: eval_mero_uhp_outside)
qed

lemma invariant_compose_shift [simp]:
  assumes "period dvd n"
  shows   "compose_modgrp_mero_uhp f (shift_modgrp n) = f"
proof (rule mero_uhp_eqI)
  from assms obtain k where k: "n = period * k"
    by (elim dvdE)
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
    by (intro eventually_in_cosparse open_halfspace_Im_gt) auto
  thus "eventually (\<lambda>z. compose_modgrp_mero_uhp f (shift_modgrp n) z = f z) (cosparse \<H>)"
    by eventually_elim (auto simp: k plus_of_nat mult.commute)
qed

(* TODO: better name? note that in practicse this will be used as e.g. "Klein_J.of_q" *)
text \<open>
  We define the expansion around the cusp in such a way that if the singularity at \<open>q = 0\<close> is
  removable, it is removed automatically.
\<close>
definition fourier :: "complex \<Rightarrow> complex" where
  "fourier q =
     (if q = 0 then if \<exists>L. (f \<longlongrightarrow> L) at_cusp then Lim at_cusp f else 0
      else f (cusp_q_inv period q))"

lemma fourier_nz_eq: "q \<noteq> 0 \<Longrightarrow> fourier q = f (cusp_q_inv period q)"
  by (simp add: fourier_def)

lemma fourier_0_aux:
  assumes "(f \<longlongrightarrow> y) at_cusp"
  shows   "fourier 0 = y"
proof -
  have "Lim at_cusp f = y"
    using assms by (intro tendsto_Lim) auto
  thus ?thesis
    using assms by (auto simp: fourier_def)
qed

lemma isCont_0_aux:
  assumes "(f \<longlongrightarrow> y) at_cusp"
  shows   "isCont fourier 0"
proof -
  have "((\<lambda>q. f (cusp_q_inv period q)) \<longlongrightarrow> y) (at 0)"
    by (rule filterlim_compose[OF assms filterlim_cusp_q_inv_at_0]) auto
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. f (cusp_q_inv period q) = fourier q) (at 0)"
    by eventually_elim (auto simp: fourier_def)
  hence "((\<lambda>q. f (cusp_q_inv period q)) \<longlongrightarrow> y) (at 0) \<longleftrightarrow> (fourier \<longlongrightarrow> y) (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    using assms by (simp add: isCont_def fourier_0_aux)
qed

lemma fourier_cusp_q [simp]: "fourier (cusp_q period \<tau>) = f \<tau>"
proof -
  obtain n where n: "cusp_q_inv period (cusp_q period \<tau>) = \<tau> + of_int n * of_nat period"
    using cusp_q_inv_cusp_q by blast
  show ?thesis
    by (simp add: fourier_def n plus_of_int)
qed

lemma fourier_tendsto_0_iff: "fourier \<midarrow>0\<rightarrow> y \<longleftrightarrow> (f \<longlongrightarrow> y) at_cusp"
proof
  assume "(f \<longlongrightarrow> y) at_cusp"
  thus "fourier \<midarrow>0\<rightarrow> y"
    using continuous_within isCont_0_aux fourier_0_aux by blast
next
  assume *: "fourier \<midarrow>0\<rightarrow> y"
  have "((\<lambda>z. fourier (cusp_q period z)) \<longlongrightarrow> y) at_cusp"
    by (rule filterlim_compose[OF * filterlim_cusp_q_at_cusp]) auto
  also have "(\<lambda>z. fourier (cusp_q period z)) = f"
    by simp
  finally show "(f \<longlongrightarrow> y) at_cusp" .
qed

lemma fourier_is_pole_0_iff:
  "is_pole fourier 0 \<longleftrightarrow> (LIM x at_cusp. f x :> at_infinity)" 
proof -
  have "is_pole fourier 0 \<longleftrightarrow> (LIM q at 0. f (cusp_q_inv period q) :> at_infinity)"
    unfolding is_pole_def fourier_def
    by (rule filterlim_cong) (auto simp add: linordered_field_no_ub eventually_at)
  also have "... \<longleftrightarrow> (LIM x at_cusp. f x :> at_infinity)"
  proof
    assume "LIM q at 0. f (cusp_q_inv period q) :> at_infinity"
    from filterlim_compose[OF this filterlim_cusp_q_at_cusp, of period] 
    have "LIM x at_cusp. f (cusp_q_inv period (cusp_q period x)) :> at_infinity"
      using period_pos by simp
    then show "filterlim f at_infinity at_cusp"
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in at_cusp. f (cusp_q_inv period (cusp_q period x)) = f x" using period_pos
        by (smt (verit, ccfv_SIG) cusp_q_nonzero eventuallyI fourier_cusp_q fourier_nz_eq)
    qed auto
  next
    assume "filterlim f at_infinity at_cusp "
    from filterlim_compose[OF this filterlim_cusp_q_inv_at_0, of period]
    show "LIM x at 0. f (cusp_q_inv period x) :> at_infinity"
      using period_pos by simp
  qed
  finally show ?thesis .
qed

lemma fourier_is_pole_cusp_q_iff: "is_pole fourier (cusp_q period z) \<longleftrightarrow> is_pole f z"
proof -
  have "is_pole f z \<longleftrightarrow> is_pole (fourier \<circ> cusp_q period) z"
    by (rule is_pole_cong) simp_all
  also have "\<dots> \<longleftrightarrow> is_pole fourier (cusp_q period z)"
    by (rule is_pole_compose_iff) (simp_all add: filtermap_cusp_q_at period_pos)
  finally show ?thesis ..
qed

lemma has_field_derivative_fourier:
  assumes "\<not>is_pole (eval_mero_uhp f) z" "Im z > 0"
  assumes q: "q = cusp_q period z"
  defines "f' \<equiv> eval_mero_uhp (deriv_mero_uhp f) z"
  shows   "(fourier has_field_derivative
              f' * period / (of_real (2 * pi) * \<i> * q)) (at q within A)"
proof -
  have [simp]: "q \<noteq> 0"
    using q by auto
  have "open (-{0 :: complex})"
    by (auto intro: open_halfspace_Im_gt)
  then obtain r where r: "r > 0" "ball q r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>q \<noteq> 0\<close> by blast
  have "simply_connected (ball q r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball q r" "\<forall>q\<in>ball q r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
      where myln_holo: "myln holomorphic_on ball q r" and "\<And>q'. q' \<in> ball q r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball q r" for q'
    using that by metis

  have [derivative_intros]: "(myln has_field_derivative 1 / q) (at q)"
    by (rule has_field_derivative_complex_logarithm[where A = "ball q r"])
       (use myln_holo exp_myln \<open>r > 0\<close> in auto)

  have "((f \<circ> (\<lambda>q. of_nat period * myln q / (of_real (2 * pi) * \<i>))) has_field_derivative 
           f' * (of_nat period / (of_real (2 * pi) * \<i> * q))) (at q)"
  proof (rule DERIV_chain)
    define z' where "z' = of_nat period * myln q / (complex_of_real (2 * pi) * \<i>)"
    have "cusp_q period z = cusp_q period z'"
      using exp_myln[of q] q r(1) by (simp add: z'_def cusp_q_def)
    then obtain n where n: "z' = z + of_int n * of_nat period"
      using cusp_q_eq_cusp_qE period_pos by blast

    have "((f \<circ> (\<lambda>w. w + z - z')) has_field_derivative f' * 1) (at z')"
      unfolding f'_def using assms by (intro DERIV_chain) (auto intro!: derivative_eq_intros)
    also have "(\<lambda>w. w + z - z') = (\<lambda>w. w - of_int n * of_nat period)"
      using n by (auto simp: fun_eq_iff)
    also have "(f \<circ> (\<lambda>w. w - of_int n * of_nat period) has_field_derivative f' * 1) (at z') \<longleftrightarrow>
               (f has_field_derivative f') (at z')"
      by (intro DERIV_cong_ev always_eventually) (auto simp: minus_of_int)
    finally show "(f has_field_derivative f') (at z')"
      by simp
  next
    show "((\<lambda>q. of_nat period * myln q / (complex_of_real (2 * pi) * \<i>)) 
            has_field_derivative (of_nat period / (2 * pi * \<i> * q))) (at q)"
      by (auto intro!: derivative_eq_intros)
  qed

  also have "?this \<longleftrightarrow> (fourier has_field_derivative f' * period / (of_real (2 * pi) * \<i> * q)) (at q)"
  proof (intro DERIV_cong_ev)
    have "eventually (\<lambda>w. w \<in> ball q r - {0}) (nhds q)"
      using assms \<open>r > 0\<close> by (intro eventually_nhds_in_open) auto
    thus "\<forall>\<^sub>F x in nhds q. (eval_mero_uhp f \<circ> (\<lambda>q. of_nat period * myln q / (of_real (2 * pi) * \<i>))) x =
                          fourier x"
    proof eventually_elim
      case (elim q')
      define z' where "z' = period * myln q' / (2 * complex_of_real pi * \<i>)"
      have "cusp_q period z' = q'"
        using elim r period_pos by (simp add: z'_def exp_myln cusp_q_def)
      hence "cusp_q period (cusp_q_inv period q') = cusp_q period z'"
        using elim period_pos by simp
      then obtain n where n: "z' = cusp_q_inv period q' + of_int n * of_nat period"
        using cusp_q_eq_cusp_qE[of period "cusp_q_inv period q'" z'] period_pos by blast

      have "(f \<circ> (\<lambda>q. of_nat period * myln q / (complex_of_real (2 * pi) * \<i>))) q' = f z'"
        using n by (simp add: z'_def cusp_q_inv_def)
      also have "\<dots> = fourier q'"
        using elim by (simp add: plus_of_int n fourier_def)
      finally show ?case .
    qed
  qed auto
  finally show ?thesis 
    using has_field_derivative_at_within by blast
qed

definition fourier_poles :: "complex set"
  where "fourier_poles = cusp_q period ` {z. 0 < Im z \<and> is_pole (eval_mero_uhp f) z}"

lemma zero_not_in_fourier_poles [simp]: "0 \<notin> fourier_poles"
  by (auto simp: fourier_poles_def)
  
lemma is_pole_cusp_q_inv_iff:
  assumes "q \<in> ball 0 1 - {0}"
  shows   "is_pole f (cusp_q_inv period q) \<longleftrightarrow> q \<in> fourier_poles"
proof
  assume "is_pole f (cusp_q_inv period q)"
  thus "q \<in> fourier_poles"
    using assms period_pos unfolding fourier_poles_def 
    by (auto simp: image_def intro!: exI[of _ "cusp_q_inv period q"] Im_cusp_q_inv_gt)
next
  assume "q \<in> fourier_poles"
  then obtain z where "Im z > 0" "is_pole f z" "q = cusp_q period z"
    by (auto simp: fourier_poles_def)
  thus "is_pole f (cusp_q_inv period q)"
    by (metis cusp_q_cusp_q_inv cusp_q_nonzero fourier_is_pole_cusp_q_iff period_pos)
qed

lemma cusp_q_in_fourier_poles_iff [simp]:
  "cusp_q period z \<in> fourier_poles \<longleftrightarrow> is_pole f z"
proof
  assume "cusp_q period z \<in> fourier_poles"
  then obtain z' where z': "cusp_q period z = cusp_q period z'" "is_pole f z'"
    by (auto simp: fourier_poles_def)
  from z'(1) obtain n where "z = z' + of_int n * of_nat period"
    using period_pos by (metis cusp_q_eq_cusp_qE)
  with z'(2) show "is_pole f z"
    by (metis fourier_expansion.fourier_is_pole_cusp_q_iff fourier_expansion_axioms z'(1))
qed (use not_is_pole_eval_mero_uhp_outside[of z f]
     in  \<open>cases "Im z > 0"; auto simp: fourier_poles_def period_pos intro!: imageI\<close>)

lemma not_islimpt_fourier_poles:
  assumes "z \<in> ball 0 1 - {0}"
  shows   "\<not>z islimpt fourier_poles"
proof
  assume "z islimpt fourier_poles"
  then obtain g where g: "\<And>n. g n \<in> fourier_poles - {z}" "g \<longlonglongrightarrow> z"
    unfolding islimpt_sequential by metis
  have [simp]: "g n \<noteq> 0" for n
    using g(1)[of n] by (auto simp: fourier_poles_def)

  from assms have "z \<noteq> 0"
    by auto
  have "open (-{0::complex})"
    by auto
  then obtain r where r: "r > 0" "ball z r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>z \<noteq> 0\<close> by blast
  have "simply_connected (ball z r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball z r" "\<forall>q\<in>ball z r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
    where myln_holo: "myln holomorphic_on ball z r" 
    and "\<And>q'. q' \<in> ball z r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball z r" for q'
    using that by metis

  define cusp_q_inv' :: "complex \<Rightarrow> complex"
    where "cusp_q_inv' = (\<lambda>z. period * myln z / (complex_of_real (2 * pi) * \<i>))"
  have cusp_q_inv': "cusp_q period (cusp_q_inv' w) = w" if "w \<in> ball z r" for w
    using that period_pos by (simp add: cusp_q_def cusp_q_inv'_def exp_myln)
  define g' where "g' = (\<lambda>n. cusp_q_inv' (g n))"      

  have "continuous_on (ball z r) myln"
    by (intro holomorphic_on_imp_continuous_on myln_holo)
  hence cont: "continuous_on (ball z r) cusp_q_inv'"
    unfolding cusp_q_inv'_def by (intro continuous_intros) auto

  have "eventually (\<lambda>x. x \<in> ball z r) (nhds z)"
    using r by (intro eventually_nhds_in_open) auto
  hence ev: "eventually (\<lambda>n. g n \<in> ball z r) sequentially"
    by (rule eventually_compose_filterlim [OF _ g(2)])
  hence "g' \<longlonglongrightarrow> cusp_q_inv' z"
    using r(1) unfolding g'_def by (intro continuous_on_tendsto_compose [OF cont g(2)]) auto

  from ev obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> g n \<in> ball z r"
    by (auto simp: eventually_at_top_linorder)

  have *: "g' n \<in> {z. is_pole f z} - {cusp_q_inv' z}" if n: "n \<ge> N" for n
  proof -
    have "g n \<in> fourier_poles"
      using g(1)[of n] by auto
    then obtain x where x: "x \<in> {z. is_pole f z}" "g n = cusp_q period x"
      by (auto simp: fourier_poles_def)
    have *: "cusp_q period x = cusp_q period (cusp_q_inv' (g n))"
      using x N[OF n] by (subst cusp_q_inv') auto
    obtain m where m: "cusp_q_inv' (g n) = x + of_int m * of_nat period"
      using cusp_q_eq_cusp_qE[OF * period_pos] .
    hence "cusp_q_inv' (g n) \<in> {z. is_pole f z}"
      by (metis * \<open>g n \<in> fourier_poles\<close> cusp_q_in_fourier_poles_iff mem_Collect_eq x(2))
    hence "g' n \<in> {z. is_pole f z}"
      by (auto simp: g'_def)
    moreover have "g' n \<noteq> cusp_q_inv' z"
    proof
      assume "g' n = cusp_q_inv' z"
      hence "cusp_q period (g' n) = cusp_q period (cusp_q_inv' z)"
        by (simp only: )
      hence "g n = z"
        using N[OF n] \<open>r > 0\<close> by (simp add: cusp_q_inv' g'_def)
      with g(1)[of n] show False
        by auto
    qed
    ultimately show ?thesis
      by blast
  qed

  define g'' where "g'' = g' \<circ> (\<lambda>n. n + N)"
  have "g'' \<longlonglongrightarrow> cusp_q_inv' z"
    unfolding g''_def using \<open>g' \<longlonglongrightarrow> _\<close>
    by (rule LIMSEQ_subseq_LIMSEQ) (auto simp: strict_mono_def)
  moreover have "g'' n \<in> {z. is_pole f z} - {cusp_q_inv' z}" for n
    using *[of "n + N"] by (auto simp: g''_def)
  ultimately have "cusp_q_inv' z islimpt {z. is_pole f z}"
    unfolding islimpt_sequential by metis
  moreover have "Im (cusp_q_inv' z) > 0"
  proof -
    have *: "cusp_q period (cusp_q_inv period z) = cusp_q period (cusp_q_inv' z)"
      using r \<open>z \<noteq> 0\<close> period_pos by (subst cusp_q_inv') auto
    obtain m where m: "cusp_q_inv' z = cusp_q_inv period z + of_int m * of_nat period"
      using cusp_q_eq_cusp_qE[OF * period_pos] .
    hence "Im (cusp_q_inv' z) = Im (cusp_q_inv period z)"
      by simp
    also from assms have "norm z < 1"
      by simp
    hence "Im (cusp_q_inv period z) > 0"
      using \<open>z \<noteq> 0\<close> period_pos by (intro Im_cusp_q_inv_gt) auto
    finally show ?thesis .
  qed
  moreover have "{z. is_pole (eval_mero_uhp f) z} sparse_in \<H>"
    by (intro meromorphic_on_imp_sparse_poles meromorphic_intros) auto
  ultimately show False
    by (subst (asm) sparse_in_open) (auto simp: open_halfspace_Im_gt)
qed

lemma open_Diff_fourier_poles':
  assumes "fourier_poles' \<subseteq> fourier_poles"
  shows   "open (ball 0 1 - {0} - fourier_poles')"
proof - 
  define D where "D = ball (0 :: complex) 1 - {0}"
  have "open (D - closure fourier_poles')"
    by (intro open_Diff) (auto simp: D_def)
  also have "D - closure fourier_poles' = D - fourier_poles'"
  proof safe
    fix x assume x: "x \<in> D" "x \<in> closure fourier_poles'" "x \<notin> fourier_poles'"
    hence "x islimpt fourier_poles'"
      by (subst islimpt_in_closure) auto
    hence "x islimpt fourier_poles"
      by (rule islimpt_subset) fact
    with assms x show False
      using not_islimpt_fourier_poles[of x] by (auto simp: D_def)
  qed (use closure_subset in auto)
  finally show ?thesis 
    by (simp add: D_def)
qed

lemma open_Diff_fourier_poles: "open (ball 0 1 - {0} - fourier_poles)"
  by (rule open_Diff_fourier_poles') auto

lemma analytic_fourier:
  assumes "A \<subseteq> ball 0 1 - fourier_poles - {0}"
  shows "fourier analytic_on A"
proof -
  define B where "B = ball 0 1 - fourier_poles"
  have "fourier holomorphic_on B - {0}"
    unfolding holomorphic_on_def
  proof
    fix q assume q: "q \<in> B - {0}"
    define z where "z = cusp_q_inv period q"
    have z: "Im z > 0"
      using q period_pos by (auto simp: B_def z_def intro!: Im_cusp_q_inv_gt)
    have z_conv_q: "cusp_q period z = q"
      using q period_pos by (auto simp: B_def z_def)
    have not_pole: "\<not>is_pole (eval_mero_uhp f) z"
    proof
      assume "is_pole (eval_mero_uhp f) z"
      hence "cusp_q period z \<notin> B"
        using z by (auto simp: B_def)
      with z_conv_q and q show False
        by simp
    qed
    have "\<exists>c. (fourier has_field_derivative c) (at q within B - {0})"
      by (rule exI, rule has_field_derivative_fourier[of z]) (use z not_pole z_conv_q in auto)
    thus "fourier field_differentiable at q within B - {0}"
      using field_differentiable_def by blast
  qed
  moreover have "open (B - {0})"
    using open_Diff_fourier_poles unfolding B_def by (metis Diff_insert Diff_insert2)
  ultimately have "fourier analytic_on B - {0}"
    by (simp add: analytic_on_open)
  thus ?thesis
    by (rule analytic_on_subset) (use assms in \<open>auto simp: B_def\<close>)
qed

lemma fourier_poles_altdef:
  "fourier_poles = {q\<in>ball 0 1-{0}. is_pole fourier q}"
proof (intro equalityI subsetI)
  fix q assume q: "q \<in> fourier_poles"
  have "q \<in> ball 0 1 - {0}"
    using q period_pos by (auto simp: fourier_poles_def)
  moreover have "is_pole fourier q"
    using q unfolding fourier_poles_def by (auto simp: fourier_is_pole_cusp_q_iff)
  ultimately show "q \<in> {q\<in>ball 0 1-{0}. is_pole fourier q}"
    by auto
next
  fix q assume q: "q \<in> {q\<in>ball 0 1-{0}. is_pole fourier q}"
  define z where "z = cusp_q_inv period q"
  have q_eq: "q = cusp_q period z"
    using q period_pos by (auto simp: z_def)
  have "Im z > 0"
    using q period_pos by (auto simp: z_def intro!: Im_cusp_q_inv_gt)
  thus "q \<in> fourier_poles"
    using q by (auto simp: fourier_poles_def q_eq fourier_is_pole_cusp_q_iff intro!: imageI)
qed

lemma fourier_meromorphic_weak:
  assumes "A \<subseteq> ball 0 1 - {0}"
  shows   "fourier meromorphic_on A"
proof (rule meromorphic_on_subset)
  show "fourier meromorphic_on (ball 0 1 - {0})"
  proof (rule meromorphic_onI_open[where pts = "fourier_poles"])
    fix q assume "q \<in> fourier_poles"
    thus "not_essential fourier q"
      by (auto simp: fourier_poles_altdef)
  next
    fix q :: complex assume q: "q \<in> ball 0 1 - {0}"
    hence "\<not>q islimpt fourier_poles"
      using not_islimpt_fourier_poles[of q] q by blast
    thus "\<not>q islimpt fourier_poles \<inter> (ball 0 1 - {0})"
      using islimpt_subset by blast
  qed (auto intro!: analytic_fourier)
qed (use assms in auto)

lemma tendsto_fourier_cusp_q:
  assumes "f \<midarrow>z\<rightarrow> c" "q = cusp_q period z"
  shows   "fourier \<midarrow>q\<rightarrow> c"
proof -
  from assms have "q \<noteq> 0"
    by auto
  have "open (-{0::complex})"
    by auto
  then obtain r where r: "r > 0" "ball q r \<subseteq> -{0 :: complex}"
    unfolding open_contains_ball using \<open>q \<noteq> 0\<close> by blast
  have "simply_connected (ball q r)"
    by (auto intro!: convex_imp_simply_connected)
  moreover have "(\<lambda>q. q) holomorphic_on ball q r" "\<forall>q\<in>ball q r. q \<noteq> 0"
    using r by (auto intro!: holomorphic_intros)
  ultimately obtain myln :: "complex \<Rightarrow> complex"
    where myln_holo: "myln holomorphic_on ball q r" 
    and "\<And>q'. q' \<in> ball q r \<Longrightarrow> q' = exp (myln q')"
    unfolding simply_connected_eq_holomorphic_log[OF open_ball] by blast
  from this(2) have exp_myln: "exp (myln q') = q'" if "q' \<in> ball q r" for q'
    using that by metis

  define cusp_q_inv' :: "complex \<Rightarrow> complex"
    where "cusp_q_inv' = (\<lambda>z. period * myln z / (complex_of_real (2 * pi) * \<i>))"
  have cusp_q_inv': "cusp_q period (cusp_q_inv' w) = w" if "w \<in> ball q r" for w
    using that by (simp add: cusp_q_def cusp_q_inv'_def exp_myln period_pos)

  obtain m where m: "cusp_q_inv' q = z + of_int m * of_nat period"
  proof -
    have "cusp_q period z = cusp_q period (cusp_q_inv' q)"
      using r(1) by (simp add: cusp_q_inv' assms)
    from cusp_q_eq_cusp_qE[OF this] period_pos and that show ?thesis
      by blast
  qed
  define cusp_q_inv'' :: "complex \<Rightarrow> complex"
    where "cusp_q_inv'' = (\<lambda>q. cusp_q_inv' q - of_int m * of_nat period)"
  have cusp_q_inv'': "cusp_q period (cusp_q_inv'' w) = w" if "w \<in> ball q r" for w
    using that by (auto simp: cusp_q_inv''_def cusp_q.minus_of_int cusp_q_inv')
  have [simp]: "cusp_q_inv'' (cusp_q period z) = z"
    using m by (simp add: cusp_q_inv''_def assms)

  have "continuous_on (ball q r) myln"
    by (intro holomorphic_on_imp_continuous_on myln_holo)
  hence cont: "continuous_on (ball q r) cusp_q_inv''"
    unfolding cusp_q_inv''_def cusp_q_inv'_def by (intro continuous_intros) auto
  moreover have "q \<in> ball q r"
    using r(1) by auto
  ultimately have "isCont cusp_q_inv'' q"
    by (simp add: continuous_on_eq_continuous_at)
  hence "cusp_q_inv'' \<midarrow>q\<rightarrow> cusp_q_inv'' q"
    by (simp add: isCont_def)
  moreover have "\<forall>\<^sub>F x in at q. cusp_q_inv'' x \<noteq> z"
  proof -
    have "eventually (\<lambda>x. x \<in> ball q r - {q}) (at q)"
      using r(1) by (intro eventually_at_in_open) auto
    thus ?thesis
    proof eventually_elim
      case (elim x)
      hence "cusp_q period (cusp_q_inv'' x) \<noteq> cusp_q period z"
        by (subst cusp_q_inv'') (auto simp: assms)
      thus ?case
        by blast
    qed
  qed
  ultimately have "filterlim cusp_q_inv'' (at z) (at q)"
    using assms by (auto simp: filterlim_at)
  hence "(f \<circ> cusp_q_inv'') \<midarrow>q\<rightarrow> c"
    unfolding o_def by (rule filterlim_compose[OF assms(1)])
  also have "?this \<longleftrightarrow> fourier \<midarrow>q\<rightarrow> c"
  proof (intro filterlim_cong refl)
    have "eventually (\<lambda>x. x \<in> ball q r - {q}) (at q)"
      using r(1) by (intro eventually_at_in_open) auto
    moreover have "eventually (\<lambda>x. x \<in> -{0}) (at q)"
      by (intro eventually_at_in_open') (auto simp: assms)
    ultimately show "\<forall>\<^sub>F x in at q. (f \<circ> cusp_q_inv'') x = fourier x"
    proof eventually_elim
      case (elim x)
      have "cusp_q period (cusp_q_inv period x) = cusp_q period (cusp_q_inv'' x)"
        using elim period_pos by (auto simp: cusp_q_inv'')
      then obtain m where *: "cusp_q_inv'' x = cusp_q_inv period x + of_int m * of_nat period"
        by (elim cusp_q_eq_cusp_qE) (use period_pos in auto)
      show ?case using elim Im_cusp_q_inv_gt[of x]
        by (auto simp: fourier_def * plus_of_int)
    qed
  qed
  finally show ?thesis .
qed

lemma deriv_fourier:
  assumes "Im z > 0" "\<not>is_pole f z" "q = cusp_q period z"
  shows   "deriv fourier q = eval_mero_uhp (deriv_mero_uhp f) z * of_nat period / (of_real (2 * pi) * \<i> * q)"
  by (rule DERIV_imp_deriv)
     (use has_field_derivative_fourier[OF assms(2,1)]
      in  \<open>auto intro!: derivative_eq_intros simp: assms(3)\<close>)

lemma eval_fourier_outside: "norm q \<ge> 1 \<Longrightarrow> fourier q = 0"
  unfolding fourier_def using period_pos
  by (auto intro!: eval_mero_uhp_outside simp: cusp_q_inv_def Im_divide)

lemma not_pole_eval_fourier_outside: "norm q \<ge> 1 \<Longrightarrow> \<not>is_pole fourier q"
  by (smt (verit, del_insts) Diff_iff cusp_q_cusp_q_inv cusp_q_in_fourier_poles_iff dist_0_norm 
       fourier_is_pole_cusp_q_iff fourier_poles_altdef mem_Collect_eq mem_ball norm_zero period_pos)

end


locale fourier_expansion_meromorphic = fourier_expansion +
  assumes fourier_meromorphic_at_0: "fourier meromorphic_on {0}"
begin

lemma fourier_meromorphic [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "fourier meromorphic_on A"
proof (rule meromorphic_on_subset)
  show "fourier meromorphic_on (ball 0 1 - {0} \<union> {0})"
    by (intro meromorphic_on_Un fourier_meromorphic_weak fourier_meromorphic_at_0 order.refl)
qed (use assms in auto)

lemma fourier_meromorphic' [meromorphic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (f z) < 1"
  shows   "(\<lambda>z. fourier (f z)) meromorphic_on A"
  by (rule meromorphic_on_compose[OF fourier_meromorphic assms(1) order.refl]) (use assms(2) in auto)

lemma fourier_nicely_meromorphic: "fourier nicely_meromorphic_on ball 0 1"
  unfolding nicely_meromorphic_on_def
proof (intro ballI conjI)
  fix q :: complex assume q: "q \<in> ball 0 1"
  show "is_pole fourier q \<and> fourier q = 0 \<or> fourier \<midarrow>q\<rightarrow> fourier q"
  proof (cases "is_pole fourier q")
    case pole: True
    have "fourier q = 0"
    proof (cases "q = 0")
      case [simp]: True
      from pole have "filterlim f at_infinity at_cusp"
        by (auto simp: fourier_is_pole_0_iff)
      hence "\<not>(\<exists>L. (eval_mero_uhp f \<longlongrightarrow> L) at_cusp)"
        using at_cusp_neq_bot not_tendsto_and_filterlim_at_infinity by blast
      thus "fourier q = 0"
        by (simp add: fourier_def)
    next
      case False
      thus ?thesis using pole
        by (metis cusp_q_cusp_q_inv eval_mero_uhp_pole fourier_def fourier_is_pole_cusp_q_iff period_pos)
    qed
    thus ?thesis
      using pole by blast
  next
    case no_pole: False
    have "fourier \<midarrow>q\<rightarrow> fourier q"
    proof (cases "q = 0")
      case [simp]: True
      have "not_essential fourier 0"
        using fourier_meromorphic_at_0 by (simp add: meromorphic_on_not_essential)
      with q no_pole obtain c where "fourier \<midarrow>0\<rightarrow> c"
        by (auto simp: not_essential_def)
      thus ?thesis
        using fourier_0_aux[of c] by (simp add: fourier_tendsto_0_iff)
    next
      case False
      define z where "z = cusp_q_inv period q"
      have q_eq: "q = cusp_q period z"
        using False q period_pos by (auto simp: z_def)
      show ?thesis
      proof (rule tendsto_fourier_cusp_q)
        have "\<not>is_pole f z"
          using fourier_is_pole_cusp_q_iff[of z] q q_eq no_pole by auto
        hence "eval_mero_uhp f \<midarrow>z\<rightarrow> eval_mero_uhp f z"
          unfolding z_def using q False 
          by (intro isContD analytic_at_imp_isCont analytic_intros) (auto intro!: Im_cusp_q_inv_gt)
        also have "eval_mero_uhp f z = fourier q"
          using False q by (simp add: q_eq)
        finally show "eval_mero_uhp f \<midarrow>z\<rightarrow> fourier q" .
      qed fact+
    qed
    thus ?thesis ..
  qed
qed (auto intro!: meromorphic_intros)

lemma frequently_fourier_eq0_imp_const:
  assumes "frequently (\<lambda>q. fourier q = c) (at q)" "norm q < 1"
  shows   "f = const_mero_uhp c"
proof -
  have "(\<forall>q\<in>ball 0 1. fourier q = c) \<or> (\<forall>\<^sub>\<approx>q\<in>ball 0 1. fourier q \<noteq> c)"
    by (intro nicely_meromorphic_imp_constant_or_avoid fourier_nicely_meromorphic) auto
  with assms have *: "fourier q = c" if "norm q < 1" for q
    using that by (auto simp: eventually_cosparse_open_eq frequently_def)
  have **: "eval_mero_uhp f z = c" if z: "Im z > 0" for z
  proof -
    have "eval_mero_uhp f z = fourier (cusp_q period z)"
      by simp
    also have "\<dots> = c"
      using z by (intro *) (use period_pos in auto)
    finally show ?thesis .
  qed
  have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
    by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
  hence "eventually (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z) (cosparse \<H>)"
    by eventually_elim (auto simp: **)
  thus ?thesis
    by (rule mero_uhp_eqI)
qed

lemma zorder_at_cusp_conv_fourier:
  assumes "f \<noteq> 0"
  shows   "zorder_at_cusp period f = zorder fourier 0"
proof (rule zorder_at_cusp_eqI)
  define F where "F = laurent_expansion fourier 0"
  have "fourier meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  hence F: "fourier has_laurent_expansion F"
    unfolding F_def by (auto simp: meromorphic_on_def')
  have "F \<noteq> 0"
  proof
    assume "F = 0"
    hence "eventually (\<lambda>q. fourier q = 0) (at 0)"
      using F has_laurent_expansion_def by force
    hence "frequently (\<lambda>q. fourier q = 0) (at 0)"
      using eventually_frequently trivial_limit_at by blast
    hence "f = const_mero_uhp 0"
      by (intro frequently_fourier_eq0_imp_const) auto
    with assms show False
      by simp
  qed
  define n where "n = zorder fourier 0"

  have "(\<lambda>z. fourier (cusp_q period z)) \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q period z powi n)"
  proof (rule landau_theta.compose[OF _ filterlim_cusp_q_at_cusp])
    have "fourier \<in> \<Theta>[at 0](\<lambda>q. q powi fls_subdegree F)"
      by (rule has_laurent_expansion_imp_bigtheta) fact+
    also have "fls_subdegree F = n"
      unfolding n_def using F \<open>F \<noteq> 0\<close> has_laurent_expansion_zorder_0 by auto
    finally show "fourier \<in> \<Theta>[at 0](\<lambda>q. q powi n)" .
  qed (fact period_pos)
  thus "eval_mero_uhp f \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q period z powi n)" (is "?P n")
    by simp
qed (fact period_pos)

lemma eventually_neq_at_cusp:
  assumes "f \<noteq> const_mero_uhp c"
  shows   "eventually (\<lambda>z. f z \<noteq> c) at_cusp"
proof (rule ccontr)
  assume "\<not>eventually (\<lambda>z. f z \<noteq> c) at_cusp"
  hence "\<exists>\<^sub>F x in at_cusp. eval_mero_uhp f x = c"
    by (simp add: not_eventually)
  hence *: "frequently (\<lambda>q. fourier q = c) (at 0)" using period_pos
    by (simp flip: at_cusp_filtermap[of period] 
             add: frequently_filtermap not_eventually del: One_nat_def)

  have "(\<forall>q\<in>ball 0 1. fourier q = c) \<or> (\<forall>\<^sub>\<approx>q\<in>ball 0 1. fourier q \<noteq> c)"
    by (intro nicely_meromorphic_imp_constant_or_avoid fourier_nicely_meromorphic) auto
  thus False
  proof
    assume *: "\<forall>q\<in>ball 0 1. fourier q = c"
    have **: "eval_mero_uhp f z = c" if z: "Im z > 0" for z
    proof -
      have "eval_mero_uhp f z = fourier (cusp_q period z)"
        by simp
      also have "cusp_q period z \<in> ball 0 1"
        using z period_pos by auto
      hence "fourier (cusp_q period z) = c"
        using * by blast
      finally show ?thesis .
    qed
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (cosparse \<H>)"
      by (intro eventually_in_cosparse open_halfspace_Im_gt order.refl)
    hence "eventually (\<lambda>z. eval_mero_uhp f z = eval_mero_uhp (const_mero_uhp c) z) (cosparse \<H>)"
      by eventually_elim (use ** in auto)
    hence "f = const_mero_uhp c"
      by (rule mero_uhp_eqI)
    thus False
      using assms by contradiction
  next
    assume "\<forall>\<^sub>\<approx>q\<in>ball 0 1. fourier q \<noteq> c"
    hence "eventually (\<lambda>q. fourier q \<noteq> c) (at 0)"
      by (auto simp: eventually_cosparse_open_eq)
    with * show False
      by (simp add: frequently_def)
  qed
qed

lemma eventually_neq_fourier:
  assumes "f \<noteq> const_mero_uhp c" "norm q < 1"
  shows   "eventually (\<lambda>q. fourier q \<noteq> c) (at q)"
  using assms frequently_fourier_eq0_imp_const unfolding frequently_def by blast

lemma eval_at_cusp_conv_fourier [simp]: "eval_mero_uhp_at_cusp f = fourier 0"
proof (cases "is_pole fourier 0")
  case True
  hence *: "\<not>(\<exists>L. (f \<longlongrightarrow> L) at_cusp)"
    using at_cusp_neq_bot fourier_is_pole_0_iff not_tendsto_and_filterlim_at_infinity by blast
  thus ?thesis
    by (auto simp: fourier_def eval_mero_uhp_at_cusp_def)
next
  case False
  thus ?thesis
    by (auto simp: fourier_def eval_mero_uhp_at_cusp_def)
qed

lemma analytic_fourier' [analytic_intros]:
  assumes "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole fourier (g z)"
  shows   "(\<lambda>z. fourier (g z)) analytic_on A"
proof (rule analytic_on_compose_gen[OF assms(1), unfolded o_def])
  have "fourier analytic_on (ball 0 1 - fourier_poles - {0})"
    by (intro analytic_fourier order.refl)
  have "fourier analytic_on {0}" if "\<not>is_pole fourier 0" 
    using that fourier_nicely_meromorphic nicely_meromorphic_on_imp_analytic_at by auto
  thus "fourier analytic_on (ball 0 1 - fourier_poles - {0} \<union> (if is_pole fourier 0 then {} else {0}))"
    unfolding analytic_on_Un by (auto intro!: analytic_fourier)
  show "g z \<in> ball 0 1 - fourier_poles - {0} \<union> (if is_pole fourier 0 then {} else {0})" if "z \<in> A" for z
    using that assms(2)[of z] by (cases "g z = 0") (auto simp: fourier_poles_altdef)
qed

lemma holomorphic_fourier [holomorphic_intros]:
  assumes "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole fourier (g z)"
  shows   "(\<lambda>z. fourier (g z)) holomorphic_on A"
proof (rule holomorphic_on_compose_gen[OF assms(1), unfolded o_def])
  show "fourier holomorphic_on (ball 0 1 - {z. is_pole fourier z})"
    by (intro analytic_imp_holomorphic analytic_intros) auto
qed (use assms(2) in auto)

lemma continuous_on_fourier [continuous_intros]:
  assumes "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> \<not>is_pole fourier (g z)"
  shows   "continuous_on A (\<lambda>z. fourier (g z))"
  by (rule continuous_on_compose[OF assms(1), unfolded o_def] holomorphic_on_imp_continuous_on holomorphic_intros)+
     (use assms(2) in auto)

lemma continuous_fourier [continuous_intros]:
  assumes "continuous (at z within A) g" assumes "norm (g z) < 1" "\<not>is_pole fourier (g z)"
  shows   "continuous (at z within A) (\<lambda>z. fourier (g z))"
  by (rule continuous_within_compose[OF assms(1), unfolded o_def]
           continuous_at_imp_continuous_within[OF analytic_at_imp_isCont] analytic_intros)+
     (use assms(2,3) in auto)

lemma tendsto_fourier [tendsto_intros]:
  assumes "(g \<longlongrightarrow> q) F" assumes "norm q < 1" "\<not>is_pole fourier q"
  shows   "((\<lambda>z. fourier (g z)) \<longlongrightarrow> fourier q) F"
  by (rule isCont_tendsto_compose[OF _ assms(1)]) (use assms in \<open>auto intro!: continuous_intros\<close>)

lemma zorder_fourier_neg_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder fourier q < 0 \<longleftrightarrow> is_pole fourier q"
proof (cases "is_pole fourier q")
  case True
  thus ?thesis using assms
    by (auto intro!: isolated_pole_imp_neg_zorder meromorphic_on_isolated_singularity meromorphic_intros)
next
  case False
  have "\<exists>\<^sub>F q in at q. fourier q \<noteq> 0"
    using assms False by (intro eventually_frequently eventually_neq_fourier) auto
  hence "zorder fourier q \<ge> 0"
    using False assms by (intro zorder_ge_0 analytic_intros) auto
  thus ?thesis
    using False by auto
qed

lemma zorder_fourier_nonneg_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder fourier q \<ge> 0 \<longleftrightarrow> \<not>is_pole fourier q"
  using zorder_fourier_neg_iff[OF assms] by linarith

lemma zorder_fourier_pos_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder fourier q > 0 \<longleftrightarrow> \<not>is_pole fourier q \<and> fourier q = 0"
proof (cases "is_pole fourier q")
  case False
  thus ?thesis
  proof (subst zorder_pos_iff')
    show "\<exists>\<^sub>F q in at q. fourier q \<noteq> 0"
      using assms False by (intro eventually_frequently eventually_neq_fourier) auto
  qed (use assms in \<open>auto intro!: analytic_intros\<close>)
next
  case True
  hence "zorder fourier q < 0"
    using assms by simp
  with True show ?thesis
    by auto
qed

lemma zorder_fourier_nonpos_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder fourier q \<le> 0 \<longleftrightarrow> is_pole fourier q \<or> fourier q \<noteq> 0"
  using zorder_fourier_pos_iff[OF assms] by linarith

lemma zorder_fourier_eq_0_iff [simp]:
  assumes "f \<noteq> 0" "norm q < 1"
  shows   "zorder fourier q = 0 \<longleftrightarrow> \<not>is_pole fourier q \<and> fourier q \<noteq> 0"
  using assms by (metis linorder_neqE_linordered_idom zorder_fourier_neg_iff zorder_fourier_pos_iff)

end

locale fourier_unop_meromorphic = fourier_expansion_meromorphic +
  fixes g :: "mero_uhp \<Rightarrow> mero_uhp" and g' :: "complex \<Rightarrow> complex" and g'' :: "complex fls \<Rightarrow> complex fls"
  assumes mero_uhp_rel_map [mero_uhp_rel_intros]:
    "mero_uhp_rel (eval_mero_uhp (g f)) (\<lambda>z. g' (eval_mero_uhp f z))"
  assumes compose_modgrp_mero_uhp_map_distrib [simp]:
    "compose_modgrp_mero_uhp (g f) h = g (compose_modgrp_mero_uhp f h)"
  assumes map_laurent_expansion:
    "\<And>f F. f has_laurent_expansion F \<Longrightarrow> (\<lambda>z. g' (f z)) has_laurent_expansion g'' F"
begin

sublocale map: fourier_expansion "g f" period
  by standard (simp_all add: period_pos)

lemma map_fourier_eq_aux:
  assumes q: "q \<in> ball 0 1 - {0}" "\<not>is_pole fourier q" "(\<lambda>q. g' (fourier q)) analytic_on {q}"
  shows   "map.fourier q = g' (fourier q)"
proof -
  define z where "z = cusp_q_inv period q"
  have "(\<lambda>z. g' (fourier (cusp_q period z))) analytic_on {z}" using period_pos q
    by (intro analytic_on_compose_gen[OF _ assms(3), unfolded o_def] analytic_intros)
       (auto simp: z_def)
  hence *: "(\<lambda>z. g' (f z)) analytic_on {z}"
    by simp

  have "map.fourier q = eval_mero_uhp (g f) z"
    using assms by (auto simp: map.fourier_def z_def)
  also have "\<dots> = g' (eval_mero_uhp f z)" using period_pos q *
    by (subst mero_uhp_rel_imp_eval_mero_uhp_eq[OF mero_uhp_rel_map])
       (auto intro!: simp: z_def intro!: Im_cusp_q_inv_gt)
  also have "\<dots> = g' (fourier q)"
    using q by (simp add: fourier_def z_def)
  finally show ?thesis .
qed

lemma meromorphic_map [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "(\<lambda>w. g' (fourier w)) meromorphic_on A"
  unfolding meromorphic_on_def
proof safe
  fix q assume "q \<in> A"
  hence [simp]: "norm q < 1"
    using assms by auto
  have "(\<lambda>w. g' (fourier (q + w))) has_laurent_expansion g'' (laurent_expansion fourier q)"
    by (intro map_laurent_expansion meromorphic_on_imp_has_laurent_expansion[of _ "{q}"])
       (auto intro!: meromorphic_intros)
  thus "\<exists>L. (\<lambda>w. g' (fourier (q + w))) has_laurent_expansion L" ..
qed

lemma eventually_map_fourier_eq:
  "eventually (\<lambda>q. map.fourier q = g' (fourier q)) (cosparse (ball 0 1))"
  unfolding eventually_cosparse_open_eq[OF open_ball]
proof safe
  fix q :: complex assume q: "q \<in> ball 0 1"
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at q)"
    using q by (intro eventually_at_in_open') auto
  moreover have "eventually (\<lambda>q. q \<noteq> 0) (at q)"
    by (intro eventually_neq_at_within)
  moreover have "eventually (\<lambda>q. \<not>is_pole fourier q) (at q)"
  proof -
    have "fourier meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. (\<lambda>q. g' (fourier q)) analytic_on {q}) (at q)"
  proof -
    have "(\<lambda>q. g' (fourier q)) meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      using isolated_singularity_at_altdef meromorphic_on_isolated_singularity by blast
  qed
  ultimately show "eventually (\<lambda>q. map.fourier q = g' (fourier q)) (at q)"
    by eventually_elim (use map_fourier_eq_aux in auto)
qed

sublocale fourier_expansion_meromorphic "g f" period
proof
  have "(\<lambda>q. g' (fourier q)) meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  also have "?this \<longleftrightarrow> map.fourier meromorphic_on {0}"
    by (intro meromorphic_on_cong)
       (use eventually_map_fourier_eq in \<open>simp_all add: eq_commute eventually_cosparse_open_eq\<close>)
  finally show \<dots> .
qed

lemma map_fourier_eq:
  assumes q: "q \<in> ball 0 1" "\<not>is_pole fourier q" "(\<lambda>q. g' (fourier q)) analytic_on {q}"
  shows   "map.fourier q = g' (fourier q)"
proof (cases "q = 0")
  case True
  have "is_pole map.fourier 0 \<longleftrightarrow> is_pole (\<lambda>q. g' (fourier q)) 0"
    using eventually_map_fourier_eq by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq)
  also have "\<not>is_pole (\<lambda>q. g' (fourier q)) 0"
    using q(3) True by (simp add: analytic_at_imp_no_pole)
  finally have "map.fourier \<midarrow>0\<rightarrow> map.fourier 0"
    unfolding True by (intro isContD analytic_at_imp_isCont analytic_intros) auto
  also have "?this \<longleftrightarrow> (\<lambda>q. g' (fourier q)) \<midarrow>0\<rightarrow> map.fourier 0"
    using eventually_map_fourier_eq by (intro tendsto_cong) (auto simp: eventually_cosparse_open_eq)
  finally have "(\<lambda>q. g' (fourier q)) \<midarrow>0\<rightarrow> map.fourier 0" .
  moreover have "(\<lambda>q. g' (fourier q)) \<midarrow>0\<rightarrow> g' (fourier 0)"
    by (intro isContD analytic_at_imp_isCont) (use True q(3) in auto)
  ultimately show ?thesis
    using LIM_unique True by blast
qed (use map_fourier_eq_aux q in auto)

lemma map_has_laurent_expansion_at_cusp:
  assumes "fourier has_laurent_expansion F"
  shows   "map.fourier has_laurent_expansion g'' F"
proof (subst has_laurent_expansion_cong)
  show "eventually (\<lambda>q. map.fourier q = g' (fourier q)) (at 0)"
    using eventually_map_fourier_eq unfolding eventually_cosparse_open_eq[OF open_ball] by auto
  show "(\<lambda>q. g' (fourier q)) has_laurent_expansion g'' F"
    by (intro map_laurent_expansion assms)
qed auto

end



locale fourier_binop_meromorphic =
  f: fourier_expansion_meromorphic f period + g: fourier_expansion_meromorphic g period
  for f g period +
  fixes h :: "mero_uhp \<Rightarrow> mero_uhp \<Rightarrow> mero_uhp" and h' :: "complex \<Rightarrow> complex \<Rightarrow> complex" 
    and h'' :: "complex fls \<Rightarrow> complex fls \<Rightarrow> complex fls"
  assumes mero_uhp_rel_map [mero_uhp_rel_intros]:
    "mero_uhp_rel (eval_mero_uhp (h f g)) (\<lambda>z. h' (eval_mero_uhp f z) (eval_mero_uhp g z))"
  assumes compose_modgrp_mero_uhp_map_distrib [simp]:
    "compose_modgrp_mero_uhp (h f g) j = h (compose_modgrp_mero_uhp f j) (compose_modgrp_mero_uhp g j)"
  assumes map_laurent_expansion:
    "\<And>f g F G. f has_laurent_expansion F \<Longrightarrow> g has_laurent_expansion G \<Longrightarrow>
       (\<lambda>z. h' (f z) (g z)) has_laurent_expansion h'' F G"
begin

sublocale map: fourier_expansion "h f g" period
  by standard (simp_all add: f.period_pos)

lemma map_fourier_eq_aux:
  assumes q: "q \<in> ball 0 1 - {0}" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q"
  assumes  "(\<lambda>q. h' (f.fourier q) (g.fourier q)) analytic_on {q}"
  shows   "map.fourier q = h' (f.fourier q) (g.fourier q)"
proof -
  define z where "z = cusp_q_inv period q"
  have "(\<lambda>z. h' (f.fourier (cusp_q period z)) (g.fourier (cusp_q period z))) analytic_on {z}"
    using f.period_pos q
    by (intro analytic_on_compose_gen[OF _ assms(4), unfolded o_def] analytic_intros)
       (auto simp: z_def)
  hence *: "(\<lambda>z. h' (f z) (g z)) analytic_on {z}"
    by simp

  have "map.fourier q = eval_mero_uhp (h f g) z"
    using assms by (auto simp: map.fourier_def z_def)
  also have "\<dots> = h' (eval_mero_uhp f z) (eval_mero_uhp g z)" using f.period_pos q *
    by (subst mero_uhp_rel_imp_eval_mero_uhp_eq[OF mero_uhp_rel_map])
       (auto intro!: simp: z_def intro!: Im_cusp_q_inv_gt)
  also have "\<dots> = h' (f.fourier q) (g.fourier q)"
    using q by (simp add: f.fourier_def g.fourier_def z_def)
  finally show ?thesis .
qed

lemma meromorphic_map [meromorphic_intros]:
  assumes "A \<subseteq> ball 0 1"
  shows   "(\<lambda>w. h' (f.fourier w) (g.fourier w)) meromorphic_on A"
  unfolding meromorphic_on_def
proof safe
  fix q assume "q \<in> A"
  hence [simp]: "norm q < 1"
    using assms by auto
  have "(\<lambda>w. h' (f.fourier (q + w)) (g.fourier (q + w))) has_laurent_expansion
          h'' (laurent_expansion f.fourier q) (laurent_expansion g.fourier q)"
    by (intro map_laurent_expansion meromorphic_on_imp_has_laurent_expansion[of _ "{q}"])
       (auto intro!: meromorphic_intros)
  thus "\<exists>L. (\<lambda>w. h' (f.fourier (q + w)) (g.fourier (q + w))) has_laurent_expansion L" ..
qed

lemma eventually_map_fourier_eq:
  "eventually (\<lambda>q. map.fourier q = h' (f.fourier q) (g.fourier q)) (cosparse (ball 0 1))"
  unfolding eventually_cosparse_open_eq[OF open_ball]
proof safe
  fix q :: complex assume q: "q \<in> ball 0 1"
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at q)"
    using q by (intro eventually_at_in_open') auto
  moreover have "eventually (\<lambda>q. q \<noteq> 0) (at q)"
    by (intro eventually_neq_at_within)
  moreover have "eventually (\<lambda>q. \<not>is_pole f.fourier q) (at q)"
  proof -
    have "f.fourier meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. \<not>is_pole g.fourier q) (at q)"
  proof -
    have "g.fourier meromorphic_on {q}"
      by (intro meromorphic_intros) (use q in auto)
    thus ?thesis
      by (simp add: eventually_not_pole meromorphic_on_isolated_singularity)
  qed
  moreover have "eventually (\<lambda>q. (\<lambda>q. h' (f.fourier q) (g.fourier q)) analytic_on {q}) (at q)"
  proof -
    have "(\<lambda>q. h' (f.fourier q) (g.fourier q)) meromorphic_on {q}"
      using q by (auto intro!: meromorphic_intros)
    thus ?thesis
      using isolated_singularity_at_altdef meromorphic_on_isolated_singularity by blast
  qed
  ultimately show "eventually (\<lambda>q. map.fourier q = h' (f.fourier q) (g.fourier q)) (at q)"
    by eventually_elim (use map_fourier_eq_aux in auto)
qed

sublocale fourier_expansion_meromorphic "h f g" period
proof
  have "(\<lambda>q. h' (f.fourier q) (g.fourier q)) meromorphic_on {0}"
    by (intro meromorphic_intros) auto
  also have "?this \<longleftrightarrow> map.fourier meromorphic_on {0}"
    by (intro meromorphic_on_cong)
       (use eventually_map_fourier_eq in \<open>simp_all add: eq_commute eventually_cosparse_open_eq\<close>)
  finally show \<dots> .
qed

lemma map_fourier_eq:
  assumes q: "q \<in> ball 0 1" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q"
  assumes "(\<lambda>q. h' (f.fourier q) (g.fourier q)) analytic_on {q}"
  shows   "map.fourier q = h' (f.fourier q) (g.fourier q)"
proof (cases "q = 0")
  case True
  have "is_pole map.fourier 0 \<longleftrightarrow> is_pole (\<lambda>q. h' (f.fourier q) (g.fourier q)) 0"
    using eventually_map_fourier_eq by (intro is_pole_cong) (auto simp: eventually_cosparse_open_eq)
  also have "\<not>is_pole (\<lambda>q. h' (f.fourier q) (g.fourier q)) 0"
    using assms(4) True by (simp add: analytic_at_imp_no_pole)
  finally have "map.fourier \<midarrow>0\<rightarrow> map.fourier 0"
    unfolding True by (intro isContD analytic_at_imp_isCont analytic_intros) auto
  also have "?this \<longleftrightarrow> (\<lambda>q. h' (f.fourier q) (g.fourier q)) \<midarrow>0\<rightarrow> map.fourier 0"
    using eventually_map_fourier_eq by (intro tendsto_cong) (auto simp: eventually_cosparse_open_eq)
  finally have "(\<lambda>q. h' (f.fourier q) (g.fourier q)) \<midarrow>0\<rightarrow> map.fourier 0" .
  moreover have "(\<lambda>q. h' (f.fourier q) (g.fourier q)) \<midarrow>0\<rightarrow> h' (f.fourier 0) (g.fourier 0)"
    by (intro isContD analytic_at_imp_isCont) (use True assms(4) in auto)
  ultimately show ?thesis
    using LIM_unique True by blast
qed (use map_fourier_eq_aux assms in auto)

lemma map_has_laurent_expansion_at_cusp:
  assumes "f.fourier has_laurent_expansion F" "g.fourier has_laurent_expansion G"
  shows   "map.fourier has_laurent_expansion h'' F G"
proof (subst has_laurent_expansion_cong)
  show "eventually (\<lambda>q. map.fourier q = h' (f.fourier q) (g.fourier q)) (at 0)"
    using eventually_map_fourier_eq unfolding eventually_cosparse_open_eq[OF open_ball] by auto
  show "(\<lambda>q. h' (f.fourier q) (g.fourier q)) has_laurent_expansion h'' F G"
    by (intro map_laurent_expansion assms)
qed auto

end
  



locale fourier_expansion_context =
  fixes period :: nat
  assumes period_pos: "period > 0"
begin

sublocale const: fourier_expansion "const_mero_uhp c" period
  by standard (auto intro: period_pos)

lemma fourier_const [simp]: 
  assumes "norm q < 1"
  shows   "const.fourier c q = c"
proof -
  have *: "const.fourier c q = c" if q: "q \<in> ball 0 1 - {0}" for q
  proof -
    have "Im (cusp_q_inv period q) > 0"
      using assms q by (intro Im_cusp_q_inv_gt) auto
    thus ?thesis using assms period_pos q
      by (auto simp: const.fourier_def)
  qed
  show ?thesis
  proof (cases "q = 0")
    case True
    have "eventually (\<lambda>q. q \<in> ball 0 1 - {0}) (at 0)"
      by (intro eventually_at_in_open) auto
    hence "eventually (\<lambda>q. const.fourier c q = c) (at 0)"
      by eventually_elim (simp_all add: *)
    hence "const.fourier c \<midarrow>0\<rightarrow> c"
      using tendsto_eventually by blast
    thus ?thesis
      using True const.fourier_0_aux const.fourier_tendsto_0_iff by blast
  qed (use *[of q] assms in auto)
qed

lemma not_is_pole_const_fourier [simp]: "\<not>is_pole (const.fourier c) q"
proof (cases "q \<in> ball 0 1")
  case True
  have "eventually (\<lambda>q::complex. q \<in> ball 0 1) (at q)"
    using True by (intro eventually_at_in_open') auto
  hence "eventually (\<lambda>q. const.fourier c q = c) (at q)"
    by eventually_elim auto
  hence "is_pole (const.fourier c) q \<longleftrightarrow> is_pole (\<lambda>_. c) q"
    by (intro is_pole_cong refl) auto
  thus ?thesis by auto
next
  case False
  thus ?thesis
    by (simp add: const.not_pole_eval_fourier_outside)
qed

sublocale const: fourier_expansion_meromorphic "const_mero_uhp c" period
proof
  have "(\<lambda>_. c) holomorphic_on ball 0 1"
    by auto
  also have "?this \<longleftrightarrow> const.fourier c holomorphic_on ball 0 1"
    by (intro holomorphic_cong) auto
  finally have "const.fourier c analytic_on {0}"
    by (rule holomorphic_on_imp_analytic_at) auto
  thus "const.fourier c meromorphic_on {0}"
    by (rule analytic_on_imp_meromorphic_on)
qed

lemma zorder_fourier_0_const [simp]:
  assumes "c \<noteq> 0"
  shows   "zorder (const.fourier c) 0 = 0"
proof (rule zorder_eq_0I)
  show "const.fourier c analytic_on {0}"
    by (auto intro!: analytic_intros)
qed (use assms in auto)

lemma const_fourier_has_fps_expansion [fps_expansion_intros]:
  "const.fourier c has_fps_expansion fps_const c"
proof (subst has_fps_expansion_cong)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (nhds (0 :: complex))"
    by (rule eventually_nhds_in_open) auto
  thus "eventually (\<lambda>q. const.fourier c q = c) (nhds 0)"
    by eventually_elim auto
  show "(\<lambda>_ :: complex. c) has_fps_expansion fps_const c"
    by (intro fps_expansion_intros)
qed auto

lemma const_fourier_has_laurent_expansion [fps_expansion_intros]:
  "const.fourier c has_laurent_expansion fls_const c"
proof (subst has_laurent_expansion_cong)
  have "eventually (\<lambda>q. q \<in> ball 0 1) (at (0 :: complex))"
    by (rule eventually_at_in_open') auto
  thus "eventually (\<lambda>q. const.fourier c q = c) (at 0)"
    by eventually_elim auto
  show "(\<lambda>_ :: complex. c) has_laurent_expansion fls_const c"
    by (intro laurent_expansion_intros)
qed auto

end


lemma zorder_at_cusp_const [simp]: "zorder_at_cusp n (const_mero_uhp c) = 0"
proof (cases "n > 0")
  case True
  interpret fourier_expansion_context n
    by standard fact
  show ?thesis 
  proof (cases "c = 0")
    case [simp]: False
    show ?thesis
    proof (rule zorder_at_cusp_eqI)
      have ev: "eventually (\<lambda>z. Im z > 0) at_cusp"
        by (simp add: eventually_at_cusp)
      have "eval_mero_uhp (const_mero_uhp c) \<in> \<Theta>[at_cusp](\<lambda>z. c)"
        by (intro bigthetaI_cong eventually_mono[OF ev]) auto
      also have "(\<lambda>z. c) \<in> \<Theta>[at_cusp](\<lambda>z. cusp_q 1 z powi 0)"
        by simp
      finally show "eval_mero_uhp (const_mero_uhp c) \<in> \<Theta>[at_cusp](\<lambda>x. cusp_q n x powi 0)"
        by simp
    qed fact
  qed auto
qed (auto simp: zorder_at_cusp_def)


context fourier_expansion
begin

lemma fourier_expansion_inverse: "fourier_expansion (inverse f) period"
  and fourier_expansion_uminus: "fourier_expansion (-f) period"
  and fourier_expansion_power: "fourier_expansion (f ^ n) period"
  and fourier_expansion_power_int: "fourier_expansion (f ^ n) period"
  by unfold_locales (auto intro: period_pos simp: hom_distribs)

end


locale fourier_expansion_pair = fourier_expansion_context period +
   f: fourier_expansion f period + g: fourier_expansion g period
   for f g period
begin

lemma fourier_expansion_add: "fourier_expansion (f + g) period"
  and fourier_expansion_diff: "fourier_expansion (f - g) period"
  and fourier_expansion_mult: "fourier_expansion (f * g) period"
  and fourier_expansion_divide: "fourier_expansion (f / g) period"
  by unfold_locales (auto intro: period_pos simp: hom_distribs)

end



context fourier_expansion_meromorphic
begin

interpretation minus: fourier_unop_meromorphic f period "\<lambda>x. -x" "\<lambda>x. -x" "\<lambda>x. -x"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_minus: "fourier_expansion_meromorphic (-f) period" ..
lemmas fourier_minus_eventually_eq = minus.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_minus = minus.map_has_laurent_expansion_at_cusp

lemma fourier_minus_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole fourier q"
  shows   "minus.map.fourier q = - fourier q"
  by (rule minus.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_minus_eq:
  assumes "q \<in> ball 0 1 - {0}"
  shows   "zorder (minus.map.fourier) q = zorder fourier q"
proof -
  have "zorder minus.map.fourier q = zorder (\<lambda>q. -1 * fourier q) q"
    using fourier_minus_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder fourier q"
    by (intro zorder_cmult) auto
  finally show ?thesis .
qed



interpretation cmult_left: fourier_unop_meromorphic f period "\<lambda>x. const_mero_uhp c * x" "\<lambda>x. c * x" "\<lambda>x. fls_const c * x"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_cmult_left: "fourier_expansion_meromorphic (const_mero_uhp c * f) period" ..
lemmas fourier_cmult_left_eventually_eq = cmult_left.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_cmult_left = cmult_left.map_has_laurent_expansion_at_cusp

lemma fourier_cmult_left_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole fourier q"
  shows   "cmult_left.map.fourier c q = c * fourier q"
  by (rule cmult_left.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_cmult_left_eq:
  assumes "q \<in> ball 0 1 - {0}" "c \<noteq> 0"
  shows   "zorder (cmult_left.map.fourier c) q = zorder fourier q"
proof -
  have "zorder (cmult_left.map.fourier c) q = zorder (\<lambda>q. c * fourier q) q"
    using fourier_cmult_left_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder fourier q"
    using assms by (intro zorder_cmult) auto
  finally show ?thesis .
qed



interpretation cmult_right: fourier_unop_meromorphic f period "\<lambda>x. x * const_mero_uhp c" "\<lambda>x. x * c" "\<lambda>x. x * fls_const c"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_cmult_right: "fourier_expansion_meromorphic (const_mero_uhp c * f) period" ..
lemmas fourier_cmult_right_eventually_eq = cmult_right.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_cmult_right = cmult_right.map_has_laurent_expansion_at_cusp

lemma fourier_cmult_right_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole fourier q"
  shows   "cmult_right.map.fourier c q = fourier q * c"
  by (rule cmult_right.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_cmult_right_eq:
  assumes "q \<in> ball 0 1 - {0}" "c \<noteq> 0"
  shows   "zorder (cmult_right.map.fourier c) q = zorder fourier q"
proof -
  have "zorder (cmult_right.map.fourier c) q = zorder (\<lambda>q. fourier q * c) q"
    using fourier_cmult_right_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder fourier q"
    by (subst mult.commute, intro zorder_cmult) (use assms in auto)
  finally show ?thesis .
qed


interpretation inverse: fourier_unop_meromorphic f period inverse inverse inverse
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_inverse: "fourier_expansion_meromorphic (inverse f) period" ..
lemmas fourier_inverse = inverse.map_fourier_eq
lemmas fourier_inverse_eventually_eq = inverse.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_inverse = inverse.map_has_laurent_expansion_at_cusp

lemma fourier_inverse_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole fourier q" "fourier q \<noteq> 0"
  shows   "inverse.map.fourier q = inverse (fourier q)"
  by (rule inverse.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_inverse_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (inverse.map.fourier) q = -zorder fourier q"
proof -
  have "zorder inverse.map.fourier q = zorder (\<lambda>q. inverse (fourier q)) q"
    using fourier_inverse_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = -zorder fourier q"
  proof (rule zorder_inverse) 
    show "\<exists>\<^sub>F q in at q. fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_on_isolated_singularity 
                       meromorphic_on_not_essential meromorphic_intros\<close>)
  finally show ?thesis .
qed


interpretation power: fourier_unop_meromorphic f period "\<lambda>x. x ^ n" "\<lambda>x. x ^ n" "\<lambda>x. x ^ n"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_power: "fourier_expansion_meromorphic (f ^ n) period" ..
lemmas fourier_power_eventually_eq = power.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_power = power.map_has_laurent_expansion_at_cusp

lemma fourier_power_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole fourier q"
  shows   "power.map.fourier n q = fourier q ^ n"
  by (rule power.map_fourier_eq[OF assms]) (use assms in \<open>auto intro!: analytic_intros\<close>)


interpretation power_int: fourier_unop_meromorphic f period "\<lambda>x. x powi n" "\<lambda>x. x powi n" "\<lambda>x. x powi n"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_power_int: "fourier_expansion_meromorphic (f powi n) period" ..
lemmas fourier_power_int_eventually_eq = power_int.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_power_int = power_int.map_has_laurent_expansion_at_cusp

lemma zorder_fourier_power_int_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (power_int.map.fourier n) q = n * zorder fourier q"
proof -
  have "zorder (power_int.map.fourier n) q = zorder (\<lambda>q. fourier q powi n) q"
    using fourier_power_int_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = n * zorder fourier q"
  proof (rule zorder_power_int) 
    show "\<exists>\<^sub>F q in at q. fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_power_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0"
  shows   "zorder (power.map.fourier n) q = n * zorder fourier q"
  using zorder_fourier_power_int_eq[OF assms, of "int n"] by simp

end



locale fourier_expansion_meromorphic_pair =
   f: fourier_expansion_meromorphic f period + g: fourier_expansion_meromorphic g period
   for f g period
begin

sublocale add: fourier_binop_meromorphic f g period "(+)" "(+)" "(+)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_add: "fourier_expansion_meromorphic (f + g) period" ..
lemmas fourier_add_eventually_eq = add.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_add = add.map_has_laurent_expansion_at_cusp

lemma fourier_add_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q"
  shows   "add.map.fourier q = f.fourier q + g.fourier q"
  by (rule add.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_add_eq1:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f.fourier q < zorder g.fourier q"
  shows   "zorder add.map.fourier q = zorder f.fourier q"
proof -
  have "zorder add.map.fourier q = zorder (\<lambda>q. f.fourier q + g.fourier q) q"
    using fourier_add_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f.fourier q"
  proof (rule zorder_add1) 
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_add_eq2:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f.fourier q > zorder g.fourier q"
  shows   "zorder add.map.fourier q = zorder g.fourier q"
proof -
  have "zorder add.map.fourier q = zorder (\<lambda>q. f.fourier q + g.fourier q) q"
    using fourier_add_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder g.fourier q"
  proof (rule zorder_add2) 
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale diff: fourier_binop_meromorphic f g period "(-)" "(-)" "(-)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_diff: "fourier_expansion_meromorphic (f - g) period" ..
lemmas fourier_diff_eventually_eq = diff.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_diff = diff.map_has_laurent_expansion_at_cusp

lemma fourier_diff_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q"
  shows   "diff.map.fourier q = f.fourier q - g.fourier q"
  by (rule diff.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_diff_eq1:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f.fourier q < zorder g.fourier q"
  shows   "zorder diff.map.fourier q = zorder f.fourier q"
proof -
  have "zorder diff.map.fourier q = zorder (\<lambda>q. f.fourier q - g.fourier q) q"
    using fourier_diff_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f.fourier q"
  proof (rule zorder_diff1) 
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

lemma zorder_fourier_diff_eq2:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0" "zorder f.fourier q > zorder g.fourier q"
  shows   "zorder diff.map.fourier q = zorder g.fourier q"
proof -
  have "zorder diff.map.fourier q = zorder (\<lambda>q. f.fourier q - g.fourier q) q"
    using fourier_diff_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder g.fourier q"
  proof (rule zorder_diff2) 
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale mult: fourier_binop_meromorphic f g period "(*)" "(*)" "(*)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_mult: "fourier_expansion_meromorphic (f * g) period" ..
lemmas fourier_mult_eventually_eq = mult.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_mult = mult.map_has_laurent_expansion_at_cusp

lemma fourier_mult_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q"
  shows   "mult.map.fourier q = f.fourier q * g.fourier q"
  by (rule mult.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>)

lemma zorder_fourier_mult_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0"
  shows   "zorder mult.map.fourier q = zorder f.fourier q + zorder g.fourier q"
proof -
  have "zorder mult.map.fourier q = zorder (\<lambda>q. f.fourier q * g.fourier q) q"
    using fourier_mult_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f.fourier q + zorder g.fourier q"
  proof (rule zorder_mult) 
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed


sublocale divide: fourier_binop_meromorphic f g period "(/)" "(/)" "(/)"
  by standard (mero_uhp_rel, auto intro!: meromorphic_intros laurent_expansion_intros simp: hom_distribs)
lemma fourier_expansion_meromorphic_divide: "fourier_expansion_meromorphic (f / g) period" ..
lemmas fourier_divide_eventually_eq = divide.eventually_map_fourier_eq
lemmas has_laurent_expansion_at_cusp_divide = divide.map_has_laurent_expansion_at_cusp

lemma fourier_divide_eq:
  assumes "q \<in> ball 0 1" "\<not>is_pole f.fourier q" "\<not>is_pole g.fourier q" "g.fourier q \<noteq> 0"
  shows   "divide.map.fourier q = f.fourier q / g.fourier q"
  by (rule divide.map_fourier_eq[OF assms(1-2)]) (use assms in \<open>auto intro!: analytic_intros\<close>) 

lemma zorder_fourier_divide_eq:
  assumes "q \<in> ball 0 1" "f \<noteq> 0" "g \<noteq> 0"
  shows   "zorder divide.map.fourier q = zorder f.fourier q - zorder g.fourier q"
proof -
  have "zorder divide.map.fourier q = zorder (\<lambda>q. f.fourier q / g.fourier q) q"
    using fourier_divide_eventually_eq assms
    by (intro zorder_cong refl) (auto simp: eventually_cosparse_open_eq)
  also have "\<dots> = zorder f.fourier q - zorder g.fourier q"
  proof (rule zorder_divide)
    show "\<exists>\<^sub>F q in at q. f.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently f.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
    show "\<exists>\<^sub>F q in at q. g.fourier q \<noteq> 0" using assms
      by (metis Diff_iff assms at_neq_bot eventually_frequently g.eventually_neq_fourier
                mem_ball_0 zero_mero_uhp_def)
  qed (use assms in \<open>auto intro!: meromorphic_intros\<close>)
  finally show ?thesis .
qed

end
  
end
