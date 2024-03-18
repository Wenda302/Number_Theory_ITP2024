section \<open>Expanding complex functions in terms of $q = \exp(2i\pi z)$\<close>
theory Fourier_Expansion
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Real_Asymp.Real_Asymp"
  Library_Extras
  More_Trigonometric
  Meromorphic_Extras
  Meromorphic_Upper_Half_Plane
begin

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

definition cusp_q :: "complex \<Rightarrow> complex" where
  "cusp_q \<tau> = exp (2 * pi * \<i> * \<tau>)"

interpretation cusp_q: periodic_fun_simple' cusp_q
proof
  show "cusp_q (z + 1) = cusp_q z" for z
    by (simp add: cusp_q_def ring_distribs exp_add)
qed

lemma Ln_cusp_q:
  assumes "x\<in>Re -` {-1/2<..1/2}" 
  shows "Ln (cusp_q x) = 2 * pi * \<i> * x"
unfolding cusp_q_def 
proof (rule Ln_exp)
  have "-1/2<Re x" "Re x \<le> 1/2" 
    using assms by auto
  from this(1)
  have "- pi < pi * (Re x * 2)" 
    by (metis divide_less_eq_numeral1(1) mult_less_cancel_left_pos 
        mult_minus1_right pi_gt_zero)
  then show "- pi < Im (complex_of_real (2 * pi) * \<i> * x)" by simp

  show "Im (complex_of_real (2 * pi) * \<i> * x) \<le> pi"
    using \<open>Re x \<le> 1/2\<close> by simp
qed

lemma cusp_q_nonzero [simp]: "cusp_q \<tau> \<noteq> 0"
  by (auto simp: cusp_q_def)

lemma norm_cusp_q [simp]: "norm (cusp_q z) = exp (-2 * pi * Im z)"
  by (simp add: cusp_q_def)

lemma cusp_q_has_field_derivative [derivative_intros]:
  assumes [derivative_intros]: "(f has_field_derivative f') (at z)"
  shows   "((\<lambda>z. cusp_q (f z)) has_field_derivative (2 * pi * \<i> * f' * cusp_q (f z))) (at z)"
  unfolding cusp_q_def by (rule derivative_eq_intros refl)+ simp  

lemma deriv_cusp_q [simp]: "deriv cusp_q z = 2 * pi * \<i> * cusp_q z"
  by (auto intro!: DERIV_imp_deriv derivative_eq_intros)

lemma cusp_q_holomorphic_on [holomorphic_intros]:
  "f holomorphic_on A \<Longrightarrow> (\<lambda>z. cusp_q (f z)) holomorphic_on A"
  unfolding cusp_q_def by (intro holomorphic_intros)

lemma cusp_q_analytic_on [analytic_intros]:
  "f analytic_on A \<Longrightarrow> (\<lambda>z. cusp_q (f z)) analytic_on A"
  unfolding cusp_q_def by (intro analytic_intros)

lemma cusp_q_continuous_on [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>z. cusp_q (f z))"
  unfolding cusp_q_def by (intro continuous_intros)

lemma cusp_q_continuous [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>z. cusp_q (f z))"
  unfolding cusp_q_def by (intro continuous_intros)

lemma cusp_q_tendsto [tendsto_intros]:
  "(f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>z. cusp_q (f z)) \<longlongrightarrow> cusp_q x) F"
  unfolding cusp_q_def by (intro tendsto_intros)

lemma cusp_q_eq_cusp_qE:
  assumes "cusp_q \<tau> = cusp_q \<tau>'"
  obtains n where "\<tau>' = \<tau> + of_int n"
proof -
  from assms obtain n where "2 * pi * \<i> * \<tau> = 2 * pi * \<i> * \<tau>' + real_of_int (2 * n) * pi * \<i>"
    using assms unfolding cusp_q_def exp_eq by blast
  also have "\<dots> = 2 * pi * \<i> * (\<tau>' + of_int n)"
    by (simp add: algebra_simps)
  finally have "\<tau> = \<tau>' + of_int n"
    by (subst (asm) mult_cancel_left) auto
  thus ?thesis
    by (intro that[of "-n"]) auto
qed

lemma cusp_q_inj_on_standard:
  "inj_on cusp_q (Re -` {-1/2..<1/2})"
  unfolding inj_on_def
proof safe+
  fix x y::complex
  assume eq:"cusp_q x = cusp_q y" 
      and xRe:"Re x \<in> {- 1 / 2..<1 / 2}" and yRe:"Re y \<in> {- 1 / 2..<1 / 2}"
  obtain rx ix where x:"x=Complex rx ix" by (meson complex.exhaust_sel)
  obtain ry iy where y:"y=Complex ry iy" by (meson complex.exhaust_sel)
  define pp where "pp= 2*pi"
  have rxry:"rx\<in>{-1/2..<1/2}" "ry\<in>{-1/2..<1/2}" 
    using xRe yRe x y by auto

  define prx where "prx = pp*rx"
  define pry where "pry = pp*ry"

  have coseq:"exp (- (pp * ix)) * cos prx 
        = exp (- (pp * iy)) * cos pry"
  proof -
    have "Re (cusp_q x) = Re (cusp_q y)"
      using eq by simp
    then show ?thesis
      unfolding x y cusp_q_def Re_exp Im_exp pp_def prx_def pry_def
      by simp 
  qed
  moreover have sineq:"exp (- (pp * ix)) * sin prx 
        = exp (- (pp * iy)) * sin pry"
  proof -
    have "Im (cusp_q x) = Im (cusp_q y)"
      using eq by simp
    then show ?thesis
      unfolding x y cusp_q_def Re_exp Im_exp pp_def prx_def pry_def
      by simp
  qed
  ultimately have "(exp (- (pp * ix)) * sin (prx))
    / (exp (- (pp * ix)) * cos (prx))
    = (exp (- (pp * iy)) * sin (pry))
    / (exp (- (pp * iy)) * cos (pry))"
    by auto
  then have teq:"tan prx  = tan pry"
    apply (subst (asm) (1 2) mult_divide_mult_cancel_left)
    unfolding tan_def by auto

  have sgn_eq_cos:"sgn (cos (prx)) = sgn (cos (pry))" 
  proof -
    have "sgn (exp (- (pp * ix)) * cos prx) 
        = sgn (exp (- (pp * iy)) * cos pry)"
      using coseq by simp
    then show ?thesis by (simp add:sgn_mult)
  qed
  have sgn_eq_sin:"sgn (sin (prx)) = sgn (sin (pry))" 
  proof -
    have "sgn (exp (- (pp * ix)) * sin prx) 
        = sgn (exp (- (pp * iy)) * sin pry)"
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
      then have "rx=real_of_int k0/4" 
        unfolding pp_def prx_def by auto
      with rxry have "k0\<in>{-2,-1,0,1}"
        by auto
      then show ?thesis using k0 pi2_def by auto
    qed
    moreover have "pry\<in>{-pi,-pi2,0,pi2}" 
    proof -
      from tan_eq_0_Ex that teq
      obtain k0 where k0:"pry = real_of_int k0 / 2 * pi"
        by auto
      then have "ry=real_of_int k0/4" 
        unfolding pp_def pry_def by auto
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
    then have "pi * (2* rx) = pi* (2 * ry + real_of_int k0)"
      unfolding pp_def prx_def pry_def by (auto simp:algebra_simps)
    then have "real_of_int k0 = 2 * (rx - ry)" 
      apply (subst (asm) mult_left_cancel)
      by auto
    also have "... \<in> {-2<..<2}"
      using rxry by simp
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
  then have "rx = ry" unfolding prx_def pry_def pp_def by auto
  moreover have "ix = iy"
  proof - 
    have "cos prx \<noteq>0 \<or>  sin prx\<noteq>0"
      using sin_zero_norm_cos_one by force 
    then have "exp (- (pp * ix))  = exp (- (pp * iy))"
      using coseq sineq \<open>prx = pry\<close> by auto
    then show "ix= iy" unfolding pp_def by auto
  qed
  ultimately show "x=y" unfolding x y by auto
qed

lemma filterlim_cusp_q_at_cusp' [tendsto_intros]: "filterlim cusp_q (nhds 0) at_cusp"
proof -
  have "((\<lambda>z. exp (- (2 * pi * Im z))) \<longlongrightarrow> 0) at_cusp"
    unfolding at_cusp_def 
    by (rule filterlim_compose[OF _ filterlim_filtercomap]) real_asymp
  hence "filterlim (\<lambda>z. norm (cusp_q z)) (nhds 0) at_cusp"
    by (simp add: cusp_q_def)
  thus ?thesis
    using tendsto_norm_zero_iff by blast
qed

lemma filterlim_cusp_q_at_cusp [tendsto_intros]: "filterlim cusp_q (at 0) at_cusp"
  using filterlim_cusp_q_at_cusp' by (auto simp: filterlim_at)  

lemma eventually_cusp_q_neq: "eventually (\<lambda>w. cusp_q w \<noteq> cusp_q z) (at z)"
proof -
  have "eventually (\<lambda>w. w \<in> ball z 1 - {z}) (at z)"
    by (intro eventually_at_in_open) auto
  thus ?thesis
  proof eventually_elim
    case (elim w)
    show ?case
    proof
      assume "cusp_q w = cusp_q z"
      then obtain n where eq: "z = w + of_int n"
        by (elim cusp_q_eq_cusp_qE)
      with elim show False
        by (auto simp: dist_norm)
    qed
  qed
qed


lemma inj_on_cusp_q: "inj_on cusp_q (ball z (1/2))"
proof
  fix x y assume xy: "x \<in> ball z (1/2)" "y \<in> ball z (1/2)" "cusp_q x = cusp_q y"
  from xy have "dist x z < 1 / 2" "dist y z < 1 / 2"
    by (auto simp: dist_commute)
  hence "dist x y < 1 / 2 + 1 / 2"
    using dist_triangle_less_add by blast
  moreover from xy obtain n where n: "y = x + of_int n"
    by (elim cusp_q_eq_cusp_qE)
  ultimately show "x = y"
    by (auto simp: dist_norm)
qed

lemma filtermap_cusp_q_nhds: "filtermap cusp_q (nhds z) = nhds (cusp_q z)"
proof (rule filtermap_nhds_open_map')
  show "open (ball z (1 / 2))" "z \<in> ball z (1 / 2)" "isCont cusp_q z"
    by (auto intro!: continuous_intros)
  show "open (cusp_q ` S)" if "open S" "S \<subseteq> ball z (1 / 2)" for S
  proof (rule open_mapping_thm3)
    show "inj_on cusp_q S"
      using that by (intro inj_on_subset[OF inj_on_cusp_q])
  qed (use that in \<open>auto intro!: holomorphic_intros\<close>)
qed

lemma filtermap_cusp_q_at: "filtermap cusp_q (at z) = at (cusp_q z)"
  using filtermap_cusp_q_nhds
proof (rule filtermap_nhds_eq_imp_filtermap_at_eq)
  show "eventually (\<lambda>x. cusp_q x = cusp_q z \<longrightarrow> x = z) (at z)"
    using eventually_cusp_q_neq[of z] by eventually_elim auto
qed

lemma is_pole_cusp_q_iff:
  "is_pole f (cusp_q x) \<longleftrightarrow> is_pole (f o cusp_q) x"
proof -
  have "filtermap f (at (cusp_q x)) 
          = filtermap f (filtermap cusp_q (at x)) "
    unfolding filtermap_cusp_q_at by simp
  also have "... = filtermap (f \<circ> cusp_q) (at x)"
    unfolding filtermap_filtermap unfolding comp_def by simp
  finally show ?thesis unfolding is_pole_def filterlim_def by simp
qed

definition cusp_q_inv :: "complex \<Rightarrow> complex" where
  "cusp_q_inv q = ln q / (2 * pi * \<i>)"

lemma Im_cusp_q_inv: "q \<noteq> 0 \<Longrightarrow> Im (cusp_q_inv q) = -ln (norm q) / (2 * pi)"
  by (simp add: cusp_q_inv_def Im_divide power2_eq_square)

lemma Im_cusp_q_inv_gt:
  assumes "norm q < exp (-2 * pi * c)" "q \<noteq> 0"
  shows   "Im (cusp_q_inv q) > c"
proof -
  have "-Im (cusp_q_inv q) = ln (norm q) / (2 * pi)"
    using assms by (subst Im_cusp_q_inv) auto
  also have "ln (norm q) < ln (exp (-2 * pi * c))"
    by (subst ln_less_cancel_iff) (use assms in auto)
  hence "ln (norm q) / (2 * pi) < ln (exp (-2 * pi * c)) / (2 * pi)"
    by (intro divide_strict_right_mono) auto
  also have "\<dots> = -c"
    by simp
  finally show ?thesis
    by simp
qed

lemma cusp_q_cusp_q_inv [simp]: "q \<noteq> 0 \<Longrightarrow> cusp_q (cusp_q_inv q) = q"
  by (simp add: cusp_q_def cusp_q_inv_def)

lemma cusp_q_inv_cusp_q: "\<exists>n. cusp_q_inv (cusp_q \<tau>) = \<tau> + of_int n"
proof
  show "cusp_q_inv (cusp_q \<tau>) = \<tau> + of_int (-unwinding (complex_of_real (2 * pi) * \<i> * \<tau>))"
    using unwinding[of "2 * pi * \<i> * \<tau>"]
    by (simp add: cusp_q_inv_def cusp_q_def field_simps)
qed

lemma filterlim_norm_at_0: "filterlim norm (at_right 0) (at 0)"
  unfolding filterlim_at
  by (auto simp: eventually_at tendsto_norm_zero_iff intro: exI[of _ 1])

lemma filterlim_cusp_q_inv_at_0: "filterlim cusp_q_inv at_cusp (at 0)"
proof -
  have "filterlim (\<lambda>q. -ln (norm q) / (2 * pi)) at_top (at 0)"
    by (rule filterlim_compose[OF _ filterlim_norm_at_0]) real_asymp
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. -ln (norm q) / (2 * pi) = Im (cusp_q_inv q)) (at 0)"
    by eventually_elim (simp add: Im_cusp_q_inv)
  hence "filterlim (\<lambda>q::complex. -ln (norm q) / (2 * pi)) at_top (at 0) \<longleftrightarrow>
         filterlim (\<lambda>q. Im (cusp_q_inv q)) at_top (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    by (simp add: at_cusp_def filterlim_filtercomap_iff o_def)
qed

lemma at_cusp_filtermap: "filtermap cusp_q at_cusp = at 0"
  by (rule filtermap_fun_inverse[OF 
           filterlim_cusp_q_inv_at_0 filterlim_cusp_q_at_cusp])
     (simp add: eventually_at_filter)

lemma eventually_at_cusp_cusp_q:
  "eventually P (at 0) = (\<forall>\<^sub>F x in at_cusp. P (cusp_q x))"
proof -
  have "(\<forall>\<^sub>F x in at_cusp. P (cusp_q x)) \<longleftrightarrow> (\<forall>\<^sub>F x in filtermap cusp_q at_cusp. P x)"
    by (simp add: eventually_filtermap)
  also have "\<dots> \<longleftrightarrow> eventually P (at 0)"
    by (simp add: at_cusp_filtermap)
  finally show ?thesis ..
qed

lemma cusp_q_inv_tendsto:
  assumes "x\<in>Re -` {-1/2<..<1/2}"
  shows "cusp_q_inv \<midarrow>cusp_q x\<rightarrow> x"
proof -
  obtain rx ix where x:"x = Complex rx ix" 
    using complex.exhaust_sel by blast
  have "Re (cusp_q x) > 0" if "Im (cusp_q x) = 0" 
  proof -
    have "sin (2 * pi * rx) = 0" 
      using that unfolding cusp_q_def x Im_exp Re_exp by simp
    then obtain k where k:"2 * rx = real_of_int k "
      unfolding sin_zero_iff_int2 by auto
    moreover have "2*rx \<in> {-1<..<1}"
      using assms unfolding x by simp
    ultimately have "k=0" by auto
    then have "rx=0" using k by auto
    then show ?thesis unfolding cusp_q_def x
      using Re_exp by simp
  qed
  then have "cusp_q x \<notin> \<real>\<^sub>\<le>\<^sub>0" 
    unfolding complex_nonpos_Reals_iff
    unfolding Im_exp Re_exp cusp_q_def
    by (auto simp add: complex_nonpos_Reals_iff)
  moreover have "Ln (cusp_q x) / (2 * complex_of_real pi * \<i>) = x" 
    apply (subst Ln_cusp_q)
    using assms by auto
  ultimately show "cusp_q_inv \<midarrow>cusp_q x\<rightarrow> x"
    unfolding cusp_q_inv_def by (auto intro!: tendsto_eq_intros )
qed

lemma cusp_q_inv_cusp_q_Re:
  assumes "x\<in>Re -` {-1/2<..1/2}"
  shows "cusp_q_inv (cusp_q x) = x"
proof -
  have "- pi < Im (complex_of_real (2 * pi) * \<i> * x)"
  proof -
    have "pi* (-1/2) < pi * Re x" 
      apply (rule mult_strict_left_mono)
      using assms by auto
    then show ?thesis by auto
  qed
  moreover have "Im (complex_of_real (2 * pi) * \<i> * x) \<le> pi"
    using assms by auto
  ultimately show ?thesis
    unfolding cusp_q_def cusp_q_inv_def
    by (subst Ln_exp) auto
qed


bundle cusp_notation
begin
notation cusp_q ("\<q>")
end

bundle no_cusp_notation
begin
no_notation cusp_q ("\<q>")
end


subsection \<open>Functions that are invariant under a shift of 1\<close>

locale periodic_mero_uhp = periodic_fun_simple "eval_mero_uhp f" "of_nat period"
  for f :: mero_uhp and period :: nat +
  assumes period_pos: "period > 0"
begin

abbreviation cusp_q' ("\<q>") where "\<q> \<equiv> cusp_q period"

term cusp_q_inv

definition fourier :: "complex \<Rightarrow> complex" where
  "fourier q = (if q = 0 then Lim at_cusp f else f (cusp_q_inv period q))"

lemma fourier_nz_eq: "q \<noteq> 0 \<Longrightarrow> fourier q = f (cusp_q_inv q)"
  by (simp add: fourier_def)

definition zorder_at_cusp :: int where
  "zorder_at_cusp = fls_subdegree (laurent_expansion fourier 0)"

lemma fourier_0_aux:
  assumes "(f \<longlongrightarrow> y) at_cusp"
  shows   "fourier 0 = y"
proof -
  have "Lim at_cusp f = y"
    using assms by (intro tendsto_Lim) auto
  thus ?thesis
    by (simp add: fourier_def)
qed

lemma isCont_0_aux:
  assumes "(f \<longlongrightarrow> y) at_cusp"
  shows   "isCont fourier 0"
proof -
  have "((\<lambda>q. f (cusp_q_inv q)) \<longlongrightarrow> y) (at 0)"
    by (rule filterlim_compose[OF assms filterlim_cusp_q_inv_at_0])
  also have "eventually (\<lambda>q::complex. q \<noteq> 0) (at 0)"
    by (auto simp: eventually_at intro: exI[of _ 1])
  hence "eventually (\<lambda>q. f (cusp_q_inv q) = fourier q) (at 0)"
    by eventually_elim (auto simp: fourier_def)
  hence "((\<lambda>q. f (cusp_q_inv q)) \<longlongrightarrow> y) (at 0) \<longleftrightarrow> (fourier \<longlongrightarrow> y) (at 0)"
    by (intro filterlim_cong) auto
  finally show ?thesis
    using assms by (simp add: isCont_def fourier_0_aux)
qed

lemma fourier_cusp_q [simp]: 
  assumes "Im \<tau> > c0"
  shows   "fourier (cusp_q \<tau>) = f \<tau>"
proof -
  obtain n where n: "cusp_q_inv (cusp_q \<tau>) = \<tau> + of_int n"
    using cusp_q_inv_cusp_q by blast
  show ?thesis using assms
    by (simp add: fourier_def n plus_of_int)
qed

lemma fourier_tendsto_0_iff: "fourier \<midarrow>0\<rightarrow> y \<longleftrightarrow> (f \<longlongrightarrow> y) at_cusp"
proof
  assume "(f \<longlongrightarrow> y) at_cusp"
  thus "fourier \<midarrow>0\<rightarrow> y"
    using continuous_within isCont_0_aux fourier_0_aux by blast
next
  assume *: "fourier \<midarrow>0\<rightarrow> y"
  have "((\<lambda>z. fourier (cusp_q z)) \<longlongrightarrow> y) at_cusp"
    by (rule filterlim_compose[OF * filterlim_cusp_q_at_cusp])
  moreover have "eventually (\<lambda>z. Im z > c0) at_cusp"
    by (rule eventually_at_cusp)
  hence "eventually (\<lambda>z. fourier (cusp_q z) = f z) at_cusp"
    by eventually_elim auto
  ultimately show "(f \<longlongrightarrow> y) at_cusp"
    using Lim_transform_eventually by blast
qed

lemma fourier_is_pole_0_iff:
  "is_pole fourier 0 \<longleftrightarrow> (LIM x at_cusp. f x :> at_infinity)" 
proof -
  have "is_pole fourier 0 \<longleftrightarrow> (LIM q at 0. f (cusp_q_inv q) :> at_infinity)"
    unfolding is_pole_def fourier_def
    by (rule filterlim_cong) (auto simp add: linordered_field_no_ub eventually_at)
  also have "... \<longleftrightarrow> (LIM x at_cusp. f x :> at_infinity)"
  proof
    assume "LIM q at 0. f (cusp_q_inv q) :> at_infinity"
    from filterlim_compose[OF this filterlim_cusp_q_at_cusp] 
    have "LIM x at_cusp. f (cusp_q_inv (cusp_q x)) :> at_infinity" .
    then show "filterlim f at_infinity at_cusp"
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in at_cusp. f (cusp_q_inv (cusp_q x)) = f x"
        by (smt (verit, ccfv_threshold) cusp_q_inv_cusp_q
            eventually_at_cusp eventually_mono plus_of_int)
    qed auto
  next
    assume "filterlim f at_infinity at_cusp "
    from filterlim_compose[OF this filterlim_cusp_q_inv_at_0]
    show "LIM x at 0. f (cusp_q_inv x) :> at_infinity" .
  qed
  finally show ?thesis .
qed

lemma fourier_is_pole_cusp_q_iff:
  assumes "Im z > c0"
  shows   "is_pole fourier (cusp_q z) \<longleftrightarrow> is_pole f z"
proof -
  have "is_pole f z \<longleftrightarrow> is_pole (fourier \<circ> cusp_q) z"
  proof (rule is_pole_cong)
    have "eventually (\<lambda>w. w \<in> {w. Im w > c0}) (at z)"
      by (intro eventually_at_in_open' open_halfspace_Im_gt) (use assms in auto)
    thus "eventually (\<lambda>w. f w = (fourier \<circ> cusp_q) w) (at z)"
      by eventually_elim (auto simp: fourier_cusp_q)
  qed auto
  also have "\<dots> \<longleftrightarrow> is_pole fourier (cusp_q z)"
    by (rule is_pole_compose_iff) (simp_all add: filtermap_cusp_q_at)
  finally show ?thesis ..
qed

lemma has_field_derivative_fourier:
  assumes "Im z > c0"
  assumes f: "(f has_field_derivative f') (at z)"
  assumes q: "q = cusp_q z"
  shows   "(fourier has_field_derivative f' / (2 * pi * \<i> * q)) (at q)"
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

  have "((f \<circ> (\<lambda>q. myln q / (2 * pi * \<i>))) has_field_derivative f' * (1 / (2 * pi * \<i> * q))) (at q)"
  proof (rule DERIV_chain)
    define z' where "z' = myln q / (complex_of_real (2 * pi) * \<i>)"
    have "cusp_q z = cusp_q z'"
      using exp_myln[of q] q r(1) by (simp add: z'_def cusp_q_def)
    then obtain n where n: "z' = z + of_int n"
      using cusp_q_eq_cusp_qE by blast
    have "Im z' > c0"
      by (simp add: n assms)

    have "((f \<circ> (\<lambda>w. w + z - z')) has_field_derivative f' * 1) (at z')"
      using f by (intro DERIV_chain) (auto intro!: derivative_eq_intros)
    also have "(\<lambda>w. w + z - z') = (\<lambda>w. w - of_int n)"
      using n by (auto simp: fun_eq_iff)
    also have "(f \<circ> (\<lambda>w. w - of_int n) has_field_derivative f' * 1) (at z') \<longleftrightarrow>
               (f has_field_derivative f') (at z')"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>w. w \<in> {w. Im w > c0}) (nhds z')"
        using \<open>Im z' > c0\<close> by (intro eventually_nhds_in_open open_halfspace_Im_gt) auto
      thus "eventually (\<lambda>w. (f \<circ> (\<lambda>w. w - of_int n)) w = f w) (nhds z')"
        by eventually_elim (auto simp: minus_of_int)
    qed auto
    finally show "(f has_field_derivative f') (at z')"
      by simp
  next
    show "((\<lambda>q. myln q / (complex_of_real (2 * pi) * \<i>)) 
            has_field_derivative (1 / (2 * pi * \<i> * q))) (at q)"
      by (auto intro!: derivative_eq_intros)
  qed

  also have "?this \<longleftrightarrow> ?thesis"
  proof (rule DERIV_cong_ev)
    have "eventually (\<lambda>w. w \<in> ball q r \<inter> ball 0 (exp (-2 * pi * c0)) - {0}) (nhds q)"
      using assms \<open>r > 0\<close> by (intro eventually_nhds_in_open) auto
    thus "eventually (\<lambda>x. (f \<circ> (\<lambda>q. myln q / (complex_of_real (2 * pi) * \<i>))) x = fourier x) (nhds q)"
    proof eventually_elim
      case (elim q')
      define z' where "z' = myln q' / (2 * complex_of_real pi * \<i>)"
      have "cusp_q z' = q'"
        using elim r by (simp add: z'_def exp_myln cusp_q_def)
      hence "cusp_q (cusp_q_inv q') = cusp_q z'"
        using elim by simp
      then obtain n where n: "z' = cusp_q_inv q' + of_int n"
        using cusp_q_eq_cusp_qE[of "cusp_q_inv q'" z'] by blast
      have Im: "Im (cusp_q_inv q') > c0"
        using elim by (auto simp: Im_cusp_q_inv \<open>cusp_q z' = q'\<close> [symmetric])

      have "(f \<circ> (\<lambda>q. myln q / (complex_of_real (2 * pi) * \<i>))) q' = f z'"
        using n by (simp add: z'_def cusp_q_inv_def)
      also have "\<dots> = fourier q'"
        using elim Im by (simp add: plus_of_int n fourier_def)
      finally show ?case .
    qed
  qed auto
  finally show ?thesis .
qed

lemma eventually_fourier_cusp_q_eq: "eventually (\<lambda>z. fourier (cusp_q z) = f z) at_cusp"
proof -
  have "eventually (\<lambda>z. Im z > c0) at_cusp"
    by (simp add: eventually_at_cusp)
  thus "eventually (\<lambda>z. fourier (cusp_q z) = f z) at_cusp"
    by eventually_elim auto
qed

lemma isolated_zero_plus1:
  assumes "Im z > c0"
  shows   "isolated_zero f (z + 1) \<longleftrightarrow> isolated_zero f z"
proof -
  have *: "at (z + 1) = filtermap ((+) 1) (at z)"
    by (simp add: at_to_0' add_ac filtermap_filtermap)
  have "eventually (\<lambda>w. w \<in> {w. Im w > c0}) (at z)"
    using assms by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
  hence "(\<forall>\<^sub>F z in at z. f z \<noteq> 0) \<longleftrightarrow> (\<forall>\<^sub>F z in at z. f (z + 1) \<noteq> 0)"
    by (rule eventually_cong) (auto simp: plus_1)
  thus ?thesis
    unfolding isolated_zero_def * eventually_filtermap using assms plus_1[of z]
    by (auto simp: add_ac)
qed


definition is_identically_zero where
  "is_identically_zero \<longleftrightarrow> eventually (\<lambda>z. f z = 0) at_cusp"

lemma is_identically_zero_altdef1:
  "is_identically_zero \<longleftrightarrow> eventually (\<lambda>z. fourier z = 0) (at 0)"
  unfolding is_identically_zero_def at_cusp_filtermap [symmetric] eventually_filtermap
proof (rule eventually_cong)
  show "eventually (\<lambda>x. Im x > c0) at_cusp"
    by (rule eventually_at_cusp)
qed auto

end

locale fourier_expansion = pre_fourier_expansion +
  fixes pts :: "complex set"
  assumes pts_subset: "pts \<subseteq> {z. Im z > c0}"
  assumes pts_invariant: "z + 1 \<in> pts \<longleftrightarrow> z \<in> pts"
  assumes meromorphic: "f meromorphic_on {\<tau>. Im \<tau> > c0} pts"
begin

definition fourier_poles :: "complex set" where
  "fourier_poles = cusp_q ` pts"

lemma zero_not_in_fourier_poles [simp]: "0 \<notin> fourier_poles"
  by (auto simp: fourier_poles_def)

lemma pts_invariant_plus_of_nat: "z + of_nat n \<in> pts \<longleftrightarrow> z \<in> pts"
proof (induction n)
  case (Suc n)
  thus ?case
    using pts_invariant[of "z + of_nat n"] by (auto simp: add_ac)
qed auto

lemma pts_invariant_plus_of_int: "z + of_int n \<in> pts \<longleftrightarrow> z \<in> pts"
  using pts_invariant_plus_of_nat[of z "nat n"]
        pts_invariant_plus_of_nat[of "z - nat (-n)" "nat (-n)"]
  by (cases "n \<ge> 0") auto

lemma cusp_q_inv_in_pts_iff:
  assumes "q \<noteq> 0" "norm q < exp (-2 * pi * c0)"
  shows   "cusp_q_inv q \<in> pts \<longleftrightarrow> q \<in> fourier_poles"
proof
  assume "cusp_q_inv q \<in> pts"
  thus "q \<in> fourier_poles"
    using assms unfolding fourier_poles_def by (metis cusp_q_cusp_q_inv image_eqI)
next
  assume "q \<in> fourier_poles"
  then obtain z where "z \<in> pts" "q = cusp_q z"
    by (auto simp: fourier_poles_def)
  thus "cusp_q_inv q \<in> pts"
    by (metis cusp_q_inv_cusp_q pts_invariant_plus_of_int)
qed

lemma cusp_q_in_fourier_poles_iff [simp]: "cusp_q z \<in> fourier_poles \<longleftrightarrow> z \<in> pts"
proof
  assume "cusp_q z \<in> fourier_poles"
  then obtain z' where z': "cusp_q z = cusp_q z'" "z' \<in> pts"
    by (auto simp: fourier_poles_def)
  from z'(1) obtain n where "z = z' + of_int n"
    by (metis cusp_q_eq_cusp_qE)
  with z'(2) show "z \<in> pts"
    using pts_invariant_plus_of_int by blast
qed (auto simp: fourier_poles_def)

lemma cusp_q_range: "cusp_q ` {\<tau>. Im \<tau> > c0} = ball 0 (exp (-2 * pi * c0)) - {0}"
proof (intro equalityI subsetI)
  fix x :: complex assume x: "x \<in> ball 0 (exp (-2 * pi * c0)) - {0}"
  show "x \<in> cusp_q ` {\<tau>. Im \<tau> > c0}"
  proof (rule rev_image_eqI)
    show "x = cusp_q (cusp_q_inv x)"
      using x by auto
    show "cusp_q_inv x \<in> {\<tau>. c0 < Im \<tau>}"
      using x by (simp add: Im_cusp_q_inv_gt)
  qed
qed auto

lemma not_islimpt_fourier_poles:
  assumes "z \<in> ball 0 (exp (-2 * pi * c0)) - {0}"
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
    where "cusp_q_inv' = (\<lambda>z. myln z / (complex_of_real (2 * pi) * \<i>))"
  have cusp_q_inv': "cusp_q (cusp_q_inv' w) = w" if "w \<in> ball z r" for w
    using that by (simp add: cusp_q_def cusp_q_inv'_def exp_myln)
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

  have *: "g' n \<in> pts - {cusp_q_inv' z}" if n: "n \<ge> N" for n
  proof -
    have "g n \<in> fourier_poles"
      using g(1)[of n] by auto
    then obtain x where x: "x \<in> pts" "g n = cusp_q x"
      by (auto simp: fourier_poles_def)
    have *: "cusp_q x = cusp_q (cusp_q_inv' (g n))"
      using x N[OF n] by (subst cusp_q_inv') auto
    obtain m where m: "cusp_q_inv' (g n) = x + of_int m"
      using cusp_q_eq_cusp_qE[OF *] .
    hence "cusp_q_inv' (g n) \<in> pts"
      using pts_invariant_plus_of_int[of x m] x by auto
    hence "g' n \<in> pts"
      by (auto simp: g'_def)
    moreover have "g' n \<noteq> cusp_q_inv' z"
    proof
      assume "g' n = cusp_q_inv' z"
      hence "cusp_q (g' n) = cusp_q (cusp_q_inv' z)"
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
  moreover have "g'' n \<in> pts - {cusp_q_inv' z}" for n
    using *[of "n + N"] by (auto simp: g''_def)
  ultimately have "cusp_q_inv' z islimpt pts"
    unfolding islimpt_sequential by metis
  moreover have "Im (cusp_q_inv' z) > c0"
  proof -
    have *: "cusp_q (cusp_q_inv z) = cusp_q (cusp_q_inv' z)"
      using r \<open>z \<noteq> 0\<close> by (subst cusp_q_inv') auto
    obtain m where m: "cusp_q_inv' z = cusp_q_inv z + of_int m"
      using cusp_q_eq_cusp_qE[OF *] .
    hence "Im (cusp_q_inv' z) = Im (cusp_q_inv z)"
      by simp
    also from assms have "norm z < exp (-2 * pi * c0)"
      by simp
    hence "Im (cusp_q_inv z) > c0"
      using \<open>z \<noteq> 0\<close> Im_cusp_q_inv_gt by blast
    finally show ?thesis .
  qed
  ultimately show False
    using meromorphic by (simp add: meromorphic_on_def)
qed

lemma open_Diff_fourier_poles':
  assumes "fourier_poles' \<subseteq> fourier_poles"
  shows   "open (ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles')"
proof - 
  define D where "D = ball (0 :: complex) (exp (-2 * pi * c0)) - {0}"
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

lemma open_Diff_fourier_poles: "open (ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles)"
  by (rule open_Diff_fourier_poles') auto

lemma holomorphic_on_fourier_aux [holomorphic_intros]:
  assumes "A \<subseteq> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "fourier holomorphic_on A"
proof -
  have holo: "f holomorphic_on {\<tau>. Im \<tau> > c0} - pts"
    using meromorphic by (auto simp: meromorphic_on_def)

  have *: "(fourier has_field_derivative deriv f (cusp_q_inv q) / (2 * pi * \<i> * q)) (at q)"
    if q: "q \<in> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles" for q
  proof (rule has_field_derivative_fourier)
    show "(f has_field_derivative deriv f (cusp_q_inv q)) (at (cusp_q_inv q))"
    proof (intro holomorphic_derivI[OF holo])
      show "open ({\<tau>. c0 < Im \<tau>} - pts)"
        by (intro meromorphic_imp_open_diff [OF meromorphic])
      from q have "cusp_q_inv q \<notin> pts"
        by (metis DiffD1 DiffD2 cusp_q_cusp_q_inv fourier_poles_def imageI insertI1)
      thus "cusp_q_inv q \<in> {\<tau>. c0 < Im \<tau>} - pts"
        using q by (auto simp: fourier_poles_def Im_cusp_q_inv_gt)
    qed
    show "c0 < Im (cusp_q_inv q)"
      using q by (auto simp: Im_cusp_q_inv field_simps less_minus_iff ln_less_iff)
  qed (use q in auto)
  have "fourier holomorphic_on ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  proof (subst holomorphic_on_open)
    show "open (ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles)"
      by (rule open_Diff_fourier_poles)
    show "\<forall>x\<in>ball 0 (exp (- 2 * pi * c0)) - {0} - fourier_poles.
            \<exists>f'. (fourier has_field_derivative f') (at x)"
      using * by blast
  qed 
  thus ?thesis
    by (rule holomorphic_on_subset) fact
qed

lemma holomorphic_on_fourier [holomorphic_intros]:
  assumes "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "(\<lambda>z. fourier (g z)) holomorphic_on A"
proof -
  have "fourier \<circ> g holomorphic_on A"
    by (intro holomorphic_on_compose[OF assms(1) holomorphic_on_fourier_aux]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_fourier_aux [analytic_intros]:
  assumes "A \<subseteq> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "fourier analytic_on A"
proof -
  have "fourier holomorphic_on ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
    by (rule holomorphic_intros) auto
  hence "fourier analytic_on ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
    using open_Diff_fourier_poles by (subst analytic_on_open) auto
  thus ?thesis
    by (rule analytic_on_subset) fact
qed

lemma analytic_on_fourier [analytic_intros]:
  assumes "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "(\<lambda>z. fourier (g z)) analytic_on A"
proof -
  have "fourier \<circ> g analytic_on A"
    by (intro analytic_on_compose[OF assms(1) analytic_on_fourier_aux]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_on_fourier_aux [continuous_intros]:
  assumes "A \<subseteq> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "continuous_on A fourier"
proof -
  have "fourier holomorphic_on ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
    by (rule holomorphic_intros) auto
  hence "continuous_on (ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles) fourier"
    by (rule holomorphic_on_imp_continuous_on)
  thus ?thesis
    by (rule continuous_on_subset) fact
qed

lemma continuous_on_fourier [continuous_intros]:
  assumes "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles"
  shows   "continuous_on A (\<lambda>z. fourier (g z))"
proof -
  have "continuous_on A (fourier \<circ> g)"
    by (intro continuous_on_compose[OF assms(1) continuous_on_fourier_aux]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma tendsto_fourier:
  assumes "f \<midarrow>z\<rightarrow> c" "q = cusp_q z" "Im z > c0"
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
    where "cusp_q_inv' = (\<lambda>z. myln z / (complex_of_real (2 * pi) * \<i>))"
  have cusp_q_inv': "cusp_q (cusp_q_inv' w) = w" if "w \<in> ball q r" for w
    using that by (simp add: cusp_q_def cusp_q_inv'_def exp_myln)

  obtain m where m: "cusp_q_inv' q = z + of_int m"
  proof -
    have "cusp_q z = cusp_q (cusp_q_inv' q)"
      using r(1) by (simp add: cusp_q_inv' assms)
    from cusp_q_eq_cusp_qE[OF this] and that show ?thesis
      by blast
  qed
  define cusp_q_inv'' :: "complex \<Rightarrow> complex"
    where "cusp_q_inv'' = (\<lambda>q. cusp_q_inv' q - of_int m)"
  have cusp_q_inv'': "cusp_q (cusp_q_inv'' w) = w" if "w \<in> ball q r" for w
    using that by (auto simp: cusp_q_inv''_def cusp_q.minus_of_int cusp_q_inv')
  have [simp]: "cusp_q_inv'' (cusp_q z) = z"
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
      hence "cusp_q (cusp_q_inv'' x) \<noteq> cusp_q z"
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
    moreover have "eventually (\<lambda>x. x \<in> ball 0 (exp (-2 * pi * c0))) (at q)"
      by (intro eventually_at_in_open') (use assms in auto)
    ultimately show "\<forall>\<^sub>F x in at q. (f \<circ> cusp_q_inv'') x = fourier x"
    proof eventually_elim
      case (elim x)
      have "cusp_q (cusp_q_inv x) = cusp_q (cusp_q_inv'' x)"
        using elim by (auto simp: cusp_q_inv'')
      then obtain m where *: "cusp_q_inv'' x = cusp_q_inv x + of_int m"
        by (elim cusp_q_eq_cusp_qE)
      show ?case using elim Im_cusp_q_inv_gt[of x c0]
        by (auto simp: fourier_def * plus_of_int)
    qed
  qed
  finally show ?thesis .
qed

lemma meromorphic_fourier:
  "fourier meromorphic_on (ball 0 (exp (-2 * pi * c0)) - {0}) fourier_poles"
proof
  show "open (ball 0 (exp (- 2 * pi * c0)) - {0})"
    by auto
  show subset: "fourier_poles \<subseteq> ball 0 (exp (- 2 * pi * c0)) - {0}"
    using pts_subset by (auto simp: fourier_poles_def)
  show "fourier holomorphic_on ball 0 (exp (- 2 * pi * c0)) - {0} - fourier_poles"
    by (intro holomorphic_intros)
  show "\<not>z islimpt fourier_poles" if "z \<in> ball 0 (exp (- 2 * pi * c0)) - {0}" for z
    using not_islimpt_fourier_poles[of z] that by blast
  show "isolated_singularity_at fourier z" if "z \<in> fourier_poles" for z
  proof (rule isolated_singularity_at_holomorphic)
    have "fourier holomorphic_on ball 0 (exp (-2*pi*c0)) - {0} - fourier_poles"
      by (intro holomorphic_on_fourier_aux order.refl)
    also have "ball 0 (exp (-2*pi*c0)) - {0} - fourier_poles =
               ball 0 (exp (-2*pi*c0)) - {0} - (fourier_poles - {z}) - {z}"
      using that by auto
    finally show "fourier holomorphic_on \<dots>" .
    show "open (ball 0 (exp (- 2 * pi * c0)) - {0} - (fourier_poles - {z}))"
      by (intro open_Diff_fourier_poles') auto
    show "z \<in> ball 0 (exp (- 2 * pi * c0)) - {0} - (fourier_poles - {z})"
      using subset that by auto
  qed
  show "not_essential fourier z" if "z \<in> fourier_poles" for z
  proof -
    from that obtain x where x: "x \<in> pts" "z = cusp_q x"
      using that by (auto simp: fourier_poles_def)
    from meromorphic and x(1) have "not_essential f x"
      by (simp add: meromorphic_on_def)
    then consider "is_pole f x" | c where "f \<midarrow>x\<rightarrow> c"
      by (auto simp: not_essential_def)
    thus ?thesis
    proof cases
      assume "is_pole f x"
      hence "is_pole fourier z"
        using x pts_subset by (auto simp: fourier_is_pole_cusp_q_iff)
      thus "not_essential fourier z"
        by (auto simp: not_essential_def)
    next
      fix c assume c: "f \<midarrow>x\<rightarrow> c"
      hence "fourier \<midarrow>cusp_q x\<rightarrow> c"
        by (rule tendsto_fourier) (use x pts_subset in auto)
      thus "not_essential fourier z"
        using x by (auto simp: not_essential_def)
    qed
  qed
qed

lemma deriv_fourier:
  assumes "Im z > c0" "z \<notin> pts" "q = cusp_q z"
  shows   "deriv fourier q = deriv f z / (2 * pi * \<i> * q)"
proof (rule DERIV_imp_deriv, rule has_field_derivative_fourier)
  have holo: "f holomorphic_on {z. Im z > c0} - pts"
    using meromorphic by (auto simp: meromorphic_on_def)
  show "q = cusp_q z" "Im z > c0"
    using assms by auto
  show "(f has_field_derivative deriv f z) (at z)"
    by (intro holomorphic_derivI [OF holo])
       (use assms in \<open>auto intro!: meromorphic_imp_open_diff [OF meromorphic]\<close>)
qed

lemma fourier_expansion_plus_const: "fourier_expansion (\<lambda>x. f x + C) c0 pts"
proof -
  interpret shifted: invariant_under_shift1 "\<lambda>x. f x + C" c0
    by standard (auto simp: plus_1)
  show ?thesis
    by unfold_locales
       (use pts_subset in \<open>auto intro!: meromorphic_intros meromorphic simp: pts_invariant\<close>)
qed

end


subsection \<open>Functions that are holomorphic at the cusp\<close>

definition not_essential_at_cusp :: "(complex \<Rightarrow> complex) \<Rightarrow> bool" where
  "not_essential_at_cusp f \<longleftrightarrow> filterlim f at_infinity at_cusp \<or> (\<exists>c. (f \<longlongrightarrow> c) at_cusp)"

locale fourier_expansion_meromorphic_at_cusp = fourier_expansion +
  assumes not_essential_at_cusp': "not_essential_at_cusp f"
  assumes isolated_singularity_at_cusp''': "eventually (\<lambda>x. x \<notin> pts) at_cusp"
begin

lemma not_islimpt_0: "\<not>0 islimpt fourier_poles"
proof -
  obtain B where B: "\<And>z. Im z > B \<Longrightarrow> z \<notin> pts"
    using isolated_singularity_at_cusp''' unfolding eventually_at_cusp_iff by blast
  have "eventually (\<lambda>q. q \<in> ball 0 (exp (-2 * pi * B)) - {0}) (at 0)"
    by (intro eventually_at_in_open) auto
  hence "eventually (\<lambda>q. q \<notin> fourier_poles) (at 0)"
    by eventually_elim (use B in \<open>auto simp: fourier_poles_def\<close>)
  thus ?thesis
    by (simp add: islimpt_conv_frequently_at frequently_def)
qed

lemma open_Diff_fourier'':
  assumes "fourier_poles' \<subseteq> insert 0 fourier_poles"
  shows   "open (ball 0 (exp (-2 * pi * c0)) - fourier_poles')"
proof - 
  define D where "D = ball (0 :: complex) (exp (-2 * pi * c0))"
  have "open (D - closure fourier_poles')"
    by (intro open_Diff) (auto simp: D_def)
  also have "D - closure fourier_poles' = D - fourier_poles'"
  proof safe
    fix x assume x: "x \<in> D" "x \<in> closure fourier_poles'" "x \<notin> fourier_poles'"
    hence "x islimpt fourier_poles'"
      by (subst islimpt_in_closure) auto
    hence "x islimpt insert 0 fourier_poles"
      by (rule islimpt_subset) fact
    with assms x show False
      using not_islimpt_fourier_poles[of x] not_islimpt_0
      by (cases "x = 0") (auto simp: D_def islimpt_insert)
  qed (use closure_subset in auto)
  finally show ?thesis
    by (simp add: D_def)
qed

lemma isolated_singularity_fourier_0: "isolated_singularity_at fourier 0"
proof (rule isolated_singularity_at_holomorphic)
  show "fourier holomorphic_on ball 0 (exp(-2*pi*c0)) - fourier_poles - {0}"
    by (intro holomorphic_on_fourier_aux) auto
  show "open (ball 0 (exp (- 2 * pi * c0)) - fourier_poles)"
    using open_Diff_fourier'' by blast
qed (auto simp: fourier_poles_def)

lemma not_essential_fourier_0: "not_essential fourier 0"
  using not_essential_at_cusp' unfolding not_essential_at_cusp_def
proof
  assume "filterlim f at_infinity at_cusp"
  hence "is_pole fourier 0"
    by (simp add: fourier_is_pole_0_iff)
  thus ?thesis
    by (auto simp: not_essential_def)
next
  assume "\<exists>f0. (f \<longlongrightarrow> f0) at_cusp"
  then obtain f0 where "(f \<longlongrightarrow> f0) at_cusp"
    by blast
  hence "fourier \<midarrow>0\<rightarrow> f0"
    by (subst fourier_tendsto_0_iff)
  thus ?thesis
    by (auto simp: not_essential_def)
qed

lemma meromorphic_fourier':
  "fourier meromorphic_on (ball 0 (exp (-2 * pi * c0))) (insert 0 fourier_poles)"
proof
  show "open (ball 0 (exp (- 2 * pi * c0)))"
    by auto
  show "insert 0 fourier_poles \<subseteq> ball 0 (exp (- 2 * pi * c0))"
    using pts_subset by (auto simp: fourier_poles_def)
  show "fourier holomorphic_on ball 0 (exp (- 2 * pi * c0)) - insert 0 fourier_poles"
    by (rule holomorphic_on_fourier_aux) auto

  show "isolated_singularity_at fourier z" 
    if "z \<in> insert 0 fourier_poles" for z
  proof (cases "z = 0")
    case False
    thus ?thesis
      using meromorphic_fourier that by (auto simp: meromorphic_on_def)
  next
    case True
    thus ?thesis 
      using isolated_singularity_fourier_0 by auto
  qed

  show "not_essential fourier z" 
    if "z \<in> insert 0 fourier_poles" for z
  proof (cases "z = 0")
    case False
    thus ?thesis
      using meromorphic_fourier that by (auto simp: meromorphic_on_def)
  next
    case True
    thus ?thesis
      using not_essential_fourier_0 by auto
  qed

  show "\<not> z islimpt insert 0 fourier_poles" if "z \<in> ball 0 (exp (- 2 * pi * c0))" for z
  proof (cases "z = 0")
    case False
    thus ?thesis
      using meromorphic_fourier that by (auto simp: meromorphic_on_def islimpt_insert)
  next
    case True
    thus ?thesis
      by (auto simp: islimpt_insert not_islimpt_0)
  qed
qed

lemma is_identically_zero_altdef2:
  "is_identically_zero \<longleftrightarrow> frequently (\<lambda>z. fourier z = 0) (at 0)"
proof
  assume "is_identically_zero"
  thus "frequently (\<lambda>z. fourier z = 0) (at 0)"
    unfolding is_identically_zero_altdef1 by (intro eventually_frequently) auto
next
  assume "frequently (\<lambda>z. fourier z = 0) (at 0)"
  moreover have "isolated_singularity_at fourier 0" "not_essential fourier 0"
    by (fact isolated_singularity_fourier_0 not_essential_fourier_0)+
  ultimately show "is_identically_zero"
    unfolding is_identically_zero_altdef1 using not_essential_frequently_0_imp_eventually_0 by blast
qed

lemma is_identically_zero_altdef3:
  "is_identically_zero \<longleftrightarrow> frequently (\<lambda>z. f z = 0) at_cusp"
  unfolding is_identically_zero_altdef2 at_cusp_filtermap [symmetric] frequently_filtermap
proof (rule frequently_cong)
  show "eventually (\<lambda>x. Im x > c0) at_cusp"
    by (rule eventually_at_cusp)
qed auto

lemma is_identically_zero_altdef4:
  "is_identically_zero \<longleftrightarrow> laurent_expansion fourier 0 = 0"
proof -
  let ?F = "laurent_expansion fourier 0"
  have *: "fourier has_laurent_expansion ?F"
    by (simp add: isolated_singularity_fourier_0 not_essential_fourier_0 
                  not_essential_has_laurent_expansion_0)
  show ?thesis
    unfolding is_identically_zero_altdef2
    using has_laurent_expansion_eventually_nonzero_iff'[OF *] 
    by (auto simp: frequently_def)
qed

lemma is_identically_zero_altdef5:
  "is_identically_zero \<longleftrightarrow> (\<forall>x\<in>ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}. fourier x = 0)"
proof
  assume *: "is_identically_zero"
  define B where "B = ball 0 (exp (-2*pi*c0)) - fourier_poles"
  have [simp, intro]: "open B" "0 \<in> B"
    unfolding B_def by (intro open_Diff_fourier'') auto
  from * have "\<forall>\<^sub>F x in at 0. fourier x = 0 \<and> x \<in> B - {0}"
    unfolding is_identically_zero_altdef1 by (intro eventually_conj eventually_at_in_open) auto
  then obtain A where A: "open A" "0 \<in> A" "A - {0} \<subseteq> B" "\<And>x. x \<in> A - {0} \<Longrightarrow> fourier x = 0"
    unfolding eventually_at_topological by blast
  have "fourier x = 0" if "x \<in> B - {0}" for x
  proof (rule analytic_continuation_open[where f = fourier])
    show "A - {0} \<subseteq> B - {0}"
      using A by blast
    show "open (A - {0})" "open (B - {0})"
      using A by auto
    show "A - {0} \<noteq> {}"
      using A(1,2) not_open_singleton open_subopen by blast
    show "connected (B - {0})" unfolding B_def
      by (metis Diff_insert connected_ball meromorphic_fourier' meromorphic_imp_connected_diff)
  qed (use that A in \<open>auto intro!: holomorphic_intros simp: B_def\<close>)
  thus "(\<forall>x\<in>ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}. fourier x = 0)"
    by (auto simp: B_def)
next
  assume *: "(\<forall>x\<in>ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}. fourier x = 0)"
  have "eventually (\<lambda>x. x \<in> ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}) (at 0)"
    by (intro eventually_at_in_open open_Diff_fourier'') auto
  hence "eventually (\<lambda>x. fourier x = 0) (at 0)"
    by eventually_elim (use * in auto)
  thus is_identically_zero
    using is_identically_zero_altdef1 by blast
qed

lemma is_identically_zero_altdef6:
  "is_identically_zero \<longleftrightarrow> (\<forall>z. Im z > c0 \<and> z \<notin> pts \<longrightarrow> f z = 0)"
proof
  assume "is_identically_zero"
  hence *: "fourier z = 0" if "z \<in> ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}" for z
    unfolding is_identically_zero_altdef5 using that by blast
  have "f z = 0" if "Im z > c0" "z \<notin> pts" for z
  proof -
    have "f z = fourier (cusp_q z)"
      using that by auto
    also have "\<dots> = 0"
      using that by (intro *) auto
    finally show ?thesis .
  qed
  thus "(\<forall>z. Im z > c0 \<and> z \<notin> pts \<longrightarrow> f z = 0)"
    by auto
next
  assume *: "\<forall>z. Im z > c0 \<and> z \<notin> pts \<longrightarrow> f z = 0"
  have "fourier x = 0" if "x \<in> ball 0 (exp (-2*pi*c0)) - fourier_poles - {0}" for x
  proof -
    have 1: "Im (cusp_q_inv x) > c0"
      using that by (intro Im_cusp_q_inv_gt) auto
    have 2: "cusp_q_inv x \<notin> pts"
      using that by (simp add: cusp_q_inv_in_pts_iff)
    have "fourier x = f (cusp_q_inv x)"
      using that by (auto simp: fourier_def)
    also have "\<dots> = 0"
      using * 1 2 by (auto simp: Im_cusp_q_inv)
    finally show ?thesis .
  qed
  thus is_identically_zero
    unfolding is_identically_zero_altdef5 by blast
qed

lemma zorder_at_cusp_eq'':
  assumes "\<not>is_identically_zero"
  shows   "zorder_at_cusp = zorder fourier 0"
proof -
  let ?F = "laurent_expansion fourier 0"
  have *: "fourier has_laurent_expansion ?F"
    by (simp add: isolated_singularity_fourier_0 not_essential_fourier_0 
                  not_essential_has_laurent_expansion_0)
  from assms have "?F \<noteq> 0"
    by (simp add: is_identically_zero_altdef4)
  thus ?thesis using *
    unfolding zorder_at_cusp_def using has_laurent_expansion_zorder_0 by metis
qed

lemma fourier_expansion_meromorphic_at_cusp_plus_const:
  "fourier_expansion_meromorphic_at_cusp (\<lambda>x. f x + C) c0 pts"
proof -
  interpret shifted: fourier_expansion "\<lambda>x. f x + C" c0 pts
    by (intro fourier_expansion_plus_const)
  show ?thesis
  proof
    have "filterlim f at_infinity at_cusp \<or> (\<exists>f0. (f \<longlongrightarrow> f0) at_cusp)"
      using not_essential_at_cusp' unfolding not_essential_at_cusp_def by auto
    thus "not_essential_at_cusp (\<lambda>x. f x + C)"
      unfolding not_essential_at_cusp_def
    proof (rule disj_forward)
      assume "filterlim f at_infinity at_cusp"
      thus "filterlim (\<lambda>x. f x + C) at_infinity at_cusp"
        by (rule tendsto_add_filterlim_at_infinity') (rule tendsto_const)
    next
      assume "\<exists>f0. (f \<longlongrightarrow> f0) at_cusp"
      thus "\<exists>f0. ((\<lambda>x. f x + C) \<longlongrightarrow> f0) at_cusp"
        by (auto intro!: tendsto_eq_intros)
    qed
  qed (use isolated_singularity_at_cusp''' in auto)
qed

end


text \<open>
  If a function has a defined limit for \<open>z \<rightarrow> i\<infinity>\<close>, it is said to be holomorphic at the cusp.
  In this case, the function is analytic at \<open>q = 0\<close> as well.
\<close>

locale fourier_expansion_pole_at_cusp = fourier_expansion +
  assumes pole_at_cusp: "filterlim f at_infinity at_cusp"
  assumes isolated_singularity_at_cusp': "eventually (\<lambda>x. x \<notin> pts) at_cusp"
begin

sublocale fourier_expansion_meromorphic_at_cusp f c0 pts
  by unfold_locales
     (use pole_at_cusp isolated_singularity_at_cusp' in \<open>auto simp: not_essential_at_cusp_def\<close>)

lemma is_pole_0: "is_pole fourier 0"
  using pole_at_cusp by (simp add: fourier_is_pole_0_iff)

lemma zorder_0_neg: "zorder fourier 0 < 0"
  by (rule isolated_pole_imp_neg_zorder [OF isolated_singularity_fourier_0 is_pole_0])

lemma fourier_expansion_pole_at_cusp_plus_const:
  "fourier_expansion_pole_at_cusp (\<lambda>x. f x + C) c0 pts"
proof -
  interpret shifted: fourier_expansion "\<lambda>x. f x + C" c0 pts
    by (rule fourier_expansion_plus_const)
  show ?thesis
  proof
    show "filterlim (\<lambda>x. f x + C) at_infinity at_cusp"
      by (rule tendsto_add_filterlim_at_infinity' pole_at_cusp tendsto_const)+
  qed (use isolated_singularity_at_cusp' in auto)
qed

end
  

locale fourier_expansion_holomorphic_at_cusp = fourier_expansion +
  fixes f0 :: complex
  assumes tendsto_at_cusp [tendsto_intros]: "(f \<longlongrightarrow> f0) at_cusp"
  assumes isolated_singularity_at_cusp': "eventually (\<lambda>x. x \<notin> pts) at_cusp"
begin

sublocale fourier_expansion_meromorphic_at_cusp f c0 pts
  by unfold_locales
     (use tendsto_at_cusp isolated_singularity_at_cusp' in \<open>auto simp: not_essential_at_cusp_def\<close>)

lemmas fourier_0 [simp] = fourier_0_aux [OF tendsto_at_cusp]
lemmas isCont_0 = isCont_0_aux [OF tendsto_at_cusp]

lemma holomorphic_on_fourier'_aux [holomorphic_intros]:
  "fourier holomorphic_on ball 0 (exp (-2 * pi * c0)) - fourier_poles"
proof (rule no_isolated_singularity)
  show "fourier holomorphic_on ball 0 (exp (-2 * pi * c0)) - fourier_poles - {0}"
    by (intro holomorphic_intros) auto
  have "isCont fourier q" if q: "q \<in> ball 0 (exp (-2 * pi * c0)) - fourier_poles" for q
  proof (cases "q = 0")
    case True
    thus ?thesis by (simp add: isCont_0)
  next
    case False
    have "continuous_on (ball 0 (exp (-2 * pi * c0)) - fourier_poles - {0}) fourier"
      by (intro continuous_intros) auto
    moreover {
      have "open (ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles)"
        by (intro open_Diff_fourier_poles)
      also have "ball 0 (exp (-2 * pi * c0)) - {0} - fourier_poles =
                 ball 0 (exp (-2 * pi * c0)) - fourier_poles - {0}"
        by auto
      finally have "open \<dots>" .
    }
    with False have "q \<in> interior (ball 0 (exp (-2 * pi * c0)) - fourier_poles - {0})"
      using q by (subst interior_open) auto
    ultimately show ?thesis
      using continuous_on_interior by blast
  qed
  thus "continuous_on (ball 0 (exp (-2 * pi * c0)) - fourier_poles) fourier"
    by (intro continuous_at_imp_continuous_on) auto
qed (use open_Diff_fourier'' in auto)

lemmas [holomorphic_intros del] = holomorphic_on_fourier_aux holomorphic_on_fourier
lemmas [analytic_intros del]    = analytic_on_fourier_aux analytic_on_fourier
lemmas [continuous_intros del]  = continuous_on_fourier_aux continuous_on_fourier

lemma holomorphic_on_fourier' [holomorphic_intros]:
  assumes "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - fourier_poles"
  shows   "(\<lambda>z. fourier (g z)) holomorphic_on A"
proof -
  have "fourier \<circ> g holomorphic_on A"
    by (intro holomorphic_on_compose_gen[OF assms(1) holomorphic_on_fourier'_aux]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_fourier'_aux [analytic_intros]:
  assumes "A \<subseteq> ball 0 (exp (-2 * pi * c0)) - fourier_poles"
  shows   "fourier analytic_on A"
proof -
  have "fourier analytic_on ball 0 (exp (-2 * pi * c0)) - fourier_poles"
    using open_Diff_fourier'' by (subst analytic_on_open) (use holomorphic_on_fourier'_aux in auto)
  thus ?thesis by (rule analytic_on_subset) (use assms in auto)
qed

lemma analytic_on_fourier' [analytic_intros]:
  assumes "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - fourier_poles"
  shows   "(\<lambda>z. fourier (g z)) analytic_on A"
proof -
  have "fourier \<circ> g analytic_on A"
    by (intro analytic_on_compose_gen[OF assms(1) analytic_on_fourier'_aux[OF order.refl]])
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_on_fourier'_aux [continuous_intros]:
  assumes "A \<subseteq> ball 0 (exp (-2 * pi * c0)) - fourier_poles"
  shows   "continuous_on A fourier"
  by (intro holomorphic_on_imp_continuous_on holomorphic_intros) (use assms in auto)

lemma continuous_on_fourier' [continuous_intros]:
  assumes "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> g z \<in> ball 0 (exp (-2 * pi * c0)) - fourier_poles"
  shows   "continuous_on A (\<lambda>z. fourier (g z))"
proof -
  have "continuous_on A (fourier \<circ> g)"
    by (intro continuous_on_compose[OF assms(1) continuous_on_fourier'_aux]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

end



locale fourier_expansion_meromorphic_at_cusp_explicit = fourier_expansion +
  fixes F :: "complex fls"
  assumes laurent_at_cusp''': "fourier has_laurent_expansion F"
  assumes isolated_singularity_at_cusp'': "eventually (\<lambda>x. x \<notin> pts) at_cusp"
begin

sublocale fourier_expansion_meromorphic_at_cusp f c0 pts
proof
  have "not_essential fourier 0"
    using laurent_at_cusp''' by (simp add: has_laurent_expansion_not_essential_0)
  then consider "is_pole fourier 0" | c where "fourier \<midarrow>0\<rightarrow> c"
    by (auto simp: not_essential_def)
  thus "not_essential_at_cusp f"
  proof cases
    assume "is_pole fourier 0"
    hence "filterlim (\<lambda>z. fourier (cusp_q z)) at_infinity at_cusp"
      unfolding is_pole_def at_cusp_filtermap [symmetric] filterlim_filtermap .
    also have "?this \<longleftrightarrow> filterlim f at_infinity at_cusp"
      by (intro filterlim_cong eventually_fourier_cusp_q_eq refl)
    finally show ?thesis unfolding not_essential_at_cusp_def by blast
  next
    fix c assume "fourier \<midarrow>0\<rightarrow> c"
    hence "((\<lambda>x. fourier (cusp_q x)) \<longlongrightarrow> c) at_cusp"
      unfolding at_cusp_filtermap [symmetric] filterlim_filtermap .
    also have "?this \<longleftrightarrow> (f \<longlongrightarrow> c) at_cusp"
      by (intro filterlim_cong eventually_fourier_cusp_q_eq refl)
    finally show ?thesis unfolding not_essential_at_cusp_def by blast
  qed
qed (use isolated_singularity_at_cusp'' in auto)

lemma laurent_expansion_fourier_0_eq: "laurent_expansion fourier 0 = F"
  using laurent_at_cusp''' has_laurent_expansion_unique isolated_singularity_fourier_0 
        not_essential_fourier_0 not_essential_has_laurent_expansion_0 by blast

lemma fourier_expansion_meromorphic_at_cusp_explicit_plus_const:
  "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. f x + C) c0 pts (F + fls_const C)"
proof -
  interpret shifted: fourier_expansion_meromorphic_at_cusp "\<lambda>x. f x + C" c0 pts
    by (intro fourier_expansion_meromorphic_at_cusp_plus_const)
  show ?thesis
  proof
    have "(\<lambda>x. fourier x + C) has_laurent_expansion F + fls_const C"
      by (intro laurent_expansion_intros laurent_at_cusp''')
    also have "?this \<longleftrightarrow> shifted.fourier has_laurent_expansion F + fls_const C"
      by (intro has_laurent_expansion_cong)
         (auto simp: eventually_at_filter fourier_def shifted.fourier_def)
    finally show \<dots> .
  qed (use isolated_singularity_at_cusp'' in auto)
qed

lemma subdegree_nonneg_imp_holomorphic_at_cusp:
  assumes "fls_subdegree F \<ge> 0"
  shows   "fourier_expansion_holomorphic_at_cusp f c0 pts (fls_nth F 0)"
proof
  show "(f \<longlongrightarrow> fls_nth F 0) at_cusp"
    using assms fourier_tendsto_0_iff has_laurent_expansion_imp_tendsto_0 laurent_at_cusp''' by blast
  show "\<forall>\<^sub>F x in at_cusp. x \<notin> pts"
    by (rule isolated_singularity_at_cusp'')
qed

lemma frequently_eq_const_at_cusp_imp_laurent_const:
  assumes "frequently (\<lambda>x. f x = c) at_cusp"
  shows   "F = fls_const c" 
proof -
  interpret shift: fourier_expansion_meromorphic_at_cusp_explicit
                     "\<lambda>x. f x + (-c)" c0 pts "F + fls_const (-c)"
    by (rule fourier_expansion_meromorphic_at_cusp_explicit_plus_const)

  have "frequently (\<lambda>x. shift.fourier x = 0) (at 0)"
    unfolding frequently_def
  proof
    assume "eventually (\<lambda>x. shift.fourier x \<noteq> 0) (at 0)"
    hence "eventually (\<lambda>x. f x \<noteq> c) at_cusp"
      using eventually_at_cusp[of c0]
      unfolding at_cusp_filtermap [symmetric] eventually_filtermap
    proof eventually_elim
      case (elim x)
      thus ?case
        by (subst (asm) shift.fourier_cusp_q) auto
    qed
    with assms show False
      by (auto simp: frequently_def)
  qed
  hence *: "F + fls_const (-c) = 0"
    using has_laurent_expansion_eventually_nonzero_iff'[OF shift.laurent_at_cusp''']
    by (auto simp: frequently_def)
  thus "F = fls_const c"
    by simp
qed

lemma constant_imp_zorder_at_cusp_eq_0:
  assumes "f constant_on {z. Im z > c0}"
  shows   "zorder_at_cusp = 0"
proof -
  from assms obtain c where c: "\<And>z. Im z > c0 \<Longrightarrow> f z = c"
    by (auto simp: constant_on_def)
  have "eventually (\<lambda>z. Im z > c0) at_cusp"
    by (intro eventually_at_cusp)
  hence "eventually (\<lambda>z. f z = c) at_cusp"
    by eventually_elim (use c in auto)
  hence "frequently (\<lambda>z. f z = c) at_cusp"
    by (intro eventually_frequently) auto
  hence "F = fls_const c"
    by (rule frequently_eq_const_at_cusp_imp_laurent_const)
  thus ?thesis
    unfolding zorder_at_cusp_def laurent_expansion_fourier_0_eq by simp
qed  

end


context fourier_expansion_meromorphic_at_cusp
begin

lemma fourier_expansion_meromorphic_at_cusp_explicit [intro?]:
  "fourier_expansion_meromorphic_at_cusp_explicit f c0 pts (laurent_expansion fourier 0)"
proof
  show "fourier has_laurent_expansion laurent_expansion fourier 0"
    using isolated_singularity_fourier_0 not_essential_fourier_0
          not_essential_has_laurent_expansion_0 by blast
qed (use isolated_singularity_at_cusp''' in auto)

lemma frequently_eq_const_at_cuspD:
  assumes "frequently (\<lambda>x. f x = c) at_cusp"
  shows   "\<And>z. z \<in> ball 0 (exp (- (2 * pi * c0))) - fourier_poles \<Longrightarrow> fourier z = c"
          "\<And>z. Im z > c0 \<Longrightarrow> z \<notin> pts \<Longrightarrow> f z = c"
proof -
  let ?F = "laurent_expansion fourier 0"
  interpret fourier_expansion_meromorphic_at_cusp_explicit f c0 pts ?F ..
  have "?F = fls_const c"
    using assms by (rule frequently_eq_const_at_cusp_imp_laurent_const)

  have eq: "fourier z - c = 0" if "z \<in> ball 0 (exp (- (2 * pi * c0))) - fourier_poles - {0}" for z
  proof (rule has_laurent_expansion_0_analytic_continuation[of _ _ z])
    have "(\<lambda>x. fourier x - c) has_laurent_expansion fls_const c - fls_const c"
      using \<open>?F = _\<close> laurent_at_cusp''' by (intro laurent_expansion_intros) auto
    thus "(\<lambda>x. fourier x - c) has_laurent_expansion 0"
      by simp
    show "(\<lambda>x. fourier x - c) holomorphic_on ball 0 (exp (- (2 * pi * c0))) - fourier_poles - {0}"
      by (intro holomorphic_on_fourier holomorphic_intros) auto
    show "open (ball 0 (exp (- (2 * pi * c0))) - fourier_poles)"
      using open_Diff_fourier'' by auto
    show "connected (ball 0 (exp (- (2 * pi * c0))) - fourier_poles)"
      using meromorphic_imp_connected_diff'[OF meromorphic_fourier', of fourier_poles]
      by auto
  qed (use that in auto)
          
  show eq': "fourier z = c" if "z \<in> ball 0 (exp (-(2*pi*c0))) - fourier_poles" for z
  proof (cases "z = 0")
    case False
    thus ?thesis
      using eq[of z] that unfolding fourier_def by auto
  next
    case True
    have "fourier has_laurent_expansion fls_const c"
      using laurent_at_cusp''' \<open>?F = _\<close> by simp
    from has_laurent_expansion_imp_tendsto_0[OF this] have "fourier \<midarrow>0\<rightarrow> c"
      by simp
    thus ?thesis
      using True by (simp add: fourier_0_aux fourier_tendsto_0_iff)
  qed

  show "f z = c" if "Im z > c0" "z \<notin> pts" for z
  proof -
    have "f z = fourier (cusp_q z)"
      using that by simp
    also have "\<dots> = c"
      by (rule eq') (use that in auto)
    finally show ?thesis .
  qed
qed

lemma eventually_no_isolated_zero: "\<forall>\<^sub>F x in at_cusp. \<not> isolated_zero f x"
proof (rule ccontr)
  assume "\<not>(\<forall>\<^sub>F x in at_cusp. \<not> isolated_zero f x)"
  hence isolated: "\<exists>\<^sub>F x in at_cusp. isolated_zero f x"
    by (auto simp: frequently_def)
  hence *: "\<exists>\<^sub>F x in at_cusp. f x = 0"
    by (rule frequently_mono [rotated]) (auto simp: isolated_zero_def)
  have zero: "f z = 0" if "Im z > c0" "z \<notin> pts" for z
    using frequently_eq_const_at_cuspD(2)[OF *] that by blast
  have "eventually (\<lambda>z. Im z > c0 \<and> z \<notin> pts) at_cusp"
    by (intro eventually_conj eventually_at_cusp isolated_singularity_at_cusp''')
  then obtain B where B: "\<And>z. Im z > B \<Longrightarrow> Im z > c0 \<and> z \<notin> pts"
    unfolding eventually_at_cusp_iff by auto
  from isolated obtain x where x: "Im x > B" "isolated_zero f x"
    by (auto simp: frequently_def eventually_at_cusp_iff)
  have "eventually (\<lambda>y. y \<in> {y. Im y > B}) (at x)"
    using x by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
  hence "eventually (\<lambda>y. f y = 0) (at x)"
    by eventually_elim (use B zero in auto)
  moreover from x have "eventually (\<lambda>y. f y \<noteq> 0) (at x)"
    by (auto simp: isolated_zero_def)
  ultimately have "eventually (\<lambda>y. False) (at x)"
    by eventually_elim auto
  thus False
    by simp
qed

end



locale fourier_expansion_meromorphic_at_cusp_explicit' = fourier_expansion +
  fixes F :: "complex fls"
  assumes laurent_at_cusp'': "fourier has_laurent_expansion F"
  assumes poles': "\<And>z. z \<in> pts \<Longrightarrow> is_pole f z"
begin

definition fourier_poles'
  where "fourier_poles' = (if is_pole fourier 0 then {0} else {}) \<union> fourier_poles"

lemma pts_eq: "pts = {z. Im z > c0 \<and> is_pole f z}"
  using poles' pts_subset meromorphic meromorphic_pole_subset by blast

lemma fourier_is_pole_cusp_q_iff':
  assumes "Im z > c0"
  shows   "is_pole fourier (cusp_q z) \<longleftrightarrow> z \<in> pts"
  using fourier_is_pole_cusp_q_iff[OF assms] pts_eq assms by auto

lemma is_pole_fourier_iff:
  assumes "norm q < exp (-2 * pi * c0)"
  shows   "is_pole fourier q \<longleftrightarrow> q \<in> fourier_poles'"
proof (cases "q = 0")
  case True
  thus ?thesis
    by (auto simp: fourier_poles'_def)
next
  case False
  from assms False have *: "c0 < Im (cusp_q_inv q)"
    using Im_cusp_q_inv_gt[of q c0] by auto
  from False have "is_pole fourier q \<longleftrightarrow> is_pole fourier (cusp_q (cusp_q_inv q))"
    by simp
  also have "\<dots> \<longleftrightarrow> cusp_q_inv q \<in> pts"
    by (subst fourier_is_pole_cusp_q_iff') (use * in auto)
  also have "cusp_q_inv q \<in> pts \<longleftrightarrow> q \<in> fourier_poles"
    using assms False by (simp add: cusp_q_inv_in_pts_iff)
  finally show ?thesis
    by (auto simp: fourier_poles'_def)
qed

sublocale fourier_expansion_meromorphic_at_cusp_explicit
proof
  have "isolated_singularity_at fourier 0"
    using laurent_at_cusp'' by (simp add: has_laurent_expansion_isolated_0)
  hence "\<forall>\<^sub>F z in at 0. \<not> is_pole fourier z"
    using eventually_not_pole by blast
  hence "\<forall>\<^sub>F z in at_cusp. \<not>is_pole fourier (cusp_q z)"
    unfolding at_cusp_filtermap [symmetric] eventually_filtermap .
  moreover have "\<forall>\<^sub>F z in at_cusp. Im z > c0"
    by (simp add: eventually_at_cusp)
  ultimately show "\<forall>\<^sub>F z in at_cusp. z \<notin> pts"
    by eventually_elim (use fourier_is_pole_cusp_q_iff' in auto)
qed (use laurent_at_cusp'' in auto)

lemma meromorphic_fourier'':
  "fourier meromorphic_on (ball 0 (exp (- 2 * pi * c0))) fourier_poles'"
proof
  show "open (ball 0 (exp (- 2 * pi * c0)))"
    by auto
  show "fourier_poles' \<subseteq> ball 0 (exp (- 2 * pi * c0))"
    using pts_subset by (auto simp: fourier_poles'_def fourier_poles_def)
  show "fourier holomorphic_on ball 0 (exp (- 2 * pi * c0)) - fourier_poles'"
  proof (cases "is_pole fourier 0")
    case True
    thus ?thesis using meromorphic_fourier'
      by (auto simp: meromorphic_on_def fourier_poles'_def)
  next
    case False
    with not_essential_fourier_0 obtain f0 where f0: "fourier \<midarrow>0\<rightarrow> f0"
      by (auto simp: not_essential_def)
    interpret fourier_expansion_holomorphic_at_cusp f c0 pts f0
    proof
      show "(f \<longlongrightarrow> f0) at_cusp"
        using f0 fourier_tendsto_0_iff by fastforce
    qed (use isolated_singularity_at_cusp''' in auto)
    show "fourier holomorphic_on ball 0 (exp (- 2 * pi * c0)) - fourier_poles'"
      by (auto intro!: holomorphic_on_fourier' simp: fourier_poles'_def)
  qed
  show "\<not> z islimpt fourier_poles'" if "z \<in> ball 0 (exp (- 2 * pi * c0))" for z
    using meromorphic_fourier' that
    by (auto simp: meromorphic_on_def fourier_poles'_def islimpt_insert)
  show "isolated_singularity_at fourier z" if "z \<in> fourier_poles'" for z
    using that isolated_singularity_fourier_0 meromorphic_fourier' 
    unfolding fourier_poles'_def meromorphic_on_def by (auto split: if_splits)
  show "not_essential fourier z" if "z \<in> fourier_poles'" for z
    using that meromorphic_fourier' 
    unfolding fourier_poles'_def meromorphic_on_def by (auto split: if_splits)
qed

lemma fourier_expansion_meromorphic_at_cusp_explicit'_plus_const:
  "fourier_expansion_meromorphic_at_cusp_explicit' (\<lambda>x. f x + C) c0 pts (F + fls_const C)"
proof -
  interpret shifted:
     fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. f x + C" c0 pts "F + fls_const C"
    by (intro fourier_expansion_meromorphic_at_cusp_explicit_plus_const)
  show ?thesis
  proof
    show "shifted.fourier has_laurent_expansion F + fls_const C"
      using shifted.laurent_at_cusp''' by blast
    show "is_pole (\<lambda>x. f x + C) x" if "x \<in> pts" for x
      using is_pole_plus_const_iff poles' that by blast
  qed
qed

end


subsection \<open>Composition properties\<close>

interpretation fourier_const:
  fourier_expansion "\<lambda>_. c" c0 "{}"
  by standard (auto intro!: meromorphic_intros open_halfspace_Im_gt)

interpretation fourier_const:
  fourier_expansion_holomorphic_at_cusp "\<lambda>_. c" c0 "{}" c
  by standard (auto intro!: meromorphic_intros open_halfspace_Im_gt)

lemma fourier_const_fourier_eq [simp]: "fourier_const.fourier c = (\<lambda>_. c)"
  by (metis fourier_const.fourier_0 fourier_const.fourier_nz_eq)

interpretation fourier_const:
  fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>_. c" c0 "{}" "fls_const c"
  by standard auto


context fourier_expansion
begin

lemma fourier_expansion_compose: 
  assumes "(\<lambda>x. h (f x)) meromorphic_on {z. Im z > c0} pts"
  shows   "fourier_expansion (\<lambda>x. h (f x)) c0 pts"
  by standard (use pts_subset pts_invariant assms in \<open>auto simp: plus_1\<close>)

lemma fourier_expansion_cmult: "fourier_expansion (\<lambda>x. c * f x) c0 pts"
  by (intro fourier_expansion_compose meromorphic_on_cmult_left meromorphic)

lemma fourier_expansion_scaleR: "fourier_expansion (\<lambda>x. c *\<^sub>R f x) c0 pts"
  by (intro fourier_expansion_compose meromorphic_intros meromorphic)

lemma fourier_expansion_uminus: "fourier_expansion (\<lambda>x. -f x) c0 pts"
  by (intro fourier_expansion_compose meromorphic_intros meromorphic)

lemma fourier_expansion_power: "fourier_expansion (\<lambda>x. f x ^ n) c0 pts"
  by (intro fourier_expansion_compose meromorphic_intros meromorphic)

lemma fourier_expansion_inverse:
  "fourier_expansion (\<lambda>x. inverse (f x)) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z})"
proof
  show "(z + 1 \<in> pts \<union> {z. c0 < Im z \<and> isolated_zero f z}) =
         (z \<in> pts \<union> {z. c0 < Im z \<and> isolated_zero f z})" for z
    using pts_invariant[of z] by (auto simp: isolated_zero_plus1)
  show "(\<lambda>x. inverse (f x)) meromorphic_on {\<tau>. c0 < Im \<tau>} pts \<union> {z. c0 < Im z \<and> isolated_zero f z}"
    using meromorphic_on_inverse [OF meromorphic] by simp
qed (use pts_subset in \<open>auto simp: plus_1\<close>)

lemma fourier_expansion_power_int: 
  "fourier_expansion (\<lambda>x. f x powi n) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z})"
proof
  show "(z + 1 \<in> pts \<union> {z. c0 < Im z \<and> isolated_zero f z}) =
         (z \<in> pts \<union> {z. c0 < Im z \<and> isolated_zero f z})" for z
    using pts_invariant[of z] by (auto simp: isolated_zero_plus1)
  show "(\<lambda>x. f x powi n) meromorphic_on {\<tau>. c0 < Im \<tau>} pts \<union> {z. c0 < Im z \<and> isolated_zero f z}"
    using meromorphic_on_power_int [OF meromorphic, of n] by simp
qed (use pts_subset in \<open>auto simp: plus_1\<close>)

end


context fourier_expansion_meromorphic_at_cusp_explicit
begin

lemma fourier_expansion_meromorphic_at_cusp_explicit_compose: 
  assumes "(\<lambda>x. h (f x)) meromorphic_on {z. Im z > c0} pts"
  assumes "(\<lambda>x. h (fourier x)) has_laurent_expansion H"
  shows   "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. h (f x)) c0 pts H"
proof -
  interpret aux: fourier_expansion "\<lambda>x. h (f x)" c0 pts
    by (rule fourier_expansion_compose [OF assms(1)])
  show ?thesis
  proof
    have "aux.fourier has_laurent_expansion H \<longleftrightarrow> (\<lambda>x. h (fourier x)) has_laurent_expansion H"
      by (rule has_laurent_expansion_cong)
         (auto simp: aux.fourier_def fourier_def eventually_at_filter)
    with assms show "aux.fourier has_laurent_expansion H"
      by simp
  qed (use isolated_singularity_at_cusp'' in auto)
qed

lemma fourier_expansion_meromorphic_at_cusp_explicit_cmult:
  "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. c * f x) c0 pts (fls_const c * F)"
  by (intro fourier_expansion_meromorphic_at_cusp_explicit_compose
            meromorphic_on_cmult_left meromorphic laurent_expansion_intros laurent_at_cusp''')

lemma fourier_expansion_meromorphic_at_cusp_explicit_scaleR:
  "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. c *\<^sub>R f x) c0 pts (fls_const (of_real c) * F)"
  by (intro fourier_expansion_meromorphic_at_cusp_explicit_compose
            meromorphic_intros laurent_expansion_intros laurent_at_cusp''' meromorphic)

lemma fourier_expansion_meromorphic_at_cusp_explicit_uminus:
  "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. -f x) c0 pts (-F)"
  by (intro fourier_expansion_meromorphic_at_cusp_explicit_compose
            meromorphic_intros laurent_expansion_intros laurent_at_cusp''' meromorphic)

lemma fourier_expansion_meromorphic_at_cusp_explicit_power:
  "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. f x ^ n) c0 pts (F ^ n)"
  by (intro fourier_expansion_meromorphic_at_cusp_explicit_compose
            meromorphic_intros laurent_expansion_intros laurent_at_cusp''' meromorphic)

lemma fourier_expansion_meromorphic_at_cusp_explicit_inverse:
  "fourier_expansion_meromorphic_at_cusp_explicit
     (\<lambda>x. inverse (f x)) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z}) (inverse F)"
proof -
  interpret aux: fourier_expansion "\<lambda>x. inverse (f x)" c0 "pts \<union> {z. Im z > c0 \<and> isolated_zero f z}"
    by (rule fourier_expansion_inverse)
  show ?thesis
  proof
    have "aux.fourier has_laurent_expansion inverse F \<longleftrightarrow>
          (\<lambda>x. inverse (fourier x)) has_laurent_expansion inverse F"
      by (rule has_laurent_expansion_cong)
         (auto simp: aux.fourier_def fourier_def eventually_at_filter)
    also have "\<dots>"
      by (intro laurent_expansion_intros laurent_at_cusp''')
    finally show "aux.fourier has_laurent_expansion inverse F" .
  next
    have "\<forall>\<^sub>F x in at_cusp. c0 < Im x \<longrightarrow> \<not> isolated_zero f x"
      using eventually_no_isolated_zero by eventually_elim auto
    thus "\<forall>\<^sub>F x in at_cusp. x \<notin> pts \<union> {z. c0 < Im z \<and> isolated_zero f z}"
      using isolated_singularity_at_cusp'' by (auto simp: eventually_conj_iff)
  qed
qed

lemma fourier_expansion_meromorphic_at_cusp_explicit_power_int:
  "fourier_expansion_meromorphic_at_cusp_explicit
     (\<lambda>x. f x powi n) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z}) (F powi n)"
proof -
  interpret aux: fourier_expansion "\<lambda>x. f x powi n" c0 "pts \<union> {z. Im z > c0 \<and> isolated_zero f z}"
    by (rule fourier_expansion_power_int)
  show ?thesis
  proof
    have "aux.fourier has_laurent_expansion F powi n \<longleftrightarrow>
          (\<lambda>x. fourier x powi n) has_laurent_expansion F powi n"
      by (rule has_laurent_expansion_cong)
         (auto simp: aux.fourier_def fourier_def eventually_at_filter)
    also have "\<dots>"
      by (intro laurent_expansion_intros laurent_at_cusp''')
    finally show "aux.fourier has_laurent_expansion F powi n" .
  next
    have "\<forall>\<^sub>F x in at_cusp. c0 < Im x \<longrightarrow> \<not> isolated_zero f x"
      using eventually_no_isolated_zero by eventually_elim auto
    thus "\<forall>\<^sub>F x in at_cusp. x \<notin> pts \<union> {z. c0 < Im z \<and> isolated_zero f z}"
      using isolated_singularity_at_cusp'' by (auto simp: eventually_conj_iff)
  qed
qed

end



context fourier_expansion_meromorphic_at_cusp
begin

interpretation aux: fourier_expansion_meromorphic_at_cusp_explicit f c0 pts "laurent_expansion fourier 0"
  ..

lemma fourier_expansion_meromorphic_at_cusp_cmult:
  "fourier_expansion_meromorphic_at_cusp (\<lambda>x. c * f x) c0 pts"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. c * f x" c0 pts
                    "fls_const c * laurent_expansion fourier 0"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_cmult)
  show ?thesis ..
qed

lemma fourier_expansion_meromorphic_at_cusp_scaleR:
  "fourier_expansion_meromorphic_at_cusp (\<lambda>x. c *\<^sub>R f x) c0 pts"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. c *\<^sub>R f x" c0 pts
                    "fls_const (of_real c) * laurent_expansion fourier 0"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_scaleR)
  show ?thesis ..
qed

lemma fourier_expansion_meromorphic_at_cusp_uminus:
  "fourier_expansion_meromorphic_at_cusp (\<lambda>x. -f x) c0 pts"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. -f x" c0 pts
                    "-laurent_expansion fourier 0"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_uminus)
  show ?thesis ..
qed

lemma fourier_expansion_meromorphic_at_cusp_power:
  "fourier_expansion_meromorphic_at_cusp (\<lambda>x. f x ^ n) c0 pts"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. f x ^ n" c0 pts
                    "laurent_expansion fourier 0 ^ n"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_power)
  show ?thesis ..
qed

lemma fourier_expansion_meromorphic_at_cusp_inverse:
  "fourier_expansion_meromorphic_at_cusp
     (\<lambda>x. inverse (f x)) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z})"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. inverse (f x)" c0 
                    "pts \<union> {z. Im z > c0 \<and> isolated_zero f z}"
                    "inverse (laurent_expansion fourier 0)"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_inverse)
  show ?thesis ..
qed

lemma fourier_expansion_meromorphic_at_cusp_power_int:
  "fourier_expansion_meromorphic_at_cusp
     (\<lambda>x. f x powi n) c0 (pts \<union> {z. Im z > c0 \<and> isolated_zero f z})"
proof -
  interpret aux': fourier_expansion_meromorphic_at_cusp_explicit "\<lambda>x. f x powi n" c0 
                    "pts \<union> {z. Im z > c0 \<and> isolated_zero f z}"
                    "laurent_expansion fourier 0 powi n"
    by (rule aux.fourier_expansion_meromorphic_at_cusp_explicit_power_int)
  show ?thesis ..
qed

end



locale fourier_expansion_pair =
  f: fourier_expansion f c0 pts1 + g: fourier_expansion g c0 pts2 for f g c0 pts1 pts2
begin

lemma meromorphic1 [meromorphic_intros]: "f meromorphic_on {z. Im z > c0} (pts1 \<union> pts2)"
  using f.meromorphic
  by (rule meromorphic_on_superset_pts)
     (use f.meromorphic g.meromorphic g.pts_subset in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)

lemma meromorphic2 [meromorphic_intros]: "g meromorphic_on {z. Im z > c0} (pts1 \<union> pts2)"
  using g.meromorphic
  by (rule meromorphic_on_superset_pts)
     (use f.meromorphic g.meromorphic g.pts_subset in \<open>auto simp: meromorphic_on_def islimpt_Un\<close>)

lemma combine:
  assumes "(\<lambda>x. h (f x) (g x)) meromorphic_on {z. Im z > c0} (pts1 \<union> pts2)"
  shows   "fourier_expansion (\<lambda>x. h (f x) (g x)) c0 (pts1 \<union> pts2)"
  by unfold_locales
     (use f.pts_subset g.pts_subset f.pts_invariant g.pts_invariant assms
      in  \<open>auto simp: f.plus_1 g.plus_1\<close>)

sublocale add: fourier_expansion "\<lambda>x. f x + g x" c0 "pts1 \<union> pts2"
  by (intro combine meromorphic_intros)

sublocale diff: fourier_expansion "\<lambda>x. f x - g x" c0 "pts1 \<union> pts2"
  by (intro combine meromorphic_intros)

sublocale mult: fourier_expansion "\<lambda>x. f x * g x" c0 "pts1 \<union> pts2"
  by (intro combine meromorphic_intros)

sublocale div:
  fourier_expansion "\<lambda>x. f x / g x" c0 "pts1 \<union> pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}"
proof -
  interpret inv: fourier_expansion "\<lambda>x. inverse (g x)" c0 "pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}"
    by (rule g.fourier_expansion_inverse)
  interpret aux:
    fourier_expansion_pair f "\<lambda>x. inverse (g x)" c0 pts1 "pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}"
    ..
  show "fourier_expansion (\<lambda>x. f x / g x) c0 (pts1 \<union> pts2 \<union> {z. c0 < Im z \<and> isolated_zero g z})"
    using aux.mult.fourier_expansion_axioms by (simp add: field_simps Un_ac)
qed

end


locale fourier_expansion_meromorphic_at_cusp_explicit_pair =
  f: fourier_expansion_meromorphic_at_cusp_explicit f c0 pts1 F + 
  g: fourier_expansion_meromorphic_at_cusp_explicit g c0 pts2 G for f g c0 pts1 pts2 F G
begin

sublocale fourier_expansion_pair f g c0 pts1 pts2 ..

lemmas [laurent_expansion_intros] = f.laurent_at_cusp''' g.laurent_at_cusp'''

lemma combine':
  assumes "(\<lambda>x. h (f x) (g x)) meromorphic_on {z. Im z > c0} (pts1 \<union> pts2)"
  assumes "(\<lambda>x. h (f.fourier x) (g.fourier x)) has_laurent_expansion H"
  shows   "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. h (f x) (g x)) c0 (pts1 \<union> pts2) H"
proof -
  interpret fourier_expansion "\<lambda>x. h(f x) (g x)" c0 "pts1 \<union> pts2"
    by (rule combine [OF assms(1)])
  show ?thesis
  proof
    have "fourier has_laurent_expansion H \<longleftrightarrow>
          (\<lambda>x. h (f.fourier x) (g.fourier x)) has_laurent_expansion H"
      by (rule has_laurent_expansion_cong)
         (auto simp: fourier_def f.fourier_def g.fourier_def eventually_at_filter)
    with assms(2) show "fourier has_laurent_expansion H"
      by simp
  next
    show  "\<forall>\<^sub>F x in at_cusp. x \<notin> pts1 \<union> pts2"
      using f.isolated_singularity_at_cusp'' g.isolated_singularity_at_cusp''
      by (auto simp: eventually_conj_iff)
  qed
qed

sublocale add: fourier_expansion_meromorphic_at_cusp_explicit 
  "\<lambda>x. f x + g x" c0 "pts1 \<union> pts2" "F + G"
  by (intro combine' laurent_expansion_intros meromorphic_intros)

sublocale diff: fourier_expansion_meromorphic_at_cusp_explicit 
  "\<lambda>x. f x - g x" c0 "pts1 \<union> pts2" "F - G"
  by (intro combine' laurent_expansion_intros meromorphic_intros)

sublocale mult: fourier_expansion_meromorphic_at_cusp_explicit 
  "\<lambda>x. f x * g x" c0 "pts1 \<union> pts2" "F * G"
  by (intro combine' laurent_expansion_intros meromorphic_intros)

sublocale div: fourier_expansion_meromorphic_at_cusp_explicit
  "\<lambda>x. f x / g x" c0 "pts1 \<union> pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}" "F / G"
proof -
  interpret inv: fourier_expansion_meromorphic_at_cusp_explicit
    "\<lambda>x. inverse (g x)" c0 "pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}" "inverse G"
    by (rule g.fourier_expansion_meromorphic_at_cusp_explicit_inverse)
  interpret aux:
    fourier_expansion_meromorphic_at_cusp_explicit_pair
      f "\<lambda>x. inverse (g x)" c0 pts1 "pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}" F "inverse G" ..
  show "fourier_expansion_meromorphic_at_cusp_explicit (\<lambda>x. f x / g x) c0
          (pts1 \<union> pts2 \<union> {z. c0 < Im z \<and> isolated_zero g z}) (F / G)"
    using aux.mult.fourier_expansion_meromorphic_at_cusp_explicit_axioms
    by (simp add: field_simps Un_ac)
qed

end


locale fourier_expansion_meromorphic_at_cusp_pair =
  f: fourier_expansion_meromorphic_at_cusp f c0 pts1 + 
  g: fourier_expansion_meromorphic_at_cusp g c0 pts2 for f g c0 pts1 pts2
begin

sublocale fourier_expansion_pair f g c0 pts1 pts2 ..

sublocale fourier_expansion_meromorphic_at_cusp_explicit_pair f g c0 pts1 pts2
  "laurent_expansion f.fourier 0" "laurent_expansion g.fourier 0"
proof
  show "f.fourier has_laurent_expansion laurent_expansion f.fourier 0"
    using f.isolated_singularity_fourier_0 f.not_essential_fourier_0
          not_essential_has_laurent_expansion_0 by blast
  show "g.fourier has_laurent_expansion laurent_expansion g.fourier 0"
    using g.isolated_singularity_fourier_0 g.not_essential_fourier_0
          not_essential_has_laurent_expansion_0 by blast
qed (use f.isolated_singularity_at_cusp''' g.isolated_singularity_at_cusp''' in auto)

sublocale add: fourier_expansion_meromorphic_at_cusp 
  "\<lambda>x. f x + g x" c0 "pts1 \<union> pts2" ..

sublocale diff: fourier_expansion_meromorphic_at_cusp 
  "\<lambda>x. f x - g x" c0 "pts1 \<union> pts2" ..

sublocale mult: fourier_expansion_meromorphic_at_cusp 
  "\<lambda>x. f x * g x" c0 "pts1 \<union> pts2" ..

sublocale div: fourier_expansion_meromorphic_at_cusp 
  "\<lambda>x. f x / g x" c0 "pts1 \<union> pts2 \<union> {z. Im z > c0 \<and> isolated_zero g z}" ..

end

end
