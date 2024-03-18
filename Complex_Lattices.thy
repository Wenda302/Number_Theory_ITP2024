theory Complex_Lattices
  imports "HOL-Complex_Analysis.Residue_Theorem" Library_Extras 
begin

lemma inj_complex_plus_real: 
  assumes "Im z \<noteq> 0"
  shows "inj (\<lambda>(\<alpha>,\<beta>). of_real \<alpha> * z + of_real \<beta>)"
proof -
  have 1: "a = c" if "of_real a * z + of_real b = of_real c * z + of_real d"
    for a b c d
    using that assms by (cases z) (auto simp: plus_complex.code)
  then have "b = d" if "of_real a * z + of_real b = of_real c * z + of_real d"
    for a b c d
    using that by fastforce
  with 1 show ?thesis
    by (auto simp: inj_on_def)
qed

lemma of_real_eq_of_int_iff [simp]: "of_real x = of_int n \<longleftrightarrow> x = of_int n"
  by (metis of_real_eq_iff of_real_of_int_eq)

lemma of_int_eq_of_real_iff [simp]: "of_int n = of_real x \<longleftrightarrow> x = of_int n"
  by (metis of_real_eq_iff of_real_of_int_eq)


section \<open>Introduction\<close>

section \<open>Doubly Periodic Functions\<close>

(* definition in 1.2 p.1 *)
definition is_periodic:: "'b :: ab_group_add \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_periodic \<omega> f \<equiv> \<forall>z. f (z + \<omega>) = f (z)"

lemma is_periodicD: "is_periodic \<omega> f \<Longrightarrow> f x = f (x + \<omega>)"
  by (auto simp: is_periodic_def)

lemma is_periodic: "is_periodic \<omega> f \<longleftrightarrow> (\<lambda>z. f (z + \<omega>)) = f"
  by (auto simp: is_periodic_def fun_eq_iff)

lemma is_periodic_const [intro]: "is_periodic x (\<lambda>x. c)"
  by (simp add: is_periodic_def)

lemma is_periodic_compose:
  assumes "is_periodic x f"
  shows   "is_periodic x (\<lambda>x. g (f x))"
  using assms unfolding is_periodic_def by auto

lemma is_periodic_minus [simp]: "is_periodic (-\<omega>) f \<longleftrightarrow> is_periodic \<omega> f"
  unfolding is_periodic_def
  using add_diff_cancel diff_add_cancel
  by (metis ab_group_add_class.ab_diff_conv_add_uminus)

lemma is_periodic_plus: 
  "\<lbrakk>is_periodic \<omega>1 f; is_periodic \<omega>2 f\<rbrakk> \<Longrightarrow> is_periodic (\<omega>1+\<omega>2) f"
  unfolding is_periodic_def by (metis add.assoc)

lemma is_periodic_diff: 
  "\<lbrakk>is_periodic \<omega>1 f; is_periodic \<omega>2 f\<rbrakk> \<Longrightarrow> is_periodic (\<omega>1-\<omega>2) f"
  by (metis is_periodic_minus is_periodic_plus uminus_add_conv_diff)

lemma is_periodic_times_nat:
  "is_periodic \<omega> f \<Longrightarrow> is_periodic (of_nat n * \<omega> :: 'a :: comm_ring_1) f"
proof (induction n)
  case 0
  then show ?case by (simp add: is_periodic_def)
next
  case (Suc n)
  then show ?case 
    by (simp add: is_periodic_def add.commute distrib_left group_cancel.add2 mult.commute)
qed

lemma is_periodic_times_int:
  "is_periodic \<omega> f \<Longrightarrow> is_periodic (of_int n * \<omega> :: 'a :: comm_ring_1) f"
  by (rule int_cases2 [of n]) (use is_periodic_times_nat in auto)

lemma is_periodic_plus_times:
  "\<lbrakk>is_periodic \<omega>1 f; is_periodic \<omega>2 f\<rbrakk> \<Longrightarrow>
    is_periodic (of_int m * \<omega>1 + of_int n * \<omega>2 :: 'a :: comm_ring_1) f"
  by (simp add: is_periodic_plus is_periodic_times_int)

lemma is_periodic_comp_plus_eq: "is_periodic \<omega> f \<Longrightarrow> f \<circ> (+) \<omega> = f"
  by (auto simp: is_periodic_def fun_eq_iff add.commute)

lemma is_periodic_pole_minus:
  assumes "is_periodic \<omega> f" 
  shows "is_pole f (z - \<omega>) \<longleftrightarrow> is_pole f (z :: complex)"
  using assms
  unfolding is_pole_def by (metis filterlim_shift_iff is_periodic_comp_plus_eq) 

lemma is_periodic_pole_plus:
  assumes "is_periodic \<omega> f" 
  shows "is_pole f (z + \<omega>) \<longleftrightarrow> is_pole f (z :: complex)"
  using assms
  by (metis is_periodic_comp_plus_eq is_pole_shift_iff)

lemma is_periodic_holomorphic_plus:
  assumes "f holomorphic_on S" "is_periodic \<omega> f"
  shows "f holomorphic_on ((+)\<omega> ` S)"
proof (clarsimp simp add: holomorphic_on_def field_differentiable_def)
  fix x
  assume "x \<in> S"
  obtain f' where "(f has_field_derivative f') (at x within S)"
    using \<open>x \<in> S\<close> assms(1) field_differentiable_def holomorphic_on_def by blast
  then have "((\<lambda>x. f (\<omega>+x)) has_field_derivative f') (at x within S)"
    using assms by (simp add: is_periodic add.commute)
  then show "\<exists>f'. (f has_field_derivative f') (at (\<omega> + x) within (+) \<omega> ` S)"
    using DERIV_at_within_shift by blast
qed

lemma is_periodic_analytic_plus:
  assumes "f analytic_on S" "is_periodic \<omega> f"
  shows "f analytic_on ((+)\<omega> ` S)"
  using assms ball_translation is_periodic_holomorphic_plus 
  unfolding analytic_on_def by fastforce

lemma punctured_ball_translate:
  fixes z::"'a::{real_normed_vector,ab_group_add}"
  shows "(+)\<omega> ` (ball z r - {z}) = ball (z+\<omega>) r - {z+\<omega>}"   (is "?lhs = ?rhs")
proof -
  have "?lhs = ball (z + \<omega>) r - (+) \<omega> ` {z}"
    by (simp add: translation_diff)
  also have "... = ?rhs"
    by (simp add: add.commute)
  finally show ?thesis .
qed

lemma isolated_singularity_plus:
  assumes "isolated_singularity_at f z" "is_periodic \<omega> f"
  shows "isolated_singularity_at f (z + \<omega>)"
  using assms by (metis punctured_ball_translate isolated_singularity_at_def is_periodic_analytic_plus)

lemma periodic_isolated_singularity_plus_iff:
  assumes "is_periodic \<omega> f" 
  shows "isolated_singularity_at f (z + \<omega>) \<longleftrightarrow> isolated_singularity_at f z"
  by (metis add_diff_cancel_left' assms diff_add_cancel is_periodic_minus isolated_singularity_plus minus_diff_eq)

lemma periodic_not_essential_plus_iff:
  assumes "is_periodic \<omega> f" 
  shows "not_essential f (z + \<omega>) \<longleftrightarrow> not_essential f z"
proof -
  have "(\<exists>x. f \<midarrow>z + \<omega>\<rightarrow> x) \<longleftrightarrow> (\<exists>x. f \<midarrow>z\<rightarrow> x)"
    using assms 
    by (metis add_diff_cancel_right' filterlim_shift_iff 
        is_periodic_comp_plus_eq)
  with is_periodic_pole_plus[OF assms] 
  show ?thesis
    unfolding not_essential_def by auto
qed

(* definition in 1.2 p.2 *)
definition is_doubly_periodic:: "complex \<Rightarrow> complex \<Rightarrow> (complex \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_doubly_periodic \<omega>1 \<omega>2 f \<equiv> is_periodic \<omega>1 f \<and> is_periodic \<omega>2 f \<and> Im (\<omega>2/\<omega>1) \<noteq> 0"

lemma is_doubly_periodic_const [intro]: "Im (\<omega>2 / \<omega>1) \<noteq> 0 \<Longrightarrow> is_doubly_periodic \<omega>1 \<omega>2 (\<lambda>x. c)"
  by (simp add: is_doubly_periodic_def is_periodic_const)

lemma is_periodic_compose2:
  assumes "is_periodic x f" "is_periodic x g"
  shows   "is_periodic x (\<lambda>x. h (f x) (g x))"
  using assms unfolding is_periodic_def by auto

lemma is_doubly_periodic_compose:
  assumes "is_doubly_periodic x1 x2 f"
  shows   "is_doubly_periodic x1 x2 (\<lambda>x. g (f x))"
  using assms unfolding is_doubly_periodic_def
  by (intro conjI is_periodic_compose[where g = g]) auto

lemma is_doubly_periodic_compose2:
  assumes "is_doubly_periodic x1 x2 f" "is_doubly_periodic x1 x2 g"
  shows   "is_doubly_periodic x1 x2 (\<lambda>x. h (f x) (g x))"
  using assms unfolding is_doubly_periodic_def
  by (intro conjI is_periodic_compose2[where h = h]) auto


definition triangle:: "complex \<Rightarrow> complex \<Rightarrow> complex set" where
  "triangle \<omega>1 \<omega>2 \<equiv> 
     {z. \<exists>\<alpha> \<beta>. z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2 \<and> \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<and> \<alpha> + \<beta> \<le> 1}"

lemma triangle_altdef: "triangle \<omega>1 \<omega>2 = convex hull {0, \<omega>1, \<omega>2}"
  unfolding convex_hull_3_alt triangle_def scaleR_conv_of_real by auto

lemma triangleI [simp, intro]: "0 \<in> triangle \<omega>1 \<omega>2" "\<omega>1 \<in> triangle \<omega>1 \<omega>2" "\<omega>2 \<in> triangle \<omega>1 \<omega>2"
  unfolding triangle_altdef by (simp_all add: hull_inc)

lemma is_doubly_periodic_imp_is_periodic: 
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "is_periodic (of_int m * \<omega>1 + of_int n * \<omega>2) f"
  by (meson assms is_doubly_periodic_def is_periodic_plus_times)

lemma is_periodic_image: 
  assumes "is_periodic \<omega> f" 
  shows "f ` (+) \<omega> ` A = f ` A"
  using assms by (simp add: is_periodic_def image_image add.commute)

lemma is_doubly_periodic_image: 
  assumes "is_doubly_periodic \<omega>1 \<omega>2 f" 
  shows "f ` (+) (of_int m * \<omega>1 + of_int n * \<omega>2) ` A = f ` A"
  by (meson assms is_doubly_periodic_imp_is_periodic is_periodic_image)

lemma Im_divide_zero_iff: "Im (z/w) = 0 \<longleftrightarrow> Im (w/z) = 0"
  by (auto simp: Im_divide mult.commute)

lemma Im_divide_minus_iff: "Im (-z/w) = 0 \<longleftrightarrow> Im (z/w) = 0"
  by (auto simp: Im_divide mult.commute)

lemma Im_divide_mult_iff: "Im (of_real c * z / w) = 0 \<longleftrightarrow> Im (z/w) = 0 \<or> c=0"
  by (auto simp: Im_divide mult.commute)

lemma Im_divide_zero_trans: "\<lbrakk>Im (u/w) = 0; Im (w/z) = 0; w \<noteq> 0\<rbrakk> \<Longrightarrow> Im (u/z) = 0"
  apply (simp flip: complex_is_Real_iff)
  by (metis (no_types) Reals_mult nonzero_eq_divide_eq times_divide_eq_right)


section \<open> Fundamental Pairs of Periods \<close>

locale pre_gen_lattice =
  fixes \<omega>1 \<omega>2:: "complex"
begin

definition omega:: "complex set" ("\<Omega>") where
  "\<Omega> \<equiv> {\<omega>. \<exists>m n. \<omega> = of_int m * \<omega>1 + of_int n * \<omega>2}"

definition omega_minus_zero:: "complex set" ("\<Omega>*") where
  "\<Omega>* \<equiv> \<Omega> - {0}"

lemma omegaI: "of_int m * \<omega>1 + of_int n * \<omega>2 \<in> \<Omega>"
  using omega_def by auto

lemma omegaE: 
  assumes "\<omega> \<in> \<Omega>" obtains m n where "\<omega> = of_int m * \<omega>1 + of_int n * \<omega>2"
  using assms omega_def by auto

lemma omegaI1: "\<omega>1 \<in> \<Omega>"
  using omegaI [of 1 0] by simp

lemma omegaI2: "\<omega>2 \<in> \<Omega>"
  using omegaI [of 0 1] by simp

lemma zero_in_omega [iff]: "0 \<in> \<Omega>"
  by (metis group_cancel.rule0 mult_zero_left of_int_0 omegaI)

lemma zero_notin_omega_mz: "0 \<notin> \<Omega>*" and omega_omega_minus_zero: "\<Omega> = insert 0 \<Omega>*"
  by (auto simp: omega_minus_zero_def)

lemma omega_minus: "x \<in> \<Omega> \<Longrightarrow> -x \<in> \<Omega>"
  by (clarsimp simp add: omega_def) (metis add_uminus_conv_diff mult_minus_left of_int_minus)

lemma omega_minus_iff: "-x \<in> \<Omega> \<longleftrightarrow> x \<in> \<Omega>"
  using omega_minus[of x] omega_minus[of "-x"] by auto

lemma omega_minus_zero_minus_iff: "-x \<in> \<Omega>* \<longleftrightarrow> x \<in> \<Omega>*"
  by (auto simp: omega_minus_zero_def omega_minus_iff)

lemma omega_add [intro]: "\<lbrakk>x \<in> \<Omega>; y \<in> \<Omega>\<rbrakk> \<Longrightarrow> x+y \<in> \<Omega>"
  by (clarsimp simp add: omega_def) (metis (no_types, lifting) add.commute add.left_commute combine_common_factor of_int_add)

lemma omega_diff [intro]: "\<lbrakk>x \<in> \<Omega>; y \<in> \<Omega>\<rbrakk> \<Longrightarrow> x-y \<in> \<Omega>"
  by (metis add_uminus_conv_diff omega_add omega_minus)

lemma omega_mult_left [intro]: 
  assumes "x \<in> \<Omega>" "y \<in> \<int>"
  shows   "y * x \<in> \<Omega>"
proof -
  from assms obtain a b n where *: "x = of_int a * \<omega>1 + of_int b * \<omega>2" "y = of_int n"
    by (auto elim!: omegaE Ints_cases)
  hence "y * x = of_int (n * a) * \<omega>1 + of_int (n * b) * \<omega>2"
    by (simp add: algebra_simps)
  thus ?thesis
    unfolding omega_def by blast
qed

lemma omega_mult_right [intro]: 
  assumes "x \<in> \<Omega>" "y \<in> \<int>"
  shows   "x * y \<in> \<Omega>"
  using omega_mult_left[OF assms] by (simp add: mult.commute)

lemma omega_is_periodic:
  "\<lbrakk>\<omega> \<in> \<Omega>; is_doubly_periodic \<omega>1 \<omega>2 f\<rbrakk> \<Longrightarrow> is_periodic \<omega> f"
  unfolding is_doubly_periodic_def is_periodic_plus_times omega_def 
  using is_periodic_plus_times by blast

lemma omega_shift_omega:
  assumes "\<omega> \<in> \<Omega>"
  shows "(+)\<omega> ` \<Omega> = \<Omega>"
proof
  show "(+) \<omega> ` \<Omega> \<subseteq> \<Omega>"
    using assms by (simp add: image_subset_iff omega_add)
  show "\<Omega> \<subseteq> (+) \<omega> ` \<Omega>"
    unfolding subset_iff image_iff
    by (metis add_diff_cancel_left' add_diff_eq assms omega_diff)
qed

lemma \<omega>12_continuous_on:
  "continuous_on UNIV (\<lambda>(x::real,y::real). x * \<omega>1 + y * \<omega>2)"
proof (rule linear_continuous_on)
  define ff where "ff=(\<lambda>(x::real,y::real). x * \<omega>1 + y * \<omega>2)"
  have "norm (x * \<omega>1 + y * \<omega>2) \<le> norm (x,y) * sqrt (Re(\<omega>1 * cnj \<omega>1  + \<omega>2 * cnj \<omega>2))"
        for x y :: real
  proof -
    define w1a w1b w2a w2b where "w1a=Re \<omega>1" and "w1b=Im \<omega>1" and
      "w2a=Re \<omega>2" and "w2b=Im \<omega>2"
  
    have "cmod (x * \<omega>1 + y * \<omega>2)^2 \<le> 
            (norm (x,y) * sqrt (Re (\<omega>1 * cnj \<omega>1 + \<omega>2 * cnj \<omega>2)))^2"
      unfolding  power_mult_distrib cmod_power2
      apply (simp add:norm_Pair algebra_simps power2_eq_square
              flip:w1a_def w1b_def w2a_def w2b_def)
      by (sos "(((A<0 * R<1) + (R<1 * ((R<1 * [~1*x__*w2a__ + y__*w1a__]^2) 
                + (R<1 * [~1*x__*w2b__ + y__*w1b__]^2)))))")
    moreover have "0 \<le> norm (x,y) * sqrt (Re (\<omega>1 * cnj \<omega>1 + \<omega>2 * cnj \<omega>2))"
       by simp
    ultimately show ?thesis 
      using power2_le_imp_le by blast
  qed
  then have "bounded_linear_axioms ff"
    unfolding bounded_linear_axioms_def ff_def by auto
  moreover have "linear ff"
    unfolding ff_def 
    by (auto intro!:linearI simp:algebra_simps scaleR_conv_of_real)
  ultimately show "bounded_linear ff" 
    unfolding bounded_linear_def by auto
qed

lemma countable_omega: "countable \<Omega>"
proof -
  have "\<Omega> = (\<lambda>(m,n). of_int m * \<omega>1 + of_int n * \<omega>2) ` UNIV"
    by (auto simp: omega_def)
  also have "countable \<dots>"
    by (intro countable_image) auto
  finally show ?thesis .
qed

definition of_\<omega>12_coords :: "real \<times> real \<Rightarrow> complex" where
  "of_\<omega>12_coords = (\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2)"

lemma linear_of_\<omega>12_coords: "linear of_\<omega>12_coords"
  by unfold_locales (auto simp: algebra_simps of_\<omega>12_coords_def scaleR_conv_of_real)

definition \<omega>12_coords :: "complex \<Rightarrow> real \<times> real" where
  "\<omega>12_coords = inv_into UNIV of_\<omega>12_coords"

abbreviation "\<omega>1_coord z \<equiv> fst (\<omega>12_coords z)"
abbreviation "\<omega>2_coord z \<equiv> snd (\<omega>12_coords z)"

lemma of_\<omega>12_coords_add [simp]: "of_\<omega>12_coords (z1 + z2) = of_\<omega>12_coords z1 + of_\<omega>12_coords z2"
  and of_\<omega>12_coords_diff [simp]: "of_\<omega>12_coords (z1 - z2) = of_\<omega>12_coords z1 - of_\<omega>12_coords z2"
  and of_\<omega>12_coords_uminus [simp]: "of_\<omega>12_coords (-z1) = -of_\<omega>12_coords z1"
  and of_\<omega>12_coords_fst [simp]: "of_\<omega>12_coords (a, 0) = of_real a * \<omega>1"
  and of_\<omega>12_coords_snd [simp]: "of_\<omega>12_coords (0, a) = of_real a * \<omega>2"
  and of_\<omega>12_coords_scaleR [simp]: "of_\<omega>12_coords (c *\<^sub>R z) = c *\<^sub>R of_\<omega>12_coords z"
  and of_\<omega>12_coords_scaleR': "of_\<omega>12_coords (c *\<^sub>R z) = of_real c * of_\<omega>12_coords z"
  and of_\<omega>12_coords_0 [simp]: "of_\<omega>12_coords 0 = 0"
  by (simp_all add: of_\<omega>12_coords_def algebra_simps case_prod_unfold 
                    scaleR_prod_def scaleR_conv_of_real)

lemma omega_altdef: "\<Omega> = of_\<omega>12_coords ` (\<int> \<times> \<int>)"
proof -
  have "\<Omega> = of_\<omega>12_coords ` map_prod of_int of_int ` (UNIV \<times> UNIV)"
    unfolding omega_def map_prod_image 
    by (force simp: of_\<omega>12_coords_def case_prod_unfold)
  also have "map_prod of_int of_int ` (UNIV \<times> UNIV) = ((\<int> \<times> \<int>) :: (real \<times> real) set)"
    by (auto elim!: Ints_cases)
  finally show ?thesis .
qed

end



locale gen_lattice = pre_gen_lattice +
  assumes ratio_notin_real: "Im (\<omega>2/\<omega>1) \<noteq> 0"
begin

lemma inj_plus_times: 
  shows "inj (\<lambda>(\<alpha>,\<beta>). of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2)"
proof -
  have "\<omega>1 \<noteq> 0"
    using ratio_notin_real by force
  moreover have "inj (\<lambda>(\<alpha>,\<beta>). of_real \<alpha> + of_real \<beta> * (\<omega>2/\<omega>1))"
    using inj_complex_plus_real [OF ratio_notin_real] by (auto simp: inj_on_def add.commute)
  ultimately show ?thesis  
    apply (simp add:inj_on_def)
    by (simp add: add_divide_eq_iff)
qed

lemma \<omega>1\<omega>2_decompose:
  obtains \<alpha> \<beta> where "z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2"
proof -
  define dd where "dd \<equiv> Re \<omega>2 * Im \<omega>1 -  Im \<omega>2 * Re \<omega>1"
  have "dd \<noteq> 0" 
    using ratio_notin_real unfolding dd_def Im_complex_div_eq_0
    by auto

  define \<alpha> where "\<alpha> = (Im z * Re \<omega>2 - Re z * Im \<omega>2) / dd"
  define \<beta> where "\<beta> = (Re z * Im \<omega>1 - Im z * Re \<omega>1) / dd"

  have "\<alpha> * Re \<omega>1 + \<beta> * Re \<omega>2= Re z"
    using \<open>dd \<noteq> 0\<close> unfolding \<alpha>_def \<beta>_def 
    apply (auto simp:divide_simps)
    by (auto simp:algebra_simps dd_def)
  moreover have "\<alpha> * Im \<omega>1 + \<beta> * Im \<omega>2= Im z"
    using \<open>dd \<noteq> 0\<close> unfolding \<alpha>_def \<beta>_def 
    apply (auto simp:divide_simps)
    by (auto simp:algebra_simps dd_def)
  ultimately have "z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2"
    by (simp add: complex_eqI)
  then show ?thesis using that by simp
qed

lemma surj_plus_times: 
  shows "surj (\<lambda>(\<alpha>,\<beta>). of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2)"
unfolding surj_def
proof 
  fix z
  obtain \<alpha> \<beta> where "z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2" 
    using \<omega>1\<omega>2_decompose by auto
  then show "\<exists>x. z = (case x of
                  (\<alpha>, \<beta>) \<Rightarrow> complex_of_real \<alpha> * \<omega>1 + complex_of_real \<beta> * \<omega>2)"
    by auto
qed

lemma eq_zero_iff: "of_real r1 * \<omega>1 + of_real r2 * \<omega>2 = 0 \<longleftrightarrow> r1=0 \<and> r2=0"
  using inj_plus_times
  by (simp add: inj_on_def) (metis group_cancel.rule0 mult_eq_0_iff of_real_0)

lemma eq_\<omega>1_iff [simp]: "of_real r1 * \<omega>1 + of_real r2 * \<omega>2 = \<omega>1 \<longleftrightarrow> r1=1 \<and> r2=0"
  using inj_plus_times
  by (simp add: inj_on_def) (metis group_cancel.rule0 mult_cancel_right2 mult_zero_left of_real_0 of_real_1)

lemma eq_\<omega>2_iff [simp]: "of_real r1 * \<omega>1 + of_real r2 * \<omega>2 = \<omega>2 \<longleftrightarrow> r1=0 \<and> r2=1"
  using inj_plus_times
  by (simp add: inj_on_def) (metis add.left_neutral mult_cancel_right2 mult_zero_left of_real_0 of_real_1)

lemma inj_plus_times_int: 
  shows "inj (\<lambda>(\<alpha>,\<beta>). of_int \<alpha> * \<omega>1 + of_int \<beta> * \<omega>2)"
  using inj_plus_times
  by (simp add: inj_on_def) (metis of_int_eq_iff of_real_of_int_eq)

lemma eq_\<omega>12_iff: 
  "of_real r1 * \<omega>1 + of_real r2 * \<omega>2 = of_real s1 * \<omega>1 + of_real s2 * \<omega>2 \<longleftrightarrow> r1=s1 \<and> r2=s2"
  using inj_plus_times by (auto simp: inj_on_def)

lemma eq_\<omega>12_iff_int: 
  "of_int r1 * \<omega>1 + of_int r2 * \<omega>2 = of_int s1 * \<omega>1 + of_int s2 * \<omega>2 \<longleftrightarrow> r1=s1 \<and> r2=s2"
  using inj_plus_times_int by (auto simp: inj_on_def)

lemma omega_distinct [iff]: "\<omega>1 \<noteq> \<omega>2" "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0"
  using Im_divide ratio_notin_real by auto

lemma indep12: "independent {\<omega>1,\<omega>2}"
  by (rule independent_insertI) (use Im_divide ratio_notin_real span_singleton in force)+

lemma span12: "span {\<omega>1, \<omega>2} = UNIV"
  by (simp add: dim_eq_card_independent [OF indep12] flip: eucl.dim_eq_full)

lemma of_\<omega>12_coords_\<omega>12_coords [simp]: "of_\<omega>12_coords (\<omega>12_coords z) = z"
proof -
  have "(\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2) \<circ> inv_into UNIV (\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2) = id"
    using surj_plus_times unfolding surj_iff .
  thus ?thesis by (simp add: o_def fun_eq_iff case_prod_unfold \<omega>12_coords_def of_\<omega>12_coords_def)
qed

lemma \<omega>12_coords_of_\<omega>12_coords [simp]: "\<omega>12_coords (of_\<omega>12_coords z) = z"
proof -
  have "inv_into UNIV (\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2) \<circ> (\<lambda>(x,y). of_real x * \<omega>1 + of_real y * \<omega>2) = id"
    using inj_plus_times unfolding inj_iff .
  thus ?thesis by (simp_all add: o_def fun_eq_iff case_prod_unfold \<omega>12_coords_def of_\<omega>12_coords_def)
qed

lemma \<omega>12_coords_eqI:
  assumes "of_\<omega>12_coords a = b"
  shows   "\<omega>12_coords b = a"
  unfolding assms[symmetric] by auto

lemma \<omega>12_coords_add [simp]: "\<omega>12_coords (z1 + z2) = \<omega>12_coords z1 + \<omega>12_coords z2"
  and \<omega>12_coords_diff [simp]: "\<omega>12_coords (z1 - z2) = \<omega>12_coords z1 - \<omega>12_coords z2"
  and \<omega>12_coords_uminus [simp]: "\<omega>12_coords (-z1) = -\<omega>12_coords z1"
  and \<omega>12_coords_times_\<omega>1 [simp]: "\<omega>12_coords (of_real a * \<omega>1) = (a, 0)"
  and \<omega>12_coords_times_\<omega>2 [simp]: "\<omega>12_coords (of_real a * \<omega>2) = (0, a)"
  and \<omega>12_coords_times_\<omega>1' [simp]: "\<omega>12_coords (\<omega>1 * of_real a) = (a, 0)"
  and \<omega>12_coords_times_\<omega>2' [simp]: "\<omega>12_coords (\<omega>2 * of_real a) = (0, a)"
  and \<omega>12_coords_\<omega>1 [simp]: "\<omega>12_coords \<omega>1 = (1, 0)"
  and \<omega>12_coords_\<omega>2 [simp]: "\<omega>12_coords \<omega>2 = (0, 1)"
  and \<omega>12_coords_0 [simp]: "\<omega>12_coords 0 = 0"
  and \<omega>12_coords_scaleR [simp]: "\<omega>12_coords (c *\<^sub>R z) = c *\<^sub>R \<omega>12_coords z"
  and \<omega>12_coords_mult_of_real [simp]: "\<omega>12_coords (of_real c * z) = c *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_mult_of_int [simp]: "\<omega>12_coords (of_int i * z) = of_int i *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_mult_of_nat [simp]: "\<omega>12_coords (of_nat n * z) = of_nat n *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_divide_of_real [simp]: "\<omega>12_coords (z / of_real c) = \<omega>12_coords z /\<^sub>R c"
  and \<omega>12_coords_mult_numeral [simp]: "\<omega>12_coords (numeral num * z) = numeral num *\<^sub>R  \<omega>12_coords z"
  and \<omega>12_coords_divide_numeral [simp]: "\<omega>12_coords (z / numeral num) = \<omega>12_coords z /\<^sub>R numeral num"
  by (rule \<omega>12_coords_eqI; simp add: scaleR_conv_of_real field_simps; fail)+

lemma of_\<omega>12_coords_eq_iff: "of_\<omega>12_coords z1 = of_\<omega>12_coords z2 \<longleftrightarrow> z1 = z2"
  using \<omega>12_coords_eqI by blast

lemma \<omega>12_coords_eq_iff: "\<omega>12_coords z1 = \<omega>12_coords z2 \<longleftrightarrow> z1 = z2"
  by (metis of_\<omega>12_coords_\<omega>12_coords)

lemma of_\<omega>12_coords_eq_0_iff: "of_\<omega>12_coords z = 0 \<longleftrightarrow> z = 0"
  using of_\<omega>12_coords_eq_iff[of z 0] by simp

lemma \<omega>12_coords_eq_0_0_iff [simp]: "\<omega>12_coords x = (0, 0) \<longleftrightarrow> x = 0"
  by (metis \<omega>12_coords_0 of_\<omega>12_coords_\<omega>12_coords zero_prod_def)

lemma bij_of_\<omega>12_coords: "bij of_\<omega>12_coords"
proof -
  have "\<exists>z'. z = of_\<omega>12_coords z'" for z
    by (rule exI[of _ "\<omega>12_coords z"]) auto
  hence "surj of_\<omega>12_coords"
    by blast
  thus ?thesis
    unfolding bij_def by (auto intro!: injI simp: of_\<omega>12_coords_eq_iff)
qed

lemma \<omega>12_coords_image_eq: "\<omega>12_coords ` X = of_\<omega>12_coords -` X"
  unfolding \<omega>12_coords_def using bij_of_\<omega>12_coords
  by (rule bij_vimage_eq_inv_image [symmetric])

lemma of_\<omega>12_coords_image_eq: "of_\<omega>12_coords ` X = \<omega>12_coords -` X"
  by (metis \<omega>12_coords_image_eq of_\<omega>12_coords_def surj_image_vimage_eq surj_plus_times vimage_UNIV)

lemma of_\<omega>12_coords_linepath:
   "of_\<omega>12_coords (linepath a b x) = linepath (of_\<omega>12_coords a) (of_\<omega>12_coords b) x"
  by (simp add: linepath_def scaleR_prod_def scaleR_conv_of_real
                 of_\<omega>12_coords_def algebra_simps case_prod_unfold)

lemma of_\<omega>12_coords_linepath':
  "of_\<omega>12_coords o (linepath a b) =
      linepath (of_\<omega>12_coords a) (of_\<omega>12_coords b)"
  unfolding comp_def using of_\<omega>12_coords_linepath
  by auto

lemma \<omega>12_coords_linepath:
   "\<omega>12_coords (linepath a b x) = linepath (\<omega>12_coords a) (\<omega>12_coords b) x"
  by (rule \<omega>12_coords_eqI) (simp add: of_\<omega>12_coords_linepath)

lemma of_\<omega>12_coords_in_omega_iff:
  "of_\<omega>12_coords z \<in> \<Omega> \<longleftrightarrow> fst z \<in> \<int> \<and> snd z \<in> \<int>"
proof
  assume "of_\<omega>12_coords z \<in> \<Omega>"
  then obtain m n where mn:
    "of_\<omega>12_coords z = of_int m * \<omega>1 + of_int n * \<omega>2"
    by (auto simp: omega_def)
  hence eq: "(fst z - m) * \<omega>1 = (n - snd z) * \<omega>2"
    by (simp add: algebra_simps of_\<omega>12_coords_def case_prod_unfold)
  have "snd z = n"
  proof (rule ccontr)
    assume "snd z \<noteq> n"
    with eq have "\<omega>2 / \<omega>1 = (fst z - m) / (n - snd z)"
      by (auto simp add: divide_simps mult_ac)
    also have "Im \<dots> = 0"
      by simp
    finally show False
      using ratio_notin_real by contradiction
  qed
  with eq show "fst z \<in> \<int> \<and> snd z \<in> \<int>"
    by simp
qed (auto intro: omegaI elim!: Ints_cases simp: of_\<omega>12_coords_def case_prod_unfold)

lemma of_\<omega>12_coords_in_omega [simp, intro]:
  "fst z \<in> \<int> \<Longrightarrow> snd z \<in> \<int> \<Longrightarrow> of_\<omega>12_coords z \<in> \<Omega>"
  by (subst of_\<omega>12_coords_in_omega_iff) auto

lemma in_omega_conv_\<omega>12_coords: "z \<in> \<Omega> \<longleftrightarrow> \<omega>12_coords z \<in> \<int> \<times> \<int>"
  using of_\<omega>12_coords_in_omega_iff[of "\<omega>12_coords z"] by (auto simp: mem_Times_iff)

lemma \<omega>12_coords_in_Z_times_Z: "z \<in> \<Omega> \<Longrightarrow> \<omega>12_coords z \<in> \<int> \<times> \<int>"
  by (subst (asm) in_omega_conv_\<omega>12_coords) auto


text \<open>Lemma 9.2 of Wilkins: Any holomorphic doubly-periodic function defined throughout 
the complex plane is constant.\<close>
lemma holomorphic_is_doubly_periodic_const:
  assumes holf: "f holomorphic_on UNIV" 
      and is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 f"
  shows "f constant_on UNIV"
proof -
  let ?p = "\<lambda>\<omega>::complex. path_image(\<lambda>s. of_real s * \<omega>)"
  have com: "compact (?p \<omega>)" for \<omega>
    using compact_continuous_image
    by (simp add: compact_path_image continuous_on_mult_right path_def)
  define K where "K \<equiv> (\<Union>x \<in> ?p \<omega>1. \<Union>y \<in> ?p \<omega>2. {x + y})"
  have "compact K"
    unfolding K_def by (simp add: compact_sums' com)
  then have "compact (f ` K)"
    by (meson assms compact_continuous_image continuous_on_subset holomorphic_on_imp_continuous_on subset_UNIV)
  then obtain B where B: "\<And>z. z \<in> K \<Longrightarrow> norm (f z) \<le> B"
    by (meson bounded_iff compact_eq_bounded_closed imageI)
  have "norm (f z) \<le> B" for z
  proof -
    have "z \<in> span {\<omega>1,\<omega>2}"
      by (simp add: span12)
    then obtain t1 t2 where t12: "z = of_real t1 * \<omega>1 + of_real t2 * \<omega>2"
      by (metis add.commute diff_add_cancel right_minus_eq scaleR_conv_of_real singletonD span_breakdown_eq span_empty)
    define r1 where "r1 = t1 - floor t1"
    define r2 where "r2 = t2 - floor t2"
    define w where "w \<equiv> r1 * \<omega>1 + r2 * \<omega>2"
    have w: "z - (\<lfloor>t1\<rfloor> * \<omega>1 + \<lfloor>t2\<rfloor> * \<omega>2) = w"
      by (auto simp: t12 r1_def r2_def w_def left_diff_distrib)
    have 01: "0 \<le> r1" "r1 < 1" "0 \<le> r2" "r2 < 1"
      unfolding r1_def r2_def by linarith+
    then have "w \<in> K"
      by (force simp: w_def K_def path_image_def)
    have "is_periodic (\<lfloor>t1\<rfloor> * \<omega>1 + \<lfloor>t2\<rfloor> * \<omega>2) f"
      by (meson is_doubly_periodic is_doubly_periodic_def is_periodic_plus_times)
    then have "f z = f w"
      by (metis diff_add_cancel is_periodic_def w)
    then show ?thesis
      by (simp add: B \<open>w \<in> K\<close>)
  qed
  then show ?thesis
    by (metis Liouville_theorem boundedI holf image_iff)
qed

text \<open>The next two lemmas correspond to Theorem 1.1 p.3\<close>
lemma triangle_contains_no_multiples:
  assumes zin: "z \<in> triangle \<omega>1 \<omega>2" and znot: "z \<notin> {0, \<omega>1, \<omega>2}"
  shows "z \<noteq> of_int m * \<omega>1 + of_int n * \<omega>2"
proof -
  obtain \<alpha> \<beta> where \<section>: "z = of_real \<alpha> * \<omega>1 + of_real \<beta> * \<omega>2" "\<alpha> \<ge> 0" "\<beta> \<ge> 0" "\<alpha> + \<beta> \<le> 1"
    using triangle_def zin by fastforce
  then have "\<alpha>+\<beta> \<noteq> 0"
    by (smt (z3) add.right_neutral assms(2) insert_iff mult_zero_left of_real_0)
  moreover have "\<alpha> \<noteq> 1" "\<beta> \<noteq> 1"
    using "\<section>" znot by force+
  ultimately obtain "\<alpha> < 1" "\<beta> < 1"  "\<alpha> > 0 \<or> \<beta> > 0"
    using \<section> by linarith
  then have "\<alpha> * \<omega>1 + \<beta> * \<omega>2 \<noteq> of_int m * \<omega>1 + of_int n * \<omega>2" for m n
    using inj_plus_times 
    by (simp add: inj_on_def) (smt (verit, best) of_int_0_less_iff of_int_less_1_iff of_real_of_int_eq)
  with \<section> show ?thesis
    by (simp add: omega_def)
qed


end (* gen_lattice *)


(* first definition p.4 *)
definition are_equivalent :: "[complex, complex, complex, complex] \<Rightarrow> bool" where
  "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2' \<equiv> pre_gen_lattice.omega \<omega>1 \<omega>2 = pre_gen_lattice.omega \<omega>1' \<omega>2'"

text \<open>For theorem 1.2\<close>
lemma int_cases_lemma:
  fixes p::int
  assumes "p * c + q * a = 0" "p * d + q * b = 1"
          "r * c + s * a = 1" "r * d + s * b = 0"
  shows "a * d - b * c = 1 \<or> a * d - b * c = -1"
proof -
  have "r * b * c + s * a * b = b"
    by (metis assms(3) distrib_left mult.left_commute mult.right_neutral)
  moreover have "r * a * d + s * a * b = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  ultimately have "r dvd b"
    by (metis mult.assoc dvd_0_right dvd_add_right_iff dvd_triv_left)
  have "p * r * d + p * s * b = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  moreover have "p * r * d + q * r * b = r"
    by (metis assms(2) int_distrib(2) mult.assoc mult.left_commute mult.right_neutral)
  ultimately have "b dvd r"
    by (metis dvd_0_right mult.commute zdvd_reduce)
  have "r * c * d + s * b * c = 0"
    by (metis assms(4) distrib_left mult.commute mult.left_commute mult_zero_right)
  moreover have "r * c * d + s * a * d = d"
    by (metis assms(3) distrib_left mult.commute mult.right_neutral)
  ultimately have "s dvd d"
    by (metis dvd_0_right dvd_add_times_triv_right_iff mult.assoc mult.commute)
  have "q * r * d + q * s * b = 0"
    by (metis mult.assoc assms(4) int_distrib(2) mult_not_zero)
  moreover have "p * s * d + q * s * b = s"
    by (metis assms(2) int_distrib(2) mult.assoc mult.left_commute mult.right_neutral)
  ultimately have "d dvd s"
    by (metis add.commute dvd_0_right mult.commute zdvd_reduce)
  have "\<bar>b\<bar> = \<bar>r\<bar>" "\<bar>d\<bar> = \<bar>s\<bar>"
    by (meson \<open>b dvd r\<close> \<open>r dvd b\<close> \<open>d dvd s\<close> \<open>s dvd d\<close> zdvd_antisym_abs)+
  then show ?thesis
    by (smt (verit, best) assms(3,4) mult.commute mult_cancel_left mult_eq_0_iff mult_minus_left)
qed

text \<open>For theorem 1.2\<close>
lemma are_equiv_lemma:
  fixes a::int
  assumes "a * d - b * c = 1"
  shows "\<exists>p q. m = b*q + d*p \<and> n = a*q + c*p"
proof -
  obtain p q where m: "1 = b * q + d * p \<and> 0 = a * q + c * p"
    by (smt (verit, ccfv_threshold) assms mult.commute mult_minus_right)
  obtain r s where n: "0 = b * s + d * r \<and> 1 = a * s + c * r"
    by (metis add.commute assms diff_self mult.commute mult_minus_right uminus_add_conv_diff)
  have "m = m * 1 + n * 0"
    by simp
  also have "... = m * (b * q + d * p) + n * (b * s + d * r)"
    using m n by presburger
  also have "\<dots> = ( b * (m*q + n * s)) + ( d *  (m*p+n*r))"
    by (simp add: algebra_simps)
  finally have meq: "m = (b * (m*q + n * s)) + (d * (m*p+n*r))" .
  have "n = m * 0 + n * 1"
    by simp
  also have "... = m * (a * q + c * p) + n * (a * s + c * r)"
    using m n by presburger
  also have "\<dots> = a * (m * q + n * s) + c * (m * p + n * r)"
    by (simp add: algebra_simps)
  finally have neq: "n = a * (m * q + n * s) + c * (m * p + n * r)" .
  show ?thesis
    using meq neq
    by blast
qed


text \<open>Theorem 1.2\<close>
theorem are_equivalent_iff:
  fixes \<omega>1 \<omega>2 \<omega>1' \<omega>2'
  assumes "Im (\<omega>2 / \<omega>1) \<noteq> 0" and "Im (\<omega>2' / \<omega>1') \<noteq> 0"
  shows "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2' \<longleftrightarrow> 
           (\<exists>a b c d. (a*d - b*c = (1::int) \<or> a*d - b*c = -1) \<and> 
                      (\<omega>2' = a*\<omega>2 + b*\<omega>1) \<and> (\<omega>1' = c*\<omega>2 + d*\<omega>1))"
    (is "?lhs = ?rhs")
proof -
  interpret gl: gen_lattice \<omega>1 \<omega>2
    using assms gen_lattice_def by presburger 
  interpret gl': gen_lattice \<omega>1' \<omega>2'
    using assms gen_lattice_def by presburger 
  show ?thesis
  proof
    assume L: ?lhs
    have \<section>: "\<exists>m n. v = of_int m * u + of_int n * v" for u v::complex
      by (metis add.left_neutral mult.left_neutral mult_zero_left of_int_0 of_int_1)
    have "\<omega>2' \<in> gl'.omega"
      by (simp add: gl'.omega_def \<section>)
    then obtain a b where ab: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
      using L by (fastforce simp: are_equivalent_def gl.omega_def algebra_simps)
    have "\<omega>1' \<in> gl'.omega"
      by (simp add: gl'.omega_def) (metis \<section> add.commute)
    then obtain c d where cd: "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      using L by (fastforce simp: are_equivalent_def gl.omega_def algebra_simps)
    have "\<omega>1 \<in> gl.omega"
      by (simp add: gl.omega_def) (metis \<section> add.commute)
    then obtain p q where pq: "\<omega>1 = of_int p * \<omega>1' + of_int q * \<omega>2'"
      using L are_equivalent_def gl'.omega_def by auto
    have "\<omega>2 \<in> gl.omega"
      by (simp add: gl.omega_def \<section>)
    then obtain r s where rs: "\<omega>2 = of_int r * \<omega>1' + of_int s * \<omega>2'"
      using L are_equivalent_def gl'.omega_def by auto

    have "\<omega>1 = p * (c * \<omega>2 + d * \<omega>1) + q * (a * \<omega>2 + b * \<omega>1)"
      using pq cd ab by metis
    also have "... = (p * c + q * a) * \<omega>2 + (p * d + q * b) * \<omega>1"
      by (simp add: algebra_simps)
    finally have pc: "(p * c + q * a) = 0 \<and> p * d + q * b = 1"
      by (metis add.commute gl.eq_\<omega>1_iff of_int_eq_0_iff of_int_eq_1_iff of_real_of_int_eq)
    have "\<omega>2 = r * (c * \<omega>2 + d * \<omega>1) + s * (a * \<omega>2 + b * \<omega>1)"
      using cd rs ab  by blast
    also have "... = (r * c + s * a) * \<omega>2 + (r * d + s * b) * \<omega>1"
      by (simp add: algebra_simps)
    finally have rc: "r * c + s * a = 1 \<and> r * d + s * b = 0"
      by (metis gl.eq_\<omega>2_iff add.commute of_int_1 of_int_eq_0_iff of_int_eq_iff of_real_of_int_eq) 
    with pc have "a*d - b*c = 1 \<or> a*d - b*c = -1"
      by (meson int_cases_lemma)
    then show ?rhs using cd ab by blast
  next
    assume ?rhs
    then obtain a b c d::int where 1: "a * d - b * c = 1 \<or> a * d - b * c = -1"
      and eq: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      by blast
    then consider "a * d - b * c = 1" | "b * c - a * d = 1"
      by linarith
    then show ?lhs
    proof cases
      case 1
      have "\<exists>ma na. of_int m * \<omega>1 + of_int n * \<omega>2 = of_int ma * \<omega>1' + of_int na * \<omega>2'"
        for m n
        using are_equiv_lemma [OF 1, of m n] by clarify (auto simp: algebra_simps eq)
      moreover have "\<exists>ma na. of_int m * \<omega>1' + of_int n * \<omega>2' = of_int ma * \<omega>1 + of_int na * \<omega>2"
        for m n
        using are_equiv_lemma [OF 1, of "-m" "-m"]
        apply (clarsimp simp: eq algebra_simps)
        by (metis (no_types, opaque_lifting) add.assoc distrib_left of_int_add of_int_mult)
      ultimately show ?thesis
        unfolding are_equivalent_def gl.omega_def gl'.omega_def by auto
    next
      case 2
      have "\<exists>ma na. of_int m * \<omega>1 + of_int n * \<omega>2 = of_int ma * \<omega>1' + of_int na * \<omega>2'"
        for m n
        using are_equiv_lemma [OF 2, of n m]
        by clarify (auto simp add: algebra_simps eq)
      moreover have "\<exists>ma na. of_int m * \<omega>1' + of_int n * \<omega>2' = of_int ma * \<omega>1 + of_int na * \<omega>2"
        for m n
        using are_equiv_lemma [OF 2, of "-n" "-m"]
        apply (clarsimp simp: eq algebra_simps)
        by (metis (no_types, opaque_lifting) add.assoc distrib_left of_int_add of_int_mult)
      ultimately show ?thesis
        unfolding are_equivalent_def gl.omega_def gl'.omega_def by auto
    qed
  qed
qed


definition (in gen_lattice) fundamental_pair :: "complex \<Rightarrow> complex \<Rightarrow> bool" where
  "fundamental_pair \<omega>1' \<omega>2' \<longleftrightarrow>
     \<omega>1' \<in> \<Omega> \<and> \<omega>2' \<in> \<Omega> \<and> Im (\<omega>2' / \<omega>1') \<noteq> 0 \<and> omega \<subseteq> pre_gen_lattice.omega \<omega>1' \<omega>2'"



lemma (in gen_lattice) omega_Int_triangle: "triangle \<omega>1 \<omega>2 \<inter> \<Omega> = {0, \<omega>1, \<omega>2}"
proof (intro equalityI subsetI)
  fix x assume x: "x \<in> triangle \<omega>1 \<omega>2 \<inter> \<Omega>"
  then obtain a b where ab: "a \<ge> 0" "b \<ge> 0" "a + b \<le> 1" "x = of_\<omega>12_coords (a, b)"
    by (auto simp: triangle_def of_\<omega>12_coords_def)
  from ab(4) and x have "a \<in> \<int>" "b \<in> \<int>"
    by (auto simp: omega_altdef of_\<omega>12_coords_eq_iff)
  with ab(1-3) have "(a, b) \<in> {(0, 0), (0, 1), (1, 0)}"
    by (auto elim!: Ints_cases)
  with ab show "x \<in> {0, \<omega>1, \<omega>2}"
    by auto
qed (auto simp: omegaI1 omegaI2)  

lemma (in gen_lattice) fundamental_pair_equivalent:
  assumes "fundamental_pair \<omega>1' \<omega>2'"
  shows   "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
  unfolding are_equivalent_def
proof (rule antisym)
  show "\<Omega> \<subseteq> pre_gen_lattice.omega \<omega>1' \<omega>2'"
    using assms by (auto simp: fundamental_pair_def)
next
  interpret \<Omega>': gen_lattice \<omega>1' \<omega>2'
    by unfold_locales (use assms in \<open>auto simp: fundamental_pair_def\<close>)
  from assms have "\<omega>1' \<in> \<Omega>" "\<omega>2' \<in> \<Omega>"
    by (auto simp: fundamental_pair_def)
  thus "\<Omega>'.omega \<subseteq> \<Omega>"
    unfolding \<Omega>'.omega_def using assms by (auto simp: omega_add omega_mult_left)
qed

lemma (in gen_lattice) are_equivalent_imp_ratio_notin_real:
  assumes "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
  shows   "Im (\<omega>2' / \<omega>1') \<noteq> 0"
proof
  assume *: "Im (\<omega>2' / \<omega>1') = 0"
  interpret \<Omega>': pre_gen_lattice \<omega>1' \<omega>2' .
  from * have "\<omega>2' / \<omega>1' \<in> \<real>"
    by (auto simp: complex_is_Real_iff)
  then obtain r where r: "\<omega>2' / \<omega>1' = of_real r"
    by (elim Reals_cases)
  from assms have eq: "\<Omega>'.omega = \<Omega>"
    by (simp add: are_equivalent_def)

  have "z1 / z2 \<in> \<real>" if z12: "z1 \<in> \<Omega>" "z2 \<in> \<Omega>" for z1 z2
  proof (cases "\<omega>1' = 0")
    case True
    thus ?thesis
      using that unfolding eq[symmetric] \<Omega>'.omega_def by auto
  next
    case False
    hence r': "\<omega>2' = of_real r * \<omega>1'"
      using r by (auto simp: field_simps)
    have *: "\<exists>a. z = of_real a * \<omega>1'" if "z \<in> \<Omega>" for z
    proof -
      from that have "z \<in> \<Omega>'.omega"
        unfolding eq by simp
      then obtain m n where "z = of_int m * \<omega>1' + of_int n * \<omega>2'"
        by (auto simp: \<Omega>'.omega_def)
      also have "\<dots> = of_real (of_int m + r * of_int n) * \<omega>1'"
        by (simp add: r' algebra_simps)
      finally show ?thesis
        by blast
    qed
    obtain a b where "z1 = of_real a * \<omega>1'" "z2 = of_real b * \<omega>1'"
      using *[OF z12(1)] *[OF z12(2)] by blast
    thus "z1 / z2 \<in> \<real>"
      by (auto simp: divide_simps)
  qed
  from this[of \<omega>2 \<omega>1] have "\<omega>2 / \<omega>1 \<in> \<real>"
    by (auto simp: omegaI1 omegaI2)
  with ratio_notin_real show False
    by (auto simp: complex_is_Real_iff)
qed

lemma (in gen_lattice) fundamental_pair_iff_equivalent:
  "fundamental_pair \<omega>1' \<omega>2' \<longleftrightarrow> are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
proof
  assume *: "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
  interpret \<Omega>': pre_gen_lattice \<omega>1' \<omega>2' .
  from * have eq: "\<Omega>'.omega = \<Omega>"
    by (simp add: are_equivalent_def)
  have 1: "\<omega>1' \<in> \<Omega>" "\<omega>2' \<in> \<Omega>"
    using \<Omega>'.omegaI1 \<Omega>'.omegaI2 by (simp_all only: eq)
  have 2: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
    using * are_equivalent_imp_ratio_notin_real by blast
  show "fundamental_pair \<omega>1' \<omega>2'"
    unfolding fundamental_pair_def using 1 2 by (simp add: eq)
qed (use fundamental_pair_equivalent in auto)

lemma (in gen_lattice) in_triangle_iff:
  fixes x
  defines "a \<equiv> \<omega>1_coord x" and "b \<equiv> \<omega>2_coord x"
  shows   "x \<in> triangle \<omega>1 \<omega>2 \<longleftrightarrow> a \<ge> 0 \<and> b \<ge> 0 \<and> a + b \<le> 1"
proof -
  have triangle_eq: "triangle \<omega>1 \<omega>2 = {of_\<omega>12_coords (\<alpha>, \<beta>) |\<alpha> \<beta>. 0 \<le> \<alpha> \<and> 0 \<le> \<beta> \<and> \<alpha> + \<beta> \<le> 1}"
    unfolding triangle_def of_\<omega>12_coords_def by simp
  have "x = of_\<omega>12_coords (a, b)"
    by (simp add: a_def b_def)
  also have "\<dots> \<in> triangle \<omega>1 \<omega>2 \<longleftrightarrow> a \<ge> 0 \<and> b \<ge> 0 \<and> a + b \<le> 1"
    by (simp add: triangle_eq of_\<omega>12_coords_eq_iff)
  finally show ?thesis .
qed

lemma (in gen_lattice) fundamental_pair_iff_triangle:
  "fundamental_pair \<omega>1' \<omega>2' \<longleftrightarrow> Im (\<omega>2' / \<omega>1') \<noteq> 0 \<and> triangle \<omega>1' \<omega>2' \<inter> \<Omega> = {0, \<omega>1', \<omega>2'}"
proof
  assume *: "fundamental_pair \<omega>1' \<omega>2'"
  hence "\<omega>1' \<in> \<Omega>" "\<omega>2' \<in> \<Omega>" and nz: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
    by (auto simp: fundamental_pair_def)
  interpret \<Omega>': gen_lattice \<omega>1' \<omega>2'
    by unfold_locales fact+
  from * have "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
    by (simp add: fundamental_pair_equivalent)
  hence eq: "\<Omega>'.omega = \<Omega>"
    by (simp add: are_equivalent_def)
  thus "Im (\<omega>2' / \<omega>1') \<noteq> 0 \<and> triangle \<omega>1' \<omega>2' \<inter> \<Omega> = {0, \<omega>1', \<omega>2'}"
    using \<Omega>'.omega_Int_triangle nz by simp
next
  assume *: "Im (\<omega>2' / \<omega>1') \<noteq> 0 \<and> triangle \<omega>1' \<omega>2' \<inter> \<Omega> = {0, \<omega>1', \<omega>2'}"
  interpret \<Omega>': gen_lattice \<omega>1' \<omega>2'
    by unfold_locales (use * in auto)
  show "fundamental_pair \<omega>1' \<omega>2'"
    unfolding fundamental_pair_def
  proof (intro conjI subsetI)
    fix x assume x: "x \<in> \<Omega>"
    define a b where "a = \<Omega>'.\<omega>1_coord x" and "b = \<Omega>'.\<omega>2_coord x"
    have eq: "x = \<Omega>'.of_\<omega>12_coords (a, b)"
      by (simp add: a_def b_def)
    define y where "y = x - of_int \<lfloor>a\<rfloor> * \<omega>1' - of_int \<lfloor>b\<rfloor> * \<omega>2'"
    have "y \<in> \<Omega>"
      using x * unfolding y_def by (intro omega_diff omega_mult_left) auto

    show "x \<in> \<Omega>'.omega"
    proof (cases "a - real_of_int \<lfloor>a\<rfloor> + (b - real_of_int \<lfloor>b\<rfloor>) \<le> 1")
      case True
      hence "y \<in> triangle \<omega>1' \<omega>2'"
        by (auto simp: y_def \<Omega>'.in_triangle_iff eq)
      hence "y \<in> {0, \<omega>1', \<omega>2'}"
        using * \<open>y \<in> \<Omega>\<close> by auto
      hence "y \<in> \<Omega>'.omega"
        by (auto intro: \<Omega>'.omegaI1 \<Omega>'.omegaI2)
      hence "y + of_int \<lfloor>a\<rfloor> * \<omega>1' + of_int \<lfloor>b\<rfloor> * \<omega>2' \<in> \<Omega>'.omega"
        by (intro \<Omega>'.omega_add \<Omega>'.omega_mult_left \<Omega>'.omegaI1 \<Omega>'.omegaI2) auto
      thus "x \<in> \<Omega>'.omega"
        by (simp add: y_def)
    next
      case False
      define y' where "y' = \<omega>1' + \<omega>2' - y"
      have "a - real_of_int \<lfloor>a\<rfloor> \<le> 1 \<and> b - real_of_int \<lfloor>b\<rfloor> \<le> 1 \<and>
             1 + (real_of_int \<lfloor>a\<rfloor> + (real_of_int \<lfloor>b\<rfloor> + (- b - a))) \<le> 0"
        using False by linarith
      hence "y' \<in> triangle \<omega>1' \<omega>2'"
        unfolding \<Omega>'.in_triangle_iff by (simp add: y_def y'_def eq)
      moreover have "y' \<in> \<Omega>"
        using * unfolding y'_def by (intro omega_diff omega_add \<open>y \<in> \<Omega>\<close>) auto
      ultimately have "y' \<in> {0, \<omega>1', \<omega>2'}"
        using * by blast
      hence "-y' + \<omega>1' + \<omega>2' + of_int \<lfloor>a\<rfloor> * \<omega>1' + of_int \<lfloor>b\<rfloor> * \<omega>2' \<in> \<Omega>'.omega"
        using * \<Omega>'.omegaI1 \<Omega>'.omegaI2
        by (intro \<Omega>'.omega_add \<Omega>'.omega_mult_left \<Omega>'.omega_minus) auto
      thus "x \<in> \<Omega>'.omega"
        by (simp add: y_def y'_def)
    qed
  qed (use * in auto)
qed


text \<open>The definition @{term "triangle"} below represents the triangle with vertices 
$0, \omega_1 \text{ and } \omega_2$ described anticlockwise.\<close>

(*
  TODO: Why does this notion of "fundamental pair" have a function attached to it?
  Later on (e.g. at the beginning of Chapter 2) Apostol uses it without any function attached
  to it. I added a similar notion without a function f called "fundamental_pair" now, 
  but we should sort this out eventually. -- Manuel
  REPLY: Fundamental pair is one of the first and most prominent definitions in the volume,
  given on page 2. Apostol's use of the notion in chapter 2 seems careless, at first sight
  it's simply a pair of complex numbers whose ratio is nonreal. 
  The definition of fundamental_pair given above seemingly refers to what Apostol calls
  "equivalent" (to a previously given pair), page 4. -- LCP
*)
locale fundamental_pair_old = gen_lattice +
  fixes f:: "complex \<Rightarrow> 'a"
  assumes is_doubly_periodic: "is_doubly_periodic \<omega>1 \<omega>2 f"
    and is_fundamental: "\<And>\<omega>. is_periodic \<omega> f \<Longrightarrow> \<omega> \<in> \<Omega>"
begin

text \<open>The next two lemmas correspond to Theorem 1.1 p.3\<close>
lemma triangle_contains_no_periods:
  assumes "z \<in> triangle \<omega>1 \<omega>2" "z \<notin> {0, \<omega>1, \<omega>2}"
  shows "\<not> (is_periodic z f)"
  using triangle_contains_no_multiples [OF assms] is_fundamental omega_def by force


end (* fundamental_pair_old *)

lemma is_fundamental_pair_old:
  fixes \<omega>1 \<omega>2:: complex and f:: "complex \<Rightarrow> 'a"
  assumes f: "is_periodic \<omega>1 f" "is_periodic \<omega>2 f" and nonreal: "Im (\<omega>2/\<omega>1) \<noteq> 0"
      and nonper: "\<And>z. z \<in> triangle \<omega>1 \<omega>2 - {0, \<omega>1, \<omega>2} \<Longrightarrow> \<not> is_periodic z f"
shows "fundamental_pair_old \<omega>1 \<omega>2 f"
proof
  interpret gen_lattice
    using nonreal gen_lattice_def by presburger
  show "is_doubly_periodic \<omega>1 \<omega>2 f"
    by (simp add: assms is_doubly_periodic_def)
  fix \<omega>
  assume \<omega>: "is_periodic \<omega> f"
  have "\<omega> \<in> span {\<omega>1,\<omega>2}"
    by (simp add: span12)
  then obtain t1 t2 where t12: "\<omega> = of_real t1 * \<omega>1 + of_real t2 * \<omega>2"
    by (simp add: span_breakdown_eq) (metis add.commute diff_add_cancel scaleR_conv_of_real)
  define r1 where "r1 = t1 - floor t1"
  define r2 where "r2 = t2 - floor t2"
  have 01: "0 \<le> r1" "r1 < 1" "0 \<le> r2" "r2 < 1"
    unfolding r1_def r2_def by linarith+
  show "\<omega> \<in> \<Omega>" 
  proof (cases "r1=0 \<and> r2=0")
    case True
    with t12 show ?thesis
      unfolding omega_def r1_def r2_def
      by (smt (verit, best) mem_Collect_eq of_real_of_int_eq)
  next
    case False
    define w where "w \<equiv> r1 * \<omega>1 + r2 * \<omega>2"
    have w: "\<omega> - \<lfloor>t1\<rfloor> * \<omega>1 - \<lfloor>t2\<rfloor> * \<omega>2 = w"
      by (auto simp: t12 r1_def r2_def w_def left_diff_distrib)
    with \<omega> f have "is_periodic w f"
      by (metis is_periodic_minus is_periodic_plus is_periodic_times_int uminus_add_conv_diff)
    consider "w \<in> triangle \<omega>1 \<omega>2" | "\<omega>1 + \<omega>2 - w \<in> triangle \<omega>1 \<omega>2"
    proof (cases "r1+r2\<le>1")
      case True
      with that 01 show ?thesis
        by (auto simp: w_def triangle_def)
    next
      case False
      with 01 have "\<omega>1 + \<omega>2 - w \<in> Complex_Lattices.triangle \<omega>1 \<omega>2"
        apply (simp add: triangle_def)
        apply (rule_tac x="1-r1" in exI)
        apply (rule_tac x="1-r2" in exI)
        apply (auto simp: algebra_simps w_def)
        done
      with that show ?thesis
        by (auto simp: w_def triangle_def)
    qed
    then have False
    proof cases
      case 1
      have "w \<notin> {0, \<omega>1, \<omega>2}"
        using False 01 by (auto simp: eq_zero_iff w_def)
      then show ?thesis
        using "1" \<open>is_periodic w f\<close> nonper by auto
    next
      case 2
      have "\<omega>1 + \<omega>2 - w \<notin> {0, \<omega>1, \<omega>2}"
        using False 01 inj_plus_times
        apply (simp add: w_def inj_on_def algebra_simps)
        by (metis eq_\<omega>1_iff eq_\<omega>2_iff less_irrefl mult.commute mult.right_neutral of_real_1)
      then have "\<not> is_periodic (\<omega>1 + \<omega>2 - w) f"
        by (simp add: "2" nonper)
      with f show ?thesis
        by (metis \<open>is_periodic w f\<close> ab_group_add_class.ab_diff_conv_add_uminus is_periodic_minus is_periodic_plus)
    next
    qed
    then show ?thesis ..
  qed
qed (use assms in auto)



subsection \<open>Lemma 1\<close>

context gen_lattice begin

definition omega_iter :: "nat \<Rightarrow> complex set" where
  "omega_iter k =
     of_\<omega>12_coords ` map_prod of_int of_int `
       ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"

lemma in_omega_iter_iff:
  "z \<in> omega_iter k \<longleftrightarrow>
     \<omega>12_coords z \<in> \<int> \<times> \<int> \<inter> ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    unfolding omega_iter_def of_\<omega>12_coords_image_eq by (auto simp: case_prod_unfold)
next
  assume ?rhs
  thus ?lhs unfolding omega_iter_def image_Un map_prod_image of_\<omega>12_coords_image_eq
    by (auto elim!: Ints_cases)
qed

lemma of_\<omega>12_coords_of_int_in_omega_iter:
  "of_\<omega>12_coords (of_int a, of_int b) \<in> omega_iter (nat (max \<bar>a\<bar> \<bar>b\<bar>))"
  unfolding in_omega_iter_iff by (auto simp flip: of_int_minus simp: max_def)

lemma omega_iter_covers: "\<Omega> = (\<Union>k. omega_iter k)"
proof -
  have "(\<Union>k. omega_iter k) = of_\<omega>12_coords ` map_prod real_of_int real_of_int ` 
          (\<Union>k. ({int k, - int k} \<times> {- int k..int k} \<union> {- int k..int k} \<times> {- int k, int k}))"
    (is "_ = _ ` _ ` (\<Union>k. ?A k)") unfolding omega_iter_def by blast
  also have "(\<Union>k. ?A k) = UNIV"
  proof safe
    fix a b :: int
    have "(a, b) \<in> ?A (nat (max \<bar>a\<bar> \<bar>b\<bar>))"
      unfolding max_def by simp linarith
    thus "(a, b) \<in> (\<Union>k. ?A k)"
      by blast
  qed blast+
  also have "range (map_prod real_of_int real_of_int) = \<int> \<times> \<int>"
    by (auto elim!: Ints_cases)
  finally show ?thesis
    by (simp add: omega_altdef)
qed

lemma finite_omega_iter: "finite (omega_iter k)"
  unfolding omega_iter_def by auto

lemma omega_iter_0: "omega_iter 0 = {0}"
  by (auto simp: omega_iter_def)

lemma omega_iter_disjoint:
  assumes "m \<noteq> n"
  shows   "omega_iter m \<inter> omega_iter n = {}"
  using assms by (auto simp: omega_iter_def of_\<omega>12_coords_eq_iff)

lemma card_omega_iter:
  assumes "k > 0"
  shows "card (omega_iter k) = 8 * k"
proof -
  define f where "f = of_\<omega>12_coords \<circ> map_prod real_of_int real_of_int"
  have "omega_iter k = f ` ({int k, - int k} \<times> {- int k..int k} \<union> {- int k..int k} \<times> {- int k, int k})"
    (is "_ = _ ` ?A") unfolding omega_iter_def f_def image_image o_def ..
  also have "card \<dots> = card ?A"
    by (intro card_image)
       (auto simp: inj_on_def of_\<omega>12_coords_eq_iff f_def map_prod_def case_prod_unfold)
  also have "?A = {int k, -int k} \<times> {-int k..int k} \<union> {-int k+1..int k-1} \<times> {-int k, int k}"
    by auto
  also have "card \<dots> = 8 * k" using \<open>k > 0\<close>
    by (subst card_Un_disjoint)
       (auto simp: nat_diff_distrib nat_add_distrib nat_mult_distrib Suc_diff_Suc)
  finally show ?thesis .
qed

lemma omega_iter_nonempty: "omega_iter k \<noteq> {}"
  by (auto simp: omega_iter_def)

definition omega_iter_path :: "complex set" where
  "omega_iter_path = of_\<omega>12_coords ` ({1, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1, 1})"

lemma in_omega_iter_path_iff:
  "z \<in> omega_iter_path \<longleftrightarrow> \<omega>12_coords z \<in> ({1, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1, 1})"
  unfolding omega_iter_path_def of_\<omega>12_coords_image_eq by blast

lemma omega_iter_path_nonempty: "omega_iter_path \<noteq> {}"
proof -
  have "\<omega>1 \<in> omega_iter_path"
    by (auto simp: in_omega_iter_path_iff)
  thus ?thesis by blast
qed

lemma compact_omega_iter_path [intro]: "compact omega_iter_path"
  unfolding omega_iter_path_def of_\<omega>12_coords_def case_prod_unfold
  by (intro compact_continuous_image continuous_intros compact_Un compact_Times) auto

lemma omega_iter_subset_rhombus: "omega_iter k \<subseteq> (*) (of_nat k) ` omega_iter_path"
proof
  fix x
  assume "x \<in> omega_iter k"
  then obtain m n where x: "x = of_\<omega>12_coords (of_int m, of_int n)"
    "(m, n) \<in> ({int k, -int k} \<times> {-int k..int k} \<union> {-int k..int k} \<times> {-int k, int k})"
    unfolding omega_iter_def by blast

  show "x \<in> (*) (of_nat k) ` omega_iter_path"
  proof (cases "k > 0")
    case True
    have "x = of_nat k * of_\<omega>12_coords (of_int m / of_int k, of_int n / of_int k)"
         "(of_int m / of_int k, of_int n / of_int k) \<in> {1::real, -1} \<times> {-1..1} \<union> {-1..1} \<times> {-1::real, 1}"
      using x True by (auto simp: divide_simps of_\<omega>12_coords_def)
    thus ?thesis
      unfolding omega_iter_path_def by blast
  qed (use x in \<open>auto simp: omega_iter_path_def image_iff
                      intro!: exI[of _ "\<omega>1"] bexI[of _ "(1, 0)"]\<close>)
qed

definition Inf_para where \<comment>\<open>@{term r} in the proof of Lemma 1\<close>
  "Inf_para \<equiv> Inf (norm ` omega_iter_path)"

lemma Inf_para_positive: "Inf_para > 0"
proof -
  have "compact (norm ` omega_iter_path)"
    by (intro compact_continuous_image continuous_intros) auto
  hence "Inf_para \<in> norm ` omega_iter_path"
    unfolding Inf_para_def
    by (intro closed_contains_Inf)
       (use omega_iter_path_nonempty in \<open>auto simp: compact_imp_closed bdd_below_norm_image\<close>)
  moreover have "\<forall>x\<in>norm ` omega_iter_path. x > 0"
    by (auto simp: in_omega_iter_path_iff zero_prod_def)
  ultimately show ?thesis
    by blast
qed

lemma Inf_para_le:
  assumes "z \<in> omega_iter_path"
  shows   "Inf_para \<le> norm z"
  unfolding Inf_para_def by (rule cInf_lower) (use assms bdd_below_norm_image in auto)

lemma omega_iter_le_norm: 
  assumes "\<omega> \<in> omega_iter k"
  shows "k * Inf_para \<le> norm \<omega>"
proof -
  obtain z where z: "z \<in> omega_iter_path" "\<omega> = of_nat k * z"
    using omega_iter_subset_rhombus[of k] assms by auto
  have "real k * Inf_para \<le> real k * norm z"
    by (intro mult_left_mono Inf_para_le z) auto
  also have "\<dots> = norm \<omega>"
    by (simp add: z norm_mult)
  finally show ?thesis .
qed

corollary Inf_para_le_norm: 
  assumes "\<omega> \<in> \<Omega>*"
  shows "Inf_para \<le> norm \<omega>"
proof -
  obtain k where \<omega>: "\<omega> \<in> omega_iter k" and "k \<noteq> 0"
    by (metis DiffE UN_iff assms omega_iter_0 omega_iter_covers omega_minus_zero_def)
  with Inf_para_positive have "Inf_para \<le> real k * Inf_para"
    by auto
  then show ?thesis
    using \<omega> omega_iter_le_norm by force
qed

lemma Inf_para_le_dist:
  assumes "x \<in> \<Omega>" "y \<in> \<Omega>" "x \<noteq> y"
  shows   "dist x y \<ge> Inf_para"
proof -
  have "x - y \<in> \<Omega>" "x - y \<noteq> 0"
    using assms by (auto intro: omega_diff)
  hence "x - y \<in> \<Omega>*"
    by (simp add: omega_minus_zero_def)
  hence "Inf_para \<le> norm (x - y)"
    by (rule Inf_para_le_norm)
  thus ?thesis
    by (simp add: dist_norm)
qed

lemma zero_in_omega_iter_iff [simp]: "0 \<in> omega_iter k \<longleftrightarrow> k = 0"
  by (auto simp: in_omega_iter_iff zero_prod_def)

definition Sup_para where \<comment>\<open>@{term R} in the proof of Lemma 1\<close>
  "Sup_para \<equiv> Sup (norm ` omega_iter_path)"

lemma Sup_para_ge: 
  assumes "z \<in> omega_iter_path"
  shows   "Sup_para \<ge> norm z"
  unfolding Sup_para_def
proof (rule cSup_upper)
  show "bdd_above (norm ` omega_iter_path)"
    unfolding bdd_above_norm by (rule compact_imp_bounded) auto
qed (use assms in auto)

lemma Sup_para_positive: "Sup_para > 0"
proof -
  have "0 < norm \<omega>1"
    by auto
  also have "\<dots> \<le> Sup_para"
    by (rule Sup_para_ge) (auto simp: in_omega_iter_path_iff)
  finally show ?thesis .
qed

lemma omega_iter_ge_norm: 
  assumes "\<omega> \<in> omega_iter k"
  shows "norm \<omega> \<le> k * Sup_para"
proof -
  obtain z where z: "z \<in> omega_iter_path" "\<omega> = of_nat k * z"
    using omega_iter_subset_rhombus[of k] assms by auto
  have "norm \<omega> = real k * norm z"
    by (simp add: z norm_mult)
  also have "\<dots> \<le> real k * Sup_para"
    by (intro mult_left_mono Sup_para_ge z) auto
  finally show ?thesis .
qed   
    
lemma not_islimpt_omega: "\<not>z islimpt \<Omega>"
proof (rule discrete_imp_not_islimpt[of Inf_para])
  fix x y assume "x \<in> \<Omega>" "y \<in> \<Omega>" "dist x y < Inf_para"
  with Inf_para_le_dist[of x y] show "x = y"
    by (cases "x = y") auto
qed (fact Inf_para_positive)

lemma closed_subset_omega:
  assumes "X \<subseteq> \<Omega>"
  shows   "closed X"
proof -
  have "\<not>z islimpt X" for z
    using islimpt_subset not_islimpt_omega assms by blast
  thus ?thesis
    by (simp add: closed_limpt)
qed

lemma finite_omega_Int_bounded:
  assumes "bounded X"
  shows   "finite (X \<inter> \<Omega>)"
proof -
  from assms obtain r where r: "\<forall>x\<in>X. norm x \<le> r"
    unfolding bounded_iff by auto
  hence "X \<subseteq> cball 0 r"
    by auto
  have "finite (cball 0 r \<inter> \<Omega>)"
    by (intro finite_not_islimpt_in_compact not_islimpt_omega) auto
  moreover have "X \<inter> \<Omega> \<subseteq> cball 0 r \<inter> \<Omega>"
    using r by auto
  ultimately show ?thesis
    using finite_subset by blast
qed

end


section \<open>The lattice generated by 1 and \<open>\<tau>\<close>\<close>

locale std_lattice =
  fixes \<tau> :: complex
  assumes \<tau>_not_real: "\<tau> \<notin> \<real>"
begin

sublocale gen_lattice 1 \<tau>
  using \<tau>_not_real by unfold_locales (auto simp: complex_is_Real_iff)

lemma bij_betw_omega_minus_zero:
  "bij_betw (of_\<omega>12_coords \<circ> map_prod of_int of_int) (-{(0,0)}) omega_minus_zero"
proof -
  have "bij_betw of_\<omega>12_coords (\<int>\<times>\<int>-{(0, 0)}) omega_minus_zero"
    by (intro bij_betwI[of _ _ _ \<omega>12_coords])
       (auto simp: omega_minus_zero_def \<omega>12_coords_in_Z_times_Z
                   of_\<omega>12_coords_eq_0_iff zero_prod_def)  
  moreover have "bij_betw (map_prod of_int of_int) (-{(0,0)}) (\<int>\<times>\<int>-{(0 :: real, 0 :: real)})"
    by (auto simp: bij_betw_def inj_on_def elim!: Ints_cases)
  ultimately show ?thesis
    by (intro bij_betw_trans)
qed

end

end