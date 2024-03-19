theory Wiggle_Prerequisites
  imports 
    "HOL-Complex_Analysis.Residue_Theorem" 
    "Winding_Number_Eval.Missing_Analysis"
    "Winding_Number_Eval.Missing_Transcendental"
    More_Topology
    Path_Nhds
    Library_Extras
    Real_Mod
begin

lemma linear_image_valid_path:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes  "valid_path p" "linear f"
  shows    "valid_path (f \<circ> p)"
  unfolding valid_path_def piecewise_C1_differentiable_on_def
proof safe
  from assms have "path p"
    by (simp add: valid_path_imp_path)
  thus "continuous_on {0..1} (f \<circ> p)"
    unfolding o_def path_def by (intro linear_continuous_on_compose[OF _ assms(2)])
  from assms(1) obtain S where S: "finite S" "p C1_differentiable_on {0..1} - S"
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  from S(2) obtain p' :: "real \<Rightarrow> 'a"
    where p': "\<And>x. x \<in> {0..1} - S \<Longrightarrow> (p has_vector_derivative p' x) (at x)"
              "continuous_on ({0..1} - S) p'"
    by (fastforce simp: C1_differentiable_on_def)

  have "(f \<circ> p has_vector_derivative f (p' x)) (at x)" if "x \<in> {0..1} - S" for x
    by (rule vector_derivative_diff_chain_within [OF p'(1)[OF that]]
             linear_imp_has_derivative assms)+
  moreover have "continuous_on ({0..1} - S) (\<lambda>x. f (p' x))"
    by (rule linear_continuous_on_compose [OF p'(2) assms(2)])
  ultimately have "f \<circ> p C1_differentiable_on {0..1} - S"
    unfolding C1_differentiable_on_def by (intro exI[of _ "\<lambda>x. f (p' x)"]) fast
  thus "\<exists>S. finite S \<and> f \<circ> p C1_differentiable_on {0..1} - S"
    using \<open>finite S\<close> by blast
qed


section \<open>More Winding Numbers\<close>

lemma contour_integral_affine:
  assumes "valid_path \<gamma>" "c \<noteq> 0"
  shows "contour_integral ((\<lambda>x. c * x + b) \<circ> \<gamma>) f 
         = contour_integral \<gamma> (\<lambda>w. c * f (c * w + b))"
proof -
  define ff where "ff=(\<lambda>x. c*x+b)"
  have "contour_integral (ff \<circ> \<gamma>) f
          = contour_integral \<gamma> (\<lambda>w. deriv ff w * f (ff w))"
  proof (rule contour_integral_comp_holoW)
    show "open UNIV" "ff holomorphic_on UNIV"
          "path_image \<gamma> \<subseteq> UNIV" "valid_path \<gamma>"
    unfolding ff_def using \<open>valid_path \<gamma>\<close>
    by (auto intro:holomorphic_intros)
  qed
  also have "\<dots> = contour_integral \<gamma> (\<lambda>w. c * f (c * w + b))"
  proof -
    have "deriv ff  x = c" "ff x = c*x+b" for x
      unfolding ff_def by auto
    then show ?thesis by auto
  qed
  finally show ?thesis unfolding ff_def .
qed

lemma valid_path_plus[simp]:
  fixes \<gamma>::"real \<Rightarrow> 'a ::real_normed_field"
  shows "valid_path ((+) c \<circ> \<gamma>) = valid_path \<gamma>"
  by (simp add: valid_path_translation_eq)

lemma valid_path_times:
  fixes \<gamma>::"real \<Rightarrow> 'a ::real_normed_field"
  assumes "c\<noteq>0"
  shows "valid_path ((*) c \<circ> \<gamma>) = valid_path \<gamma>"
proof 
  assume "valid_path ((*) c \<circ> \<gamma>)"
  then have "valid_path ((*) (1/c) \<circ> ((*) c \<circ> \<gamma>))"
    apply (elim valid_path_compose)
    by (auto intro:derivative_intros)
  then show "valid_path \<gamma>" 
    unfolding comp_def using \<open>c\<noteq>0\<close> by auto
next
  assume "valid_path \<gamma>"
  then show "valid_path ((*) c \<circ> \<gamma>)"
    apply (elim valid_path_compose)
    by (auto intro:derivative_intros)
qed


lemma has_integral_cnj: "(cnj o f has_integral (cnj I)) A 
          = (f has_integral I) A"
  unfolding has_integral_iff comp_def
  apply (subst integral_cnj[symmetric])
  by (simp add:integrable_on_cnj_iff)

lemma integrable_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> f x = g x"
  shows "f integrable_on T \<longleftrightarrow> g integrable_on T"
  using integrable_spike_finite[of S T f g] integrable_spike_finite[of S T g f] assms by auto

lemma contour_integrable_on_compose_cnj_iff:
  assumes "valid_path \<gamma>"
  shows   "f contour_integrable_on (cnj \<circ> \<gamma>) \<longleftrightarrow> (cnj \<circ> f \<circ> cnj) contour_integrable_on \<gamma>"
proof -
  from assms obtain S where S: "finite S" "\<gamma> C1_differentiable_on {0..1} - S"
    unfolding valid_path_def piecewise_C1_differentiable_on_def by blast
  have "f contour_integrable_on (cnj \<circ> \<gamma>) \<longleftrightarrow>
        ((\<lambda>t. cnj (cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t))) integrable_on {0..1})"
    unfolding contour_integrable_on o_def
  proof (intro integrable_spike_finite_eq [OF S(1)])
    fix t :: real assume "t \<in> {0..1} - S"
    hence "\<gamma> differentiable at t"
      using S(2) by (meson C1_differentiable_on_eq)
    hence "vector_derivative (\<lambda>x. cnj (\<gamma> x)) (at t) = cnj (vector_derivative \<gamma> (at t))"
      by (rule vector_derivative_cnj)
    thus "f (cnj (\<gamma> t)) * vector_derivative (\<lambda>x. cnj (\<gamma> x)) (at t) =
          cnj (cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t))"
      by simp
  qed
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t)) integrable_on {0..1})"
    by (rule integrable_on_cnj_iff)
  also have "\<dots> \<longleftrightarrow> (cnj \<circ> f \<circ> cnj) contour_integrable_on \<gamma>"
    by (simp add: contour_integrable_on o_def)
  finally show ?thesis .
qed

lemma contour_integral_cnj:
  assumes "valid_path \<gamma>"
  shows   "contour_integral (cnj \<circ> \<gamma>) f = cnj (contour_integral \<gamma> (cnj \<circ> f \<circ> cnj))"
proof -
  from assms obtain S where S: "finite S" "\<gamma> C1_differentiable_on {0..1} - S"
    unfolding valid_path_def piecewise_C1_differentiable_on_def by blast
  have "contour_integral (cnj \<circ> \<gamma>) f =
          integral {0..1} (\<lambda>t. cnj (cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t)))"
    unfolding contour_integral_integral
  proof (intro integral_spike)
    fix t assume "t \<in> {0..1} - S"
    hence "\<gamma> differentiable at t"
      using S(2) by (meson C1_differentiable_on_eq)
    hence "vector_derivative (\<lambda>x. cnj (\<gamma> x)) (at t) = cnj (vector_derivative \<gamma> (at t))"
      by (rule vector_derivative_cnj)
    thus "cnj (cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t)) =
            f ((cnj \<circ> \<gamma>) t) * vector_derivative (cnj \<circ> \<gamma>) (at t)"
      by (simp add: o_def)
  qed (use S(1) in auto)
  also have "\<dots> = cnj (integral {0..1} (\<lambda>t. cnj (f (cnj (\<gamma> t))) * vector_derivative \<gamma> (at t)))"
    by (subst integral_cnj [symmetric]) auto
  also have "\<dots> = cnj (contour_integral \<gamma> (cnj \<circ> f \<circ> cnj))"
    by (simp add: contour_integral_integral)
  finally show ?thesis .
qed

lemma contour_integral_negatepath:
  assumes "valid_path \<gamma>"
  shows   "contour_integral (uminus \<circ> \<gamma>) f = -(contour_integral \<gamma> (\<lambda>x. f (-x)))" (is "?lhs = ?rhs")
proof (cases "f contour_integrable_on (uminus \<circ> \<gamma>)")
  case True
  hence *: "(f has_contour_integral ?lhs) (uminus \<circ> \<gamma>)"
    using has_contour_integral_integral by blast
  have "((\<lambda>z. f (-z)) has_contour_integral - contour_integral (uminus \<circ> \<gamma>) f)
            (uminus \<circ> (uminus \<circ> \<gamma>))"
    by (rule has_contour_integral_negatepath) (use * assms in auto)
  hence "((\<lambda>x. f (-x)) has_contour_integral -?lhs) \<gamma>"
    by (simp add: o_def)
  thus ?thesis
    by (simp add: contour_integral_unique)
next
  case False
  hence "\<not>(\<lambda>z. f (- z)) contour_integrable_on \<gamma>"
    using contour_integrable_negatepath[of \<gamma> f] assms by auto
  with False show ?thesis
    by (simp add: not_integrable_contour_integral)
qed

lemma cnj_differentiable[simp]:" cnj differentiable at x"
  by (simp add: bounded_linear_cnj bounded_linear_imp_differentiable)

lemma path_compose_cnj_iff [simp]: "path (cnj \<circ> p) \<longleftrightarrow> path p"
proof -
  have "path (cnj \<circ> p)" if "path p" for p
    by (intro path_continuous_image continuous_intros that)
  from this[of p] and this[of "cnj \<circ> p"] show ?thesis
    by (auto simp: o_def)
qed

lemma valid_path_cnj:
  fixes g::"real \<Rightarrow> complex"
    shows "valid_path (cnj \<circ> g) = valid_path g"
proof
  show valid:"valid_path (cnj \<circ> g)" if "valid_path g" for g
  proof -
    obtain S where "finite S" and g_diff: "g C1_differentiable_on {0..1} - S"
      using \<open>valid_path g\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto
  
    have g_diff':"g differentiable at t" when "t\<in>{0..1} - S" for t
      by (meson C1_differentiable_on_eq \<open>g C1_differentiable_on {0..1} - S\<close> that)
    then have "(cnj \<circ> g) differentiable at t" when "t\<in>{0..1} - S" for t
      apply (rule differentiable_chain_at)
      using that by auto
    moreover have "continuous_on ({0..1} - S)
        (\<lambda>x. vector_derivative (cnj \<circ> g) (at x))"
    proof -
      have "continuous_on ({0..1} - S)
          (\<lambda>x. vector_derivative (cnj \<circ> g) (at x))
        = continuous_on ({0..1} - S)
          (\<lambda>x. cnj (vector_derivative g (at x)))"
        apply (rule continuous_on_cong[OF refl])
        unfolding comp_def using g_diff'
        by (subst vector_derivative_cnj) auto
      also have "\<dots>"
        apply (intro continuous_intros)
        using C1_differentiable_on_eq g_diff by blast
      finally show ?thesis .
    qed
    ultimately have "cnj \<circ> g C1_differentiable_on {0..1} - S"
      using C1_differentiable_on_eq by blast
    moreover have "path (cnj \<circ> g)"
      apply (rule path_continuous_image[OF valid_path_imp_path[OF \<open>valid_path g\<close>]])
      by (intro continuous_intros)
    ultimately show ?thesis unfolding valid_path_def piecewise_C1_differentiable_on_def path_def
      using \<open>finite S\<close> by auto
  qed
  from this[of "cnj o g"]
  show "valid_path (cnj \<circ> g) \<Longrightarrow> valid_path g"
    unfolding comp_def by simp
qed


lemma winding_number_prop_reversepath:
  assumes "winding_number_prop \<gamma> z e p n"
  shows   "winding_number_prop (reversepath \<gamma>) z e (reversepath p) (-n)"
proof -
  have p: "valid_path p" "z \<notin> path_image p" "pathstart p = pathstart \<gamma>"
          "pathfinish p = pathfinish \<gamma>" "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (\<gamma> t - p t) < e"
          "contour_integral p (\<lambda>w. 1 / (w - z)) = 2 * complex_of_real pi * \<i> * n"
    using assms by (auto simp: winding_number_prop_def)
  show ?thesis
    unfolding winding_number_prop_def
  proof safe
    show "norm (reversepath \<gamma> t - reversepath p t) < e" if "t \<in> {0..1}" for t
      unfolding reversepath_def using p(5)[of "1 - t"] that by auto
    show "contour_integral (reversepath p) (\<lambda>w. 1 / (w - z)) =
             complex_of_real (2 * pi) * \<i> * - n"
      using p by (subst contour_integral_reversepath) auto
  qed (use p in auto)
qed

lemma winding_number_prop_reversepath_iff:
  "winding_number_prop (reversepath \<gamma>) z e p n \<longleftrightarrow> winding_number_prop \<gamma> z e (reversepath p) (-n)"
  using winding_number_prop_reversepath[of "reversepath \<gamma>" z e p n]
        winding_number_prop_reversepath[of \<gamma> z e "reversepath p" "-n"] by auto

(*
TODO: update the definition of "winding_number_prop" by incorporating 
      the condition of "path \<gamma>" "z \<notin> path_image \<gamma>" so that the following
      lemma stands unconditionally.
*)
lemma winding_number_comp_plus:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
  shows "winding_number ((+) c \<circ> \<gamma>) (z + c) = winding_number \<gamma> z"
proof (rule winding_number_unique)
  define f where "f = (\<lambda>x. c+x)"
  have f_alt:"f = (\<lambda>x. x+c)" unfolding f_def by auto

  show "\<exists>p. winding_number_prop (f \<circ> \<gamma>)
                (z + c) e p (winding_number \<gamma> z)"
    if "e>0" for e
  proof -
    obtain p where "winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
      using \<open>0 < e\<close> assms winding_number by blast
    then have p:"valid_path p" "z \<notin> path_image p"
        "pathstart p = pathstart \<gamma>"
        "pathfinish p = pathfinish \<gamma>"
        "(\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < e)" and
        p_cont:"contour_integral p (\<lambda>w. 1 / (w - z)) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" 
      unfolding winding_number_prop_def by auto
    
    have "valid_path (f \<circ> p)"
      using p(1) unfolding f_def by simp
    moreover have "z + c \<notin> path_image (f \<circ> p)"
      using p(2) unfolding f_def by (auto simp add:path_image_def)
    moreover have "pathstart (f \<circ> p) = pathstart (f \<circ> \<gamma>)" 
      using p(3) by (simp add:pathstart_compose)
    moreover have "pathfinish (f \<circ> p) = pathfinish (f \<circ> \<gamma>)" 
      using p(4) by (simp add:pathfinish_compose)
    moreover have "(\<forall>t\<in>{0..1}. cmod ((f \<circ> \<gamma>) t 
            - (f \<circ> p) t) < e)" 
      using p(5) unfolding f_def by simp
    moreover have "contour_integral (f \<circ> p) 
              (\<lambda>w. 1 / (w - (z + c))) =
                  complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
      unfolding f_alt
      apply (subst contour_integral_affine[where c=1,simplified])
      using p_cont p(1,2) by auto
    ultimately show ?thesis
      apply (rule_tac x="f \<circ> p" in exI)
      unfolding winding_number_prop_def by auto
  qed
  show "path (f \<circ> \<gamma>)"
    using \<open>path \<gamma>\<close> unfolding f_def by (simp add:path_translation_eq)
  show "z + c \<notin> path_image (f \<circ> \<gamma>)"
    using \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def f_def by auto
qed

lemma winding_number_comp_times:
  assumes "path \<gamma>"
        and "z \<notin> path_image \<gamma>" 
        and "c \<noteq> 0"
      shows "winding_number ((*) c \<circ> \<gamma>) (z * c) = winding_number \<gamma> z"
proof (rule winding_number_unique)
  define f where "f = (\<lambda>x. c*x)"
  have f_alt:"f = (\<lambda>x. x*c)" unfolding f_def by auto

  show "\<exists>p. winding_number_prop (f \<circ> \<gamma>)
                (z * c) e p (winding_number \<gamma> z)"
    if "e>0" for e
  proof -
    have "cmod c>0" using \<open>c\<noteq>0\<close> by simp
    then have "(1/cmod c) * e>0"
      using that by auto
    from winding_number[OF assms(1,2) this]
    obtain p where "winding_number_prop \<gamma> z ((1/cmod c) * e) 
        p (winding_number \<gamma> z)"
      by blast
    then have p:"valid_path p" "z \<notin> path_image p"
        "pathstart p = pathstart \<gamma>"
        "pathfinish p = pathfinish \<gamma>"
        "(\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < ((1/cmod c) * e))" and
        p_cont:"contour_integral p (\<lambda>w. 1 / (w - z)) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" 
      unfolding winding_number_prop_def by auto
    
    have "valid_path (f \<circ> p)"
      using p(1) \<open>c\<noteq>0\<close> valid_path_times 
      unfolding f_def by auto
    moreover have "z * c \<notin> path_image (f \<circ> p)"
      using p(2) \<open>c\<noteq>0\<close> unfolding f_def 
      by (auto simp add:path_image_def)
    moreover have "pathstart (f \<circ> p) = pathstart (f \<circ> \<gamma>)" 
      using p(3) by (simp add:pathstart_compose)
    moreover have "pathfinish (f \<circ> p) = pathfinish (f \<circ> \<gamma>)" 
      using p(4) by (simp add:pathfinish_compose)
    moreover have "cmod ((f \<circ> \<gamma>) t - (f \<circ> p) t) < e"
      if "t\<in>{0..1}" for t
    proof -
      have "cmod ((f \<circ> \<gamma>) t - (f \<circ> p) t) = cmod (c*(\<gamma> t - p t))"
        unfolding f_def by (auto simp:algebra_simps)
      also have "\<dots> = cmod c * cmod (\<gamma> t - p t)"
        by (auto simp:norm_mult)
      also have "\<dots> < cmod c * (1 / cmod c * e)"
        using p(5)[rule_format,OF that] \<open>cmod c>0\<close> 
        using mult_less_cancel_left_pos by blast
      also have "\<dots> = e"
        using \<open>cmod c>0\<close> by auto
      finally show ?thesis .
    qed
    moreover have "contour_integral (f \<circ> p)
              (\<lambda>w. 1 / (w - (z * c))) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" (is "?L=?R")
    proof -
      have "?L = contour_integral p (\<lambda>w. c / (c * (w - z)))"
        unfolding f_def
        apply (subst contour_integral_affine[where b=0,simplified])
        using p(1,2) \<open>c\<noteq>0\<close> by (auto simp:algebra_simps)
      also have "\<dots> = contour_integral p (\<lambda>w. 1 / ( w - z))"
        using \<open>c\<noteq>0\<close> by simp
      also have "\<dots> = ?R" using p_cont .
      finally show ?thesis .
    qed
    ultimately show ?thesis
      apply (rule_tac x="f \<circ> p" in exI)
      unfolding winding_number_prop_def by auto
  qed
  show "path (f \<circ> \<gamma>)"
    using path_mult[OF path_const \<open>path \<gamma>\<close>] unfolding f_def comp_def
    by simp
  show "z * c \<notin> path_image (f \<circ> \<gamma>)"
    using \<open>z \<notin> path_image \<gamma>\<close> \<open>c\<noteq>0\<close> 
    unfolding path_image_def f_def by auto
qed

lemma winding_number_cnj:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
  shows   "winding_number (cnj \<circ> \<gamma>) (cnj z) = -cnj (winding_number \<gamma> z)"
proof (rule winding_number_unique)
  show "\<exists>p. winding_number_prop (cnj \<circ> \<gamma>) (cnj z) e p (-cnj (winding_number \<gamma> z))"
    if "e > 0" for e
  proof -
    from winding_number[OF assms(1,2) \<open>e > 0\<close>]
    obtain p where "winding_number_prop \<gamma> z e p (winding_number \<gamma> z)"
      by blast
    then have p: "valid_path p" "z \<notin> path_image p"
        "pathstart p = pathstart \<gamma>"
        "pathfinish p = pathfinish \<gamma>"
        "\<And>t. t \<in> {0..1} \<Longrightarrow> cmod (\<gamma> t - p t) < e" and
        p_cont:"contour_integral p (\<lambda>w. 1 / (w - z)) =
          complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z" 
      unfolding winding_number_prop_def by auto
    
    have "valid_path (cnj \<circ> p)"
      using p(1) by (subst valid_path_cnj) auto
    moreover have "cnj z \<notin> path_image (cnj \<circ> p)"
      using p(2) by (auto simp: path_image_def)
    moreover have "pathstart (cnj \<circ> p) = pathstart (cnj \<circ> \<gamma>)" 
      using p(3) by (simp add: pathstart_compose)
    moreover have "pathfinish (cnj \<circ> p) = pathfinish (cnj \<circ> \<gamma>)" 
      using p(4) by (simp add: pathfinish_compose)
    moreover have "cmod ((cnj \<circ> \<gamma>) t - (cnj \<circ> p) t) < e"
      if t: "t \<in> {0..1}" for t
    proof -
      have "(cnj \<circ> \<gamma>) t - (cnj \<circ> p) t = cnj (\<gamma> t - p t)"
        by simp
      also have "norm \<dots> = norm (\<gamma> t - p t)"
        by (subst complex_mod_cnj) auto
      also have "\<dots> < e"
        using p(5)[OF t] by simp
      finally show ?thesis .
    qed
    moreover have "contour_integral (cnj \<circ> p) (\<lambda>w. 1 / (w - cnj z)) =
          cnj (complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z)" (is "?L=?R")
    proof -
      have "?L = contour_integral (cnj \<circ> p) (cnj \<circ> (\<lambda>w. 1 / (cnj w - z)))"
        by (simp add: o_def)
      also have "\<dots> = cnj (contour_integral p (\<lambda>x. 1 / (x - z)))"
        using p(1) by (subst contour_integral_cnj) (auto simp: o_def)
      also have "\<dots> = ?R"
        using p_cont by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by (intro exI[of _ "cnj \<circ> p"]) (auto simp: winding_number_prop_def)
  qed
  show "path (cnj \<circ> \<gamma>)"
    by (intro path_continuous_image continuous_intros) (use assms in auto)
  show "cnj z \<notin> path_image (cnj \<circ> \<gamma>)"
    using \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def by auto
qed


subsection \<open>Continuous transformations that preserve the winding number in some way\<close>

locale winding_preserving =
  fixes A :: "complex set" and f :: "complex \<Rightarrow> complex" and g :: "complex \<Rightarrow> complex"
  assumes inj: "inj_on f A"
  assumes cont: "continuous_on A f"
  assumes winding_number_eq:
    "\<And>p x. path p \<Longrightarrow> path_image p \<subseteq> A \<Longrightarrow> pathstart p = pathfinish p \<Longrightarrow> x \<in> A - path_image p \<Longrightarrow>
        winding_number (f \<circ> p) (f x) = g (winding_number p x)"

lemma winding_preserving_comp:
  assumes "winding_preserving B f2 g2"
  assumes "winding_preserving A f1 g1"
  assumes subset: "f1 ` A \<subseteq> B"
  shows   "winding_preserving A (f2 \<circ> f1) (g2 \<circ> g1)"
proof
  interpret f1: winding_preserving A f1 g1
    by fact
  interpret f2: winding_preserving B f2 g2
    by fact
  show "inj_on (f2 \<circ> f1) A"
    by (intro comp_inj_on f1.inj inj_on_subset[OF f2.inj] assms)
  show "continuous_on A (f2 \<circ> f1)"
    by (intro continuous_on_compose f1.cont continuous_on_subset[OF f2.cont] subset)
  show "winding_number (f2 \<circ> f1 \<circ> p) ((f2 \<circ> f1) x) = (g2 \<circ> g1) (winding_number p x)"
    if p: "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" "pathstart p = pathfinish p" for p x
  proof -
    have [simp]: "f1 x = f1 (p t) \<longleftrightarrow> x = p t" if "t \<in> {0..1}" for t
      using f1.inj that p unfolding inj_on_def path_image_def by blast
    have "winding_number (f2 \<circ> f1 \<circ> p) ((f2 \<circ> f1) x) =
          winding_number (f2 \<circ> (f1 \<circ> p)) (f2 (f1 x))"
      by (simp add: o_def)
    also have "\<dots> = g2 (winding_number (f1 \<circ> p) (f1 x))"
    proof (rule f2.winding_number_eq)
      show "path (f1 \<circ> p)"
        using that by (intro path_continuous_image continuous_on_subset[OF f1.cont])
      show "path_image (f1 \<circ> p) \<subseteq> B"
        using that subset by (auto simp: path_image_def)
      show "f1 x \<in> B - path_image (f1 \<circ> p)"
        using that subset f1.inj by (auto simp: path_image_def)
    qed (use p in \<open>auto simp: pathstart_compose pathfinish_compose\<close>)
    also have "winding_number (f1 \<circ> p) (f1 x) = g1 (winding_number p x)"
      by (rule f1.winding_number_eq) (use p in auto)
    finally show ?thesis
      by (simp add: o_def)
  qed
qed

lemmas winding_preserving_comp' = winding_preserving_comp [unfolded o_def]

lemma winding_preserving_subset:
  assumes "winding_preserving A f g" "B \<subseteq> A"
  shows   "winding_preserving B f g"
proof -
  interpret winding_preserving A f g
    by fact
  show ?thesis
  proof
    show "inj_on f B"
      by (rule inj_on_subset[OF inj]) (use assms(2) in auto)
    show "continuous_on B f"
      by (rule continuous_on_subset[OF cont]) (use assms(2) in auto)
    show "winding_number (f \<circ> p) (f x) = g (winding_number p x)"
      if "path p" "path_image p \<subseteq> B" "x \<in> B - path_image p" "pathstart p = pathfinish p" for p x
      using that winding_number_eq[of p x] assms(2) by auto
  qed
qed

lemma winding_preserving_translate: "winding_preserving A (\<lambda>x. c + x) (\<lambda>x. x)"
proof
  show "winding_number ((+) c \<circ> p) (c + x) = winding_number p x"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_comp_plus[of p x c] by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_mult: "c \<noteq> 0 \<Longrightarrow> winding_preserving A (\<lambda>x. c * x) (\<lambda>x. x)"
proof
  assume "c \<noteq> 0"
  show "winding_number ((*) c \<circ> p) (c * x) = winding_number p x"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_comp_times[of p x c] \<open>c \<noteq> 0\<close> by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_cnj: "winding_preserving A cnj (\<lambda>x. -cnj x)"
proof
  show "winding_number (cnj \<circ> p) (cnj x) = -cnj (winding_number p x)"
    if "path p" "path_image p \<subseteq> A" "x \<in> A - path_image p" for p x
    using that winding_number_cnj[of p x] by (auto simp: algebra_simps)
qed (auto intro!: inj_onI continuous_intros)

lemma winding_preserving_uminus: "winding_preserving A (\<lambda>x. -x) (\<lambda>x. x)"
  using winding_preserving_mult[of "-1" A] by simp

section \<open>Wiggle Prerequisites\<close>

lemma arcD: "arc p \<Longrightarrow> p x = p y \<Longrightarrow> x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x = y"
  by (auto simp: arc_def inj_on_def)

lemma simple_pathI [intro?]:
  assumes "path p"
  assumes "\<And>x y. 0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> y \<le> 1 \<Longrightarrow> p x = p y \<Longrightarrow> x = 0 \<and> y = 1"
  shows   "simple_path p"
  unfolding simple_path_def loop_free_def
proof (intro ballI conjI impI)
  fix x y assume "x \<in> {0..1}" "y \<in> {0..1}" "p x = p y"
  thus "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
    by (cases x y rule: linorder_cases) (use assms(2)[of x y] assms(2)[of y x] in auto)
qed fact+

lemma simple_path_joinI:
  assumes "arc p1" "arc p2" "pathfinish p1 = pathstart p2"
  assumes "path_image p1 \<inter> path_image p2 \<subseteq>
             (insert (pathstart p2) (if pathstart p1 = pathfinish p2 then {pathstart p1} else {}))"
  shows   "simple_path (p1 +++ p2)"
proof (rule simple_pathI)
  show "path (p1 +++ p2)"
    using assms by (auto simp: arc_imp_path)
next
  fix x y :: real
  assume xy: "0 \<le> x" "x < y" "y \<le> 1" "(p1 +++ p2) x = (p1 +++ p2) y"

  show "x = 0 \<and> y = 1"
  proof (cases "x \<le> 1/2"; cases "y \<le> 1/2")
    assume xy': "x \<le> 1 / 2" "y \<le> 1 / 2"
    with xy have "p1 (2 * x) = p1 (2 * y)"
      by (simp add: joinpaths_def)
    from \<open>arc p1\<close> and this have "2 * x = 2 * y"
      by (rule arcD) (use xy xy' in auto)
    thus ?thesis using xy
      by auto
  next
    assume xy': "\<not>x \<le> 1 / 2" "\<not>y \<le> 1 / 2"
    with xy have "p2 (2 * x - 1) = p2 (2 * y - 1)"
      by (simp add: joinpaths_def)
    from \<open>arc p2\<close> and this have "2 * x - 1 = 2 * y - 1"
      by (rule arcD) (use xy xy' in auto)
    thus ?thesis using xy
      by auto
  next
    assume xy': "x \<le> 1 / 2" "\<not>y \<le> 1 / 2"
    with xy have eq1: "p1 (2 * x) = p2 (2 * y - 1)"
      by (simp add: joinpaths_def)
    moreover have "p1 (2 * x) \<in> path_image p1"
      using xy xy' by (auto simp: path_image_def)
    moreover have "p2 (2 * y - 1) \<in> path_image p2"
      using xy xy' by (auto simp: path_image_def)
    ultimately have "p1 (2 * x) = pathstart p1 \<and> pathfinish p2 = pathstart p1 \<or> 
                     p1 (2 * x) = pathstart p2"
      using assms by (auto split: if_splits)
    thus ?thesis
    proof (elim disjE conjE)
      assume "p1 (2 * x) = pathstart p2"
      hence "p2 (2 * y - 1) = p2 0"
        using eq1 unfolding pathstart_def by simp
      from \<open>arc p2\<close> and this have "2 * y - 1 = 0"
        by (rule arcD) (use xy xy' in auto)
      with xy' show ?thesis
        by auto
    next
      assume eq2: "p1 (2 * x) = pathstart p1" "pathfinish p2 = pathstart p1"
      hence "p1 (2 * x) = p1 0"
        by (simp add: pathstart_def)
      from \<open>arc p1\<close> and this have "2 * x = 0"
        by (rule arcD) (use xy xy' in auto)
      hence "x = 0"
        by simp
      moreover have "p2 (2 * y - 1) = p2 1"
        using eq1 eq2 by (simp add: pathfinish_def)
      from \<open>arc p2\<close> and this have "2 * y - 1 = 1"
        by (rule arcD) (use xy xy' in auto)
      hence "y = 1"
        by simp
      ultimately show ?thesis
        by blast
    qed
  qed (use xy in auto)
qed

lemma simple_path_join3I:
  assumes "arc p1" "arc p2" "arc p3"
  assumes "path_image p1 \<inter> path_image p2 \<subseteq> {pathstart p2}"
  assumes "path_image p2 \<inter> path_image p3 \<subseteq> {pathstart p3}"
  assumes "path_image p1 \<inter> path_image p3 \<subseteq> {pathstart p1} \<inter> {pathfinish p3}"
  assumes "pathfinish p1 = pathstart p2" "pathfinish p2 = pathstart p3"
  shows   "simple_path (p1 +++ p2 +++ p3)"
  using assms by (intro simple_path_joinI arc_join) (auto simp: path_image_join)

lemma part_circlepath_altdef:
  "part_circlepath z r a b = (\<lambda>t. z + rcis r (linepath a b t))"
  unfolding part_circlepath_def rcis_def cis_conv_exp ..

lemmas [simp del] = pathstart_part_circlepath pathfinish_part_circlepath

lemma pathstart_part_circlepath' [simp]: "pathstart (part_circlepath z r a b) = z + rcis r a"
  and pathfinish_part_circlepath' [simp]: "pathfinish (part_circlepath z r a b) = z + rcis r b"
  unfolding part_circlepath_altdef by (simp_all add: pathstart_def pathfinish_def linepath_def)

lemma (in order_topology) at_within_Icc_Icc_right:
  assumes "a \<le> x" "x < b" "b \<le> c"
  shows   "at x within {a..c} = at x within {a..b}"
  by (cases "x = a") (use assms in \<open>simp_all add: at_within_Icc_at_right at_within_Icc_at\<close>)

lemma (in order_topology) at_within_Icc_Icc_left:
  assumes "a \<le> b" "b < x" "x \<le> c"
  shows   "at x within {a..c} = at x within {b..c}"
  by (cases "x = c") (use assms in \<open>simp_all add: at_within_Icc_at_left at_within_Icc_at\<close>)

lemma (in order_topology)
  assumes "a < b"
  shows at_within_Ico_at_right: "at a within {a..<b} = at_right a"
    and at_within_Ico_at_left:  "at b within {a..<b} = at_left b"
  using order_tendstoD(2)[OF tendsto_ident_at assms, of "{a<..}"]
  using order_tendstoD(1)[OF tendsto_ident_at assms, of "{..<b}"]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

lemma (in order_topology)
  assumes "a < b"
  shows at_within_Ioc_at_right: "at a within {a<..b} = at_right a"
    and at_within_Ioc_at_left:  "at b within {a<..b} = at_left b"
  using order_tendstoD(2)[OF tendsto_ident_at assms, of "{a<..}"]
  using order_tendstoD(1)[OF tendsto_ident_at assms, of "{..<b}"]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

lemma (in order_topology) at_within_Ico_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a..<b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Ioc_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a<..b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Ioo_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a<..<b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Icc_Ico:
  assumes "a \<le> x" "x < b"
  shows   "at x within {a..b} = at x within {a..<b}"
  by (cases "x = a")
     (use assms in \<open>simp_all add: at_within_Icc_at_right at_within_Ico_at_right
                                  at_within_Ico_at at_within_Icc_at\<close>)

lemma (in order_topology) at_within_Icc_Ioc:
  assumes "a < x" "x \<le> b"
  shows   "at x within {a..b} = at x within {a<..b}"
  by (cases "x = b")
     (use assms in \<open>simp_all add: at_within_Icc_at_left at_within_Ioc_at_left
                                  at_within_Ioc_at at_within_Icc_at\<close>)

lemma continuous_cong:
  assumes "eventually (\<lambda>x. f x = g x) F" "f (netlimit F) = g (netlimit F)"
  shows   "continuous F f \<longleftrightarrow> continuous F g"
  unfolding continuous_def using assms by (intro filterlim_cong) simp_all

lemma at_within_atLeastAtMost_eq_bot_iff_real:
  "at x within {a..b} = bot \<longleftrightarrow> x \<notin> {a..b::real} \<or> a = b"
  by (cases a b rule: linorder_cases) (auto simp: trivial_limit_within islimpt_finite)

lemma eventually_in_pointed_at: "eventually (\<lambda>x. x \<in> A - {y}) (at y within A)"
  by (simp add: eventually_at_filter)

lemma isCont_real_If_combine:
  fixes x :: real
  assumes [simp]: "f x = h x" "g x = h x"
  assumes contf: "continuous (at_left x) f"
  assumes contg: "continuous (at_right x) g"
  assumes f: "eventually (\<lambda>y. h y = f y) (at_left x)"
  assumes g: "eventually (\<lambda>y. h y = g y) (at_right x)"
  shows   "continuous (at x) h"
  unfolding continuous_at_split
proof
  have "continuous (at_left x) f \<longleftrightarrow> continuous (at_left x) h"
    by (intro continuous_cong eventually_mono[OF f]) (auto simp: Lim_ident_at)
  with contf show "continuous (at_left x) h" by blast
next
  have "continuous (at_right x) g \<longleftrightarrow> continuous (at_right x) h"
    by (intro continuous_cong eventually_mono[OF g]) (auto simp: Lim_ident_at)
  with contg show "continuous (at_right x) h" by blast
qed


lemma continuous_on_real_If_combine:
  fixes f g :: "real \<Rightarrow> 'a :: topological_space"
  assumes "continuous_on {a..b} f"
  assumes "continuous_on {b..c} g"
  assumes "f b = g b" "a \<le> b" "b \<le> c"
  defines "h \<equiv> (\<lambda>x. if x \<le> b then f x else g x)"
  shows   "continuous_on {a..c} h"
proof (cases "a = b \<or> b = c")
  case True
  thus ?thesis
  proof
    assume [simp]: "a = b"
    have "continuous_on {a..c} g"
      using assms by (simp add: continuous_on_imp_continuous_within)
    also have "?this \<longleftrightarrow> continuous_on {a..c} h"
      by (intro continuous_on_cong) (auto simp: assms)
    finally show ?thesis .
  next
    assume [simp]: "b = c"
    have "continuous_on {a..c} f"
      using assms by (simp add: continuous_on_imp_continuous_within)
    also have "?this \<longleftrightarrow> continuous_on {a..c} h"
      by (intro continuous_on_cong) (auto simp: assms)
    finally show ?thesis .
  qed
next
  case False
  hence abc: "a < b" "b < c"
    using assms by auto
  note [simp] = at_within_atLeastAtMost_eq_bot_iff_real Lim_ident_at
  have "continuous (at x within {a..c}) h" if x: "x \<in> {a..c}" for x
  proof (cases x b rule: linorder_cases)
    case [simp]: equal
    have "continuous (at b) h"
      unfolding continuous_at_split
    proof
      have "continuous (at b within {a..b}) f"
        using assms x by (simp add: continuous_on_imp_continuous_within)
      also have "at b within {a..b} = at_left b"
        using abc by (simp add: at_within_Icc_at_left)
      also have ev: "eventually (\<lambda>x. x < b) (at_left b)"
        using eventually_at_topological by blast
      have "continuous (at_left b) f \<longleftrightarrow> continuous (at_left b) h"
        using assms by (intro continuous_cong eventually_mono[OF ev]) (auto simp: h_def)
      finally show "continuous (at_left b) h" .
    next
      have "continuous (at b within {b..c}) g"
        using assms x by (simp add: continuous_on_imp_continuous_within)
      also have "at b within {b..c} = at_right b"
        using abc by (simp add: at_within_Icc_at_right)
      also have ev: "eventually (\<lambda>x. x > b) (at_right b)"
        using eventually_at_topological by blast
      have "continuous (at_right b) g \<longleftrightarrow> continuous (at_right b) h"
        using assms by (intro continuous_cong eventually_mono[OF ev]) (auto simp: h_def)
      finally show "continuous (at_right b) h" .
    qed
    thus ?thesis
      using continuous_at_imp_continuous_at_within local.equal by blast
  next
    case less
    have "continuous (at x within {a..b}) f"
      using assms less x by (simp add: continuous_on_imp_continuous_within)
    also have "eventually (\<lambda>y. y \<in> {a..b} - {x}) (at x within {a..b})"
      by (rule eventually_in_pointed_at)
    hence "eventually (\<lambda>y. f y = h y) (at x within {a..b})"
      by eventually_elim (auto simp: h_def)
    hence "continuous (at x within {a..b}) f \<longleftrightarrow> continuous (at x within {a..b}) h"
      using assms less x by (intro continuous_cong) simp_all
    also have "at x within {a..b} = at x within {a..c}"
      by (rule sym, rule at_within_Icc_Icc_right) (use x less assms in auto)
    finally show ?thesis .
  next
    case greater
    have "continuous (at x within {b..c}) g"
      using assms greater x by (simp add: continuous_on_imp_continuous_within)
    also {
      have "eventually (\<lambda>y. y \<in> {b<..c} - {x}) (at x within {b<..c})"
        by (rule eventually_in_pointed_at)
      also have "at x within {b<..c} = at x within {b..c}"
        using greater assms x by (metis atLeastAtMost_iff at_within_Icc_Ioc)
      finally have "eventually (\<lambda>y. g y = h y) (at x within {b..c})"
        by eventually_elim (use greater in \<open>auto simp: h_def\<close>)
    }
    hence "continuous (at x within {b..c}) g \<longleftrightarrow> continuous (at x within {b..c}) h"
      using assms greater x by (intro continuous_cong) simp_all
    also have "at x within {b..c} = at x within {a..c}"
      by (rule sym, rule at_within_Icc_Icc_left) (use x greater assms in auto)
    finally show ?thesis .
  qed
  thus ?thesis
    using continuous_on_eq_continuous_within by blast
qed

lemma continuous_on_real_If_combine':
  fixes f g :: "real \<Rightarrow> 'a :: topological_space"
  assumes "continuous_on {a..b} f"
  assumes "continuous_on {b..c} g"
  assumes "f b = g b" "a \<le> b" "b \<le> c"
  defines "h \<equiv> (\<lambda>x. if x < b then f x else g x)"
  shows   "continuous_on {a..c} h"
proof -
  have "continuous_on {-c..-a} ((\<lambda>x. if x \<le> -b then (g \<circ> uminus) x else (f \<circ> uminus) x))"
    (is "continuous_on _ ?h'")
    using assms
    by (intro continuous_on_real_If_combine continuous_on_compose continuous_intros) auto
  hence "continuous_on {a..c} (?h' \<circ> uminus)"
    by (intro continuous_on_compose continuous_intros) auto
  also have "?h' \<circ> uminus = h"
    by (auto simp: h_def fun_eq_iff)
  finally show ?thesis .
qed
      
lemma part_circlepath_empty: "part_circlepath x r a a = linepath (x + rcis r a) (x + rcis r a)"
  by (auto simp: part_circlepath_altdef linepath_def algebra_simps fun_eq_iff)

lemma homotopic_paths_rid':
  assumes "path p" "path_image p \<subseteq> s" "x = pathfinish p"
  shows "homotopic_paths s (p +++ linepath x x) p"
  using homotopic_paths_rid[of p s] assms by simp

lemma homotopic_paths_lid':
   "\<lbrakk>path p; path_image p \<subseteq> s; x = pathstart p\<rbrakk> \<Longrightarrow> homotopic_paths s (linepath x x +++ p) p"
  using homotopic_paths_lid[of p s] by simp


lemma part_circlepath_cong:
  assumes "x = x'" "r = r'" "cis a' = cis a" "b' = a' + b - a"
  shows   "part_circlepath x r a b = part_circlepath x' r' a' b'"
  by (simp add: part_circlepath_altdef rcis_def linepath_def algebra_simps assms
           flip: cis_mult cis_divide)

lemma continuous_on_linepath [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g" "continuous_on A h"
  shows   "continuous_on A (\<lambda>x. linepath (f x) (g x) (h x))"
  unfolding linepath_def by (intro continuous_intros assms)

lemma frac_1 [simp]: "frac 1 = 0"
  by (auto simp: frac_def)

lemma frac_id [simp]: "x \<in> {0..<1} \<Longrightarrow> frac x = x"
  by (subst frac_eq) auto

lemma frac_add_int_left [simp]: "x \<in> \<int> \<Longrightarrow> frac (x + y) = frac y"
  by (auto simp: frac_def elim!: Ints_cases)

lemma frac_add_int_right [simp]: "y \<in> \<int> \<Longrightarrow> frac (x + y) = frac x"
  by (auto simp: frac_def elim!: Ints_cases)

lemma floor_less_not_int: "x \<notin> \<int> \<Longrightarrow> floor x < (x :: real)"
  by (metis Ints_of_int floor_correct order_less_le)

lemma less_ceiling_not_int: "x \<notin> \<int> \<Longrightarrow> ceiling x > (x :: real)"
  by (meson floor_less_iff floor_less_not_int less_ceiling_iff)

lemma tendsto_frac [tendsto_intros]:
  assumes "(x :: real) \<notin> \<int>"
  shows   "(frac \<longlongrightarrow> frac x) (at x within A)"
  using assms continuous_at_imp_continuous_at_within continuous_frac continuous_within by blast

lemma tendsto_frac_at_left_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "(frac \<longlongrightarrow> 1) (at_left x)"
proof -
  have "((\<lambda>y. y - real_of_int \<lfloor>x\<rfloor> + 1) \<longlongrightarrow> 1) (at_left x)"
    by (rule tendsto_eq_intros refl)+ (use assms in \<open>auto elim!: Ints_cases\<close>)
  moreover have "eventually (\<lambda>y. y \<in> {x-1<..<x}) (at_left x)"
    using eventually_at_left_real by force
  hence "eventually (\<lambda>y. frac y = y - real_of_int \<lfloor>x\<rfloor> + 1) (at_left x)"
  proof eventually_elim
    case (elim y)
    show "frac y = y - real_of_int \<lfloor>x\<rfloor> + 1"
      using assms elim by (subst frac_unique_iff) (auto elim!: Ints_cases)
  qed
  ultimately show ?thesis
    by (simp add: filterlim_cong)
qed

lemma filterlim_at_frac_at_left_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "filterlim frac (at_left 1) (at_left x)"
  unfolding filterlim_at
proof
  show "\<forall>\<^sub>F y in at_left x. frac y \<in> {..<1} \<and> frac y \<noteq> 1"
  proof (intro always_eventually allI)
    fix y :: real
    show "frac y \<in> {..<1} \<and> frac y \<noteq> 1"
      using frac_lt_1[of y] by auto
  qed
qed (auto intro!: tendsto_frac_at_left_int_real assms)

lemma tendsto_frac_at_right_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "(frac \<longlongrightarrow> 0) (at_right x)"
proof -
  have "((\<lambda>y. y - real_of_int \<lfloor>x\<rfloor>) \<longlongrightarrow> 0) (at_right x)"
    by (rule tendsto_eq_intros refl)+ (use assms in \<open>auto elim!: Ints_cases\<close>)
  moreover have "eventually (\<lambda>y. y \<in> {x<..<x+1}) (at_right x)"
    using eventually_at_right_real by force
  hence "eventually (\<lambda>y. frac y = y - real_of_int \<lfloor>x\<rfloor>) (at_right x)"
  proof eventually_elim
    case (elim y)
    show "frac y = y - real_of_int \<lfloor>x\<rfloor>"
      using assms elim by (subst frac_unique_iff) (auto elim!: Ints_cases)
  qed
  ultimately show ?thesis
    by (simp add: filterlim_cong)
qed

lemma filterlim_at_frac_at_right_int_real [tendsto_intros]:
  assumes "(x :: real) \<in> \<int>"
  shows   "filterlim frac (at_right 0) (at_right x)"
  unfolding filterlim_at
proof
  have "eventually (\<lambda>y. y \<in> {x<..<x+1}) (at_right x)"
    using eventually_at_right_real by force
  thus "\<forall>\<^sub>F x in at_right x. frac x \<in> {0<..} \<and> frac x \<noteq> 0"
  proof eventually_elim
    case (elim y)
    hence "y \<notin> \<int>"
      using assms by (auto elim!: Ints_cases)
    thus "frac y \<in> {0<..} \<and> frac y \<noteq> 0"
      using frac_ge_0[of x] by auto
  qed
qed (auto intro!:  tendsto_frac_at_right_int_real assms)

(* TODO: version for continuous? *)
lemma continuous_on_frac_real:
  assumes "continuous_on {0..1} f" "f 0 = f 1"
  shows   "continuous_on A (\<lambda>x::real. f (frac x))"
proof -
  have isCont_f: "isCont f x" if "x \<in> {0<..<1}" for x
    by (rule continuous_on_interior[OF assms(1)]) (use that in auto)
  note [continuous_intros] = continuous_at_compose[OF _ isCont_f, unfolded o_def]

  have contfl: "(f \<longlongrightarrow> f 0) (at_right 0)"
    using assms(1) by (simp add: continuous_on_Icc_at_rightD)
  have contfr: "(f \<longlongrightarrow> f 1) (at_left 1)"
    using assms(1) by (simp add: continuous_on_Icc_at_leftD)
  note tendsto_intros = filterlim_compose[OF contfr] filterlim_compose[OF contfl]

  have "continuous (at x) (\<lambda>x. f (frac x))" for x
  proof (cases "x \<in> \<int>")
    case True
    have "((\<lambda>x. f (frac x)) \<longlongrightarrow> f 1) (at_left x)"
      by (rule tendsto_intros filterlim_at_frac_at_left_int_real True)+
    moreover have "((\<lambda>x. f (frac x)) \<longlongrightarrow> f 0) (at_right x)"
      by (rule tendsto_intros filterlim_at_frac_at_right_int_real True)+
    ultimately show ?thesis
      using assms(2) True unfolding continuous_at_split unfolding continuous_def
      by (auto simp: Lim_ident_at elim!: Ints_cases)
  next
    case False
    have "x < 1 + real_of_int \<lfloor>x\<rfloor>"
      by linarith
    hence "continuous (at x) (\<lambda>y. f (y - \<lfloor>x\<rfloor>))"
      using floor_less_not_int[of x] False
      by (intro continuous_intros) (auto simp: algebra_simps)
    also have "eventually (\<lambda>y. y \<in> {floor x<..<ceiling x}) (nhds x)"
      using eventually_floor_less[OF filterlim_ident False]
            eventually_less_ceiling[OF filterlim_ident False]
      by eventually_elim auto
    hence "eventually (\<lambda>y. frac y = y - \<lfloor>x\<rfloor>) (nhds x)"
    proof eventually_elim
      case (elim y)
      hence "y - real_of_int \<lfloor>x\<rfloor> < 1"
        unfolding greaterThanLessThan_iff using ceiling_diff_floor_le_1[of x] by linarith
      thus ?case using elim
        by (subst frac_unique_iff) auto
    qed
    hence "eventually (\<lambda>y. f (y - \<lfloor>x\<rfloor>) = f (frac y)) (at x)"
      unfolding eventually_at_filter by eventually_elim (auto simp: frac_def)
    hence "isCont (\<lambda>y. f (y - \<lfloor>x\<rfloor>)) x = isCont (\<lambda>y. f (frac y)) x"
      by (intro continuous_cong) (auto simp: frac_def)
    finally show ?thesis .
  qed
  thus ?thesis
    using continuous_at_imp_continuous_on by blast
qed

lemma continuous_on_frac_real':
  assumes "continuous_on {0..1} f" "continuous_on A g" "f 0 = f 1"
  shows   "continuous_on A (\<lambda>x. f (frac (g x :: real)))"
  using continuous_on_compose2[OF continuous_on_frac_real[OF assms(1,3)] assms(2)] by blast

proposition homotopic_loops_reparametrize:
  assumes "path p" "pathstart p = pathfinish p"
      and pips: "path_image p \<subseteq> s"
      and contf: "continuous_on {0..1} f"
      and q: "\<And>t. t \<in> {0..1} \<Longrightarrow> q t = p (frac (f t))"
      and closed: "f 1 = f 0 + 1"
    shows "homotopic_loops s p q"
proof -
  note [continuous_intros] = continuous_on_frac_real'[OF continuous_on_path[OF \<open>path p\<close>]]
  note [continuous_intros] = continuous_on_compose2[OF contf]
  define h :: "real \<times> real \<Rightarrow> 'a" where "h = (\<lambda>(u,v). p (frac (linepath v (f v) u)))"

  have [simp]: "p (frac t) = p t" if "t \<in> {0..1}" for t
    using that assms(2) by (cases "t = 1") (auto simp: pathstart_def pathfinish_def)

  show ?thesis
    unfolding homotopic_loops
  proof (rule exI[of _ h]; safe)
    fix v :: real assume v: "v \<in> {0..1}"
    show "h (0, v) = p v" and "h (1, v) = q v"
      using q v by (simp_all add: h_def linepath_def)
  next
    fix u v :: real assume uv: "u \<in> {0..1}" "v \<in> {0..1}"
    have "h (u, v) \<in> path_image p"
      by (auto simp: h_def path_image_def intro!: imageI less_imp_le[OF frac_lt_1])
    also have "\<dots> \<subseteq> s"
      by fact
    finally show "h (u, v) \<in> s" .
  next
    fix t :: real assume t: "t \<in> {0..1}"
    show "pathfinish (h \<circ> Pair t) = pathstart (h \<circ> Pair t)"
      using t by (auto simp: h_def pathfinish_def pathstart_def linepath_def closed algebra_simps)
  next
    show "continuous_on ({0..1}\<times>{0..1}) h"
      unfolding h_def case_prod_unfold using \<open>pathstart p = pathfinish p\<close>
      by (auto intro!: continuous_intros order.refl continuous_on_fst less_imp_le[OF frac_lt_1]
               simp: pathstart_def pathfinish_def)
  qed
qed

lemma frac_of_Int [simp]: "x \<in> \<int> \<Longrightarrow> frac x = 0"
  by (subst frac_eq_0_iff)

lemma shiftpath_loop_altdef:
  assumes "pathstart p = pathfinish p" "x \<in> {0..1}" "a \<in> {0..1}"
  shows   "shiftpath a p x = p (frac (x + a))"
proof -
  consider "x + a < 1" | "x + a = 1" | "x + a > 1" "x + a < 2" | "x + a = 2"
    using assms(2,3) by fastforce
  thus ?thesis
  proof cases
    case 3
    hence [simp]: "frac (a + x) = x + a - 1"
      using assms unfolding atLeastAtMost_iff by (subst frac_unique_iff) auto
    show ?thesis using assms 3
      by (auto simp: shiftpath_def pathstart_def pathfinish_def algebra_simps)
  qed (use assms in \<open>auto simp: shiftpath_def algebra_simps pathstart_def pathfinish_def\<close>)
qed

definition shiftpath' :: "real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)"
  where "shiftpath' a p = (\<lambda>x. p (frac (x + a)))"

lemma homotopic_loops_shiftpath'_left:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p"
  shows   "homotopic_loops A (shiftpath' x p) p"
proof (rule homotopic_loops_sym, rule homotopic_loops_reparametrize)
  show "continuous_on {0..1} ((+) x)"
    by (intro continuous_intros)
  show "shiftpath' x p t = p (frac (x + t))" if "t \<in> {0..1}" for t
    using that assms by (simp add: shiftpath'_def add_ac)
qed (use assms in auto)

lemma homotopic_loops_shiftpath'_right:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p"
  shows   "homotopic_loops A p (shiftpath' x p)"
  using homotopic_loops_shiftpath'_left[OF assms] by (simp add: homotopic_loops_sym)


lemma homotopic_loops_shiftpath_left:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p" "x \<in> {0..1}"
  shows   "homotopic_loops A (shiftpath x p) p"
proof (rule homotopic_loops_sym, rule homotopic_loops_reparametrize)
  show "continuous_on {0..1} ((+) x)"
    by (intro continuous_intros)
  show "shiftpath x p t = p (frac (x + t))" if "t \<in> {0..1}" for t
    using that assms by (simp add: shiftpath_loop_altdef add_ac)
qed (use assms in auto)

lemma homotopic_loops_shiftpath_right:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p" "x \<in> {0..1}"
  shows   "homotopic_loops A p (shiftpath x p)"
  using homotopic_loops_shiftpath_left[OF assms] by (simp add: homotopic_loops_sym)

lemma shiftpath'_eq_shiftpath:
  assumes "pathstart p = pathfinish p" "c \<in> {0..1}" "t \<in> {0..1}"
  shows   "shiftpath' c p t = shiftpath c p t"
proof -
  consider "t + c < 1" | "t + c = 1" | "t + c > 1" "t + c < 2" | "t + c \<ge> 2"
    by linarith
  thus ?thesis
  proof cases
    case 1
    hence "frac (t + c) = t + c"
      using assms by (subst frac_unique_iff) auto
    thus ?thesis
      using assms 1 by (simp add: shiftpath'_def shiftpath_def add_ac)
  next
    case 3
    hence "frac (t + c) = t + c - 1"
      using assms by (subst frac_unique_iff) (auto simp: algebra_simps)
    thus ?thesis
      using assms 3 by (simp add: shiftpath'_def shiftpath_def add_ac)
  next
    case 4
    with assms have "t + c = 2"
      by auto
    thus ?thesis using assms
      by (simp add: shiftpath'_def shiftpath_def pathstart_def pathfinish_def add_ac)
  qed (use assms in \<open>auto simp: shiftpath'_def shiftpath_def add_ac pathstart_def pathfinish_def\<close>)
qed

lemma cis_multiple_2pi' [simp]:
  "n \<in> \<int> \<Longrightarrow> cis (2 * n * pi) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (2 * (n * pi)) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (pi * (2 * n)) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (pi * (n * 2)) = 1"
  using cis_multiple_2pi[of n] by (simp_all only: mult_ac)

lemma shiftpath_full_part_circlepath:
  "shiftpath c (part_circlepath x r a (a + 2 * of_int n * pi)) =
   part_circlepath x r (a + 2 * n * pi * c) (a + 2 * n * pi * (c + 1))"
  unfolding shiftpath_def
  by (simp add: shiftpath_def part_circlepath_altdef fun_eq_iff rcis_def linepath_def
                field_simps flip: cis_mult cis_divide)

lemma shiftpath'_full_part_circlepath:
  "shiftpath' c (part_circlepath x r a (a + 2 * of_int n * pi)) =
   part_circlepath x r (a + 2 * n * pi * c) (a + 2 * n * pi * (c + 1))"
  apply (simp add: shiftpath'_def fun_eq_iff part_circlepath_altdef rcis_def linepath_def algebra_simps frac_def divide_conv_cnj flip: cis_mult cis_divide)
  by (metis cis.ctr cos_int_2pin mult.assoc mult.left_commute of_int_mult one_complex.ctr sin_int_2pin)

lemma shiftpath_circlepath:
  "shiftpath c (circlepath x r) = part_circlepath x r (c * 2 * pi) ((c + 1) * 2 * pi)"
  unfolding circlepath_def using shiftpath_full_part_circlepath[of c x r 0 1]
  by (simp add: algebra_simps)

lemma shiftpath'_circlepath:
  "shiftpath' c (circlepath x r) = part_circlepath x r (c * 2 * pi) ((c + 1) * 2 * pi)"
  unfolding circlepath_def using shiftpath'_full_part_circlepath[of c x r 0 1]
  by (simp add: algebra_simps)


lemma homotopic_loops_part_circlepath_circlepath:
  assumes "b = a + 2 * pi" "sphere x r \<subseteq> A" "r \<ge> 0"
  shows   "homotopic_loops A (part_circlepath x r a b) (circlepath x r)"
proof -
  have "homotopic_loops A (shiftpath' (a / (2 * pi)) (circlepath x r)) (circlepath x r)"
    using assms by (intro homotopic_loops_shiftpath'_left) auto
  also have "shiftpath' (a / (2 * pi)) (circlepath x r) = part_circlepath x r a ((a / pi + 2) * pi)"
    by (simp add: shiftpath'_circlepath)
  also have "(a / pi + 2) * pi = b"
    using assms by (simp add: divide_simps del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  finally show ?thesis .
qed

lemma homotopic_loops_reversepath_D:
  "homotopic_loops A p q \<Longrightarrow> homotopic_loops A (reversepath p) (reversepath q)"
  apply (simp add: homotopic_loops_def homotopic_with_def, clarify)
  apply (rule_tac x="h \<circ> (\<lambda>x. (fst x, 1 - snd x))" in exI)
  apply (rule conjI continuous_intros)+
  apply (auto simp: reversepath_def pathstart_def pathfinish_def elim!: continuous_on_subset)
  done

lemma homotopic_loops_reversepath:
  "homotopic_loops A (reversepath p) (reversepath q) \<longleftrightarrow> homotopic_loops A p q"
  using homotopic_loops_reversepath_D reversepath_reversepath by metis

lemmas [trans] = homotopic_loops_trans

lemma winding_number_part_circlepath_full:
  assumes "y \<in> ball x r" "\<alpha> + 2 * pi = \<beta>"
  shows   "winding_number (part_circlepath x r \<alpha> \<beta>) y = 1"
proof -
  have "0 \<le> dist x y"
    by auto
  also have "\<dots> < r"
    using assms by auto
  finally have "r > 0" .
  have "homotopic_loops (-{y}) (part_circlepath x r \<alpha> (\<alpha> + 2 * pi)) (circlepath x r)"
    by (rule homotopic_loops_part_circlepath_circlepath) (use assms \<open>r > 0\<close> in auto)
  hence "winding_number (part_circlepath x r \<alpha> (\<alpha> + 2 * pi)) y = winding_number (circlepath x r) y"
    by (rule winding_number_homotopic_loops)
  also have "\<dots> = 1"
    by (intro winding_number_circlepath) (use assms in \<open>auto simp: dist_norm norm_minus_commute\<close>)
  also have "\<alpha> + 2 * pi = \<beta>"
    using assms(2) by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma winding_number_part_circlepath_full':
  assumes "y \<in> ball x r" "\<alpha> - 2 * pi = \<beta>"
  shows   "winding_number (part_circlepath x r \<alpha> \<beta>) y = -1"
proof -
  have "0 \<le> dist x y"
    by simp
  also from assms have "dist x y < r"
    by auto
  finally have r: "r > 0"
    by simp
  have "winding_number (part_circlepath x r (\<alpha> - 2 * pi) \<alpha>) y = 1"
    by (rule winding_number_part_circlepath_full) (use assms in auto)
  also have "part_circlepath x r (\<alpha> - 2 * pi) \<alpha> = reversepath (part_circlepath x r \<alpha> (\<alpha> - 2 * pi))"
    by simp
  also have "winding_number \<dots> y = -winding_number (part_circlepath x r \<alpha> (\<alpha> - 2 * pi)) y"
    using path_image_part_circlepath_subset'[of r x \<alpha> "\<alpha> - 2 * pi"] r assms
    by (intro winding_number_reversepath) auto
  also have "\<alpha> - 2 * pi = \<beta>"
    using assms(2) by (simp add: algebra_simps)
  finally show ?thesis
    by Groebner_Basis.algebra
qed

text \<open>
  The following lemma is very difficult to bypass some nasty geometric reasoning:
  If a path only touches the frontier of a set at its beginning or end,
  then it is either fully inside the set or fully outside the set.
\<close>
lemma path_fully_inside_or_fully_outside:
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "path p" "\<And>x. x \<in> {0<..<1} \<Longrightarrow> p x \<notin> frontier A"
  shows   "path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {}"
proof (rule ccontr)
  assume *: "\<not>(path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {})"
  from * obtain x y where xy: "x \<in> {0..1}" "y \<in> {0..1}" "p x \<notin> closure A" "p y \<in> interior A"
    unfolding path_image_def by blast
  define x' y' where "x' = min x y" and "y' = max x y"
  have xy': "x' \<in> {0..1}" "y' \<in> {0..1}" "x' \<le> y'"
    using xy by (auto simp: x'_def y'_def)

  define q where "q = subpath x' y' p"
  have [simp]: "path q"
    using xy' by (auto simp: q_def assms)

  have "path_image q \<inter> frontier A \<noteq> {}"
  proof (rule connected_Int_frontier)
    show "connected (path_image q)"
      by auto
  next
    have "q (if x \<le> y then 0 else 1) \<in> path_image q"
      by (auto simp: path_image_def)
    moreover have "q (if x \<le> y then 0 else 1) \<notin> A"
      using xy closure_subset by (auto simp: q_def subpath_def x'_def y'_def)
    ultimately show "path_image q - A \<noteq> {}"
      by blast
  next
    have "q (if x \<le> y then 1 else 0) \<in> path_image q"
      by (auto simp: path_image_def)
    moreover have "q (if x \<le> y then 1 else 0) \<in> A"
      using xy interior_subset by (auto simp: q_def subpath_def x'_def y'_def)
    ultimately show "path_image q \<inter> A \<noteq> {}"
      by blast
  qed
  then obtain w where w: "w \<in> {x'..y'}" "p w \<in> frontier A"
    unfolding q_def path_image_subpath using xy' by (force split: if_splits)

  have "w \<noteq> x"
    using xy w by (metis DiffE frontier_def)
  moreover have "w \<noteq> y"
    using xy w unfolding frontier_def by auto
  ultimately have "w \<in> {x'<..<y'}"
    using w(1) by (auto simp: x'_def y'_def)
  also have "\<dots> \<subseteq> {0<..<1}"
    using xy' by auto
  finally have "w \<in> {0<..<1}" .
  with assms(2)[of w] have "p w \<notin> frontier A"
    by blast
  with \<open>p w \<in> frontier A\<close> show False
    by contradiction
qed

lemma between_trans1:
  assumes "between (a, c) b" "between (b, d) c" "b \<noteq> c" "a \<noteq> d"
  shows   "between (a, d) b"
proof (cases "distinct [a, b, c, d]")
  case False
  with assms show ?thesis
    by (auto simp: between_def)
next
  case True
  from assms(1) obtain u where u: "u \<in> {0..1}" "b = (1 - u) *\<^sub>R a + u *\<^sub>R c"
    by (auto simp: between_def closed_segment_def)
  from assms(2) obtain v where v: "v \<in> {0..1}" "c = (1 - v) *\<^sub>R b + v *\<^sub>R d"
    by (auto simp: between_def closed_segment_def)

  have "u \<noteq> 0" "u \<noteq> 1" "v \<noteq> 0" "v \<noteq> 1"
    using u v True by auto
  with u(1) v(1) have uv: "u \<in> {0<..<1}" "v \<in> {0<..<1}"
    by auto

  define z where "z = 1 - u * (1 - v)"
  define t where "t = (u * v) / z"
  have "u * (1 - v) < 1 * 1"
    using uv by (intro mult_strict_mono) auto
  hence *: "z > 0"
    unfolding z_def by auto

  have "b = (1 - u) *\<^sub>R a + (u * (1 - v)) *\<^sub>R b + (u * v) *\<^sub>R d"
    by (subst u, subst v) (simp add: algebra_simps)
  hence "z *\<^sub>R b = (1 - u) *\<^sub>R a + (u * v) *\<^sub>R d"
    by (simp add: algebra_simps z_def)
  hence "inverse z *\<^sub>R z *\<^sub>R b = inverse z *\<^sub>R ((1 - u) *\<^sub>R a + (u * v) *\<^sub>R d)"
    by (simp only: )
  also have "inverse z *\<^sub>R z *\<^sub>R b = b"
    using * by (simp add: field_simps)
  also have "inverse z *\<^sub>R ((1 - u) *\<^sub>R a + (u * v) *\<^sub>R d) =
             ((1 - u) / z) *\<^sub>R a + ((u * v) / z) *\<^sub>R d"
    using * by (simp add: algebra_simps divide_inverse)
  also have "(1 - u) / z = 1 - t"
    using * by (simp add: field_simps t_def z_def)
  also have "(u * v) / z = t"
    by (simp add: t_def)
  finally have "b = (1 - t) *\<^sub>R a + t *\<^sub>R d" .

  moreover have "t \<ge> 0"
    unfolding t_def using u(1) v(1) *
    by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
  moreover have "(1 - u) / z \<ge> 0"
    using u(1) * by (intro divide_nonneg_pos) auto
  with \<open>(1 - u) / z = 1 - t\<close> have "t \<le> 1"
    by simp
  ultimately show ?thesis
    unfolding between_def prod.case closed_segment_def by blast
qed

lemma between_trans2:
  "between (a, c) b \<Longrightarrow> between (b, d) c \<Longrightarrow> b \<noteq> c \<Longrightarrow> a \<noteq> d \<Longrightarrow> between (a, d) c"
  using between_trans1[of d b c a] by (simp add: between_commute)

lemma between_trans1':
  assumes "between (a :: 'a :: euclidean_space, c) b" "between (b, d) c" "b \<noteq> c"
  shows   "between (a, d) b"
proof (cases "a = d")
  case True
  with assms show ?thesis
    using between_antisym between_commute by metis
qed (use between_trans1[OF assms] in simp)

lemma between_trans2':
  assumes "between (a :: 'a :: euclidean_space, c) b" "between (b, d) c" "b \<noteq> c"
  shows   "between (a, d) c"
proof (cases "a = d")
  case True
  with assms show ?thesis
    using between_antisym between_commute by metis
qed (use between_trans2[OF assms] in simp)

fun betweens :: "'a :: euclidean_space list \<Rightarrow> bool" where
  "betweens (x # y # z # xs) \<longleftrightarrow> between (x, z) y \<and> betweens (y # z # xs)"
| "betweens _ \<longleftrightarrow> True"

lemma dist_linepath1: "dist (linepath a b x) a = \<bar>x\<bar> * dist a b"
proof -
  have "dist (linepath a b x) a = norm (x *\<^sub>R (b - a))"
    unfolding scaleR_diff_right
    by (simp add: linepath_def dist_norm algebra_simps)
  also have "\<dots> = \<bar>x\<bar> * dist a b"
    by (subst norm_scaleR) (auto simp: dist_norm norm_minus_commute)
  finally show ?thesis .
qed

lemma dist_linepath2: "dist (linepath a b x) b = \<bar>1 - x\<bar> * dist a b"
proof -
  have "dist (linepath a b x) b = norm ((x - 1) *\<^sub>R (b - a))"
    unfolding scaleR_diff_right
    by (simp add: linepath_def dist_norm algebra_simps)
  also have "\<dots> = \<bar>x - 1\<bar> * dist a b"
    by (subst norm_scaleR) (auto simp: dist_norm norm_minus_commute)
  finally show ?thesis
    by (simp add: abs_minus_commute)
qed

lemma between_conv_linepath:
  fixes a b c :: "'a :: euclidean_space"
  assumes "between (a, c) b"
  shows   "b = linepath a c (dist a b / dist a c)" (is "_ = ?b'")
proof (cases "a = c")
  case False
  from assms obtain u where u: "u \<in> {0..1}" "b = (1 - u) *\<^sub>R a + u *\<^sub>R c"
    using assms by (auto simp: between_def closed_segment_def)
  have "dist a b = norm (u *\<^sub>R (a - c))"
    unfolding scaleR_diff_right by (simp add: u dist_norm algebra_simps)
  hence ab: "dist a b = u * dist a c"
    using u(1) by (simp add: dist_norm norm_minus_commute)
  define t where "t = dist a b / dist a c"
  have "linepath a c t =
          (1 - dist a b / dist a c) *\<^sub>R a + (dist a b / dist a c) *\<^sub>R c"
    by (simp add: ab linepath_def t_def)
  also have "(1 - dist a b / dist a c) = 1 - u"
    using False by (simp add: ab)
  also have "dist a b / dist a c = u"
    using False by (simp add: ab)
  also have "(1 - u) *\<^sub>R a + u *\<^sub>R c = b"
    by (simp add: u)
  finally show ?thesis
    by (simp add: u t_def)
qed (use assms in auto)

lemma cis_minus_pi [simp]: "cis (-pi) = -1"
  by (simp flip: cis_cnj)

lemma complex_derivative_on_convex_imp_lipschitz:
  fixes f' :: "complex \<Rightarrow> complex"
  assumes deriv: "\<And>z. z \<in> A \<Longrightarrow> (f has_field_derivative f' z) (at z within A)"
  assumes A: "convex A" and C: "\<And>x. x \<in> A \<Longrightarrow> norm (f' x) \<le> C" "C \<ge> 0"
  shows   "C-lipschitz_on A f"
proof (rule lipschitz_onI)
  fix x y assume xy: "x \<in> A" "y \<in> A"
  let ?l = "linepath y x"
  have "(f' has_contour_integral f (pathfinish ?l) - f (pathstart ?l)) ?l"
  proof (rule contour_integral_primitive)
    show "(f has_field_derivative f' z) (at z within A)" if "z \<in> A" for z
      using deriv[OF that] .
    show "path_image (linepath y x) \<subseteq> A"
      unfolding path_image_linepath by (intro closed_segment_subset xy A)
  qed auto
  hence "norm (f (pathfinish ?l) - f (pathstart ?l)) \<le> C * norm (x - y)"
  proof (rule has_contour_integral_bound_linepath)
    fix z assume "z \<in> closed_segment y x"
    also have "closed_segment y x \<subseteq> A"
      by (intro closed_segment_subset xy A)
    finally show "norm (f' z) \<le> C"
      using C(1)[of z] by auto
  qed fact+
  thus "dist (f x) (f y) \<le> C * dist x y"
    by (simp add: dist_norm norm_minus_commute)
qed fact+

(* TODO: convex is *probably* not needed here. Just decompose into a finite union of discs. *)
lemma analytic_on_compact_convex_imp_lipschitz:
  assumes "f analytic_on A" "convex A" "compact A"
  obtains C where "C-lipschitz_on A f"
proof -
  have "deriv f analytic_on A"
    by (intro analytic_intros assms)
  define C where "C = Sup (norm ` (insert 0 (deriv f ` A)))"

  have "compact (insert 0 (deriv f ` A))"
    by (intro compact_insert compact_continuous_image analytic_imp_holomorphic
              holomorphic_on_imp_continuous_on analytic_intros assms)
  hence "bounded (insert 0 (deriv f ` A))"
    by (rule compact_imp_bounded)
  hence bdd: "bdd_above (norm ` insert 0 (deriv f ` A))"
    unfolding bdd_above_norm .

  show ?thesis
  proof (rule that[of C], rule complex_derivative_on_convex_imp_lipschitz)
    show "C \<ge> 0"
      unfolding C_def by (intro cSup_upper bdd) auto
  next
    show "(f has_field_derivative deriv f z) (at z within A)" if "z \<in> A" for z
      using that assms(1) analytic_on_holomorphic holomorphic_derivI by blast
  next
    show "norm (deriv f z) \<le> C" if "z \<in> A" for z
    proof -
      have "norm (deriv f z) \<in> norm ` insert 0 (deriv f ` A)"
        using that by auto
      moreover have "norm ` insert 0 (deriv f ` A) \<noteq> {}"
        by blast
      ultimately show "norm (deriv f z) \<le> C"
        unfolding C_def using bdd by (intro cSup_upper)
    qed
  qed fact+
qed

lemma lipschitz_on_complex_inverse:
  assumes "C > 0"
  shows   "(1/C^2)-lipschitz_on {z. Im z \<ge> C} (\<lambda>z. inverse z :: complex)"
proof (rule complex_derivative_on_convex_imp_lipschitz)
  show "((\<lambda>z. inverse z :: complex) has_field_derivative (-1 / z ^ 2)) (at z within {z. Im z \<ge> C})"
    if "z \<in> {z. Im z \<ge> C}" for z
    using that assms by (auto intro!: derivative_eq_intros simp: power2_eq_square field_simps)
  show "convex {z. Im z \<ge> C}"
    by (simp add: convex_halfspace_Im_ge)
  show "cmod (- 1 / z\<^sup>2) \<le> 1 / C\<^sup>2" if "z \<in> {z. Im z \<ge> C}" for z
  proof -
    from that and assms have [simp]: "z \<noteq> 0"
      by auto
    have "C ^ 2 \<le> Im z ^ 2"
      using assms that by (intro power_mono) auto
    also have "\<dots> \<le> norm z ^ 2"
      unfolding cmod_power2 by simp
    finally show ?thesis
      using assms by (simp add: field_simps norm_divide norm_power)
  qed
qed (use assms in auto)

lemma lipschitz_on_cnj [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f"
  shows "C-lipschitz_on U (\<lambda>x. cnj (f x))"
proof (rule lipschitz_onI)
  fix x y assume xy: "x \<in> U" "y \<in> U"
  have "dist (cnj (f x)) (cnj (f y)) = norm (cnj (f x) - cnj (f y))"
    by (simp add: dist_norm)
  also have "cnj (f x) - cnj (f y) = cnj (f x - f y)"
    by simp
  also have "norm \<dots> = dist (f x) (f y)"
    by (subst complex_mod_cnj) (auto simp: dist_norm)
  also have "\<dots> \<le> C * dist x y"
    by (rule lipschitz_onD[OF assms]) fact+
  finally show "dist (cnj (f x)) (cnj (f y)) \<le> C * dist x y"
    by (simp add: mult_ac)
qed (use assms lipschitz_on_nonneg in blast)

lemma lipschitz_on_cmult_complex [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f"
  shows "(norm c * C)-lipschitz_on U (\<lambda>x. c * f x)"
proof (rule lipschitz_onI)
  have "C \<ge> 0"
    using assms lipschitz_on_nonneg by blast
  thus "norm c * C \<ge> 0"
    by simp
next
  fix x y assume xy: "x \<in> U" "y \<in> U"
  have "dist (c * f x) (c * f y) = norm c * dist (f x) (f y)"
    by (metis dist_norm norm_mult vector_space_over_itself.scale_right_diff_distrib)
  also have "\<dots> \<le> norm c * (C * dist x y)"
    by (intro mult_left_mono lipschitz_onD[OF assms]) (use xy in auto)
  finally show "dist (c * f x) (c * f y) \<le> cmod c * C * dist x y"
    by (simp add: mult_ac)
qed

lemma lipschitz_on_cmult_complex' [lipschitz_intros]:
  fixes f::"'a::metric_space \<Rightarrow> complex"
  assumes "C-lipschitz_on U f" "C' \<ge> norm c * C"
  shows "C'-lipschitz_on U (\<lambda>x. c * f x)"
  using lipschitz_on_cmult_complex[OF assms(1), of c] assms(2) lipschitz_on_le by blast

lemma lipschitz_on_cadd_left [lipschitz_intros]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_vector"
  assumes "C-lipschitz_on A f"
  shows   "C-lipschitz_on A (\<lambda>x. c + f x)"
proof (rule lipschitz_onI)
  fix x y assume "x \<in> A" "y \<in> A" 
  thus "dist (c + f x) (c + f y) \<le> C * dist x y"
    using lipschitz_onD[OF assms, of x y] by (simp add: dist_norm)
qed (use assms lipschitz_on_nonneg in blast)

lemma lipschitz_on_cadd_right [lipschitz_intros]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_vector"
  assumes "C-lipschitz_on A f"
  shows   "C-lipschitz_on A (\<lambda>x. f x + c)"
  by (subst add.commute, rule lipschitz_on_cadd_left [OF assms])

lemma inner_mult_both_complex: "(z * x :: complex) \<bullet> (z * y) = norm z ^ 2 * (x \<bullet> y)"
  unfolding cmod_power2 by (simp add: inner_complex_def algebra_simps power2_eq_square)

lemma orthogonal_transformation_mult_complex [intro]:
  "norm z = 1 \<Longrightarrow> orthogonal_transformation ((*) (z :: complex))"
  unfolding orthogonal_transformation_def
  by (auto intro!: linear_times simp: inner_mult_both_complex)

lemma simple_path_continuous_image:
  assumes "simple_path p" "inj_on f (path_image p)" "continuous_on (path_image p) f"
  shows   "simple_path (f \<circ> p)"
  using assms by (auto simp: simple_path_def inj_on_def path_image_def loop_free_def intro!: path_continuous_image)

lemma linepath_scaleR: "(*\<^sub>R) c \<circ> linepath a b = linepath (c *\<^sub>R a) (c *\<^sub>R b)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

lemma linepath_mult_complex: "(*) c \<circ> linepath a b = linepath (c * a) (c * b :: complex)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

lemma part_circlepath_scaleR:
  "(*\<^sub>R) c \<circ> part_circlepath x r a b = part_circlepath (c *\<^sub>R x) (c * r) a b"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  thus ?thesis
    by (simp add: part_circlepath_altdef fun_eq_iff algebra_simps linepath_def rcis_def cis_Arg 
                  complex_sgn_def scaleR_conv_of_real flip: cis_divide cis_mult)
qed (auto simp: fun_eq_iff part_circlepath_altdef)

lemma part_circlepath_mult_complex:
  "(*) c \<circ> part_circlepath x r a b = part_circlepath (c * x :: complex) (norm c * r) (a + Arg c) (b + Arg c)"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  thus ?thesis
    by (simp add: part_circlepath_altdef fun_eq_iff algebra_simps linepath_def rcis_def cis_Arg 
                  complex_sgn_def scaleR_conv_of_real flip: cis_divide cis_mult)
qed (auto simp: fun_eq_iff part_circlepath_altdef)  

lemma part_circlepath_mult_complex':
  assumes "cis a' = cis (a + Arg c)" "b' = a' + b - a"
  shows   "(*) c \<circ> part_circlepath x r a b = part_circlepath (c * x :: complex) (norm c * r) a' b'"
  unfolding part_circlepath_mult_complex by (rule part_circlepath_cong) (use assms in auto)

lemma linepath_translate: "(+) c \<circ> linepath a b = linepath (c + a) (c + b)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

lemma part_circlepath_translate:
  "(+) c \<circ> part_circlepath x r a b = part_circlepath (c + x) r a b"
  by (simp add: part_circlepath_def fun_eq_iff algebra_simps)

lemma circlepath_translate:
  "(+) c \<circ> circlepath x r = circlepath (c + x) r"
  by (simp add: circlepath_def part_circlepath_translate)

lemma rectpath_translate:
  "(+) c \<circ> rectpath a b = rectpath (c + a) (c + b)"
  by (simp add: rectpath_def linepath_translate Let_def path_compose_join plus_complex.ctr)

lemma dist_cmult_left_complex: "dist (c * a) (c * b) = norm c * dist a (b :: complex)"
  by (simp add: dist_norm ring_distribs flip: norm_mult)

lemma dist_cmult_right_complex: "dist (a * c) (b * c) = dist a (b :: complex) * norm c"
  by (simp add: dist_norm ring_distribs flip: norm_mult)
  
lemma circlepath_altdef: "circlepath x r t = x + rcis r (2 * pi * t)"
  by (simp add: circlepath_def part_circlepath_altdef mult_ac)  

lemma path_image_cong: "(\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x) \<Longrightarrow> path_image p = path_image q"
  by (auto simp: path_image_def)

lemma path_cong: "(\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x) \<Longrightarrow> path p = path q"
  unfolding path_def by (intro continuous_on_cong) auto

lemma simple_path_cong:
  shows "(\<And>x. x \<in> {0..1} \<Longrightarrow> f x = g x) \<Longrightarrow> simple_path f \<longleftrightarrow> simple_path g"
  unfolding simple_path_def loop_free_def
  by (intro arg_cong2[of _ _ _ _ "(\<and>)"] path_cong) auto
  
  

definition pathends where "pathends p = {pathstart p, pathfinish p}"

lemma simple_path_joinE':
  assumes "simple_path (g1 +++ g2)" and "pathfinish g1 = pathstart g2"
  shows   "path_image g1 \<inter> path_image g2 \<subseteq> 
             (insert (pathstart g2) (if pathstart g1 = pathfinish g2 then {pathstart g1} else {}))"
  using assms
  by (smt (verit, del_insts) arc_join_eq insert_commute pathfinish_join pathstart_join simple_path_cases simple_path_joinE)

lemma simple_path_joinE'':
  assumes "simple_path (g1 +++ g2)" and "pathfinish g1 = pathstart g2"
          "x \<in> path_image g1" "x \<in> path_image g2"
  shows   "x = pathstart g2 \<or> x = pathfinish g2 \<and> pathstart g1 = pathfinish g2"
  using simple_path_joinE'[OF assms(1,2)] assms(3,4) by (auto split: if_splits)
  
lemma arc_continuous_image:
  assumes "arc p" "inj_on f (path_image p)" "continuous_on (path_image p) f"
  shows   "arc (f \<circ> p)"
  using assms by (auto simp: arc_def inj_on_def path_image_def intro!: path_continuous_image)

lemma simply_connected_imp_homotopic_paths:
  fixes S :: "'a :: real_normed_vector set"
  assumes "simply_connected S" "path p" "path_image p \<subseteq> S" "path q" "path_image q \<subseteq> S"
  assumes "pathstart q = pathstart p \<and> pathfinish q = pathfinish p"
  shows   "homotopic_paths S p q"
  using assms unfolding simply_connected_eq_homotopic_paths by blast

lemma simple_path_reversepath' [simp]: "simple_path (reversepath g) \<longleftrightarrow> simple_path g"
  using simple_path_reversepath[of g] simple_path_reversepath[of "reversepath g"]
  by auto

definition simple_loop where "simple_loop p \<longleftrightarrow> simple_path p \<and> pathstart p = pathfinish p"

lemma simple_loop_reversepath [simp]: "simple_loop (reversepath p) \<longleftrightarrow> simple_loop p"
  by (auto simp: simple_loop_def)

definition simple_loop_ccw :: "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "simple_loop_ccw p \<longleftrightarrow> simple_loop p \<and> (\<exists>z. z \<notin> path_image p \<and> winding_number p z = 1)"

definition simple_loop_cw :: "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "simple_loop_cw p \<longleftrightarrow> simple_loop p \<and> (\<exists>z. z \<notin> path_image p \<and> winding_number p z = -1)"

definition simple_loop_orientation :: "(real \<Rightarrow> complex) \<Rightarrow> int" where
  "simple_loop_orientation p =
     (if simple_loop_ccw p then 1 else if simple_loop_cw p then -1 else 0)"

lemma simple_loop_ccwI:
  "simple_loop p \<Longrightarrow> z \<notin> path_image p \<Longrightarrow> winding_number p z = 1 \<Longrightarrow> simple_loop_ccw p"
  unfolding simple_loop_ccw_def by auto

lemma simple_loop_cwI:
  "simple_loop p \<Longrightarrow> z \<notin> path_image p \<Longrightarrow> winding_number p z = -1 \<Longrightarrow> simple_loop_cw p"
  unfolding simple_loop_cw_def by auto

(* TODO cleanup *)
lemma simple_path_not_cw_and_ccw: "\<not>simple_loop_cw p \<or> \<not>simple_loop_ccw p"
  unfolding simple_loop_cw_def simple_loop_ccw_def simple_loop_def
  by (metis ComplI UnE inside_Un_outside one_neq_neg_one simple_closed_path_winding_number_inside
            simple_path_def winding_number_zero_in_outside zero_neq_neg_one zero_neq_one)

(* TODO cleanup *)
lemma simple_loop_cw_or_ccw:
  assumes "simple_loop p"
  shows   "simple_loop_cw p \<or> simple_loop_ccw p"
  using assms unfolding simple_loop_cw_def simple_loop_ccw_def simple_loop_def
  by (metis Compl_iff UnCI inside_Un_outside simple_closed_path_winding_number_inside
        simple_closed_path_wn3)

lemma simple_loop_ccw_conv_cw:
  assumes "simple_loop p"
  shows   "simple_loop_ccw p \<longleftrightarrow> \<not>simple_loop_cw p"
  using assms simple_path_not_cw_and_ccw simple_loop_cw_or_ccw by blast

lemma simple_loop_orientation_eqI:
  assumes "simple_loop p" "z \<notin> path_image p"
  assumes "winding_number p z \<in> {-1, 1}"
  shows   "simple_loop_orientation p = winding_number p z"
  unfolding simple_loop_orientation_def
  using assms simple_loop_ccwI simple_loop_ccw_conv_cw simple_loop_cwI by force

lemma simple_loop_winding_number_cases:
  assumes "simple_loop p" "z \<notin> path_image p"
  shows   "winding_number p z = (if z \<in> inside (path_image p) then simple_loop_orientation p else 0)"
proof (cases "z \<in> inside (path_image p)")
  case True
  hence "winding_number p z \<in> {-1, 1}"
    using simple_closed_path_winding_number_inside[of p] assms
    unfolding simple_loop_def by fast
  hence "simple_loop_orientation p = winding_number p z"
    by (intro simple_loop_orientation_eqI) (use assms in auto)
  thus ?thesis
    using True by simp
next
  case False
  hence "winding_number p z = 0"
    using assms unfolding simple_loop_def
    by (simp add: inside_outside simple_path_imp_path winding_number_zero_in_outside)
  thus ?thesis
    using False by auto
qed

lemma simple_loop_orientation_eq_0_iff [simp]:
  "simple_loop_orientation p = 0 \<longleftrightarrow> \<not>simple_loop p"
  using simple_loop_cw_or_ccw[of p]
  by (auto simp: simple_loop_orientation_def simple_loop_cw_def simple_loop_ccw_def)

lemma simple_loop_ccw_reversepath_aux:
  assumes "simple_loop_ccw p"
  shows   "simple_loop_cw (reversepath p)"
proof -
  from assms obtain z where *: "simple_loop p" "z \<notin> path_image p" "winding_number p z = 1"
    by (auto simp: simple_loop_ccw_def)
  moreover from * have "winding_number (reversepath p) z = -winding_number p z"
    by (subst winding_number_reversepath) (auto simp: simple_path_imp_path simple_loop_def)
  ultimately show ?thesis using *
    by (auto simp: simple_loop_cw_def simple_loop_def simple_path_reversepath)
qed

lemma simple_loop_cw_reversepath_aux:
  assumes "simple_loop_cw p"
  shows   "simple_loop_ccw (reversepath p)"
proof -
  from assms obtain z where *: "simple_loop p" "z \<notin> path_image p" "winding_number p z = -1"
    by (auto simp: simple_loop_cw_def)
  moreover from * have "winding_number (reversepath p) z = -winding_number p z"
    by (subst winding_number_reversepath) (auto simp: simple_path_imp_path simple_loop_def)
  ultimately show ?thesis using *
    by (auto simp: simple_loop_ccw_def simple_loop_def simple_path_reversepath)
qed

lemma simple_loop_cases: "simple_loop_ccw p \<or> simple_loop_cw p \<or> \<not>simple_loop p"
  using simple_loop_cw_or_ccw[of p] by blast

lemma simple_loop_cw_reversepath [simp]: "simple_loop_cw (reversepath p) \<longleftrightarrow> simple_loop_ccw p"
  using simple_loop_ccw_reversepath_aux reversepath_reversepath simple_loop_cw_reversepath_aux
  by metis

lemma simple_loop_ccw_reversepath [simp]: "simple_loop_ccw (reversepath p) \<longleftrightarrow> simple_loop_cw p"
  using simple_loop_ccw_reversepath_aux reversepath_reversepath simple_loop_cw_reversepath_aux
  by metis
  
lemma simple_loop_orientation_reversepath [simp]:
  "simple_loop_orientation (reversepath p) = -simple_loop_orientation p"
  using simple_path_not_cw_and_ccw[of p] by (auto simp: simple_loop_orientation_def)

lemma simple_loop_orientation_cases:
  assumes "simple_loop p"
  shows   "simple_loop_orientation p \<in> {-1, 1}"
  using simple_loop_cases[of p] assms by (auto simp: simple_loop_orientation_def)

lemma inside_simple_loop_iff:
  assumes "simple_loop p"
  shows   "z \<in> inside (path_image p) \<longleftrightarrow> z \<notin> path_image p \<and> winding_number p z \<noteq> 0"
  using assms
  by (smt (verit, best) disjoint_iff_not_equal inside_no_overlap norm_zero of_int_0
     simple_closed_path_norm_winding_number_inside simple_loop_def simple_loop_winding_number_cases)

lemma outside_simple_loop_iff:
  assumes "simple_loop p"
  shows   "z \<in> outside (path_image p) \<longleftrightarrow> z \<notin> path_image p \<and> winding_number p z = 0"
  using assms by (metis Compl_iff Un_iff inside_Un_outside inside_outside inside_simple_loop_iff)


(* TODO: remove? *)
lemma finite_imp_eventually_sparse_at_0:
  assumes "finite X"
  shows   "eventually (\<lambda>\<epsilon>. sparse \<epsilon> X) (at_right 0)"
proof (cases "X = {} \<or> is_singleton X")
  case False
  hence ne: "Sigma X (\<lambda>x. X - {x}) \<noteq> {}"
    unfolding is_singleton_def by auto
  define m where "m = Min ((\<lambda>(x,y). dist x y) ` (Sigma X (\<lambda>x. X - {x})))"
  have "m > 0"
    unfolding m_def using ne by (subst Min_gr_iff) (use assms in auto)
  show ?thesis
    using eventually_at_right_real[OF \<open>m > 0\<close>]
  proof eventually_elim
    case (elim \<epsilon>)
    show ?case
    proof (intro sparseI)
      fix x y assume xy: "x \<in> X" "y \<in> X" "x \<noteq> y"
      have "\<epsilon> < m"
        using elim by simp
      also have "m \<le> dist x y"
        using xy unfolding m_def by (intro Min.coboundedI) (use assms in auto)
      finally show "dist x y > \<epsilon>" .
    qed
  qed
qed (auto elim!: is_singletonE)

(* TODO: could probably be generalised a lot. But do we still need it? *)
lemma homotopic_paths_split:
  assumes p: "path p" and A: "path_image p \<subseteq> A"
  assumes a: "a \<in> {0..1}"
  assumes eq1: "\<And>x. x \<in> {0..1} \<Longrightarrow> p1 x = subpath 0 a p x"
  assumes eq2: "\<And>x. x \<in> {0..1} \<Longrightarrow> p2 x = subpath a 1 p x"
  shows   "homotopic_paths A p (p1 +++ p2)"
proof -
  have "homotopic_paths (path_image p) (subpath 0 a p +++ subpath a 1 p) (subpath 0 1 p)"
    by (rule homotopic_join_subpaths) (use a p in auto)
  hence "homotopic_paths (path_image p) (subpath 0 1 p) (subpath 0 a p +++ subpath a 1 p)"
    by (simp add: homotopic_paths_sym_eq)
  also have "homotopic_paths (path_image p) (subpath 0 a p +++ subpath a 1 p) (p1 +++ p2)"
    using assms
    apply (intro homotopic_paths_eq)
      apply auto
     apply (subst (asm) path_image_join)
    apply auto
      apply (auto simp: joinpaths_def path_image_def split: if_splits)
      apply (metis (no_types, opaque_lifting) atLeastAtMost_iff image_subset_iff le_numeral_extra(3) path_image_def path_image_subpath_subset zero_less_one_class.zero_le_one)
    apply (metis (full_types) atLeastAtMost_iff image_subset_iff le_numeral_extra(4) path_image_def path_image_subpath_subset zero_less_one_class.zero_le_one)
    done
  also have "subpath 0 1 p = p"
    by simp
  finally show ?thesis
    by (rule homotopic_paths_subset) fact
qed

lemma eventually_path_image_cball_subset:
  fixes p :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "path p" "path_image p \<subseteq> interior A"
  shows "eventually (\<lambda>\<epsilon>. (\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
proof -
  from assms have "compact ( path_image p)"
    by (intro compact_path_image) auto
  moreover have "path_image p \<inter> frontier A = {}"
    using assms by (simp add: disjoint_iff frontier_def subset_eq)
  ultimately have "eventually (\<lambda>\<epsilon>. setdist_gt \<epsilon> (path_image p) (frontier A)) (at_right 0)"
    by (intro compact_closed_imp_eventually_setdist_gt_at_right_0) auto
  moreover have "eventually (\<lambda>\<epsilon>. \<epsilon> > 0) (at_right (0 :: real))"
    by (simp add: eventually_at_right_less)
  ultimately have "eventually (\<lambda>\<epsilon>. (\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
  proof eventually_elim
    case (elim \<epsilon>)
    show "(\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A"
    proof (intro subsetI, elim UN_E)
      fix x y assume xy: "x \<in> path_image p" "y \<in> cball x \<epsilon>"
      show "y \<in> A"
      proof (rule ccontr)
        assume "y \<notin> A"
        have "cball x \<epsilon> \<inter> frontier A \<noteq> {}"
        proof (rule connected_Int_frontier)
          have "x \<in> cball x \<epsilon>"
            using \<open>\<epsilon> > 0\<close> by simp
          moreover have "x \<in> A"
            using \<open>x \<in> path_image p\<close> assms interior_subset by blast
          ultimately show "cball x \<epsilon> \<inter> A \<noteq> {}"
            by blast
        next
          from xy show "cball x \<epsilon> - A \<noteq> {}"
            using \<open>y \<notin> A\<close> by blast
        qed auto
        hence "\<not>setdist_gt \<epsilon> {x} (frontier A)"
          by (force simp: setdist_gt_def)
        moreover have "setdist_gt \<epsilon> {x} (frontier A)"
          by (rule setdist_gt_mono[OF elim(1)]) (use xy in auto)
        ultimately show False by contradiction
      qed
    qed
  qed
  thus ?thesis
    by eventually_elim (use assms interior_subset in auto)
qed

lemma eventually_path_image_cball_subset':
  fixes p :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "path p" "path_image p \<subseteq> interior A" "X \<subseteq> path_image p"
  shows "eventually (\<lambda>\<epsilon>. path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) \<subseteq> A) (at_right 0)"
  using eventually_path_image_cball_subset[OF assms(1-2)]
        eventually_at_right_less[of 0]
proof eventually_elim
  case (elim \<epsilon>)
  have "path_image p \<union> (\<Union>x\<in>X. cball x \<epsilon>) = (\<Union>x\<in>path_image p. {x}) \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
    by blast
  also have "\<dots> \<subseteq> (\<Union>x\<in>path_image p. cball x \<epsilon>) \<union> (\<Union>x\<in>X. cball x \<epsilon>)"
    using elim(2) by (intro Un_mono UN_mono) auto
  also have "\<dots> = (\<Union>x\<in>path_image p \<union> X. cball x \<epsilon>)"
    by blast
  also have "path_image p \<union> X = path_image p"
    using assms by blast
  also have "(\<Union>x\<in>path_image p. cball x \<epsilon>) \<subseteq> A"
    by fact
  finally show ?case .
qed



(* TODO: better name? *)
text \<open>
  We say that a path does not cross a set \<open>A\<close> if it enters \<open>A\<close> at most at its beginning and
  end, and never inbetween.
\<close>
definition does_not_cross :: "(real \<Rightarrow> 'a :: real_vector) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "does_not_cross p A \<longleftrightarrow> (\<forall>x\<in>{0<..<1}. p x \<notin> A)"

lemma does_not_cross_simple_path:
  assumes "simple_path p"
  shows   "does_not_cross p A \<longleftrightarrow> path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}"
proof
  assume "does_not_cross p A"
  thus "path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}" using assms
    by (force simp: does_not_cross_def simple_path_def path_image_def pathstart_def pathfinish_def)
next
  assume *: "path_image p \<inter> A \<subseteq> {pathstart p, pathfinish p}"
  show "does_not_cross p A"
    unfolding does_not_cross_def
  proof safe
    fix x :: real assume x: "x \<in> {0<..<1}" "p x \<in> A"
    hence "p x \<notin> {pathstart p, pathfinish p}"
      using assms by (force simp: simple_path_def loop_free_def pathstart_def pathfinish_def)+
    moreover from x have "p x \<in> path_image p"
      by (auto simp: path_image_def)
    ultimately show False
      using * and x by blast
  qed
qed

lemma path_fully_inside_or_fully_outside':
  fixes p :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "path p" "does_not_cross p (frontier A)"
  shows   "path_image p \<subseteq> closure A \<or> path_image p \<inter> interior A = {}"
  using path_fully_inside_or_fully_outside[OF assms(1), of A] assms unfolding does_not_cross_def
  by auto

lemma in_path_image_part_circlepathI:
  assumes "y = x + rcis r u" "u \<in> closed_segment a b"
  shows   "y \<in> path_image (part_circlepath x r a b)"
proof -
  have "u \<in> path_image (linepath a b)"
    using assms by simp
  then obtain v where v: "v \<in> {0..1}" "u = linepath a b v"
    unfolding path_image_def by blast
  have "y = part_circlepath x r a b v"
    by (simp add: part_circlepath_altdef v assms)
  with v(1) show ?thesis
    unfolding path_image_def by blast
qed

lemma in_path_image_part_circlepathI':
  assumes "Arg (y - x) \<in> closed_segment a b" "dist y x = r"
  shows   "y \<in> path_image (part_circlepath x r a b)"
proof (rule in_path_image_part_circlepathI)
  show "y = x + rcis r (Arg (y - x))"
    using assms
    by (cases "x = y")
       (auto simp: rcis_def cis_Arg complex_sgn_def dist_commute scaleR_conv_of_real
                   field_simps dist_norm norm_minus_commute)
qed fact

lemma path_image_part_circlepath':
  "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` closed_segment a b"
proof -
  have "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` path_image (linepath a b)"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  thus ?thesis
    by simp
qed

lemma path_image_part_circlepath:
  assumes "a \<in> {-pi<..pi}" "b \<in> {-pi<..pi}" "r > 0"
  shows   "path_image (part_circlepath x r a b) = {y\<in>sphere x r. Arg (y - x) \<in> closed_segment a b}"
proof safe
  fix y assume y: "y \<in> path_image (part_circlepath x r a b)"
  show "y \<in> sphere x r"
    using y path_image_part_circlepath_subset'[of r x a b] assms by auto

  from y obtain u where u: "u \<in> {0..1}" "y = part_circlepath x r a b u"
    by (auto simp: path_image_def)
  have "linepath a b u \<in> closed_segment a b"
    using linepath_in_path u(1) by blast
  also have "\<dots> \<subseteq> {-pi<..pi}"
    using assms by (intro closed_segment_subset) auto
  finally have *: "linepath a b u \<in> {-pi<..pi}" .

  have "Arg (y - x) = Arg (rcis r (linepath a b u))"
    by (simp add: u part_circlepath_altdef)
  also have "\<dots> = linepath a b u"
    using * assms by (subst Arg_rcis) auto
  also have "\<dots> \<in> closed_segment a b"
    by fact
  finally show "Arg (y - x) \<in> closed_segment a b" .
next
  fix y assume y: "y \<in> sphere x r" "Arg (y - x) \<in> closed_segment a b"
  show "y \<in> path_image (part_circlepath x r a b)"
    using y by (intro in_path_image_part_circlepathI') (auto simp: dist_commute)
qed

lemma path_image_part_circlepath_mono:
  assumes "min a' b' \<le> min a b" "max a' b' \<ge> max a b"
  shows   "path_image (part_circlepath x r a b) \<subseteq> path_image (part_circlepath x r a' b')"
proof -
  have "path_image (part_circlepath x r a b) = (\<lambda>t. x + rcis r t) ` path_image (linepath a b)"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  also have "\<dots> \<subseteq> (\<lambda>t. x + rcis r t) ` path_image (linepath a' b')"
    unfolding path_image_linepath using assms
    by (intro image_mono) (auto simp: closed_segment_eq_real_ivl split: if_splits)
  also have "\<dots> = path_image (part_circlepath x r a' b')"
    by (simp add: path_image_def part_circlepath_altdef image_image)
  finally show ?thesis .
qed

lemma cis_eq_1_iff: "cis x = 1 \<longleftrightarrow> (\<exists>n. x = 2 * of_int n * pi)"
  by (metis Ints_of_int cis.sel(1) cis_multiple_2pi'(4) cos_one_2pi_int mult.commute)

lemma arcsin_pos: "x \<in> {0<..1} \<Longrightarrow> arcsin x > 0"
  by (metis arcsin_0 arcsin_less_arcsin greaterThanAtMost_iff neg_le_0_iff_le zero_less_one_class.zero_le_one)

lemma sin_lt_zero': "x \<in> {-pi<..<0} \<Longrightarrow> sin x < 0"
  by (metis greaterThanLessThan_iff minus_less_iff neg_0_less_iff_less sin_gt_zero sin_minus)

lemma tan_arcsin: "x \<in> {-1..1} \<Longrightarrow> tan (arcsin x) = x / sqrt (1 - x ^ 2)"
  by (simp add: tan_def cos_arcsin)

lemma Arg_neg_iff: "Arg x < 0 \<longleftrightarrow> Im x < 0"
  using Arg_less_0 linorder_not_le by blast

lemma Arg_pos_iff: "Arg x > 0 \<longleftrightarrow> Im x > 0 \<or> (Im x = 0 \<and> Re x < 0)"
  by (metis Arg_eq_pi Arg_le_pi Arg_lt_pi order_less_le pi_gt_zero)

lemma Arg_neg_real [simp]: "Im x = 0 \<Longrightarrow> Re x < 0 \<Longrightarrow> Arg x = pi"
  using Arg_eq_pi by blast

lemma cis_eq_1_iff':
  assumes "\<bar>x\<bar> < 2 * pi"
  shows   "cis x = 1 \<longleftrightarrow> x = 0"
proof
  assume "cis x = 1"
  then obtain n where n: "x = of_int n * 2 * pi"
    by (auto simp: cis_eq_1_iff)
  with assms have "n = 0"
    by (auto simp: abs_mult simp flip: of_int_abs)
  with n show "x = 0"
    by simp
qed auto

lemma DeMoivre_int: "cis x powi n = cis (of_int n * x)"
proof (cases "n \<ge> 0")
  case True
  hence "cis x powi n = cis x ^ nat n"
    by (simp add: power_int_def)
  also have "\<dots> = cis (real (nat n) * x)"
    by (rule Complex.DeMoivre)
  finally show ?thesis
    using True by simp
next
  case False
  hence "cis x powi n = cis (-x) ^ nat (-n)"
    by (simp add: power_int_def)
  also have "\<dots> = cis (-real (nat (-n)) * x)"
    by (subst Complex.DeMoivre) auto
  finally show ?thesis
    using False by simp
qed

lemma cis_of_int_times_pi_half: "cis (of_int n * pi / 2) = \<i> powi n"
 using DeMoivre_int[of "pi / 2" n] by simp

lemma cis_of_nat_times_pi_half: "cis (real n * pi / 2) = \<i> ^ n"
  using cis_of_int_times_pi_half[of "int n"] by simp

lemma cis_of_int_times_pi: "cis (of_int n * pi) = (-1) powi n"
 using DeMoivre_int[of pi n] by simp

lemma cis_of_nat_times_pi: "cis (real n * pi) = (-1) ^ n"
  using cis_of_int_times_pi[of "int n"] by simp


lemma power3_i [simp]: "\<i> ^ 3 = -\<i>"
  and power4_i [simp]: "\<i> ^ 4 = 1"
  by (simp_all add: eval_nat_numeral)

lemma i_power_mod4: "\<i> ^ n = \<i> ^ (n mod 4)"
proof -
  have "\<i> ^ n = \<i> ^ (4 * (n div 4) + n mod 4)"
    by simp
  also have "\<dots> = \<i> ^ (n mod 4)"
    by (subst power_add) (simp add: power_mult)
  finally show ?thesis .
qed

lemma cis_numeral_times_pi_half [simp]:
  "cis (numeral num * pi / 2) = \<i> ^ (numeral num mod 4)"
proof -
  have "cis (numeral num * pi / 2) = \<i> ^ numeral num"
    using cis_of_nat_times_pi_half[of "numeral num"] by simp
  also have "\<dots> = \<i> ^ (numeral num mod 4)"
    by (rule i_power_mod4)
  finally show ?thesis .
qed

lemma cis_numeral_pi_times_numeral_half [simp]:
  "cis (pi * numeral num / 2) = \<i> ^ (numeral num mod 4)"
  by (subst mult.commute) simp

lemma cis_numeral_times_pi [simp]:
  "cis (numeral num * pi) = (-1) ^ (numeral num mod 2)"
proof -
  have "cis (numeral num * pi) = (-1) ^ numeral num"
    using cis_of_nat_times_pi[of "numeral num"] by simp
  also have "\<dots> = (-1) ^ (numeral num mod 2)"
    by (metis even_mod_2_iff neg_one_even_power neg_one_odd_power)
  finally show ?thesis .
qed

lemma cis_pi_times_numeral [simp]:
  "cis (pi * numeral num) = (-1) ^ (numeral num mod 2)"
  by (subst mult.commute) simp

lemma cis_minus_numeral_times_pi_half [simp]:
  "cis (-(numeral num * pi / 2)) = (-\<i>) ^ (numeral num mod 4)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_numeral_times_pi [simp]:
  "cis (-(numeral num * pi)) = (-1) ^ (numeral num mod 2)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_pi_times_numeral_half [simp]:
  "cis (-(pi * numeral num / 2)) = (-\<i>) ^ (numeral num mod 4)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_minus_pi_times_numeral_pi [simp]:
  "cis (-(pi * numeral num)) = (-1) ^ (numeral num mod 2)"
  by (subst cis_cnj [symmetric]) auto

lemma cis_cong:
  assumes "[a = b] (rmod 2 * pi)"
  shows   "cis a = cis b"
  using assms by (auto simp: rcong_altdef mult_ac simp flip: cis_mult)

lemma rcis_cong:
  assumes "[a = b] (rmod 2 * pi)"
  shows   "rcis r a = rcis r b"
  using assms by (auto simp: rcis_def intro!: cis_cong)

lemma sin_rcong: "[x = y] (rmod (2 * pi)) \<Longrightarrow> sin x = sin y"
  and cos_rcong: "[x = y] (rmod (2 * pi)) \<Longrightarrow> cos x = cos y"
  using cis_cong[of x y] by (simp_all add: complex_eq_iff)

lemma sin_eq_sin_conv_rmod:
  assumes "sin x = sin y"
  shows   "[x = y] (rmod 2 * pi) \<or> [x = pi - y] (rmod 2 * pi)"
proof -
  from assms obtain n where n: "x = y + 2 * of_int n * pi \<or> x = -y + (2 * of_int n + 1) * pi"
    by (subst (asm) sin_eq) (auto elim!: Ints_cases)
  thus ?thesis
  proof (rule disj_forward)
    assume *: "x = y + 2 * of_int n * pi"
    have "[x - 0 = x - of_int n * (2 * pi)] (rmod 2 * pi)"
      by (intro rcong_intros)
    with * show "[x = y] (rmod 2 * pi)"
      by (simp add: mult_ac)
  next
    assume *: "x = -y + (2 * of_int n + 1) * pi"
    have "[x - 0 = x - of_int n * (2 * pi)] (rmod 2 * pi)"
      by (intro rcong_intros)
    also have "x - of_int n * (2 * pi) = pi - y"
      by (simp add: * algebra_simps)
    finally show "[x = pi - y] (rmod 2 * pi)"
      by simp
  qed
qed

lemma sin_eq_sin_conv_rmod_iff:
  "sin x = sin y \<longleftrightarrow> [x = y] (rmod 2 * pi) \<or> [x = pi - y] (rmod 2 * pi)"
  by (metis sin_eq_sin_conv_rmod sin_pi_minus sin_rcong)

lemma cos_eq_cos_conv_rmod:
  assumes "cos x = cos y"
  shows   "[x = y] (rmod 2 * pi) \<or> [x = -y] (rmod 2 * pi)"
proof -
  from assms obtain n where n: "x = y + 2 * of_int n * pi \<or> x = -y + 2 * of_int n * pi"
    by (subst (asm) cos_eq) (auto elim!: Ints_cases)
  thus ?thesis
  proof (rule disj_forward)
    assume *: "x = y + 2 * of_int n * pi"
    have "[x - 0 = x - of_int n * (2 * pi)] (rmod 2 * pi)"
      by (intro rcong_intros)
    with * show "[x = y] (rmod 2 * pi)"
      by (simp add: mult_ac)
  next
    assume *: "x = -y + 2 * of_int n * pi"
    have "[x - 0 = x - of_int n * (2 * pi)] (rmod 2 * pi)"
      by (intro rcong_intros)
    with * show "[x = -y] (rmod 2 * pi)"
      by (simp add: mult_ac)
  qed
qed

lemma cos_eq_cos_conv_rmod_iff:
  "cos x = cos y \<longleftrightarrow> [x = y] (rmod 2 * pi) \<or> [x = -y] (rmod 2 * pi)"
  by (metis cos_eq_cos_conv_rmod cos_minus cos_rcong)

lemma eventually_at_within_in_open:
  assumes "open X" "x \<in> X"
  shows   "eventually (\<lambda>z. z \<in> X \<inter> A - {x}) (at x within A)"
  using eventually_nhds_in_open[OF assms] unfolding eventually_at_filter
  by eventually_elim auto

lemma filterlim_at_withinD:
  assumes "filterlim f (at L within A) F" "open X" "L \<in> X"
  shows   "eventually (\<lambda>x. f x \<in> X \<inter> A - {L}) F"
proof -
  have "eventually (\<lambda>z. z \<in> X \<inter> A - {L}) (at L within A)"
    by (rule eventually_at_within_in_open) (use assms in auto)
  moreover from assms(1) have "filtermap f F \<le> at L within A"
    unfolding filterlim_def .
  ultimately have "eventually (\<lambda>z. z \<in> X \<inter> A - {L}) (filtermap f F)"
    unfolding le_filter_def by blast
  thus ?thesis
    by (simp add: eventually_filtermap)
qed

lemma filterlim_at_withinD':
  assumes "filterlim f (at L within A) F" "open X" "L \<in> X"
  shows   "eventually (\<lambda>x. f x \<in> X \<inter> A) F"
  using filterlim_at_withinD[OF assms] by eventually_elim auto

lemma filterlim_at_rightD:
  assumes "filterlim f (at_right L) F" "a > L"
  shows   "eventually (\<lambda>x. f x \<in> {L<..<a}) F"
  using filterlim_at_withinD'[OF assms(1), of "{..<a}"] assms(2)
  by (auto elim!: eventually_mono)

lemma filterlim_at_leftD:
  assumes "filterlim f (at_left L) F" "a < L"
  shows   "eventually (\<lambda>x. f x \<in> {a<..<L}) F"
  using filterlim_at_withinD'[OF assms(1), of "{a<..}"] assms(2)
  by (auto elim!: eventually_mono)

lemma eventually_Ball_at_right_0_real:
  assumes "eventually P (at_right (0 :: real))"
  shows   "eventually (\<lambda>x. \<forall>y\<in>{0<..x}. P y) (at_right 0)"
  using assms unfolding eventually_at_right_field by force   

lemma open_segment_same_Re:
  assumes "Re a = Re b"
  shows   "open_segment a b = {z. Re z = Re a \<and> Im z \<in> open_segment (Im a) (Im b)}"
  using assms by (auto simp: open_segment_def closed_segment_same_Re complex_eq_iff)

lemma open_segment_same_Im:
  assumes "Im a = Im b"
  shows   "open_segment a b = {z. Im z = Im a \<and> Re z \<in> open_segment (Re a) (Re b)}"
  using assms by (auto simp: open_segment_def closed_segment_same_Im complex_eq_iff)

lemma interior_halfspace_Re_ge [simp]: "interior {z. Re z \<ge> x} = {z. Re z > x}"
  and interior_halfspace_Re_le [simp]: "interior {z. Re z \<le> x} = {z. Re z < x}"
  and interior_halfspace_Im_ge [simp]: "interior {z. Im z \<ge> x} = {z. Im z > x}"
  and interior_halfspace_Im_le [simp]: "interior {z. Im z \<le> x} = {z. Im z < x}"
  using interior_halfspace_ge[of "1::complex" x] interior_halfspace_le[of "1::complex" x]
        interior_halfspace_ge[of \<i> x] interior_halfspace_le[of \<i> x]
  by (simp_all add: inner_complex_def)

lemma inverse_conv_cnj: "norm z = 1 \<Longrightarrow> inverse z = cnj z"
  by (simp add: divide_conv_cnj inverse_eq_divide)

lemma linepath_minus: "linepath (-a) (-b) x = -linepath a b x"
  by (simp add: linepath_def algebra_simps)

lemma winding_number_inverse_valid_path:
  assumes "valid_path \<gamma>" "0 \<notin> path_image \<gamma>" "z \<notin> path_image \<gamma>" "z \<noteq> 0"
  shows "winding_number (inverse \<circ> \<gamma>) (inverse z) = winding_number \<gamma> z - winding_number \<gamma> 0"
proof -
  define C where "C = 1 / (complex_of_real (2 * pi) * \<i>)"
  have "winding_number (inverse \<circ> \<gamma>) (inverse z)
        = C * contour_integral \<gamma> (\<lambda>w. deriv inverse w / (inverse w - inverse z))"
    unfolding C_def
  proof (rule winding_number_comp[of "UNIV - {0,z}"])
    show "open (UNIV - {0, z})"
      by (metis Diff_insert open_UNIV open_delete)
    show "inverse holomorphic_on UNIV - {0, z}"
      by (auto intro:holomorphic_intros)
    show "path_image \<gamma> \<subseteq> UNIV - {0, z}" "inverse z \<notin> path_image (inverse \<circ> \<gamma>)"
      using \<open>0 \<notin> path_image \<gamma>\<close> \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def
      by auto
  qed fact
  also have "\<dots> = C * (contour_integral \<gamma> (\<lambda>w. 1 / (w - z) - 1 / w))"
  proof -
    have "contour_integral \<gamma> (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
          contour_integral \<gamma> (\<lambda>w. 1 / (w - z) - 1 / w)"
    proof (rule contour_integral_cong)
      fix x assume "x \<in> path_image \<gamma>"
      then have "x\<noteq>0" "x\<noteq>z"
        using \<open>0 \<notin> path_image \<gamma>\<close> \<open>z \<notin> path_image \<gamma>\<close> unfolding path_image_def
        by auto
      then show "deriv inverse x / (inverse x - inverse z) = 1 / (x - z) - 1 / x"
        using \<open>z\<noteq>0\<close>
        by (auto simp:divide_simps power2_eq_square algebra_simps)
    qed simp
    then show ?thesis by simp
  qed
  also have "\<dots> = C * (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)) - contour_integral \<gamma> (\<lambda>w. 1 / w))"
  proof (subst contour_integral_diff)
    show "(\<lambda>w. 1 / (w - z)) contour_integrable_on \<gamma>"
      by (rule contour_integrable_inversediff) fact+
    show "(/) 1 contour_integrable_on \<gamma>"
      using contour_integrable_inversediff[OF \<open>valid_path \<gamma>\<close> \<open>0 \<notin> path_image \<gamma>\<close>]
      by simp
  qed simp
  also have "\<dots> =  winding_number \<gamma> z - winding_number \<gamma> 0"
    unfolding C_def by (subst (1 2) winding_number_valid_path) (use assms in \<open>auto simp: algebra_simps\<close>)
  finally show ?thesis .
qed

lemma winding_number_inverse:
  assumes "path \<gamma>" "path_image \<gamma> \<subseteq> {z. Im z > 0}" "z \<notin> path_image \<gamma>" "Im z > 0"
  shows   "winding_number (inverse \<circ> \<gamma>) (inverse z) = winding_number \<gamma> z - winding_number \<gamma> 0"
proof -
  have compact: "compact (Im ` ({z} \<union> (path_image \<gamma>)))"
    by (intro compact_continuous_image compact_Un compact_path_image assms continuous_intros) auto
  hence bdd: "bdd_below (Im ` ({z} \<union> path_image \<gamma>))"
    by (meson bounded_imp_bdd_below compact_imp_bounded)
  define c' where "c' = Inf (Im ` ({z} \<union> path_image \<gamma>))"
  have c'_le: "Im u \<ge> c'" if "u \<in> {z} \<union> path_image \<gamma>" for u
    using that bdd unfolding c'_def by (meson cINF_lower)
  have "c' \<in> Im ` ({z} \<union> path_image \<gamma>)"
    unfolding c'_def using compact by (intro closed_contains_Inf compact_imp_closed bdd) auto
  with assms have "c' > 0"
    by auto
  define c where "c = c' / 2"
  have "c > 0" "c < c'"
    using \<open>c' > 0\<close> by (simp_all add: c_def)
  have c: "c > 0" "Im z > c" "\<And>u. u \<in> path_image \<gamma> \<Longrightarrow> Im u > c"
    using \<open>c > 0\<close> \<open>c < c'\<close> c'_le by force+

  show ?thesis
  proof (rule winding_number_comp')
    show "inverse holomorphic_on {z. Im z > c}"
      using c by (intro holomorphic_intros) auto
    show "(1/c^2)-lipschitz_on {z. Im z > c} inverse"
      by (rule lipschitz_on_subset[OF lipschitz_on_complex_inverse[of c]]) (use c in auto)
    show "inj_on inverse {z. Im z > c}"
      using assms by (auto simp: inj_on_def)
    show "open {z. Im z > c}"
      by (simp add: open_halfspace_Im_gt)
    show "path \<gamma>" "path_image \<gamma> \<subseteq> {z. Im z > c}" "z \<in> {z. c < Im z}" "z \<notin> path_image \<gamma>"
      using c assms by auto
    have "\<forall>\<^sub>F p in valid_path_nhds \<gamma>. valid_path p \<and> path_image p \<inter> ({z. Im z \<le> c} \<union> {z}) = {}"
      by (intro eventually_conj eventually_valid_path_valid_path_nhds
                eventually_valid_path_nhds_avoid closed_Un closed_halfspace_Im_le)
         (use assms c in force)+
    moreover have "\<forall>\<^sub>F p in path_nhds \<gamma>. winding_number p 0 = winding_number \<gamma> 0 \<and>
                               winding_number p z = winding_number \<gamma> z"
      by (intro eventually_conj eventually_winding_number_eq_path_nhds) (use assms in auto)
    hence "\<forall>\<^sub>F p in valid_path_nhds \<gamma>. winding_number p 0 = winding_number \<gamma> 0 \<and>
                                      winding_number p z = winding_number \<gamma> z"
      by (meson filter_leD path_nhds_le_valid_path_nhds)
    ultimately have "\<forall>\<^sub>F p in valid_path_nhds \<gamma>.
            contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            complex_of_real (2 * pi) * \<i> * (winding_number \<gamma> z - winding_number \<gamma> 0)"
    proof eventually_elim
      case (elim p)
      have "contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            contour_integral p (\<lambda>w. 1 / (w - z) - 1 / w)"
      proof (rule contour_integral_cong)
        fix x assume "x \<in> path_image p"
        then have "x \<noteq> 0" "x \<noteq> z"
          using elim c by auto
        then show "deriv inverse x / (inverse x - inverse z) = 1 / (x - z) - 1 / x"
          using assms by (auto simp: divide_simps power2_eq_square)
      qed simp
      also have "\<dots> = contour_integral p (\<lambda>w. 1 / (w - z)) - contour_integral p ((/) 1)"
      proof (rule contour_integral_diff)
        show "(\<lambda>w. 1 / (w - z)) contour_integrable_on p"
          by (rule contour_integrable_inversediff) (use elim in auto)
        have "(\<lambda>w. 1 / (w - 0)) contour_integrable_on p"
          by (rule contour_integrable_inversediff) (use elim c in auto)
        thus "(\<lambda>w. 1 / w) contour_integrable_on p"
          by simp
      qed
      also have "\<dots> = (2 * pi * \<i>) * (winding_number p z - winding_number p 0)"
        by (subst (1 2) winding_number_valid_path) (use elim c in \<open>auto simp: algebra_simps\<close>)
      finally show ?case
        using elim by (simp add: algebra_simps)
    qed
    thus "\<exists>\<^sub>F p in valid_path_nhds \<gamma>.
            contour_integral p (\<lambda>w. deriv inverse w / (inverse w - inverse z)) =
            complex_of_real (2 * pi) * \<i> * (winding_number \<gamma> z - winding_number \<gamma> 0)"
      by (rule eventually_frequently [rotated]) (use assms in auto)
  qed
qed

lemma winding_number_inverse_valid_path_0:
  assumes "valid_path \<gamma>" "pathstart \<gamma> = pathfinish \<gamma>" "0 \<notin> path_image \<gamma>"
  shows   "winding_number (inverse \<circ> \<gamma>) 0 = -winding_number \<gamma> 0"
proof -
  have val: "valid_path (inverse \<circ> \<gamma>)" using assms
    by (intro valid_path_compose_holomorphic[of _ _ "-{0}"] assms)
       (auto intro!: holomorphic_intros)

  obtain B where B: "\<And>w. norm w \<ge> B \<Longrightarrow> winding_number \<gamma> w = 0"
    using winding_number_zero_at_infinity[of \<gamma>] val assms
    by (auto simp: valid_path_imp_path)

  have "compact (path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    using assms by (intro compact_Un compact_path_image valid_path_imp_path val) auto
  hence "open (-(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>)))"
    by (intro open_Compl compact_imp_closed)
  moreover have "0 \<in> -(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    using assms by (auto simp: path_image_compose)
  ultimately obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "cball 0 \<epsilon> \<subseteq> -(path_image \<gamma> \<union> path_image (inverse \<circ> \<gamma>))"
    unfolding open_contains_cball by blast
  define w where "w = complex_of_real (min \<epsilon> (1 / max 1 B))"

  have pos: "min \<epsilon> (1 / max 1 B) > 0"
    using \<epsilon> by (auto simp: min_less_iff_disj)
  hence norm_w: "norm w = min \<epsilon> (1 / max 1 B)"
    unfolding w_def norm_of_real by simp
  from pos have "norm w \<noteq> 0"
    unfolding norm_w by linarith
  hence "w \<noteq> 0"
    by auto
  have "w \<in> cball 0 \<epsilon>"
    by (auto simp: norm_w)

  have "B \<le> max 1 B"
    by simp
  also have "max 1 B = 1 / (1 / max 1 B)"
    by (auto simp: field_simps)
  also have "\<dots> \<le> 1 / min \<epsilon> (1 / max 1 B)"
    using \<epsilon> by (intro divide_left_mono) auto
  also have "\<dots> = norm (inverse w)"
    by (simp add: \<open>norm w = _\<close> norm_inverse field_simps norm_divide)
  finally have "B \<le> norm (inverse w)" .

  have "w \<notin> inverse ` path_image \<gamma>"
    using \<open>w \<in> cball 0 \<epsilon>\<close> \<epsilon> unfolding path_image_compose by blast
  hence "inverse w \<notin> path_image \<gamma>"
    using \<open>w \<noteq> 0\<close> by (metis image_iff inverse_inverse_eq)

  have "winding_number (inverse \<circ> \<gamma>) 0 = winding_number (inverse \<circ> \<gamma>) w"
  proof (rule winding_number_eq)
    show "w \<in> cball 0 \<epsilon>" "0 \<in> cball 0 \<epsilon>" "cball 0 \<epsilon> \<inter> path_image (inverse \<circ> \<gamma>) = {}"
         "connected (cball 0 \<epsilon> :: complex set)"
      using \<epsilon> by (auto simp: w_def)
  qed (use assms val in \<open>auto intro: valid_path_imp_path simp: pathfinish_def pathstart_def\<close>)
  also have "winding_number (inverse \<circ> \<gamma>) w = winding_number (inverse \<circ> \<gamma>) (inverse (inverse w))"
    using \<open>w \<noteq> 0\<close> by simp
  also have "\<dots> = winding_number \<gamma> (inverse w) - winding_number \<gamma> 0"
    using assms \<open>w \<in> cball 0 \<epsilon>\<close> \<open>w \<noteq> 0\<close> \<epsilon> \<open>inverse w \<notin> path_image \<gamma>\<close>
    by (subst winding_number_inverse_valid_path) (auto simp: path_image_compose)
  also have "winding_number \<gamma> (inverse w) = 0"
    using \<epsilon> \<open>B \<le> norm (inverse w)\<close> by (intro B)
  finally show ?thesis by (simp add: o_def)
qed

text \<open>
  The following allows us to compute the winding number of a non-closed circular arc with
  respect to its centre.
\<close>
lemma winding_number_part_circlepath_centre:
  assumes "r > 0"
  shows   "winding_number (part_circlepath z r a b) z = (b - a) / (2 * pi)"
proof -
  have "winding_number (part_circlepath 0 r a b) 0 = (b - a) / (2 * pi)"
  proof (induction a b rule: linorder_wlog)
    case (le a b)
    show ?case
    proof (cases "a = b")
      case True
      thus ?thesis
        using assms by (simp add: part_circlepath_empty winding_number_zero_const)
    next
      case False
      let ?p = "part_circlepath 0 r a b"
      have "((\<lambda>t. \<i>) has_integral (b - a) *\<^sub>R \<i>) {a..b}"
        using has_integral_const[of \<i> a b] assms False le by (simp add: scaleR_conv_of_real mult_ac)
      hence "((\<lambda>z. 1 / z) has_contour_integral (b - a) *\<^sub>R \<i>) ?p"
        by (subst has_contour_integral_part_circlepath_iff) (use assms False le in simp_all)
      moreover have "0 \<notin> path_image ?p"
        using assms by (auto simp: path_image_part_circlepath')
      hence "((\<lambda>z. 1 / z) has_contour_integral 2 * \<i> * pi * winding_number ?p 0) ?p"
        using has_contour_integral_winding_number[of ?p 0] assms by (auto simp add: mult_ac)
      ultimately have "(b - a) *\<^sub>R \<i> = 2 * \<i> * pi * winding_number ?p 0"
        using has_contour_integral_unique by blast
      thus ?thesis
        by (simp add: scaleR_conv_of_real)
    qed
  next
    case (sym a b)
    from assms have "0 \<notin> path_image (part_circlepath 0 r a b)"
      by (auto simp: path_image_part_circlepath')
    thus ?case using assms sym
      by (simp add: reversepath_part_circlepath [symmetric, of 0 r b a]
                    winding_number_reversepath field_simps del: reversepath_part_circlepath)
  qed
  hence "winding_number ((+) z \<circ> part_circlepath 0 r a b) (0 + z) = (b - a) / (2 * pi)"
    by (subst winding_number_comp_plus) (use assms in \<open>auto simp: path_image_part_circlepath'\<close>)
  thus ?thesis
    by (subst (asm) part_circlepath_translate) auto
qed

end
