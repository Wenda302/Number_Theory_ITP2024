theory Equivalent_Paths
  imports "HOL-Complex_Analysis.Complex_Analysis" Wiggle_Prerequisites
begin

lemma shiftpath'_frac: "shiftpath' (frac c) p = shiftpath' c p"
  unfolding shiftpath'_def by (simp add: frac_def algebra_simps)

lemma path_image_loop:
  assumes "pathstart p = pathfinish p"
  shows   "path_image p = p ` {0..<1}"
  unfolding path_image_def
proof safe
  fix x :: real assume x: "x \<in> {0..1}"
  have "(if x = 1 then 0 else x) \<in> {0..<1}" "p x = p (if x = 1 then 0 else x)"
    using assms x by (auto simp: pathstart_def pathfinish_def)
  thus "p x \<in> p ` {0..<1}"
    by blast
qed auto

lemma image_frac_atLeastLessThan_real:
  assumes "y \<ge> x + (1 :: real)"
  shows   "frac ` {x..<y} = {0..<1}"
proof safe
  fix t :: real assume t: "t \<in> {0..<1}"
  define u where "u = (if t \<ge> frac x then t + \<lfloor>x\<rfloor> else t + \<lfloor>x\<rfloor> + 1)"
  have "frac u = t"
    using t by (auto simp: u_def)
  moreover {
    have "x \<le> t + real_of_int \<lfloor>x\<rfloor> + 1"
      using assms t unfolding atLeastLessThan_iff by linarith
    moreover have "t + real_of_int \<lfloor>x\<rfloor> < y"
      using assms t unfolding atLeastLessThan_iff by linarith
    ultimately have "u \<in> {x..<y}"
      using assms by (auto simp: u_def frac_def)
  }
  ultimately show "t \<in> frac ` {x..<y}"
    by blast
qed (auto simp: frac_lt_1)

lemma image_frac_atLeastAtMost_real:
  assumes "y \<ge> x + (1 :: real)"
  shows   "frac ` {x..y} = {0..<1}"
proof 
  have "{0..<1} = frac ` {x..<y}"
    by (rule sym, intro image_frac_atLeastLessThan_real assms)
  also have "\<dots> \<subseteq> frac ` {x..y}"
    by (intro image_mono) auto
  finally show "{0..<1} \<subseteq> frac ` {x..y}" .
qed (auto simp: frac_lt_1)
    

lemma simple_pathD:
  assumes "simple_path p" "x \<in> {0..1}" "y \<in> {0..1}" "x \<noteq> y" "p x = p y"
  shows   "{x, y} = {0, 1}"
  using assms unfolding simple_path_def loop_free_def by blast

lemma strict_mono_on_atLeastAtMost_combine:
  fixes f :: "'a :: linorder \<Rightarrow> 'b :: linorder"
  assumes "strict_mono_on {a..b} f" "strict_mono_on {b..c} f"
  shows   "strict_mono_on {a..c} f"
proof (rule strict_mono_onI)
  fix r s
  assume rs: "r \<in> {a..c}" "s \<in> {a..c}" "r < s"
  consider "r \<in> {a..b}" "s \<in> {a..b}" | "r \<in> {a..b}" "s \<in> {b<..c}" | "r \<in> {b..c}" "s \<in> {b..c}"
    using rs by force
  thus "f r < f s"
  proof cases
    assume rs: "r \<in> {a..b}" "s \<in> {b<..c}"
    have "f r \<le> f b"
      using rs by (intro strict_mono_on_leD[OF assms(1)]) auto
    also have "f b < f s"
      using rs by (intro strict_mono_onD[OF assms(2)]) auto
    finally show "f r < f s" .
  qed (use assms \<open>r < s\<close> in \<open>auto simp: strict_mono_on_def\<close>)
qed

lemma strict_mono_on_compose:
  assumes "strict_mono_on B g" "strict_mono_on A f" "f ` A \<subseteq> B"
  shows   "strict_mono_on A (g \<circ> f)"
  unfolding strict_mono_on_def using assms(3)
  by (auto simp: strict_mono_on_def intro!: assms(1,2)[THEN strict_mono_onD])
  

lemma strict_mono_on_imp_less_iff:
  fixes f :: "'a :: linorder \<Rightarrow> 'b :: linorder"
  shows "strict_mono_on A f \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x < f y \<longleftrightarrow> x < y"
  by (metis not_less_iff_gr_or_eq ord.strict_mono_onD)

lemma strict_mono_on_imp_strict_mono_on_inv:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  assumes "\<And>x. x \<in> {a..b} \<Longrightarrow> g (f x) = x"
  shows   "strict_mono_on (f ` {a..b}) g"
proof (rule strict_mono_onI, safe)
  fix r s assume rs: "r \<in> {a..b}" "s \<in> {a..b}" "f r < f s"
  thus "g (f r) < g (f s)"
    using strict_mono_on_imp_less_iff[OF assms(1)] rs  by (auto simp: assms(2))
qed

lemma strict_mono_on_imp_strict_mono_on_inv_into:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  shows   "strict_mono_on (f ` {a..b}) (inv_into {a..b} f)"
  using strict_mono_on_imp_strict_mono_on_inv[OF
          assms inv_into_f_f[OF strict_mono_on_imp_inj_on[OF assms]]]
  by blast

text \<open>
  Nice lemma taken from
    Austin, A. K. (1985). 69.8 Two Curiosities. The Mathematical Gazette,
    69(447), 42–44. \<^url>\<open>https://doi.org/10.2307/3616452\<close>.

  A strictly monotonic function \<open>f\<close> on some closed real interval has a
  continuous (and strictly monotonic) inverse function \<open>g\<close> -- even if \<open>f\<close> itself
  is not continuous.
\<close>
lemma strict_mono_on_imp_continuous_on_inv:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  assumes "\<And>x. x \<in> {a..b} \<Longrightarrow> g (f x) = x"
  shows   "continuous_on (f ` {a..b}) g"
proof (cases "a < b")
  case False
  thus ?thesis
    by (cases "a = b") auto
next
  case ab: True
  show ?thesis
  proof (rule continuous_onI, safe)
    fix x \<epsilon> :: real
    assume \<epsilon>: "\<epsilon> > 0" and x: "x \<in> {a..b}"
  
    consider "x = a" | "x = b" | "x \<in> {a<..<b}"
      using x by force
    thus "\<exists>d>0. \<forall>x'\<in>f ` {a..b}. dist x' (f x) < d \<longrightarrow> dist (g x') (g (f x)) \<le> \<epsilon>"
    proof cases
      assume [simp]: "x = a"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> ((b - a) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < b - a"
        using \<epsilon> \<open>a < b\<close> by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = f (a + \<epsilon>') - f a"
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using \<open>a < b\<close> \<epsilon>' by (auto simp: \<delta>_def intro!: strict_mono_onD[OF assms(1)])
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "f t \<ge> f a"
          using \<open>a < b\<close> t by (intro strict_mono_on_leD[OF assms(1)]) auto
        with t have "f t - f a < \<delta>"
          by (simp add: dist_norm)
        hence "f t < f (a + \<epsilon>')"
          unfolding \<delta>_def by linarith
        hence "t < a + \<epsilon>'"
          using t \<epsilon>' by (subst (asm) strict_mono_on_imp_less_iff[OF assms(1)]) auto
        thus "dist (g (f t)) (g (f x)) \<le> \<epsilon>"
          using \<open>a < b\<close> t \<open>f t \<ge> f a\<close> \<epsilon>' by (simp add: assms dist_norm)
      qed

    next

      assume [simp]: "x = b"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> ((b - a) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < b - a"
        using \<epsilon> \<open>a < b\<close> by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = f b - f (b - \<epsilon>')"
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using \<open>a < b\<close> \<epsilon>' by (auto simp: \<delta>_def intro!: strict_mono_onD[OF assms(1)])
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "f t \<le> f b"
          using \<open>a < b\<close> t by (intro strict_mono_on_leD[OF assms(1)]) auto
        with t have "f b - f t < \<delta>"
          by (simp add: dist_norm)
        hence "f t > f (b - \<epsilon>')"
          unfolding \<delta>_def by linarith
        hence "t > b - \<epsilon>'"
          using t \<epsilon>' by (subst (asm) strict_mono_on_imp_less_iff[OF assms(1)]) auto
        thus "dist (g (f t)) (g (f x)) \<le> \<epsilon>"
          using \<open>a < b\<close> t \<open>f t \<le> f b\<close> \<epsilon>' by (simp add: assms dist_norm)
      qed

    next

      assume x: "x \<in> {a<..<b}"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> (min (x - a) (b - x) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < x - a" "\<epsilon>' < b - x"
        using \<epsilon> x by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = min (f x - f (x - \<epsilon>')) (f (x + \<epsilon>') - f x)"
      have *: "f (x - \<epsilon>') < f x" "f x < f (x + \<epsilon>')" 
        using \<epsilon>' by (intro strict_mono_onD[OF assms(1)]; simp)+
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using * \<epsilon>' by (auto simp add: \<delta>_def)
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "dist (g (f t)) (g (f x)) \<le> \<epsilon>'"
        proof (cases "t \<ge> x")
          case True
          hence "f t \<ge> f x"
            by (intro strict_mono_on_leD[OF assms(1)]) (use x t in auto)
          with t have "f t - f x < \<delta>"
            by (simp add: dist_norm)
          hence "f t < f (x + \<epsilon>')"
            unfolding \<delta>_def by linarith
          hence "t < x + \<epsilon>'"
            by (subst (asm) strict_mono_on_imp_less_iff[OF assms(1)]) (use x t \<epsilon>' in auto)
          thus ?thesis
            using x t True by (simp add: assms dist_norm)
        next
          case False
          hence "f t \<le> f x"
            by (intro strict_mono_on_leD[OF assms(1)]) (use x t in auto)
          with t have "f x - f t < \<delta>"
            by (simp add: dist_norm)
          hence "f t > f (x - \<epsilon>')"
            unfolding \<delta>_def by linarith
          hence "t > x - \<epsilon>'"
            by (subst (asm) strict_mono_on_imp_less_iff[OF assms(1)]) (use x t \<epsilon>' in auto)
          thus ?thesis
            using x t False by (simp add: assms dist_norm)
        qed
        also have "\<dots> \<le> \<epsilon>"
          by fact
        finally show "dist (g (f t)) (g (f x)) \<le> \<epsilon>" .
      qed
    qed
  qed
qed

lemma strict_mono_on_imp_continuous_on_inv_into:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  shows   "continuous_on (f ` {a..b}) (inv_into {a..b} f)"
proof (rule strict_mono_on_imp_continuous_on_inv)
  show "inv_into {a..b} f (f x) = x" if "x \<in> {a..b}" for x
    using inv_into_f_f[OF strict_mono_on_imp_inj_on[OF assms] that] .
qed fact+


locale eq_paths_locale =
  fixes p q :: "real \<Rightarrow> 'a :: topological_space" and f :: "real \<Rightarrow> real"
  assumes paths [simp, intro]: "path p" "path q"
  assumes cont [continuous_intros]: "continuous_on {0..1} f"
  assumes mono: "strict_mono_on {0..1} f"
  assumes ends [simp]: "f 0 = 0" "f 1 = 1"
  assumes equiv: "\<And>t. t \<in> {0..1} \<Longrightarrow> q t = p (f t)"
begin

lemmas cont' [continuous_intros] = continuous_on_compose2 [OF cont]

lemma inj: "inj_on f {0..1}"
  using strict_mono_on_imp_inj_on mono by blast

lemma inj': "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  using inj by (meson inj_on_contraD)

lemma less_iff: "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x < f y \<longleftrightarrow> x < y"
  using mono by (meson less_le_not_le linorder_linear strict_mono_onD strict_mono_on_leD)

lemma le_iff: "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x \<le> f y \<longleftrightarrow> x \<le> y"
  using mono less_iff linorder_not_le by blast

lemma eq_0_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x = 0 \<longleftrightarrow> x = 0"
  and eq_1_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x = 1 \<longleftrightarrow> x = 1"
  using inj'[of x 0] inj'[of x 1] by simp_all

lemma f_ge_0 [simp, intro]: "x \<in> {0..1} \<Longrightarrow> f x \<ge> 0"
  and f_le_1 [simp, intro]: "x \<in> {0..1} \<Longrightarrow> f x \<le> 1"
  using le_iff[of 0 x] le_iff[of x 1] ends by simp_all

lemma f_gt_0 [simp, intro]: "x \<in> {0<..1} \<Longrightarrow> f x > 0"
  and f_less_1 [simp, intro]: "x \<in> {0..<1} \<Longrightarrow> f x < 1"
  using less_iff[of 0 x] less_iff[of x 1] ends by simp_all

lemma le_0_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x \<le> 0 \<longleftrightarrow> x = 0"
  and ge_1_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x \<ge> 1 \<longleftrightarrow> x = 1"
  using le_iff[of x 0] le_iff[of 1 x] le_iff[of 0 x] le_iff[of x 1] ends by force+

lemma bij_betw: "bij_betw f {0..1} {0..1}"
proof -
  have "x \<in> f ` {0..1}" if "x \<in> {0..1}" for x
    using IVT'[of f 0 x 1] that cont by auto
  thus ?thesis
    using inj unfolding bij_betw_def by force
qed  

lemma same_ends: "pathstart p = pathstart q" "pathfinish p = pathfinish q"
  by (simp_all add: pathstart_def pathfinish_def equiv)

lemma path_image_eq: "path_image p = path_image q"
proof -
  have "path_image q = q ` {0..1}"
    by (simp add: path_image_def)
  also have "\<dots> = (p \<circ> f) ` {0..1}"
    by (intro image_cong) (auto simp: equiv)
  also have "\<dots> = p ` (f ` {0..1})"
    by (simp add: image_image)
  also have "f ` {0..1} = {0..1}"
    using bij_betw by (meson bij_betw_def)
  also have "p ` \<dots> = path_image p"
    by (simp add: path_image_def)
  finally show ?thesis ..
qed

lemma inverse: "eq_paths_locale q p (inv_into {0..1} f)"
proof
  let ?g = "inv_into {0..1} f"
  show "continuous_on {0..1} (?g)"
    using strict_mono_on_imp_continuous_on_inv_into[OF mono] bij_betw
    by (simp add: bij_betw_def)
  show *: "strict_mono_on {0..1} ?g"
    using strict_mono_on_imp_strict_mono_on_inv_into[OF mono] bij_betw
    by (simp add: bij_betw_def)
  show [simp]: "?g 0 = 0"
    using inv_into_f_f[OF inj, of 0] by simp
  show [simp]: "?g 1 = 1"
    using inv_into_f_f[OF inj, of 1] by simp
  show "p t = q (?g t)" if t: "t \<in> {0..1}" for t
  proof -
    have "?g 0 \<le> ?g t" "?g t \<le> ?g 1"
      by (rule strict_mono_on_leD[OF *]; use t in simp)+
    hence "q (?g t) = p (f (?g t))"
      by (simp add: equiv)
    also have "f (?g t) = t"
      by (rule bij_betw_inv_into_right[OF bij_betw]) (use t in auto)
    finally show ?thesis ..
  qed
qed auto

lemma reverse: "eq_paths_locale (reversepath p) (reversepath q) (\<lambda>x. 1 - f (1 - x))"
proof
  show "reversepath q t = reversepath p (1 - f (1 - t))" if "t \<in> {0..1}" for t
    using that by (auto simp: reversepath_def equiv)
qed (auto intro!: continuous_intros strict_mono_onI simp: less_iff)

lemma homotopic:
  assumes "path_image p \<subseteq> A"
  shows   "homotopic_paths A p q"
  by (rule homotopic_paths_reparametrize[where f = f])
     (use assms in \<open>auto intro!: continuous_intros simp: equiv\<close>)

lemma arc_iff: "arc p \<longleftrightarrow> arc q"
proof -
  have "arc q \<longleftrightarrow> inj_on q {0..1}"
    unfolding arc_def by simp
  also have "\<dots> \<longleftrightarrow> inj_on (p \<circ> f) {0..1}"
    by (intro inj_on_cong) (auto simp: equiv)
  also have "\<dots> \<longleftrightarrow> inj_on p (f ` {0..1})"
    by (rule comp_inj_on_iff [OF inj, symmetric])
  also have "\<dots> \<longleftrightarrow> arc p"
    using bij_betw by (simp add: bij_betw_def arc_def)
  finally show ?thesis ..
qed

lemma simple_path:
  assumes "simple_path p"
  shows   "simple_path q"
proof (rule simple_pathI)
  show "x = 0 \<and> y = 1" if "0 \<le> x" "x < y" "y \<le> 1" "q x = q y" for x y
  proof -
    have "p (f x) = p (f y)"
      using that by (simp add: equiv)
    moreover from that have "f x < f y"
      by (subst less_iff) auto
    ultimately have "{f x, f y} = {0,1}"
      using simple_pathD[OF assms, of "f x" "f y"] that by simp
    thus ?thesis using that
      by (auto simp: doubleton_eq_iff)
  qed
qed auto

lemma simple_path_iff: "simple_path p \<longleftrightarrow> simple_path q"
proof -
  interpret inv: eq_paths_locale q p "inv_into {0..1} f"
    by (rule inverse)
  show ?thesis
    using simple_path inv.simple_path by blast
qed

end


locale eq_paths_locale_compose =
  pq: eq_paths_locale p q f + qr : eq_paths_locale q r g for p q r f g
begin

sublocale eq_paths_locale p r "f \<circ> g"
proof
  show "strict_mono_on {0..1} (f \<circ> g)"
    using pq.mono qr.mono
    by (rule strict_mono_on_compose) (use qr.bij_betw in \<open>simp add: bij_betw_def\<close>)
qed (auto intro!: continuous_intros simp: pq.equiv qr.equiv)

end



locale eq_paths_locale_join =
  p1: eq_paths_locale p1 q1 f1 + p2 : eq_paths_locale p2 q2 f2 for p1 q1 f1 p2 q2 f2 +
  assumes compatible_ends: "pathfinish p1 = pathstart p2"
begin

definition f12 :: "real \<Rightarrow> real" where
  "f12 t = (if t \<le> 1 / 2 then f1 (2 * t) / 2 else (f2 (2 * t - 1) + 1) / 2)"

lemma compatible_ends': "pathfinish q1 = pathstart q2"
  using p1.same_ends p2.same_ends compatible_ends by metis

sublocale p12: eq_paths_locale "p1 +++ p2" "q1 +++ q2" f12
proof
  show "strict_mono_on {0..1} f12"
  proof (rule strict_mono_onI)
    fix r s :: real assume rs: "r \<in> {0..1}" "s \<in> {0..1}" "r < s"
    consider "s \<le> 1 / 2" | "r \<le> 1 / 2" "s > 1 / 2" | "r > 1 / 2"
      using \<open>r < s\<close> by linarith
    thus "f12 r < f12 s"
    proof cases
      assume rs': "r \<le> 1 / 2" "s > 1 / 2"
      have "f12 r = f1 (2 * r) / 2"
        using rs rs' by (simp add: f12_def)
      also have "\<dots> \<le> 1 / 2"
        using rs rs' by simp
      also have "\<dots> < (f2 (2 * s - 1) + 1) / 2"
        using rs rs' by simp
      also have "\<dots> = f12 s"
        using rs rs' by (simp add: f12_def)
      finally show ?thesis .
    qed (use p1.mono p2.mono rs in \<open>auto simp: strict_mono_on_def f12_def\<close>)
  qed
next
  show "continuous_on {0..1} f12"
    unfolding f12_def by (intro continuous_on_real_If_combine continuous_intros) auto
next
  show "(q1 +++ q2) t = (p1 +++ p2) (f12 t)" if t: "t \<in> {0..1}" for t
  proof (cases t "1 / 2 :: real" rule: linorder_cases)
    case less
    have "(p1 +++ p2) (f12 t) = q1 (2 * t)"
      using less t by (simp add: joinpaths_def f12_def p1.equiv)
    also have "\<dots> = (q1 +++ q2) t"
      using less t by (simp add: joinpaths_def)
    finally show ?thesis ..
  next
    case greater
    hence "f2 (2 * t - 1) > 0"
      using t by simp
    hence "(p1 +++ p2) (f12 t) = p2 ((2 * f2 (2 * t - 1) + 2) / 2 - 1)"
      using greater by (simp add: joinpaths_def f12_def)
    also have "(2 * f2 (2 * t - 1) + 2) / 2 - 1 = f2 (2 * t - 1)"
      by (simp add: field_simps)
    also have "p2 (f2 (2 * t - 1)) = q2 (2 * t - 1)"
      using t greater by (simp add: p2.equiv)
    also have "\<dots> = (q1 +++ q2) t"
      using greater by (simp add: joinpaths_def)
    finally show ?thesis ..
  qed (auto simp: joinpaths_def f12_def p1.equiv p2.equiv)
qed (auto simp: compatible_ends compatible_ends' f12_def)

end



locale eq_paths_locale_join_assoc =
  fixes p1 p2 p3 :: "real \<Rightarrow> 'a :: topological_space"
  assumes paths [simp, intro]: "path p1" "path p2" "path p3"
  assumes compatible_ends: "pathfinish p1 = pathstart p2" "pathfinish p2 = pathstart p3"
begin

definition f :: "real \<Rightarrow> real" where
  "f t = (if t \<le> 1 / 2 then t / 2
          else if t \<le> 3 / 4 then t - 1 / 4
          else 2 * t - 1)"

sublocale eq_paths_locale "(p1 +++ p2) +++ p3" "p1 +++ (p2 +++ p3)" f
proof
  show "(p1 +++ (p2 +++ p3)) t = ((p1 +++ p2) +++ p3) (f t)" if t: "t \<in> {0..1}" for t
    by (auto simp: joinpaths_def pathfinish_def pathstart_def f_def)
  show "strict_mono_on {0..1} f"
    by (intro strict_mono_onI) (auto simp: f_def)
  show "continuous_on {0..1} f"
    unfolding f_def by (intro continuous_on_real_If_combine continuous_intros) auto
qed (auto simp: f_def compatible_ends)

end


locale linepaths_join =
  fixes a b c :: "'a :: euclidean_space"
  assumes between: "b \<in> closed_segment a c"
begin

definition f :: "real \<Rightarrow> real" where
  "f t = (let u = (if a = c then 1 / 2 else dist a b / dist a c)
          in if t \<le> 1 / 2 then 2 * u * t else -1 + 2 * t + 2 * u - 2 * t * u)"

lemma eq_paths_locale:
  assumes not_degenerate: "a = c \<or> (a \<noteq> b \<and> b \<noteq> c)"
  shows   "eq_paths_locale (linepath a c) (linepath a b +++ linepath b c) f"
proof
  from between obtain u where u: "u \<in> {0..1}" "b = (1 - u) *\<^sub>R a + u *\<^sub>R c"
    unfolding closed_segment_def by force

  have *: "dist a b / dist a c = u" if "a \<noteq> c"
  proof -
    have "a - b = u *\<^sub>R (a - c)"
      by (simp add: dist_norm scaleR_conv_of_real u algebra_simps)
    also have "norm \<dots> = u * norm (a - c)"
      using u by simp
    finally show ?thesis using that
      by (simp add: field_simps dist_norm norm_minus_commute)
  qed

  show "(linepath a b +++ linepath b c) t = linepath a c (f t)" if "t \<in> {0..1}" for t
  proof (cases "a = c")
    case False
    have **: "(u * 2) *\<^sub>R x = u *\<^sub>R x + u *\<^sub>R x" for x :: 'a
      by (simp add: pth_8)
    show ?thesis
      unfolding f_def Let_def *[OF False]
      by (auto simp: u linepath_def joinpaths_def algebra_simps **)
  next
    case [simp]: True
    hence [simp]: "b = c"
      by (simp add: u)
    show ?thesis
      by (simp add: linepath_def joinpaths_def)
  qed
next
  define u where "u = (if a = c then 1/2 else dist a b / dist a c)"
  have "dist a b < dist a c" if "a \<noteq> b" "b \<noteq> c" "a \<noteq> c"
  proof -
    have "dist a c = dist a b + dist b c"
      using between between_mem_segment[of a c b] Line_Segment.between[of a c b]
      by simp
    with that show ?thesis
      by simp
  qed 
  hence u: "u > 0" "u < 1"
    using not_degenerate by (auto simp: u_def field_simps)
  show "continuous_on {0..1} f"
    unfolding f_def u_def [symmetric] Let_def
    by (intro continuous_on_real_If_combine continuous_intros) auto
  show "strict_mono_on {0..1} f"
    
  proof (rule strict_mono_on_atLeastAtMost_combine[where b = "1/2"])
    show "strict_mono_on {0..1 / 2} f"
    proof (rule strict_mono_onI)
      show "f r < f s" if "r \<in> {0..1/2}" "s \<in> {0..1/2}" "r < s" for r s
        using that unfolding f_def u_def [symmetric] Let_def using u by auto
    qed
    show "strict_mono_on {1 / 2..1} f"
    proof (rule strict_mono_onI)
      show "f r < f s" if "r \<in> {1/2..1}" "s \<in> {1/2..1}" "r < s" for r s
      proof (cases "r = 1/2")
        case True
        have "0 < (2 * s - 1) * (1 - u)"
          using that u by (intro mult_pos_pos) auto
        also have "(2 * s - 1) * (1 - u) = f s - f (1 / 2)"
          unfolding f_def u_def [symmetric] Let_def using that
          by (auto simp: algebra_simps)
        finally show ?thesis by (simp add: True)
      next
        case False
        have "0 < 2 * (s - r) * (1 - u)"
          by (intro mult_pos_pos) (use that u in auto)
        also have "2 * (s - r) * (1 - u) = f s - f r"
          unfolding f_def u_def [symmetric] Let_def using that False
          by (simp add: algebra_simps)
        finally show ?thesis by simp
      qed
    qed
  qed
qed (auto simp: f_def)

end


locale part_circlepaths_join =
  fixes x :: complex and r a b c :: real
  assumes between: "b \<in> closed_segment a c"
begin

sublocale angle: linepaths_join a b c 
  by unfold_locales (fact between)

lemma eq_paths_locale:
  assumes not_degenerate: "a = c \<or> (a \<noteq> b \<and> b \<noteq> c)"
  shows "eq_paths_locale (part_circlepath x r a c)
           (part_circlepath x r a b +++ part_circlepath x r b c) angle.f"
proof -
  interpret angle: eq_paths_locale "linepath a c" "linepath a b +++ linepath b c" angle.f
    by (rule angle.eq_paths_locale) fact
  show ?thesis
  proof
    show "(part_circlepath x r a b +++ part_circlepath x r b c) t =
             part_circlepath x r a c (angle.f t)" if "t \<in> {0..1}" for t
    proof -
      have "(part_circlepath x r a b +++ part_circlepath x r b c) t =
              x + rcis r ((linepath a b +++ linepath b c) t)"
        by (simp add: part_circlepath_altdef joinpaths_def)
      also have "(linepath a b +++ linepath b c) t = linepath a c (angle.f t)"
        using that by (simp add: angle.equiv)
      also have "x + rcis r \<dots> = part_circlepath x r a c (angle.f t)"
        by (simp add: part_circlepath_altdef)
      finally show ?thesis .
    qed
  qed (auto intro: angle.mono continuous_intros)
qed

end


lemma eq_paths_locale_refl [intro!]: "path p \<Longrightarrow> eq_paths_locale p p (\<lambda>x. x)"
  by unfold_locales (auto intro!: strict_mono_onI)

lemma eq_paths_locale_refl': 
  assumes "path p \<or> path q" "\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x"
  shows   "eq_paths_locale p q (\<lambda>x. x)"
proof
  have "path p \<longleftrightarrow> path q"
    unfolding path_def by (intro continuous_on_cong) (use assms(2) in auto)
  with assms show "path p" "path q"
    by auto
qed (use assms(2) in \<open>auto intro!: strict_mono_onI\<close>)


definition eq_paths :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "eq_paths p q \<longleftrightarrow> (\<exists>f. eq_paths_locale p q f)"

named_theorems eq_paths_intros

lemma eq_paths_imp_path [dest]:
  assumes "eq_paths p q"
  shows   "path p" "path q"
  using assms unfolding eq_paths_def eq_paths_locale_def by blast+

lemma eq_paths_refl [simp, intro!, eq_paths_intros]: "path p \<Longrightarrow> eq_paths p p"
  unfolding eq_paths_def by blast

lemma eq_paths_refl'': "path p \<Longrightarrow> p = q \<Longrightarrow> eq_paths p q"
  unfolding eq_paths_def by blast

lemma eq_paths_refl':
  "path p \<or> path q \<Longrightarrow> (\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x) \<Longrightarrow> eq_paths p q"
  unfolding eq_paths_def using eq_paths_locale_refl'[of p q] by blast

lemma eq_paths_sym:
  "eq_paths p q \<Longrightarrow> eq_paths q p"
  unfolding eq_paths_def using eq_paths_locale.inverse by auto

lemma eq_paths_sym_iff:
  "eq_paths p q \<longleftrightarrow> eq_paths q p"
  using eq_paths_sym by metis

lemma eq_paths_reverse [intro, eq_paths_intros]:
  "eq_paths p q \<Longrightarrow> eq_paths (reversepath p) (reversepath q)"
  unfolding eq_paths_def using eq_paths_locale.reverse by auto

lemma eq_paths_reverse_iff:
  "eq_paths (reversepath p) (reversepath q) \<longleftrightarrow> eq_paths p q"
  using eq_paths_reverse reversepath_reversepath by metis

lemma eq_paths_trans [trans]:
  assumes "eq_paths p q" "eq_paths q r"
  shows   "eq_paths p r"
proof -
  from assms(1) obtain f where "eq_paths_locale p q f"
    by (auto simp: eq_paths_def)
  then interpret pq: eq_paths_locale p q f .
  from assms(2) obtain g where "eq_paths_locale q r g"
    by (auto simp: eq_paths_def)
  then interpret qr: eq_paths_locale q r g .
  interpret eq_paths_locale_compose p q r f g ..
  show ?thesis
    unfolding eq_paths_def using eq_paths_locale_axioms by blast
qed

lemma eq_paths_eq_trans [trans]:
  "p = q \<Longrightarrow> eq_paths q r \<Longrightarrow> eq_paths p r"
  "eq_paths p q \<Longrightarrow> q = r \<Longrightarrow> eq_paths p r"
  by simp_all

lemma eq_paths_shiftpath_0 [intro, eq_paths_intros]: "path p \<Longrightarrow> eq_paths (shiftpath 0 p) p"
  by (rule eq_paths_refl') (auto simp: shiftpath_def)

lemma path_shiftpath_0_iff [simp]: "path (shiftpath 0 p) \<longleftrightarrow> path p"
  unfolding path_def by (intro continuous_on_cong) (auto simp: shiftpath_def)

lemma path_shiftpath'_int_iff [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> \<int>"
  shows   "path (shiftpath' c p) \<longleftrightarrow> path p"
  unfolding path_def 
proof (intro continuous_on_cong)
  show "shiftpath' c p x = p x" if "x \<in> {0..1}" for x
    using assms that
    by (cases "x = 1") (auto simp: shiftpath'_def pathstart_def pathfinish_def)
qed auto  

lemma eq_paths_shiftpath_0_iff [simp]: "eq_paths (shiftpath 0 p) q \<longleftrightarrow> eq_paths p q"
proof safe
  assume *: "eq_paths (shiftpath 0 p) q"
  hence "path p"
    by auto
  thus "eq_paths p q" using *
    by (meson eq_paths_shiftpath_0 eq_paths_sym_iff eq_paths_trans)
next
  assume "eq_paths p q"
  thus "eq_paths (shiftpath 0 p) q"
    by (meson eq_paths_imp_path(1) eq_paths_shiftpath_0 eq_paths_trans)
qed

lemma eq_paths_shiftpath_0_iff' [simp]: "eq_paths q (shiftpath 0 p) \<longleftrightarrow> eq_paths q p"
  using eq_paths_shiftpath_0_iff[of p q] by (simp add: eq_paths_sym_iff)

lemma eq_paths_shiftpath'_int [eq_paths_intros]:
  assumes "path p" "c \<in> \<int>" "pathstart p = pathfinish p"
  shows   "eq_paths (shiftpath' c p) p"
proof (rule eq_paths_refl')
  show "shiftpath' c p x = p x" if "x \<in> {0..1}" for x
    using that assms
    by (cases "x = 1")
       (auto simp: shiftpath'_def pathstart_def pathfinish_def elim!: Ints_cases)
qed (use assms in auto)

lemma eq_paths_shiftpath'_int_iff [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> \<int>"
  shows   "eq_paths (shiftpath' c p) q \<longleftrightarrow> eq_paths p q"
proof safe
  assume *: "eq_paths (shiftpath' c p) q"
  hence "path p"
    using assms by auto
  thus "eq_paths p q" using * assms
    by (meson eq_paths_shiftpath'_int eq_paths_sym_iff eq_paths_trans)
next
  assume "eq_paths p q"
  thus "eq_paths (shiftpath' c p) q"
    by (meson assms eq_paths_imp_path(1) eq_paths_shiftpath'_int eq_paths_trans)
qed

lemma eq_paths_shiftpath'_int_iff' [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> \<int>"
  shows "eq_paths q (shiftpath' c p) \<longleftrightarrow> eq_paths q p"
  using eq_paths_shiftpath'_int_iff[of p c q] assms by (simp add: eq_paths_sym_iff)

lemma eq_paths_join [eq_paths_intros]:
  assumes "eq_paths p1 q1" "eq_paths p2 q2"
  assumes *: "{pathfinish p1, pathfinish q1} \<inter> {pathstart p2, pathstart q2} \<noteq> {}"
  shows  "eq_paths (p1 +++ p2) (q1 +++ q2)"
proof -
  from assms(1) obtain f where "eq_paths_locale p1 q1 f"
    by (auto simp: eq_paths_def)
  then interpret p1: eq_paths_locale p1 q1 f .
  from assms(2) obtain g where "eq_paths_locale p2 q2 g"
    by (auto simp: eq_paths_def)
  then interpret p2: eq_paths_locale p2 q2 g .
  interpret eq_paths_locale_join p1 q1 f p2 q2 g
    by unfold_locales (use * in \<open>auto simp: p1.same_ends p2.same_ends\<close>)
  show ?thesis
    unfolding eq_paths_def using p12.eq_paths_locale_axioms by blast
qed

lemma eq_paths_join_assoc1 [eq_paths_intros]:
  assumes "path p1" "path p2" "path p3"
  assumes "pathfinish p1 = pathstart p2" "pathfinish p2 = pathstart p3"
  shows   "eq_paths ((p1 +++ p2) +++ p3) (p1 +++ (p2 +++ p3))"
proof -
  interpret eq_paths_locale_join_assoc p1 p2 p3
    by standard (use assms in auto)
  show ?thesis
    unfolding eq_paths_def using eq_paths_locale_axioms by blast
qed

lemma eq_paths_join_assoc2 [eq_paths_intros]:
  assumes "path p1" "path p2" "path p3"
  assumes "pathfinish p1 = pathstart p2" "pathfinish p2 = pathstart p3"
  shows   "eq_paths (p1 +++ (p2 +++ p3)) ((p1 +++ p2) +++ p3)"
  using eq_paths_join_assoc1[OF assms] by (simp add: eq_paths_sym_iff)

lemma eq_paths_imp_same_ends:
  "eq_paths p q \<Longrightarrow> pathstart p = pathstart q"
  "eq_paths p q \<Longrightarrow> pathfinish p = pathfinish q"
  unfolding eq_paths_def using eq_paths_locale.same_ends by blast+

lemma eq_paths_imp_path_image_eq:
  "eq_paths p q \<Longrightarrow> path_image p = path_image q"
  unfolding eq_paths_def using eq_paths_locale.path_image_eq by blast

lemma eq_paths_imp_homotopic:
  assumes "eq_paths p q" "path_image p \<inter> path_image q \<subseteq> A"
  shows   "homotopic_paths A p q"
proof -
  from assms obtain f where "eq_paths_locale p q f"
    by (auto simp: eq_paths_def)
  then interpret eq_paths_locale p q f .
  show ?thesis
    using homotopic[of A] path_image_eq assms(2) by blast
qed

lemma eq_paths_homotopic_paths_trans [trans]:
  "eq_paths p q \<Longrightarrow> homotopic_paths A q r \<Longrightarrow> homotopic_paths A p r"
  "homotopic_paths A p q \<Longrightarrow> eq_paths q r \<Longrightarrow> homotopic_paths A p r"
  using eq_paths_imp_homotopic
   apply (metis homotopic_paths_imp_subset homotopic_paths_trans le_infI2)
  using eq_paths_imp_homotopic
  apply (metis eq_paths_imp_path_image_eq homotopic_paths_imp_subset homotopic_paths_trans inf_idem)
  done

lemma eq_paths_imp_winding_number_eq:
  assumes "eq_paths p q" "x \<notin> path_image p \<inter> path_image q"
  shows   "winding_number p x = winding_number q x"
  using assms by (intro winding_number_homotopic_paths eq_paths_imp_homotopic) auto

lemma eq_paths_imp_contour_integral_eq:
  assumes "eq_paths p q" "valid_path p" "valid_path q"
  assumes "open A" "path_image p \<inter> path_image q \<subseteq> A" "f holomorphic_on A"
  shows   "contour_integral p f = contour_integral q f"
proof (rule Cauchy_theorem_homotopic_paths)
  show "homotopic_paths A p q"
    by (intro eq_paths_imp_homotopic assms)
qed (use assms in auto)

lemma eq_paths_imp_arc_iff:
  "eq_paths p q \<Longrightarrow> arc p \<longleftrightarrow> arc q"
  unfolding eq_paths_def using eq_paths_locale.arc_iff by blast

lemma eq_paths_arc_trans [trans]:
  "eq_paths p q \<Longrightarrow> arc q \<Longrightarrow> arc p"
  "arc p \<Longrightarrow> eq_paths p q \<Longrightarrow> arc q"
  using eq_paths_imp_arc_iff by metis+

lemma eq_paths_imp_simple_path_iff:
  "eq_paths p q \<Longrightarrow> simple_path p \<longleftrightarrow> simple_path q"
  unfolding eq_paths_def using eq_paths_locale.simple_path_iff by blast

lemma eq_paths_simple_path_trans [trans]:
  "eq_paths p q \<Longrightarrow> simple_path q \<Longrightarrow> simple_path p"
  "simple_path p \<Longrightarrow> eq_paths p q \<Longrightarrow> simple_path q"
  using eq_paths_imp_simple_path_iff by metis+

lemma eq_paths_linepaths:
  fixes a b c :: "'a :: euclidean_space"
  assumes "b \<in> closed_segment a c" "a = c \<or> (a \<noteq> b \<and> b \<noteq> c)" "b = b'"
  shows   "eq_paths (linepath a b +++ linepath b' c) (linepath a c)"
            (is "eq_paths ?g ?h")
proof -
  interpret linepaths_join a b c
    by unfold_locales fact
  interpret eq_paths_locale ?h ?g f
    unfolding \<open>b = b'\<close>[symmetric]
    by (rule eq_paths_locale) fact
  have "eq_paths ?h ?g"
    unfolding eq_paths_def using eq_paths_locale_axioms by blast
  thus ?thesis
    by (rule eq_paths_sym)
qed

lemmas eq_paths_linepaths' = eq_paths_sym [OF eq_paths_linepaths]

lemma eq_paths_joinpaths_linepath [eq_paths_intros]:
  fixes a b :: "'a :: euclidean_space"
  assumes "eq_paths p (linepath a c)"
  assumes "eq_paths q (linepath c b)"
  assumes "c \<in> closed_segment a b"
  assumes "a = b \<or> (a \<noteq> c \<and> c \<noteq> b)"
  shows   "eq_paths (p +++ q) (linepath a b)"
proof -
  have [simp]: "pathfinish p = c" "pathstart q = c"
    using eq_paths_imp_same_ends[OF assms(1)] eq_paths_imp_same_ends[OF assms(2)]
    by auto
  have "eq_paths (p +++ q) (linepath a c +++ linepath c b)"
    by (intro eq_paths_join assms) (use assms in auto)
  also have "eq_paths \<dots> (linepath a b)"
    by (intro eq_paths_linepaths) (use assms in auto)
  finally show ?thesis .
qed

lemma eq_paths_joinpaths_linepath' [eq_paths_intros]:
  fixes a b :: "'a :: euclidean_space"
  shows "eq_paths (linepath a c) p \<Longrightarrow> eq_paths (linepath c b) q \<Longrightarrow> 
           c \<in> closed_segment a b \<Longrightarrow> a = b \<or> a \<noteq> c \<and> c \<noteq> b \<Longrightarrow> eq_paths (linepath a b) (p +++ q)"
  using eq_paths_joinpaths_linepath[of p a c q b] by (simp add: eq_paths_sym_iff)

lemma eq_paths_part_circlepaths [eq_paths_intros]:
  assumes "b \<in> closed_segment a c" "a = c \<or> (a \<noteq> b \<and> b \<noteq> c)" "b = b'"
  shows   "eq_paths (part_circlepath x r a b +++ part_circlepath x r b' c)
             (part_circlepath x r a c)" (is "eq_paths ?g ?h")
proof -
  interpret part_circlepaths_join x r a b c
    by unfold_locales fact
  interpret eq_paths_locale ?h ?g angle.f
    unfolding \<open>b = b'\<close> [symmetric] by (rule eq_paths_locale) fact
  have "eq_paths ?h ?g"
    unfolding eq_paths_def using eq_paths_locale_axioms by blast
  thus ?thesis
    by (rule eq_paths_sym)
qed

lemmas eq_paths_part_circlepaths' [eq_paths_intros] =
  eq_paths_sym [OF eq_paths_part_circlepaths]

lemma eq_paths_joinpaths_part_circlepath [eq_paths_intros]:
  assumes "eq_paths p (part_circlepath x r a c)"
  assumes "eq_paths q (part_circlepath x r c b)"
  assumes "c \<in> closed_segment a b"
  assumes "a = b \<or> (a \<noteq> c \<and> c \<noteq> b)"
  shows   "eq_paths (p +++ q) (part_circlepath x r a b)"
proof -
  have "eq_paths (p +++ q) (part_circlepath x r a c +++ part_circlepath x r c b)"
    by (intro eq_paths_join assms) (use assms in auto)
  also have "eq_paths \<dots> (part_circlepath x r a b)"
    by (intro eq_paths_part_circlepaths) (use assms in auto)
  finally show ?thesis .
qed

lemma eq_paths_joinpaths_part_circlepath' [eq_paths_intros]:
  assumes "eq_paths (part_circlepath x r a c) p"
  assumes "eq_paths (part_circlepath x r c b)q "
  assumes "c \<in> closed_segment a b"
  assumes "a = b \<or> (a \<noteq> c \<and> c \<noteq> b)"
  shows   "eq_paths (part_circlepath x r a b) (p +++ q)"
  using eq_paths_joinpaths_part_circlepath[of p x r a c q b] assms by (simp add: eq_paths_sym)


subsection \<open>Subpaths\<close>

locale subpath_locale =
  fixes p q :: "real \<Rightarrow> 'a :: topological_space" and f :: "real \<Rightarrow> real"
  assumes borders: "f 0 \<ge> 0" "f 1 \<le> 1"
  assumes paths [simp, intro]: "path p" "path q"
  assumes cont [continuous_intros]: "continuous_on {0..1} f"
  assumes mono: "strict_mono_on {0..1} f"
  assumes equiv: "\<And>t. t \<in> {0..1} \<Longrightarrow> p t = q (f t)"
begin

lemmas cont' [continuous_intros] = continuous_on_compose2 [OF cont]

lemma inj: "inj_on f {0..1}"
  using strict_mono_on_imp_inj_on mono by blast

lemma inj': "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  using inj by (meson inj_on_contraD)

lemma less_iff: "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x < f y \<longleftrightarrow> x < y"
  using mono by (meson less_le_not_le linorder_linear strict_mono_onD strict_mono_on_leD)

lemma le_iff: "x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> f x \<le> f y \<longleftrightarrow> x \<le> y"
  using mono less_iff linorder_not_le by blast

lemma eq_f0_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x = f 0 \<longleftrightarrow> x = 0"
  and eq_f1_iff [simp]: "x \<in> {0..1} \<Longrightarrow> f x = f 1 \<longleftrightarrow> x = 1"
  using inj'[of x 0] inj'[of x 1] by simp_all

lemma eq_0_iff: "x \<in> {0..1} \<Longrightarrow> f x = 0 \<longleftrightarrow> x = 0 \<and> f 0 = 0"
  and eq_1_iff: "x \<in> {0..1} \<Longrightarrow> f x = 1 \<longleftrightarrow> x = 1 \<and> f 1 = 1"
  using le_iff[of x 0] le_iff[of 1 x] borders by auto

lemma eq_0_iff' [simp]: "NO_MATCH 0 x \<Longrightarrow> x \<in> {0..1} \<Longrightarrow> f x = 0 \<longleftrightarrow> x = 0 \<and> f 0 = 0"
  and eq_1_iff' [simp]: "NO_MATCH 1 x \<Longrightarrow> x \<in> {0..1} \<Longrightarrow> f x = 1 \<longleftrightarrow> x = 1 \<and> f 1 = 1"
  by (rule eq_0_iff eq_1_iff; assumption)+

lemma ge_0 [simp]: "x \<in> {0..1} \<Longrightarrow> f x \<ge> 0"
  and le_1 [simp]: "x \<in> {0..1} \<Longrightarrow> f x \<le> 1"
  using le_iff[of 0 x] le_iff[of x 1] borders by auto

lemma bij_betw: "bij_betw f {0..1} {f 0..f 1}"
proof -
  have "x \<in> f ` {0..1}" if "x \<in> {f 0..f 1}" for x
    using IVT'[of f 0 x 1] that cont by auto
  hence "f ` {0..1} = {f 0..f 1}"
    by (auto simp: le_iff)
  thus ?thesis
    using inj unfolding bij_betw_def by blast
qed

lemma in_range: "f x \<in> {0..1}" if "x \<in> {0..1}"
  using bij_betw that borders unfolding bij_betw_def by auto

lemma path_image_subset: "path_image p \<subseteq> path_image q"
proof -
  have "path_image p = p ` {0..1}"
    by (simp add: path_image_def)
  also have "\<dots> = (q \<circ> f) ` {0..1}"
    by (intro image_cong) (auto simp: equiv)
  also have "\<dots> = q ` (f ` {0..1})"
    by (simp add: image_image)
  also have "f ` {0..1} = {f 0..f 1}"
    using bij_betw by (meson bij_betw_def)
  also have "q ` \<dots> \<subseteq> q ` {0..1}"
    using borders by (intro image_mono) auto
  also have " \<dots> = path_image q"
    by (simp add: path_image_def)
  finally show ?thesis .
qed

lemma reverse: "subpath_locale (reversepath p) (reversepath q) (\<lambda>x. 1 - f (1 - x))"
proof
  show "reversepath p t = reversepath q (1 - f (1 - t))"
    if "t \<in> {0..1}" for t
    using that by (auto simp: reversepath_def equiv)
qed (auto intro!: continuous_intros strict_mono_onI simp: less_iff borders)

lemma arc:
  assumes "arc q"
  shows   "arc p"
  unfolding arc_def
proof (safe intro!: inj_onI)
  fix x y
  assume xy: "x \<in> {0..1}" "y \<in> {0..1}" "p x = p y"
  hence "q (f x) = q (f y)"
    by (simp add: equiv)
  hence "f x = f y"
    by (intro arcD[OF assms]) (use xy in auto)
  thus "x = y"
    using xy by (subst (asm) inj') auto
qed auto

lemma arc':
  assumes "simple_path q" "f 0 \<noteq> 0 \<or> f 1 \<noteq> 1"
  shows   "arc p"
  unfolding arc_def
proof (safe intro!: inj_onI)
  fix x y
  assume xy: "x \<in> {0..1}" "y \<in> {0..1}" "p x = p y"
  hence *: "q (f x) = q (f y)"
    by (simp add: equiv)
  have **: "f x \<in> {0..1}" "f y \<in> {0..1}"
    by (rule in_range; use xy in simp)+
  have "f x = f y"
  proof (rule ccontr)
    assume ***: "f x \<noteq> f y"
    hence "{f x, f y} = {0, 1}"
      using simple_pathD[OF assms(1), of "f x" "f y"] * ** by simp
    thus False
      using assms *** xy by (auto simp: doubleton_eq_iff)
  qed
  thus "x = y"
    using xy by (simp add: inj')
qed auto

lemma simple_path:
  assumes "simple_path q"
  shows   "simple_path p"
proof (rule simple_pathI)
  show "x = 0 \<and> y = 1" if "0 \<le> x" "x < y" "y \<le> 1" "p x = p y" for x y
  proof -
    have "q (f x) = q (f y)"
      using that by (simp add: equiv)
    moreover from that have "f x < f y"
      by (subst less_iff) auto
    ultimately have "{f x, f y} = {0,1}"
      using simple_pathD[OF assms, of "f x" "f y"] that by simp
    thus ?thesis using that
      by (auto simp: doubleton_eq_iff)
  qed
qed auto

end


context eq_paths_locale
begin

sublocale subpath: subpath_locale q p f
  by standard (auto simp: cont mono equiv)

end


locale subpath_locale_compose =
  pq: subpath_locale p q f + qr : subpath_locale q r g for p q r f g
begin

sublocale subpath_locale p r "g \<circ> f"
proof
  show "strict_mono_on {0..1} (g \<circ> f)"
    using qr.mono pq.mono
  proof (rule strict_mono_on_compose)
    show "f ` {0..1} \<subseteq> {0..1}"
      using pq.in_range by auto
  qed
qed (auto intro!: continuous_intros simp: pq.equiv qr.equiv)

end


definition is_subpath :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_subpath p q \<longleftrightarrow> (\<exists>f. subpath_locale p q f)"

lemma subpath_locale_refl [intro!]: "path p \<Longrightarrow> subpath_locale p p (\<lambda>x. x)"
  by unfold_locales (auto intro!: strict_mono_onI)

lemma is_subpath_refl [intro!]: "path p \<Longrightarrow> is_subpath p p"
  unfolding is_subpath_def by blast

lemma eq_paths_imp_subpath [intro]: 
  assumes "eq_paths p q"
  shows   "is_subpath p q"
proof -
  from assms obtain f where "eq_paths_locale p q f"
    by (auto simp: eq_paths_def)
  then interpret eq_paths_locale p q f .
  interpret inv: eq_paths_locale q p "inv_into {0..1} f"
    by (rule inverse)
  show ?thesis
    unfolding is_subpath_def using inv.subpath.subpath_locale_axioms by blast
qed

lemma is_subpath_reverse [intro]:
  "is_subpath p q \<Longrightarrow> is_subpath (reversepath p) (reversepath q)"
  unfolding is_subpath_def using subpath_locale.reverse by auto

lemma is_subpath_reverse_iff:
  "is_subpath (reversepath p) (reversepath q) \<longleftrightarrow> is_subpath p q"
  using is_subpath_reverse reversepath_reversepath by metis

lemma is_subpath_trans [trans]:
  assumes "is_subpath p q" "is_subpath q r"
  shows   "is_subpath p r"
proof -
  from assms(1) obtain f where "subpath_locale p q f"
    by (auto simp: is_subpath_def)
  then interpret pq: subpath_locale p q f .
  from assms(2) obtain g where "subpath_locale q r g"
    by (auto simp: is_subpath_def)
  then interpret qr: subpath_locale q r g .
  interpret subpath_locale_compose p q r f g ..
  show ?thesis
    unfolding is_subpath_def using subpath_locale_axioms by blast
qed

lemma is_subpath_eq_trans [trans]:
  "p = q \<Longrightarrow> is_subpath q r \<Longrightarrow> is_subpath p r"
  "is_subpath p q \<Longrightarrow> q = r \<Longrightarrow> is_subpath p r"
  by simp_all

lemma is_subpath_eq_paths_trans [trans]:
  "eq_paths p q \<Longrightarrow> is_subpath q r \<Longrightarrow> is_subpath p r"
  "is_subpath p q \<Longrightarrow> eq_paths q r \<Longrightarrow> is_subpath p r"
  using eq_paths_imp_subpath is_subpath_trans by metis+  

lemma is_subpath_imp_path_image_subset:
  "is_subpath p q \<Longrightarrow> path_image p \<subseteq> path_image q"
  unfolding is_subpath_def using subpath_locale.path_image_subset by blast

lemma subpath_imp_arc:
  "is_subpath p q \<Longrightarrow> arc q \<Longrightarrow> arc p"
  unfolding is_subpath_def using subpath_locale.arc by blast

lemma subpath_imp_simple_path:
  "is_subpath p q \<Longrightarrow> simple_path q \<Longrightarrow> simple_path p"
  unfolding is_subpath_def using subpath_locale.simple_path by blast

lemma is_subpath_joinI1 [intro]:
  assumes [simp]: "path p" "path q" "pathfinish p = pathstart q"
  shows   "is_subpath p (p +++ q)"
  unfolding is_subpath_def
proof
  show "subpath_locale p (p +++ q) (\<lambda>x. x / 2)"
  proof
    show "p t = (p +++ q) (t / 2)" if "t \<in> {0..1}" for t
      using that by (auto simp: joinpaths_def)
  qed (auto intro!: strict_mono_onI continuous_intros)
qed

lemma is_subpath_joinI2 [intro]:
  assumes [simp]: "path p" "path q" and "pathfinish p = pathstart q"
  shows   "is_subpath q (p +++ q)"
  unfolding is_subpath_def
proof
  show "subpath_locale q (p +++ q) (\<lambda>x. x / 2 + 1 / 2)"
  proof
    show "q t = (p +++ q) (t / 2 + 1 / 2)" if "t \<in> {0..1}" for t
      using that assms(3)
      by (cases "t = 1") (auto simp: joinpaths_def pathstart_def pathfinish_def)
  qed (auto intro!: strict_mono_onI continuous_intros simp: assms(3))
qed

lemma eq_paths_join_subpaths:
  assumes "path p" "0 \<le> a" "a < b" "b < c" "c \<le> 1"
  shows   "eq_paths (subpath a c p) (subpath a b p +++ subpath b c p)"
  unfolding eq_paths_def
proof
  from assms have "a < c"
    by simp
  define u where "u = (b - a) / (c - a)"
  have "u > 0"
    unfolding u_def using \<open>a < c\<close> \<open>a < b\<close> by (intro divide_pos_pos) auto
  define f where "f = (\<lambda>t. if t \<le> 1 / 2 then 2 * u * t else ((c - b) * (2 * t - 1) + b - a) / (c - a))"
  show "eq_paths_locale (subpath a c p) (subpath a b p +++ subpath b c p) f"
  proof
    show "(subpath a b p +++ subpath b c p) t = subpath a c p (f t)" if "t \<in> {0..1}" for t
    proof (cases "t \<le> 1 / 2")
      case True
      have "(b - a) * (2 * t) + a = (c - a) * f t + a"
        using True that \<open>a < c\<close> by (simp add: field_simps u_def f_def)
      thus ?thesis
        using that True by (simp add: joinpaths_def subpath_def)
    next
      case False
      have "(c - b) * (2 * t - 1) + b = (c - a) * f t + a"
        using False that \<open>a < c\<close> by (simp add: f_def field_simps)
      thus ?thesis
        using that False by (simp add: joinpaths_def subpath_def)
    qed
    show "continuous_on {0..1} f"
      unfolding f_def using \<open>a < c\<close>
      by (intro continuous_intros continuous_on_real_If_combine)
         (auto simp: u_def field_simps)
    show "f 0 = 0" "f 1 = 1" using \<open>a < c\<close>
      by (auto simp: field_simps f_def)
    show "path (subpath a c p)" "path (subpath a b p +++ subpath b c p)"
      using assms by auto
    show "strict_mono_on {0..1} f"
    proof (rule strict_mono_on_atLeastAtMost_combine)
      show "strict_mono_on {0..1/2} f" using assms \<open>a < c\<close> \<open>u > 0\<close>
        by (auto simp: f_def strict_mono_on_def)
      show "strict_mono_on {1/2..1} f"
      proof (rule strict_mono_onI)
        fix r s :: real assume rs: "r \<in> {1/2..1}" "s \<in> {1/2..1}" "r < s"
        have "f r = ((c - b) * (2 * r - 1) + b - a) / (c - a)"
          using rs by (cases "r = 1/2") (auto simp: f_def u_def field_simps)
        also have "\<dots> < ((c - b) * (2 * s - 1) + b - a) / (c - a)"
          using \<open>a < b\<close> \<open>b < c\<close>
          by (intro divide_strict_right_mono mult_strict_left_mono 
                diff_strict_right_mono add_strict_right_mono rs) auto
        also have "\<dots> = f s"
          using rs by (simp add: f_def)
        finally show "f r < f s" .
      qed
    qed
  qed
qed

lemma eq_paths_join_subpaths':
  assumes "path p" "0 < b" "b < 1"
  shows   "eq_paths p (subpath 0 b p +++ subpath b 1 p)"
  using eq_paths_join_subpaths[of p 0 b 1] assms by simp

locale linepath_subpath =
  fixes a b c d :: "'a :: euclidean_space"
  assumes collinear: "betweens [a, b, c, d]"
  assumes not_degenerate: "b \<noteq> c"
begin

lemma collinear': "between (a, d) b" "between (a, d) c"
  using collinear between_trans1' between_trans2' not_degenerate by auto

lemma not_degenerate': "a \<noteq> d"
  using collinear unfolding betweens.simps between_def prod.case
  by (metis IntI Int_closed_segment closed_segment_commute ends_in_segment(1)
            not_degenerate singletonD)

definition f where "f = (\<lambda>x. linepath (dist a b) (dist a c) x / dist a d)"

lemma dist_eq:
  "dist a d = dist a b + dist b c + dist c d"
  "dist a c = dist a b + dist b c" "dist b d = dist b c + dist c d"
  using collinear collinear' by (simp_all add: between)

sublocale subpath_locale "linepath b c" "linepath a d" f
proof
  have "dist a c \<le> dist a d"
    by (simp add: dist_eq)
  thus "f 0 \<ge> 0" "f 1 \<le> 1" using not_degenerate'
    by (auto simp: f_def field_simps linepath_def)
  show "continuous_on {0..1} f"
    unfolding f_def by (rule continuous_intros)+ (use not_degenerate' in auto)
  have "f x < f y" if "x \<in> {0..1}" "y \<in> {0..1}" "x < y" for x y
  proof -
    have "dist a d > 0"
      using not_degenerate' by auto
    hence "0 < (y - x) * (dist a c - dist a b) / dist a d"
      using not_degenerate that
      by (intro mult_pos_pos divide_pos_pos) (auto simp: dist_eq)
    also have "(y - x) * (dist a c - dist a b) =
               linepath (dist a b) (dist a c) y - linepath (dist a b) (dist a c) x"
      by (simp add: linepath_def algebra_simps)
    finally show ?thesis
      using \<open>dist a d > 0\<close> by (simp add: field_simps f_def)
  qed
  thus "strict_mono_on {0..1} f"
    by (intro strict_mono_onI)
  show "linepath b c t = linepath a d (f t)" if "t \<in> {0..1}" for t
  proof -
    have "dist a d > 0"
      using not_degenerate' by simp
    have b: "b = linepath a d (dist a b / dist a d)"
      by (rule between_conv_linepath) (use collinear' in auto)
    have c: "c = linepath a d (dist a c / dist a d)"
      by (rule between_conv_linepath) (use collinear' in auto)

    have "linepath b c t - linepath a d (f t) =
           (t * dist a c / dist a d + (dist a b - t * dist a b) / dist a d -
              (dist a b + t * dist a c - t * dist a b) / dist a d) *\<^sub>R d +
           ((dist a b + t * dist a c - t * dist a b) / dist a d - t * dist a c / dist a d -
              ((dist a b - t * dist a b) / dist a d)) *\<^sub>R a"
      (is "_ = ?x *\<^sub>R d + ?y *\<^sub>R a")
      by (subst b, subst c)
         (simp add: linepath_def f_def algebra_simps add_divide_distrib)
    also have "?y = 0"
      using not_degenerate' by (simp add: field_simps)
    also have "?x = 0"
      using not_degenerate' by (simp add: field_simps)
    finally show ?thesis
      by simp
  qed
qed auto

end

lemma is_subpath_linepath:
  assumes "betweens [a, b, c, d]" "b \<noteq> c"
  shows   "is_subpath (linepath b c) (linepath a d)"
proof -
  interpret linepath_subpath a b c d
    by unfold_locales fact+
  show ?thesis
    unfolding is_subpath_def using subpath_locale_axioms by auto
qed


locale part_circlepath_subpath =
  fixes x :: complex and r a b c d :: real
  assumes between: "betweens [a, b, c, d]"
  assumes not_degenerate: "b \<noteq> c"
begin

sublocale angle: linepath_subpath a b c d
  by unfold_locales (fact between not_degenerate)+

sublocale subpath_locale "part_circlepath x r b c" "part_circlepath x r a d" angle.f
proof
  show "part_circlepath x r b c t = part_circlepath x r a d (angle.f t)" if "t \<in> {0..1}" for t
    using that by (simp add: part_circlepath_altdef angle.equiv)
qed (use angle.mono angle.cont in auto)

end

lemma is_subpath_part_circlepath:
  assumes "betweens [a, b, c, d]" "b \<noteq> c"
  shows   "is_subpath (part_circlepath x r b c) (part_circlepath x r a d)"
proof -
  interpret part_circlepath_subpath x r a b c d
    by unfold_locales fact+
  show ?thesis
    unfolding is_subpath_def using subpath_locale_axioms by auto
qed


subsection \<open>Loops\<close>

definition eq_loops :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "eq_loops p q \<longleftrightarrow>
     pathstart p = pathfinish p \<and> pathstart q = pathfinish q \<and> path q \<and> (\<exists>c. eq_paths p (shiftpath' c q))"

lemma eq_paths_imp_eq_loops:
  assumes "eq_paths p q" "pathstart p = pathfinish p \<or> pathstart q = pathfinish q"
  shows   "eq_loops p q"
  unfolding eq_loops_def
proof safe
  show *: "pathstart p = pathfinish p" "pathstart q = pathfinish q"
    using eq_paths_imp_same_ends[OF assms(1)] assms(2) by auto
  have "path p" "path q"
    using eq_paths_imp_path[OF assms(1)] by auto
  thus "\<exists>c. eq_paths p (shiftpath' c q)"
    using assms(1) * by (intro exI[of _ 0]) auto
  show "path q"
    by fact
qed

lemma eq_loops_refl':
  assumes "path p \<or> path q" "pathstart p = pathfinish p \<or> pathstart q = pathfinish q"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x"
  shows   "eq_loops p q"
  by (intro eq_paths_imp_eq_loops eq_paths_refl' assms)

lemma eq_loops_refl [simp, intro!]:
  assumes [simp]: "path p" "pathstart p = pathfinish p"
  shows   "eq_loops p p"
  by (intro eq_loops_refl') auto

lemma eq_loops_imp_loop:
  assumes "eq_loops p q"
  shows   "pathstart p = pathfinish p" "pathstart q = pathfinish q"
proof -
  show "pathstart p = pathfinish p"
    using assms by (auto simp: eq_loops_def)
  show "pathstart q = pathfinish q"
    using assms unfolding eq_loops_def by auto
qed

lemma path_shiftpath' [intro]:
  "pathstart p = pathfinish p \<Longrightarrow> path p \<Longrightarrow> path (shiftpath' c p)"
  unfolding shiftpath'_def path_def
  by (rule continuous_on_frac_real')
     (auto intro!: continuous_intros simp: pathfinish_def pathstart_def)

lemma pathfinish_shiftpath':
  "pathfinish (shiftpath' c p) = pathstart (shiftpath' c p)"
  by (simp add: pathstart_def pathfinish_def shiftpath'_def)

lemma eq_loops_shiftpath'_left:
  assumes "path p" "pathstart p = pathfinish p"
  shows   "eq_loops (shiftpath' c p) p"
  unfolding eq_loops_def using assms
  by (intro conjI exI[of _ "c"]) (auto simp: pathfinish_shiftpath')

lemma shiftpath'_shiftpath': "shiftpath' c (shiftpath' d p) = shiftpath' (c + d) p"
proof
  fix x :: real
  have "shiftpath' c (shiftpath' d p) x = p (frac (frac (x + c) + d))"
    by (simp_all add: shiftpath'_def)
  also have "frac (frac (x + c) + d) =
               x + c - real_of_int \<lfloor>x + c\<rfloor> + d - real_of_int \<lfloor>x + c - real_of_int \<lfloor>x + c\<rfloor> + d\<rfloor>"
    by (simp add: frac_def)
  also have "x + c - real_of_int \<lfloor>x + c\<rfloor> + d = x + c + d - real_of_int \<lfloor>x + c\<rfloor>"
    by Groebner_Basis.algebra
  also have "floor \<dots> = \<lfloor>x + c + d\<rfloor> - \<lfloor>x + c\<rfloor>"
    by (subst floor_diff_of_int) auto
  also have "x + c + d - real_of_int \<lfloor>x + c\<rfloor> - real_of_int (\<lfloor>x + c + d\<rfloor> - \<lfloor>x + c\<rfloor>) =
               frac (x + c + d)"
    by (simp add: frac_def)
  also have "p \<dots> = shiftpath' (c + d) p x"
    by (simp add: shiftpath'_def add_ac)
  finally show "shiftpath' c (shiftpath' d p) x = shiftpath' (c + d) p x" .
qed

lemma eq_loops_shiftpath'_right:
  assumes "path p" "pathstart p = pathfinish p"
  shows   "eq_loops p (shiftpath' c p)"
  unfolding eq_loops_def using assms
  by (intro conjI exI[of _ "-c"]) (auto simp: pathfinish_shiftpath' shiftpath'_shiftpath')

locale eq_paths_shiftpath_locale = eq_paths_locale +
  fixes c :: real
  assumes c: "c \<in> {0..1}"
  assumes loop: "pathstart p = pathfinish p"
begin

lemma loop': "pathstart q = pathfinish q"
  using loop by (simp_all add: same_ends)

definition g where "g = (\<lambda>t. if t \<le> 1 - c then f (t + c) - f c else f (t + c - 1) - f c + 1)"

sublocale shifted: eq_paths_locale "shiftpath (f c) p" "shiftpath c q" g
proof
  show "shiftpath c q t = shiftpath (f c) p (g t)" if "t \<in> {0..1}" for t
  proof (cases "t + c" "1 :: real" rule: linorder_cases)
    case less thus ?thesis using that c
      by (simp add: shiftpath_def equiv add_ac g_def)
  next
    case greater thus ?thesis using that c
      by (auto simp add: shiftpath_def equiv add_ac g_def)
  next
    case equal
    thus ?thesis using that c ends
      by (auto simp: shiftpath_def g_def equiv add.commute)
  qed
  show "strict_mono_on {0..1} g"
    unfolding g_def using c
    apply (intro strict_mono_onI)
    apply (auto intro!: strict_mono_onD[OF mono])
    by (smt (verit, best) cont continuous_inj_imp_mono ends(1) ends(2) inj)
  show "continuous_on {0..1} g"
    unfolding g_def using c
    by (auto intro!: continuous_on_real_If_combine continuous_intros)
qed (use c in \<open>auto simp: loop loop' g_def intro!: path_shiftpath\<close>)

end

lemma eq_paths_locale_cong:
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> p x = p' x"
  assumes "\<And>x. x \<in> {0..1} \<Longrightarrow> q x = q' x"
  shows   "eq_paths_locale p q f \<longleftrightarrow> eq_paths_locale p' q' f"
  unfolding eq_paths_locale_def using assms
  apply (intro conj_cong path_cong refl) 
    apply auto
   apply (smt (verit, best) continuous_inj_imp_mono strict_mono_on_imp_inj_on)+
  done

locale eq_paths_shiftpath'_locale = eq_paths_locale +
  fixes c :: real
  assumes loop: "pathstart p = pathfinish p"
begin

definition g :: "real \<Rightarrow> real" where
  "g = (\<lambda>t. if t \<le> 1 - frac c then f (t + frac c) - f (frac c) else
              f (t + frac c - 1) - f (frac c) + 1)"

sublocale shifted: eq_paths_locale "shiftpath' (f (frac c)) p" "shiftpath' c q" g
proof -
  interpret aux: eq_paths_shiftpath_locale p q f "frac c"
    by unfold_locales (use loop in \<open>auto simp: frac_lt_1 less_imp_le\<close>)
  have "aux.g = g"
    by (simp add: g_def aux.g_def)
  hence "eq_paths_locale (shiftpath (f (frac c)) p) (shiftpath (frac c) q) g"
    using aux.shifted.eq_paths_locale_axioms by simp
  also have "?this \<longleftrightarrow> eq_paths_locale (shiftpath' (f (frac c)) p) (shiftpath' (frac c) q) g"
    by (intro eq_paths_locale_cong)
       (auto simp: loop less_imp_le[OF frac_lt_1] shiftpath'_eq_shiftpath aux.loop')
  also have "shiftpath' (frac c) q = shiftpath' c q"
    by (simp add: shiftpath'_frac)
  finally show "eq_paths_locale (shiftpath' (f (frac c)) p) (shiftpath' c q) g" .
qed

end

lemma eq_paths_shiftpath_shiftpath':
  "path p \<Longrightarrow> pathstart p = pathfinish p \<Longrightarrow> c \<in> {0..1} \<Longrightarrow>
     eq_paths (shiftpath c p) (shiftpath' c p)"
  by (intro eq_paths_refl' path_shiftpath) (auto simp: shiftpath'_eq_shiftpath)

lemma path_image_shiftpath':
  assumes "path p" "pathstart p = pathfinish p"
  shows   "path_image (shiftpath' c p) = path_image p"
  using assms
proof -
  have "eq_paths (shiftpath (frac c) p) (shiftpath' c p)"
    using eq_paths_shiftpath_shiftpath'[of p "frac c"] assms less_imp_le[OF frac_lt_1, of c]
    by (simp add: shiftpath'_frac)
  hence "path_image (shiftpath (frac c) p) = path_image (shiftpath' c p)"
    by (rule eq_paths_imp_path_image_eq)
  also have "path_image (shiftpath (frac c) p) = path_image p"
    by (rule path_image_shiftpath) (auto intro!: less_imp_le frac_lt_1 simp: assms)
  finally show ?thesis ..
qed

lemma eq_loops_imp_path_image_eq:
  assumes "eq_loops p q"
  shows   "path_image p = path_image q"
proof -
  from assms(1) obtain c where c: "eq_paths p (shiftpath' c q)" and [simp]:
    "pathstart p = pathfinish p" "pathstart q = pathfinish q"
    unfolding eq_loops_def by blast
  have [simp]: "path p" "path q"
    using assms by (auto simp: eq_loops_def)
  have "path_image p = path_image (shiftpath' c q)"
    using eq_paths_imp_path_image_eq[OF c] .
  also have "\<dots> = path_image q"
    by (intro path_image_shiftpath') auto
  finally show ?thesis .
qed

lemma simple_path_shiftpath':
  assumes "simple_path p" "pathfinish p = pathstart p"
  shows   "simple_path (shiftpath' c p)"
proof -
  have "simple_path (shiftpath (frac c) p)"
    by (intro simple_path_shiftpath frac_ge_0 less_imp_le[OF frac_lt_1] assms)
  also have "?this \<longleftrightarrow> simple_path (shiftpath' (frac c) p)"
    by (intro simple_path_cong) (auto simp: assms shiftpath'_eq_shiftpath less_imp_le[OF frac_lt_1])
  also have "shiftpath' (frac c) p = shiftpath' c p"
    by (simp only: shiftpath'_frac)
  finally show ?thesis .
qed

lemma shiftpath'_0 [simp]: "pathfinish p = pathstart p \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> shiftpath' 0 p t = p t"
  by (cases "t = 1") (auto simp: pathfinish_def pathstart_def shiftpath'_def)

lemma simple_path_shiftpath'_iff [simp]:
  assumes "pathfinish p = pathstart p"
  shows   "simple_path (shiftpath' c p) \<longleftrightarrow> simple_path p"
proof
  assume "simple_path (shiftpath' c p)"
  hence "simple_path (shiftpath' (-c) (shiftpath' c p))"
    by (rule simple_path_shiftpath') (use assms in \<open>auto simp: pathfinish_shiftpath'\<close>)
  also have "shiftpath' (-c) (shiftpath' c p) = shiftpath' 0 p"
    by (simp add: shiftpath'_shiftpath')
  also have "simple_path \<dots> \<longleftrightarrow> simple_path p"
    by (intro simple_path_cong) (use assms in auto)
  finally show "simple_path p" .
qed (use assms in \<open>auto intro!: simple_path_shiftpath'\<close>)

lemma eq_loops_imp_simple_path_iff:
  assumes "eq_loops p q"
  shows   "simple_path p \<longleftrightarrow> simple_path q"
proof -
  obtain c where c: "pathstart p = pathfinish p" "pathstart q = pathfinish q" "path q"
                    "eq_paths p (shiftpath' c q)"
    using assms unfolding eq_loops_def by blast
  thus ?thesis
    using eq_paths_imp_simple_path_iff[OF c(4)] by auto
qed

lemma eq_loops_simple_path_trans [trans]:
  "eq_loops p q \<Longrightarrow> simple_path p \<Longrightarrow> simple_path q"
  "simple_path p \<Longrightarrow> eq_loops p q \<Longrightarrow> simple_path q"
  using eq_loops_imp_simple_path_iff by metis+

lemma eq_loops_imp_simple_loop_iff:
  assumes "eq_loops p q"
  shows   "simple_loop p \<longleftrightarrow> simple_loop q"
  using eq_loops_imp_simple_path_iff [OF assms] eq_loops_imp_loop [OF assms]
  by (auto simp: simple_loop_def)

lemma eq_loops_imp_homotopic:
  assumes "eq_loops p q" "path_image p \<inter> path_image q \<subseteq> A"
  shows   "homotopic_loops A p q"
proof -
  from assms(1) obtain c where c: "eq_paths p (shiftpath' c q)" and [simp]:
      "pathstart p = pathfinish p" "pathstart q = pathfinish q"
    by (auto simp: eq_loops_def)
  from c obtain f where "eq_paths_locale p (shiftpath' c q) f"
    by (auto simp: eq_paths_def)
  then interpret eq_paths_locale p "shiftpath' c q" f .
  have "path q"
    using assms(1) eq_loops_def by blast
  have "homotopic_loops (path_image p) p (shiftpath' c q)"
    using c path_image_eq same_ends
    by (intro homotopic_paths_imp_homotopic_loops homotopic) (auto simp: pathfinish_shiftpath')
  also have "homotopic_loops (path_image p) (shiftpath' c q) q"
    using eq_loops_imp_path_image_eq[OF assms(1)] \<open>path q\<close>
    by (intro homotopic_loops_shiftpath'_left) auto
  finally show ?thesis
    by (rule homotopic_loops_subset) (use assms eq_loops_imp_path_image_eq[OF assms(1)] in auto)
qed

lemma eq_loops_homotopic_loops_trans [trans]:
  "eq_loops p q \<Longrightarrow> homotopic_loops A q r \<Longrightarrow> homotopic_loops A p r"
  "homotopic_loops A p q \<Longrightarrow> eq_loops q r \<Longrightarrow> homotopic_loops A p r"
  using eq_loops_imp_homotopic
   apply (metis homotopic_loops_imp_subset homotopic_loops_trans le_infI2)
  using eq_loops_imp_homotopic
  apply (metis eq_loops_imp_path_image_eq homotopic_loops_imp_subset homotopic_loops_trans inf_idem)
  done

lemma eq_loops_imp_winding_number_eq:
  assumes "eq_loops p q" "z \<notin> path_image p \<inter> path_image q"
  shows   "winding_number p z = winding_number q z"
proof (rule winding_number_homotopic_loops)
  show "homotopic_loops (-{z}) p q"
    by (rule eq_loops_imp_homotopic[OF assms(1)]) (use assms(2) in auto)
qed

lemma
  assumes "eq_loops p q"
  shows   eq_loops_imp_ccw_iff: "simple_loop_ccw p = simple_loop_ccw q"
    and   eq_loops_imp_cw_iff: "simple_loop_cw p = simple_loop_cw q"
  unfolding simple_loop_ccw_def simple_loop_cw_def
  using eq_loops_imp_path_image_eq[OF assms] eq_loops_imp_winding_number_eq[OF assms]
  by (intro conj_cong eq_loops_imp_simple_loop_iff assms ex_cong1; simp)+

lemma eq_loops_imp_same_orientation:
  assumes "eq_loops p q"
  shows   "simple_loop_orientation p = simple_loop_orientation q"
  unfolding simple_loop_orientation_def
  using eq_loops_imp_ccw_iff[OF assms] eq_loops_imp_cw_iff[OF assms] by auto

lemma eq_loops_ccw_trans [trans]:
  "eq_loops p q \<Longrightarrow> simple_loop_ccw q \<Longrightarrow> simple_loop_ccw p"
  "simple_loop_ccw p \<Longrightarrow> eq_loops p q \<Longrightarrow> simple_loop_ccw q"
  using eq_loops_imp_ccw_iff by metis+

lemma eq_loops_cw_trans [trans]:
  "eq_loops p q \<Longrightarrow> simple_loop_cw q \<Longrightarrow> simple_loop_cw p"
  "simple_loop_cw p \<Longrightarrow> eq_loops p q \<Longrightarrow> simple_loop_cw q"
  using eq_loops_imp_cw_iff by metis+

lemma eq_loops_winding_number_trans [trans]:
  "eq_loops p q \<Longrightarrow> winding_number q z = a \<Longrightarrow> z \<notin> path_image p \<inter> path_image q \<Longrightarrow>
   winding_number p z = a"
  using eq_loops_imp_winding_number_eq by metis

lemma eq_loops_simple_loop_trans [trans]:
  "eq_loops p q \<Longrightarrow> simple_loop p \<Longrightarrow> simple_loop q"
  "simple_loop p \<Longrightarrow> eq_loops p q \<Longrightarrow> simple_loop q"
  using eq_loops_imp_simple_loop_iff by metis+

lemma eq_loops_trans [trans]:
  assumes "eq_loops p q" "eq_loops q r"
  shows   "eq_loops p r"
proof -
  from assms obtain c d where
    1: "eq_paths p (shiftpath' c q)" and 2: "eq_paths (shiftpath' d r) q"
    by (auto simp: eq_loops_def eq_paths_sym_iff)

  have [simp]: "pathstart q = pathfinish q" "pathstart p = pathfinish p"
               "pathstart r = pathfinish r" "path r"
    using assms by (auto simp: eq_loops_def)

  from 1 obtain f where "eq_paths_locale p (shiftpath' c q) f"
    by (auto simp: eq_paths_def)
  then interpret pq: eq_paths_locale p "shiftpath' c q" f .
  obtain g where "eq_paths_locale (shiftpath' d r) q g"
    using 2 by (auto simp: eq_paths_def)
  then interpret qr: eq_paths_locale "shiftpath' d r" q g .

  interpret pq': eq_paths_shiftpath'_locale "shiftpath' d r" q g c
    apply standard 
    using \<open>pathstart q = pathfinish q\<close> qr.same_ends(1) qr.same_ends(2) by metis

  interpret pq'': eq_paths_locale "shiftpath' c q" "shiftpath' (g (frac c)) (shiftpath' d r)" 
                  "inv_into {0..1} pq'.g"
    using pq'.shifted.inverse by simp

  interpret pqr: eq_paths_locale_compose p "shiftpath' c q" 
    "shiftpath' (g (frac c)) (shiftpath' d r)" f "inv_into {0..1} pq'.g" ..

  have "eq_paths p (shiftpath' (g (frac c)) (shiftpath' d r))"
    using pqr.eq_paths_locale_axioms unfolding eq_paths_def by blast
  also have "\<dots> = shiftpath' (g (frac c) + d) r"
    by (simp add: shiftpath'_shiftpath')
  finally show ?thesis
    unfolding eq_loops_def by auto
qed

lemma eq_loops_eq_trans [trans]:
  "p = q \<Longrightarrow> eq_loops q r \<Longrightarrow> eq_loops p r"
  "eq_loops p q \<Longrightarrow> q = r \<Longrightarrow> eq_loops p r"
  by simp_all

lemma eq_loops_sym: 
  assumes "eq_loops p q"
  shows   "eq_loops q p"
proof -
  have [simp]: "pathstart p = pathfinish p" "pathstart q = pathfinish q"
    using assms by (auto simp: eq_loops_def)
  from assms have  [simp]: "path p" "path q"
    by (auto simp: eq_loops_def)
  from assms obtain c where "eq_paths p (shiftpath' c q)"
    by (auto simp: eq_loops_def)
  then obtain f where "eq_paths_locale p (shiftpath' c q) f"
    by (auto simp: eq_paths_def)
  then interpret pq: eq_paths_locale p "shiftpath' c q" f .
  interpret pq': eq_paths_shiftpath'_locale p "shiftpath' c q" f "-c"
    by standard auto
  have "eq_paths (shiftpath' (f (frac (- c))) p) (shiftpath' (- c) (shiftpath' c q))"
    unfolding eq_paths_def using pq'.shifted.eq_paths_locale_axioms by blast
  also have "\<dots> = shiftpath' 0 q"
    by (simp add: shiftpath'_shiftpath')
  also have "eq_paths \<dots> q"
    by simp
  finally have "eq_paths q (shiftpath' (f (frac (- c))) p)"
    by (rule eq_paths_sym)
  thus ?thesis
    unfolding eq_loops_def by auto
qed

lemma eq_loops_sym_iff: "eq_loops p q \<longleftrightarrow> eq_loops q p"
  using eq_loops_sym by metis

lemma eq_loops_shiftpath'_leftI:
  assumes "eq_loops p q"
  shows   "eq_loops (shiftpath' c p) q"
proof -
  have [simp]: "pathstart p = pathfinish p" "pathstart q = pathfinish q" "path p" "path q"
    using assms by (auto simp: eq_loops_def)
  have "eq_loops (shiftpath' c p) p"
    by (intro eq_loops_shiftpath'_left) auto
  also note \<open>eq_loops p q\<close>
  finally show "eq_loops (shiftpath' c p) q" .
qed

lemma eq_loops_shiftpath'_rightI:
  assumes "eq_loops q p"
  shows   "eq_loops q (shiftpath' c p)"
  using eq_loops_shiftpath'_leftI[of p q] assms by (simp add: eq_loops_sym_iff)

lemma path_shiftpath'_iff [simp]:
  assumes "pathstart p = pathfinish p"
  shows   "path (shiftpath' c p) \<longleftrightarrow> path p"
proof
  assume *: "path (shiftpath' c p)"
  have "path (shiftpath' (-c) (shiftpath' c p))"
    by (rule path_shiftpath') (use assms * in \<open>auto simp: pathfinish_shiftpath'\<close>)
  hence "path (shiftpath' 0 p)"
    by (simp add: shiftpath'_shiftpath')
  also have "?this \<longleftrightarrow> path p"
  proof (rule path_cong)
    show "shiftpath' 0 p x = p x" if "x \<in> {0..1}" for x
      using assms that
      by (cases "x < 1") (auto simp: pathstart_def pathfinish_def shiftpath'_def)
  qed
  finally show "path p"
    by auto
qed (use assms in auto)

lemma eq_loops_shiftpath'_left_iff [simp]:
  assumes "pathstart p = pathfinish p"
  shows   "eq_loops (shiftpath' c p) q \<longleftrightarrow> eq_loops p q"
proof
  assume *: "eq_loops (shiftpath' c p) q"
  have "path (shiftpath' c p)"
    using * by (auto simp: eq_loops_def)
  hence "path p" using assms
    by (metis "*" Ints_1 diff_add_cancel eq_loops_def eq_loops_shiftpath'_rightI eq_loops_sym path_shiftpath'_int_iff shiftpath'_shiftpath')
  have "eq_loops p (shiftpath' c p)"
    using \<open>path p\<close> assms eq_loops_shiftpath'_right by blast
  also note *
  finally show "eq_loops p q" .
qed (auto intro: eq_loops_shiftpath'_leftI)

lemma eq_loops_shiftpath'_right_iff [simp]:
  assumes "pathstart p = pathfinish p"
  shows   "eq_loops q (shiftpath' c p) \<longleftrightarrow> eq_loops q p"
  by (subst (1 2) eq_loops_sym_iff) (use assms in simp)

lemma eq_loops_shiftpath_shiftpath':
  assumes "pathstart p = pathfinish p" "path p" "c \<in> {0..1}"
  shows   "eq_loops (shiftpath c p) (shiftpath' c p)"
  by (rule eq_loops_refl')
     (use assms in \<open>auto simp: pathfinish_shiftpath' shiftpath'_eq_shiftpath\<close>)


lemma eq_loops_shiftpath_left_iff [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> {0..1}"
  shows   "eq_loops (shiftpath c p) q \<longleftrightarrow> eq_loops p q"
proof
  assume *: "eq_loops p q"
  hence [simp]: "path p"
    by (auto simp: eq_loops_def)
  have "eq_loops (shiftpath c p) (shiftpath' c p)"
    by (intro eq_loops_shiftpath_shiftpath') (use assms in auto)
  also from * have "eq_loops (shiftpath' c p) q"
    using assms by simp
  finally show "eq_loops (shiftpath c p) q" .
next
  assume "eq_loops (shiftpath c p) q"
  hence "path (shiftpath c p)"
    by (auto simp: eq_loops_def)
  hence [simp]: "path p"
    using assms by (metis path_cong path_shiftpath'_iff shiftpath'_eq_shiftpath)
  have "eq_loops p (shiftpath' c p)"
    using assms by simp
  also have "eq_loops (shiftpath' c p) (shiftpath c p)"
    by (rule eq_loops_sym, rule eq_loops_shiftpath_shiftpath') (use assms in auto)
  also have "eq_loops (shiftpath c p) q"
    by fact
  finally show "eq_loops p q" .
qed

lemma eq_loops_shiftpath_right_iff [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> {0..1}"
  shows   "eq_loops q (shiftpath c p) \<longleftrightarrow> eq_loops q p"
  by (subst (1 2) eq_loops_sym_iff) (use assms in simp)

lemma eq_loops_full_part_circlepath:
  assumes "b = a + 2 * pi"
  shows   "eq_loops (part_circlepath x r a b) (circlepath x r)"
proof -
  have "eq_loops (circlepath x r) (shiftpath' (a / (2 * pi)) (circlepath x r))"
    by simp
  also have "shiftpath' (a / (2 * pi)) (circlepath x r) = part_circlepath x r a b"
    by (simp add: shiftpath'_circlepath add_divide_distrib ring_distribs assms)
  finally show ?thesis
    by (rule eq_loops_sym)
qed

lemma eq_paths_shiftpath_join_onehalf:
  assumes "path p" "path q" "pathfinish p = pathstart q" "pathfinish q = pathstart p"
  shows   "eq_paths (shiftpath (1/2) (p +++ q)) (q +++ p)"
proof (rule eq_paths_refl')
  show "shiftpath (1 / 2) (p +++ q) x = (q +++ p) x" if "x \<in> {0..1}" for x
  proof (cases "x \<in> {0, 1 / 2, 1}")
    case True
    thus ?thesis
      using assms that by (auto simp: pathstart_def pathfinish_def shiftpath_def joinpaths_def)
  qed (use that in \<open>auto simp: shiftpath_def joinpaths_def\<close>)
qed (use assms in auto)

lemma eq_loops_eq_paths_trans [trans]:
  "eq_loops p q \<Longrightarrow> eq_paths q r \<Longrightarrow> eq_loops p r"
  "eq_paths p q \<Longrightarrow> eq_loops q r \<Longrightarrow> eq_loops p r"
  by (meson eq_loops_def eq_loops_trans eq_paths_imp_eq_loops)+

lemma eq_loops_joinpaths_commute:
  assumes "path p" "path q" "pathfinish p = pathstart q" "pathfinish q = pathstart p"
  shows   "eq_loops (p +++ q) (q +++ p)"
proof -
  have "eq_loops (p +++ q) (shiftpath (1/2) (p +++ q))"
    using assms by simp
  also have "eq_paths \<dots> (q +++ p)"
    by (intro eq_paths_shiftpath_join_onehalf) (use assms in auto)
  finally show ?thesis .
qed


bundle path_rel_notation
begin

notation eq_paths (infix "\<equiv>\<^sub>p" 60)
notation eq_loops (infix "\<equiv>\<^sub>\<circle>" 60)
notation is_subpath (infix "\<le>\<^sub>p" 60)

end


bundle no_path_rel_notation
begin

no_notation eq_paths (infix "\<equiv>\<^sub>p" 60)
no_notation eq_loops (infix "\<equiv>\<^sub>\<circle>" 60)
no_notation is_subpath (infix "\<le>\<^sub>p" 60)

end

unbundle path_rel_notation

end