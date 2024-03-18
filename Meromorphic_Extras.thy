theory Meromorphic_Extras
imports "HOL-Complex_Analysis.Complex_Analysis" 
    More_Topology
begin

lemma meromorphic_subset_closedin:
  assumes mero:"f meromorphic_on s pts" and "pp \<subseteq> pts"
  shows "closedin (top_of_set s) pp"
proof -
  have "\<forall>z\<in>s. \<not>(z islimpt pts)" 
    using assms(1) unfolding meromorphic_on_def by auto
  then have "\<forall>z\<in>s. \<not>(z islimpt pp)" 
    using assms(2) islimpt_subset by blast
  moreover have "pp \<subseteq> s" 
    using assms unfolding meromorphic_on_def by auto
  ultimately show ?thesis unfolding closedin_limpt by auto
qed


(*DOESN'T A HAVE TO BE OPEN AND CONNECTED? -- LCP*)
corollary argument_principle_simple:
  assumes f: "f analytic_on A - pts" and
          sparse: "\<And>z. z \<in> A \<Longrightarrow> \<not>z islimpt pts" and
          p: "valid_path p" "pathstart p = pathfinish p" "path_image p \<subseteq> A - pts" and
          f_nz: "\<And>z. z \<in> A - pts \<Longrightarrow> f z \<noteq> 0" and
          inside_subset: "{z. winding_number p z \<noteq> 0} \<subseteq> A"
        shows "contour_integral p (\<lambda>x. deriv f x / f x) = 2 * pi * \<i> * (\<Sum>\<^sub>\<infinity> z\<in>pts. winding_number p z * zorder f z)"
  sorry

text \<open>
  Holomorphic injective functions preserve winding numbers.
\<close>
lemma
  fixes f :: "complex \<Rightarrow> complex"
  assumes f: "f analytic_on A" "inj_on f A"
  assumes \<gamma>: "valid_path \<gamma>" "pathstart \<gamma> = pathfinish \<gamma>" "path_image \<gamma> \<subseteq> A"
  assumes outside: "\<And>z. z \<notin> A \<Longrightarrow> winding_number \<gamma> z = 0"
  shows   winding_number_compose_outside:
            "y \<notin> f ` A \<Longrightarrow> winding_number (f \<circ> \<gamma>) y = 0"
    and   winding_number_compose_inside:
            "x \<in> A - path_image \<gamma> \<Longrightarrow> winding_number (f \<circ> \<gamma>) (f x) = winding_number \<gamma> x"
proof -
  from f(1) obtain A' where A': "A \<subseteq> A'" "open A'" "f holomorphic_on A'"
    using analytic_on_holomorphic by auto

  {
    fix y :: complex
    assume \<gamma>_f_y: "path_image \<gamma> \<inter> {x\<in>A. f x = y} = {}"

    define I' where "I' = winding_number (f \<circ> \<gamma>) y"
    define \<gamma>' where "\<gamma>' = (\<lambda>x. vector_derivative \<gamma> (at x))"
    define f' where "f' = deriv (\<lambda>x. f x - y)"
    define X where "X = {w \<in> A. f w = y}"

    have X: "finite X \<and> card X \<le> 1"
    proof (cases "\<exists>x\<in>A. f x = y")
      case False
      hence "X = {}"
        by (auto simp: X_def)
      thus ?thesis
        by simp
    next
      case True
      then obtain x where "x \<in> A" "f x = y"
        by auto
      hence "X = {x}"
        using f(2) by (auto simp: X_def inj_on_def)
      thus ?thesis
        by auto
    qed
    
    from \<open>valid_path \<gamma>\<close> obtain Z 
      where Z: "continuous_on {0..1} \<gamma>" "finite Z" "\<gamma> C1_differentiable_on {0..1} - Z"
      unfolding valid_path_def piecewise_C1_differentiable_on_def by blast
  
    have diff: "f field_differentiable at (\<gamma> t)" if "t \<in> {0..1}" for t
    proof -
      from that have "\<gamma> t \<in> path_image \<gamma>"
        unfolding path_image_def by blast
      also have "\<dots> \<subseteq> A"
        using \<gamma> by blast
      finally show ?thesis
        using f(1) analytic_on_imp_differentiable_at by blast
    qed

    have "deriv f holomorphic_on A"
      using f(1) holomorphic_deriv analytic_deriv analytic_imp_holomorphic by auto
    hence "deriv f holomorphic_on path_image \<gamma>"
      by (rule holomorphic_on_subset) (use \<gamma> in auto)
    hence "valid_path (f \<circ> \<gamma>)"
      by (auto intro!: valid_path_compose holomorphic_on_imp_continuous_on \<gamma> diff simp: path_image_def)
    moreover have "y \<notin> path_image (f \<circ> \<gamma>)"
      using \<gamma>_f_y \<gamma> unfolding path_image_compose by auto
    ultimately have "((\<lambda>w. 1 / (w - y)) has_contour_integral 2 * pi * \<i> * I') (f \<circ> \<gamma>)"
      using has_contour_integral_winding_number[of "f \<circ> \<gamma>" y] by (simp add: I'_def)
    also have "?this \<longleftrightarrow> ((\<lambda>t. \<gamma>' t * f' (\<gamma> t) / (f (\<gamma> t) - y)) has_integral (2*pi*\<i>*I')) {0..1}"
      unfolding has_contour_integral
      apply (intro has_integral_spike_eq[of "Z"])
       apply (use Z in auto) []
      apply (subst vector_derivative_chain_at_general)
        apply (simp_all add: f'_def \<gamma>'_def)
       apply (meson C1_differentiable_on_def DiffI Z(3) atLeastAtMost_iff differentiableI_vector)
      using diff apply simp
      apply (subst deriv_diff)
      using diff
      apply (auto)
      done
    also have "\<dots> \<longleftrightarrow> ((\<lambda>z. f' z / (f z - y)) has_contour_integral (2*pi*\<i>*I')) \<gamma>"
      unfolding has_contour_integral \<gamma>'_def
      apply (auto simp: mult_ac)
      done
    finally have "contour_integral \<gamma> (\<lambda>z. f' z / (f z - y)) = 2 * pi * \<i> * I'"
      by (auto dest!: contour_integral_unique)
    also have "contour_integral \<gamma> (\<lambda>z. f' z / (f z - y)) =
                 2 * pi * \<i> * (\<Sum>\<^sub>\<infinity> z\<in>X. 
                   winding_number \<gamma> z * of_int (zorder (\<lambda>x. f x - y) z))"
      unfolding f'_def
    proof (subst argument_principle_simple)
      show "(\<lambda>x. f x - y) analytic_on A - X"
        by (rule analytic_on_subset[of _ A]) (auto intro!: analytic_intros f)
      show "\<not> z islimpt X" if "z \<in> A" for z
        using that by (simp add: X islimpt_finite)
      show "{z. winding_number \<gamma> z \<noteq> 0} \<subseteq> A"
        using outside by auto
      show "\<And>z. z \<in> A - X \<Longrightarrow> f z - y \<noteq> 0"
        by (auto simp: X_def)
      show "path_image \<gamma> \<subseteq> A - X"
        using assms \<gamma>_f_y by (auto simp: X_def)
    qed (use assms in auto)
    also have "(\<Sum>\<^sub>\<infinity> z \<in> X. 
                   winding_number \<gamma> z * of_int (zorder (\<lambda>x. f x - y) z)) =
               (\<Sum>p\<in>X. winding_number \<gamma> p * of_int (zorder (\<lambda>x. f x - y) p))"
      using X by (intro infsum_finite) auto
    finally have "I' = (\<Sum>p\<in>X. winding_number \<gamma> p * of_int (zorder (\<lambda>x. f x - y) p))" 
      by simp
    also have "\<dots> = (\<Sum>p\<in>X. winding_number \<gamma> p)"
    proof (intro sum.cong refl)
      fix z assume z: "z \<in> X"
      have "zorder (\<lambda>z. f z - y) z = 1"
        sorry (* TODO: some problems in this part *)
      thus "winding_number \<gamma> z * of_int (zorder (\<lambda>x. f x - y) z) = winding_number \<gamma> z"
        by simp
    qed
    finally have "winding_number (f \<circ> \<gamma>) y = sum (winding_number \<gamma>) X"
      unfolding I'_def .
  } note foo = this

  show "winding_number (f \<circ> \<gamma>) y = 0" if "y \<notin> f ` A" for y
  proof -
    have "winding_number (f \<circ> \<gamma>) y = sum (winding_number \<gamma>) {w \<in> A. f w = y}"
      by (rule foo) (use that \<gamma> in auto)
    also have "{w\<in>A. f w = y} = {}"
      using that by auto
    finally show ?thesis
      by (simp add: o_def)
  qed

  show "winding_number (f \<circ> \<gamma>) (f x) = winding_number \<gamma> x" 
    if "x \<in> A - path_image \<gamma>" for x
  proof -
    have eq: "{w\<in>A. f w = f x} = {x}"
      using f(2) that unfolding inj_on_def by blast
    have "path_image \<gamma> \<inter> {w\<in>A. f w = f x} = {}"
      using eq that by auto
    hence "winding_number (f \<circ> \<gamma>) (f x) = sum (winding_number \<gamma>) {w \<in> A. f w = f x}"
      by (intro foo) (use \<gamma> in auto)
    also note eq
    finally show ?thesis
      by (simp add: o_def)
  qed
qed

(* 
  more general version of the above
  TODO:: preconditions are much too strong right now
  (open + compact = the empty set, but the openness should not be too hard to get rid of)
*)
lemma winding_number_compose:
  fixes f :: "complex \<Rightarrow> complex"
  assumes A: "connected A" and "compact A"
  assumes f: "f meromorphic_on A poles" "poles \<subseteq> {z. is_pole f z}"
  assumes \<gamma>: "valid_path \<gamma>" "pathstart \<gamma> = pathfinish \<gamma>" "path_image \<gamma> \<subseteq> A - poles - f -` {0}"
  assumes outside: "\<And>z. z \<notin> A \<Longrightarrow> winding_number \<gamma> z = 0" (* alternative: "-A \<subseteq> outside (path_image A)" *)
  shows   "winding_number (f \<circ> \<gamma>) 0 =
             (\<Sum>w | w \<in> A \<and> (f w = 0 \<or> w \<in> poles). winding_number \<gamma> w * zorder f w)"
          (* alternative: "(\<Sum>\<^sub>\<infinity> w. winding_number \<gamma> w * zorder f w)" *)
          (* connected is probably not really necessary (just use the connected component
             that \<gamma> lies in *)
          (* compact is not necessary either, neither is all poles being poles *)
proof -
  define I' where "I' = winding_number (f \<circ> \<gamma>) 0"
  define \<gamma>' where "\<gamma>' = (\<lambda>x. vector_derivative \<gamma> (at x))"
  define f' where "f' = deriv f"

  note [[goals_limit = 20]]

  from \<open>valid_path \<gamma>\<close> obtain X 
    where X: "continuous_on {0..1} \<gamma>" "finite X" "\<gamma> C1_differentiable_on {0..1} - X"
    unfolding valid_path_def piecewise_C1_differentiable_on_def by blast

  have diff: "f field_differentiable at (\<gamma> t)" if "t \<in> {0..1}" for t
  proof -
    from that have "\<gamma> t \<in> path_image \<gamma>"
      unfolding path_image_def by blast
    also have "\<dots> \<subseteq> A - poles"
      using \<gamma> by blast
    finally show ?thesis
      using \<open>f meromorphic_on A poles\<close>
      by (meson analytic_on_imp_differentiable_at assms(2) meromorphic_imp_analytic)
  qed

  have fin: "finite {w \<in> A. f w = 0 \<or> w \<in> poles}"
  proof -
    have "finite (A \<inter> poles)"
      by (rule meromorphic_compact_finite_pts[OF f(1) \<open>compact A\<close>]) auto
    moreover have "\<not> (\<forall>w\<in>A - poles. f w = 0)"
    proof -
      have "\<gamma> 0 \<in> path_image \<gamma>"
        unfolding path_image_def by (intro imageI) auto
      also have "\<dots> \<subseteq> A - poles - f -` {0}"
        using \<gamma> by blast
      finally show ?thesis
        by blast
    qed
    hence "finite {w\<in>A. f w = 0}"
      using \<open>connected A\<close>
      by (intro meromorphic_compact_finite_zeros[OF f(1) \<open>compact A\<close>]) auto
    ultimately have "finite ((A \<inter> poles) \<union> {w\<in>A. f w = 0})"
      by (rule finite_UnI)
    also have "\<dots> = {w\<in>A. f w = 0 \<or> w \<in> poles}"
      by auto
    finally show ?thesis .
  qed

  have "deriv f meromorphic_on A poles"
    by (meson f(1) meromorphic_on_def meromorphic_on_deriv)
  hence "deriv f holomorphic_on A - poles"
    by (auto simp: meromorphic_on_def)
  hence "deriv f holomorphic_on path_image \<gamma>"
    by (rule holomorphic_on_subset) (use \<gamma> in auto)
  hence "valid_path (f \<circ> \<gamma>)"
    by (auto intro!: valid_path_compose holomorphic_on_imp_continuous_on \<gamma> diff simp: path_image_def)
  moreover have "0 \<notin> path_image (f \<circ> \<gamma>)"
    using assms by (auto simp: o_def path_image_def)
  ultimately have "((\<lambda>w. 1 / (w - 0)) has_contour_integral 2 * pi * \<i> * I') (f \<circ> \<gamma>)"
    using has_contour_integral_winding_number[of "f \<circ> \<gamma>" 0] by (simp add: I'_def)
  also have "?this \<longleftrightarrow> ((\<lambda>t. \<gamma>' t * f' (\<gamma> t) / f (\<gamma> t)) has_integral (2*pi*\<i>*I')) {0..1}"
    unfolding has_contour_integral
    apply (intro has_integral_spike_eq[of "X"])
     apply (use X in auto) []
    apply (subst vector_derivative_chain_at_general)
      apply (simp_all add: f'_def \<gamma>'_def)
     apply (meson C1_differentiable_on_def DiffI X(3) atLeastAtMost_iff differentiableI_vector)
    using diff apply simp
    done
  also have "\<dots> \<longleftrightarrow> ((\<lambda>z. f' z / f z) has_contour_integral (2*pi*\<i>*I')) \<gamma>"
    unfolding has_contour_integral \<gamma>'_def
    apply (auto simp: mult_ac)
    done
  finally have "contour_integral \<gamma> (\<lambda>z. f' z * 1 / f z) = 2 * pi * \<i> * I'"
    by (auto dest!: contour_integral_unique)
  also have "contour_integral \<gamma> (\<lambda>z. f' z * 1 / f z) =
               2 * pi * \<i> * (\<Sum>p\<in>{w \<in> A. f w = 0 \<or> w \<in> poles}. winding_number \<gamma> p * of_int (zorder f p))"
    unfolding f'_def using assms fin f(2) 
    by (subst argument_principle[of A _ poles])
       (auto simp: meromorphic_on_def)
  finally have "I' = (\<Sum>p\<in>{w \<in> A. f w = 0 \<or> w \<in> poles}. winding_number \<gamma> p * of_int (zorder f p))" 
    by simp
  thus ?thesis
    by (simp add: I'_def)
qed

end