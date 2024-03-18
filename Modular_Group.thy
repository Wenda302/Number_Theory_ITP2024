chapter \<open>Unimodular Transforms and the Modular Group\<close>
theory Modular_Group
  imports "HOL-Complex_Analysis.Residue_Theorem" Complex_Lattices
          "Winding_Number_Eval.Missing_Topology"
          "HOL-Number_Theory.Cong" Meromorphic1 Library_Extras
begin

lemma power2_mono: "\<bar>x\<bar> \<le> \<bar>y\<bar> \<Longrightarrow> x ^ 2 \<le> (y ^ 2 :: 'a :: linordered_idom)"
  by (simp add: abs_le_square_iff)

lemma power2_strict_mono: "\<bar>x\<bar> < \<bar>y\<bar> \<Longrightarrow> x ^ 2 < (y ^ 2 :: 'a :: linordered_idom)"
  using abs_le_square_iff linorder_not_le by blast

lemma closure_bij_homeomorphic_image_eq:
  assumes bij:  "bij_betw f A B"
  assumes homo: "homeomorphism A B f g"
  assumes cont: "continuous_on A' f" "continuous_on B' g"
  assumes inv:  "\<And>x. x \<in> B' \<Longrightarrow> f (g x) = x"
  assumes cl:   "closed A'" "closed B'" and X: "X \<subseteq> A" "A \<subseteq> A'" "B \<subseteq> B'"
  shows   "closure (f ` X) = f ` closure X"
proof -
  have "f ` X \<subseteq> f ` A"
    using \<open>X \<subseteq> A\<close> by blast
  also have "f ` A = B"
    using \<open>bij_betw f A B\<close> by (simp add: bij_betw_def)
  finally have *: "closure (f ` X) \<subseteq> closure B"
    by (intro closure_mono)

  show ?thesis
  proof (rule antisym)
    have "g ` closure (f ` X) \<subseteq> closure (g ` f ` X)"
    proof (rule continuous_image_closure_subset[OF _ *])
      have "closure B \<subseteq> B'"
        using X cl by (simp add: closure_minimal)
      thus "continuous_on (closure B) g"
        by (rule continuous_on_subset[OF cont(2)])
    qed
    also have "g ` f ` X = (g \<circ> f) ` X"
      by (simp add: image_image)
    also have "\<dots> = id ` X"
      using homo X by (intro image_cong) (auto simp: homeomorphism_def)
    finally have "g ` closure (f ` X) \<subseteq> closure X"
      by simp
    hence "f ` g ` closure (f ` X) \<subseteq> f ` closure X"
      by (intro image_mono)
    also have "f ` g ` closure (f ` X) = (f \<circ> g) ` closure (f ` X)"
      by (simp add: image_image)
    also have "\<dots> = id ` closure (f ` X)"
    proof (rule image_cong)
      fix x assume "x \<in> closure (f ` X)"
      also have "closure (f ` X) \<subseteq> closure B'"
      proof (rule closure_mono)
        have "f ` X \<subseteq> f ` A"
          using X by (intro image_mono) auto
        also have "\<dots> = B"
          using bij by (simp add: bij_betw_def)
        also have "\<dots> \<subseteq> B'"
          by fact
        finally show "f ` X \<subseteq> B'" .
      qed
      finally have "x \<in> B'"
        using cl by simp
      thus "(f \<circ> g) x = id x"
        by (auto simp: homeomorphism_def inv)
    qed auto
    finally show "closure (f ` X) \<subseteq> f ` closure X"
      by simp
  next
    show "f ` closure X \<subseteq> closure (f ` X)"
    proof (rule continuous_image_closure_subset)
      show "continuous_on A' f"
        by fact
      show "closure X \<subseteq> A'"
        using assms by (simp add: closure_minimal)
    qed
  qed
qed  


section \<open>Properties of Möbius Transforms\<close>

lemma moebius_uminus [simp]: "moebius (-a) (-b) (-c) (-d) = moebius a b c d"
  by (simp add: fun_eq_iff moebius_def divide_simps) (simp add: algebra_simps add_eq_0_iff2)

lemma moebius_uminus': "moebius (-a) b c d = moebius a (-b) (-c) (-d)"
  by (simp add: fun_eq_iff moebius_def divide_simps) (simp add: algebra_simps add_eq_0_iff2)

lemma moebius_diff_eq:
  fixes a b c d :: "'a :: field"
  defines "f \<equiv> moebius a b c d"
  assumes *: "c = 0 \<or> z \<noteq> -d / c \<and> w \<noteq> -d / c"
  shows   "f w - f z = (a * d - b * c) / ((c * w + d) * (c * z + d)) * (w - z)"
  using * by (auto simp: moebius_def divide_simps f_def add_eq_0_iff)
             (auto simp: algebra_simps)


lemma continuous_on_moebius [continuous_intros]:
  fixes a b c d :: "'a :: real_normed_field"
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "continuous_on A (moebius a b c d)"
  unfolding moebius_def
  by (intro continuous_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma continuous_on_moebius' [continuous_intros]:
  fixes a b c d :: "'a :: real_normed_field"
  assumes "continuous_on A f" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "continuous_on A (\<lambda>x. moebius a b c d (f x))"
proof -
  have "continuous_on A (moebius a b c d \<circ> f)" using assms
    by (intro continuous_on_compose assms continuous_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed

lemma holomorphic_on_moebius [holomorphic_intros]:
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "(moebius a b c d) holomorphic_on A"
  unfolding moebius_def
  by (intro holomorphic_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma holomorphic_on_moebius' [holomorphic_intros]:
  assumes "f holomorphic_on A" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "(\<lambda>x. moebius a b c d (f x)) holomorphic_on A"
proof -
  have "(moebius a b c d \<circ> f) holomorphic_on A" using assms
    by (intro holomorphic_on_compose assms holomorphic_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_moebius [analytic_intros]:
  assumes "c \<noteq> 0 \<or> d \<noteq> 0" "c = 0 \<or> -d / c \<notin> A"
  shows   "(moebius a b c d) analytic_on A"
  unfolding moebius_def
  by (intro analytic_intros) (use assms in \<open>auto simp: add_eq_0_iff\<close>)

lemma analytic_on_moebius' [analytic_intros]:
  assumes "f analytic_on A" "c \<noteq> 0 \<or> d \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> c = 0 \<or> f z \<noteq> -d / c"
  shows   "(\<lambda>x. moebius a b c d (f x)) analytic_on A"
proof -
  have "(moebius a b c d \<circ> f) analytic_on A" using assms
    by (intro analytic_on_compose assms analytic_on_moebius) force+
  thus ?thesis
    by (simp add: o_def)
qed


section \<open>Unimodular Transforms\<close>

locale unimodular_transform =
  fixes a b c d :: int
  assumes unimodular: "a * d - b * c = 1"
begin

definition \<phi> :: "complex \<Rightarrow> complex" where 
  "\<phi> = moebius (of_int a) (of_int b) (of_int c) (of_int d)"

lemma cnj_\<phi>: "\<phi> (cnj z) = cnj (\<phi> z)"
  by (simp add: moebius_def \<phi>_def)

lemma Im_transform:
  "Im (\<phi> z) = Im z / norm (of_int c * z + of_int d) ^ 2"
proof -
  have "Im (\<phi> z) = Im z * of_int (a * d - b * c) /
                   ((real_of_int c * Re z + real_of_int d)\<^sup>2 + (real_of_int c * Im z)\<^sup>2)"
    by (simp add: \<phi>_def moebius_def Im_divide algebra_simps)
  also have "a * d - b * c = 1"
    using unimodular by simp
  also have "((real_of_int c * Re z + real_of_int d)\<^sup>2 + (real_of_int c * Im z)\<^sup>2) =
             norm (of_int c * z + of_int d) ^ 2"
    unfolding cmod_power2 by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis
    by simp
qed

lemma Im_transform_pos_aux:
  assumes "Im z \<noteq> 0"
  shows   "of_int c * z + of_int d \<noteq> 0"
proof (cases "c = 0")
  case False
  hence "Im (of_int c * z + of_int d) \<noteq> 0"
    using assms by auto
  moreover have "Im 0 = 0"
    by simp
  ultimately show ?thesis
    by metis
next
  case True
  thus ?thesis using unimodular
    by auto
qed

lemma Im_transform_pos: "Im z > 0 \<Longrightarrow> Im (\<phi> z) > 0"
  using Im_transform_pos_aux[of z] by (auto simp: Im_transform)

lemma Im_transform_neg: "Im z < 0 \<Longrightarrow> Im (\<phi> z) < 0"
  using Im_transform_pos[of "cnj z"] by (simp add: cnj_\<phi>)

lemma Im_transform_zero_iff [simp]: "Im (\<phi> z) = 0 \<longleftrightarrow> Im z = 0"
  using Im_transform_pos_aux[of z] by (auto simp: Im_transform)

lemma Im_transform_pos_iff [simp]: "Im (\<phi> z) > 0 \<longleftrightarrow> Im z > 0"
  using Im_transform_pos[of z] Im_transform_neg[of z] Im_transform_zero_iff[of z]
  by (cases "Im z" "0 :: real" rule: linorder_cases) (auto simp del: Im_transform_zero_iff)

lemma Im_transform_neg_iff [simp]: "Im (\<phi> z) < 0 \<longleftrightarrow> Im z < 0"
  using Im_transform_pos_iff[of "cnj z"] by (simp add: cnj_\<phi>)

lemma Im_transform_nonneg_iff [simp]: "Im (\<phi> z) \<ge> 0 \<longleftrightarrow> Im z \<ge> 0"
  using Im_transform_neg_iff[of z] by linarith

lemma Im_transform_nonpos_iff [simp]: "Im (\<phi> z) \<le> 0 \<longleftrightarrow> Im z \<le> 0"
  using Im_transform_pos_iff[of z] by linarith  

lemma transform_in_reals_iff [simp]: "\<phi> z \<in> \<real> \<longleftrightarrow> z \<in> \<real>"
  using Im_transform_zero_iff[of z] by (auto simp: complex_is_Real_iff)

end


lemma Im_one_over_neg_iff [simp]: "Im (1 / z) < 0 \<longleftrightarrow> Im z > 0"
proof -
  interpret unimodular_transform 0 1 "-1" 0
    by standard auto
  show ?thesis
    using Im_transform_pos_iff[of z] by (simp add: \<phi>_def moebius_def)
qed


locale inverse_unimodular_transform = unimodular_transform
begin

sublocale inv: unimodular_transform d "-b" "-c" a
  by unfold_locales (use unimodular in Groebner_Basis.algebra)

lemma inv_\<phi>:
  assumes "of_int c * z + of_int d \<noteq> 0"
  shows   "inv.\<phi> (\<phi> z) = z"
  using unimodular assms
  unfolding inv.\<phi>_def \<phi>_def of_int_minus
  by (subst moebius_inverse) (auto simp flip: of_int_mult)

lemma inv_\<phi>':
  assumes "of_int c * z - of_int a \<noteq> 0"
  shows   "\<phi> (inv.\<phi> z) = z"
  using unimodular assms
  unfolding inv.\<phi>_def \<phi>_def of_int_minus
  by (subst moebius_inverse') (auto simp flip: of_int_mult)

end


section \<open>The modular group\<close>

subsection \<open>Definition\<close>

definition modgrp_rel :: "int \<times> int \<times> int \<times> int \<Rightarrow> int \<times> int \<times> int \<times> int \<Rightarrow> bool" where
  "modgrp_rel =
     (\<lambda>(a,b,c,d) (a',b',c',d'). a * d - b * c = 1 \<and>
                                ((a,b,c,d) = (a',b',c',d') \<or> (a,b,c,d) = (-a',-b',-c',-d')))"

lemma modgrp_rel_same_iff: "modgrp_rel x x \<longleftrightarrow> (case x of (a,b,c,d) \<Rightarrow> a * d - b * c = 1)"
  by (auto simp: modgrp_rel_def)

lemma part_equivp_modgrp_rel: "part_equivp modgrp_rel"
  unfolding part_equivp_def
proof safe
  show "\<exists>x. modgrp_rel x x"
    by (rule exI[of _ "(1,0,0,1)"]) (auto simp: modgrp_rel_def)
qed (auto simp: modgrp_rel_def case_prod_unfold fun_eq_iff)
       

quotient_type modgrp = "int \<times> int \<times> int \<times> int" / partial: modgrp_rel
  by (fact part_equivp_modgrp_rel)

instantiation modgrp :: one
begin

lift_definition one_modgrp :: modgrp is "(1, 0, 0, 1)"
  by (auto simp: modgrp_rel_def)

instance ..
end


instantiation modgrp :: times
begin

lift_definition times_modgrp :: "modgrp \<Rightarrow> modgrp \<Rightarrow> modgrp"
  is "\<lambda>(a,b,c,d) (a',b',c',d'). (a * a' + b * c', a * b' + b * d', c * a' + d * c', c * b' + d * d')"
  unfolding modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv
  by (elim conjE disjE; intro conjI) (auto simp: algebra_simps)

instance ..
end


instantiation modgrp :: inverse
begin

lift_definition inverse_modgrp :: "modgrp \<Rightarrow> modgrp"
  is "\<lambda>(a, b, c, d). (d, -b, -c, a)"
  by (auto simp: modgrp_rel_def algebra_simps)

definition divide_modgrp :: "modgrp \<Rightarrow> modgrp \<Rightarrow> modgrp" where
  "divide_modgrp x y = x * inverse y"

instance ..

end


interpretation modgrp: Groups.group "(*) :: modgrp \<Rightarrow> _" 1 inverse
proof
  show "a * b * c = a * (b * c :: modgrp)" for a b c
    by (transfer; unfold modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv;
        intro conjI; elim conjE disjE)
       (auto simp: algebra_simps)
next
  show "1 * a = a" for a :: modgrp
    by transfer (auto simp: modgrp_rel_def)
next
  show "inverse a * a = 1" for a :: modgrp
    by (transfer; unfold modgrp_rel_def case_prod_unfold prod_eq_iff fst_conv snd_conv;
        intro conjI; elim conjE disjE)
       (auto simp: algebra_simps)
qed    


instance modgrp :: monoid_mult
  by standard (simp_all add: modgrp.assoc)

lemma inverse_power_modgrp: "inverse (x ^ n :: modgrp) = inverse x ^ n"
  by (induction n) (simp_all add: algebra_simps modgrp.inverse_distrib_swap power_commuting_commutes)



subsection \<open>Basic operations\<close>

text \<open>Application to a field\<close>
lift_definition apply_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d). moebius (of_int a) (of_int b) (of_int c) (of_int d)"
  by (auto simp: modgrp_rel_def)

text \<open>The shift operation \<open>z \<mapsto> z + n\<close>\<close>
lift_definition shift_modgrp :: "int \<Rightarrow> modgrp" is "\<lambda>n. (1, n, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The shift operation \<open>z \<mapsto> z + 1\<close>\<close>
lift_definition T_modgrp :: modgrp is "(1, 1, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The operation $z \mapsto -\frac{1}{z}$\<close>
lift_definition S_modgrp :: modgrp is "(0, -1, 1, 0)"
  by transfer (auto simp: modgrp_rel_def)

text \<open>Whether or not the transformation has a pole in the complex plane\<close>
lift_definition is_singular_modgrp :: "modgrp \<Rightarrow> bool" is "\<lambda>(a,b,c,d). c \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def)

text \<open>The position of the transformation's pole in the complex plane (if it has one)\<close>
lift_definition pole_modgrp :: "modgrp \<Rightarrow> 'a :: field" is "\<lambda>(a,b,c,d). -of_int d / of_int c"
  by transfer (auto simp: modgrp_rel_def)

lemma pole_modgrp_in_Reals: "pole_modgrp f \<in> (\<real> :: 'a :: {real_field, field} set)"
  by transfer (auto intro!: Reals_divide)

lemma Im_pole_modgrp [simp]: "Im (pole_modgrp f) = 0"
  by transfer auto

text \<open>
  The complex number to which complex infinity is mapped by the transformation.
  This is undefined if the transformation maps complex infinity to itself.
\<close>
lift_definition pole_image_modgrp :: "modgrp \<Rightarrow> 'a :: field" is "\<lambda>(a,b,c,d). of_int a / of_int c"
  by transfer (auto simp: modgrp_rel_def)

lemma Im_pole_image_modgrp [simp]: "Im (pole_image_modgrp f) = 0"
  by transfer auto

text \<open>
  The normalised coefficients of the transformation. The convention that is chosen is that
  \<open>a\<close> is always non-negative, and if \<open>a\<close> is zero then \<open>b\<close> is positive.
\<close>
lift_definition modgrp_a :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -a else a"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_b :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -b else b"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_c :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). \<bar>c\<bar>"
  by transfer (auto simp: modgrp_rel_def)

lift_definition modgrp_d :: "modgrp \<Rightarrow> int" is "\<lambda>(a,b,c,d). if c < 0 \<or> c = 0 \<and> d < 0 then -d else d"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_abcd_S [simp]:
  "modgrp_a S_modgrp = 0" "modgrp_b S_modgrp = -1" "modgrp_c S_modgrp = 1" "modgrp_d S_modgrp = 0"
  by (transfer; simp)+

lemma modgrp_abcd_T [simp]:
  "modgrp_a T_modgrp = 1" "modgrp_b T_modgrp = 1" "modgrp_c T_modgrp = 0" "modgrp_d T_modgrp = 1"
  by (transfer; simp)+

lemma modgrp_abcd_shift [simp]:
  "modgrp_a (shift_modgrp n) = 1" "modgrp_b (shift_modgrp n) = n"
  "modgrp_c (shift_modgrp n) = 0" "modgrp_d (shift_modgrp n) = 1"
  by (transfer; simp)+

lemma modgrp_abcd_det: "modgrp_a x * modgrp_d x - modgrp_b x * modgrp_c x = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_c_nonneg: "modgrp_c x \<ge> 0"
  by transfer auto

lemma modgrp_a_nz_or_b_nz: "modgrp_a x \<noteq> 0 \<or> modgrp_b x \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma modgrp_c_nz_or_d_nz: "modgrp_c x \<noteq> 0 \<or> modgrp_d x \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma modgrp_cd_signs: "modgrp_c x > 0 \<or> modgrp_c x = 0 \<and> modgrp_d x > 0"
  by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

text \<open>
  Converting a quadruple of numbers into an element of the modular group.
\<close>
lift_definition modgrp :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> modgrp" is
  "\<lambda>a b c d. if a * d - b * c = 1 then (a, b, c, d) else (1, 0, 0, 1)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_wrong: "a * d - b * c \<noteq> 1 \<Longrightarrow> modgrp a b c d = 1"
  by transfer (auto simp: modgrp_rel_def algebra_simps)

lemma modgrp_cong:
  assumes "modgrp_rel (a,b,c,d) (a',b',c',d')"
  shows   "modgrp a b c d = modgrp a' b' c' d'"
  using assms by transfer (auto simp add: modgrp_rel_def)

lemma modgrp_abcd [simp]: "modgrp (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = x"
  apply transfer
  apply (auto split: if_splits)
        apply (auto simp: modgrp_rel_def)
  done

lemma
  assumes "a * d - b * c = 1"
  shows   modgrp_c_modgrp: "modgrp_c (modgrp a b c d) = \<bar>c\<bar>"
    and   modgrp_a_modgrp: "modgrp_a (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -a else a)"
    and   modgrp_b_modgrp: "modgrp_b (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -b else b)"
    and   modgrp_d_modgrp: "modgrp_d (modgrp a b c d) = (if c < 0 \<or> c = 0 \<and> d < 0 then -d else d)"
  using assms by (transfer; simp add: modgrp_rel_def)+


subsection \<open>Basic properties\<close>

lemma continuous_on_apply_modgrp [continuous_intros]:
  fixes g :: "'a :: topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes "continuous_on A g" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "continuous_on A (\<lambda>z. apply_modgrp f (g z))"
  using assms
  by transfer (auto intro!: continuous_intros simp: modgrp_rel_def)

lemma holomorphic_on_apply_modgrp [holomorphic_intros]:
  assumes "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "(\<lambda>z. apply_modgrp f (g z)) holomorphic_on A"
  using assms
  by transfer (auto intro!: holomorphic_intros simp: modgrp_rel_def)

lemma analytic_on_apply_modgrp [analytic_intros]:
  assumes "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> \<not>is_singular_modgrp f \<or> g z \<noteq> pole_modgrp f"
  shows   "(\<lambda>z. apply_modgrp f (g z)) analytic_on A"
  using assms
  by transfer (auto intro!: analytic_intros simp: modgrp_rel_def)

lemma isCont_apply_modgrp [continuous_intros]:
  fixes z :: "'a :: real_normed_field"
  assumes "\<not>is_singular_modgrp f \<or> z \<noteq> pole_modgrp f"
  shows   "isCont (apply_modgrp f) z"
proof -
  define S where "S = (if is_singular_modgrp f then -{pole_modgrp f} else (UNIV :: 'a set))"
  have "continuous_on S (apply_modgrp f)"
    unfolding S_def by (intro continuous_intros) auto
  moreover have "open S" "z \<in> S"
    using assms by (auto simp: S_def)
  ultimately show ?thesis
    using continuous_on_eq_continuous_at by blast
qed

lemmas tendsto_apply_modgrp [tendsto_intros] = isCont_tendsto_compose[OF isCont_apply_modgrp]

lift_definition diff_scale_factor_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d) w z. (of_int c * w + of_int d) * (of_int c * z + of_int d)"
  by (auto simp: modgrp_rel_def algebra_simps)

lemma diff_scale_factor_modgrp_commutes:
  "diff_scale_factor_modgrp f w z = diff_scale_factor_modgrp f z w"
  by transfer (simp add: case_prod_unfold)

lemma diff_scale_factor_modgrp_zero_iff:
  fixes w z :: "'a :: field_char_0"
  shows "diff_scale_factor_modgrp f w z = 0 \<longleftrightarrow> is_singular_modgrp f \<and> pole_modgrp f \<in> {w, z}"
  by transfer
     (auto simp: case_prod_unfold modgrp_rel_def divide_simps add_eq_0_iff mult.commute 
                    minus_equation_iff[of "of_int x" for x])

lemma apply_modgrp_diff_eq:
  fixes g :: modgrp
  defines "f \<equiv> apply_modgrp g"
  assumes *: "\<not>is_singular_modgrp g \<or> pole_modgrp g \<notin> {w, z}"
  shows   "f w - f z = (w - z) / diff_scale_factor_modgrp g w z"
  unfolding f_def using *
  by transfer
     (auto simp: modgrp_rel_def moebius_diff_eq zmult_eq_1_iff
           simp flip: of_int_diff of_int_mult split: if_splits)

lemma norm_modgrp_dividend_ge:
  fixes z :: complex
  shows   "norm (of_int c * z + of_int d) \<ge> \<bar>c * Im z\<bar>"
proof -
  define x y where "x = Re z" and "y = Im z"
  have z_eq: "z = Complex x y"
    by (simp add: x_def y_def)
  have "(real_of_int c * y) ^ 2 \<le> (real_of_int c * x + real_of_int d) ^ 2 + (real_of_int c * y) ^ 2"
    by simp
  also have "\<dots> = norm (of_int c * z + of_int d) ^ 2"
    by (simp add: cmod_power2 x_def y_def)
  finally show "norm (of_int c * z + of_int d) \<ge> \<bar>c * y\<bar>"
    by (metis abs_le_square_iff abs_norm_cancel)
qed

lemma diff_scale_factor_modgrp_altdef:
  fixes g :: modgrp
  defines "c \<equiv> modgrp_c g" and "d \<equiv> modgrp_d g"
  shows "diff_scale_factor_modgrp g w z = (of_int c * w + of_int d) * (of_int c * z + of_int d)"
  unfolding c_def d_def by transfer (auto simp: algebra_simps)

lemma norm_diff_scale_factor_modgrp_ge_complex:
  fixes w z :: complex
  assumes "w \<noteq> z"
  shows   "norm (diff_scale_factor_modgrp g w z) \<ge> of_int (modgrp_c g) ^ 2 * \<bar>Im w * Im z\<bar>"
proof -
  have "norm (diff_scale_factor_modgrp g w z) \<ge>
        \<bar>of_int (modgrp_c g) * Im w\<bar> * \<bar>of_int (modgrp_c g) * Im z\<bar>"
    unfolding diff_scale_factor_modgrp_altdef norm_mult
    by (intro mult_mono norm_modgrp_dividend_ge) auto
  thus ?thesis
    by (simp add: algebra_simps abs_mult power2_eq_square)
qed

lemma apply_shift_modgrp [simp]: "apply_modgrp (shift_modgrp n) z = z + of_int n"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_T [simp]: "apply_modgrp T_modgrp z = z + 1"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_S [simp]: "apply_modgrp S_modgrp z = -1 / z"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_1 [simp]: "apply_modgrp 1 z = z"
  by transfer (auto simp: moebius_def)

lemma apply_modgrp_mult_aux:
  fixes z :: "'a :: field_char_0"
  assumes ns: "c' = 0 \<or> z \<noteq> -d' / c'"
  assumes det: "a * d - b * c = 1" "a' * d' - b' * c' = 1"
  shows   "moebius a b c d (moebius a' b' c' d' z) =
           moebius (a * a' + b * c') (a * b' + b * d')
                   (c * a' + d * c') (c * b' + d * d') z"
proof -
  have det': "c \<noteq> 0 \<or> d \<noteq> 0" "c' \<noteq> 0 \<or> d' \<noteq> 0"
    using det by auto
  from assms have nz: "c' * z + d' \<noteq> 0"
    by (auto simp add: divide_simps add_eq_0_iff split: if_splits)
  show ?thesis using det nz
    by (simp add: moebius_def divide_simps) (auto simp: algebra_simps)
qed

lemma apply_modgrp_mult:
  fixes z :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp y \<or> z \<noteq> pole_modgrp y"
  shows   "apply_modgrp (x * y) z = apply_modgrp x (apply_modgrp y z)"
  using assms
proof (transfer, goal_cases)
  case (1 y z x)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  obtain a' b' c' d' where [simp]: "y = (a', b', c', d')"
    using prod_cases4 by blast
  show ?case
    using apply_modgrp_mult_aux[of "of_int c'" z "of_int d'" "of_int a" "of_int d"
                                   "of_int b" "of_int c" "of_int a'" "of_int b'"] 1
    by (simp flip: of_int_mult of_int_add of_int_diff of_int_minus add: modgrp_rel_def)
qed

lemma is_singular_modgrp_altdef: "is_singular_modgrp x \<longleftrightarrow> modgrp_c x \<noteq> 0"
  by transfer (auto split: if_splits)

lemma not_is_singular_modgrpD:
  assumes "\<not>is_singular_modgrp x"
  shows   "x = shift_modgrp (sgn (modgrp_a x) * modgrp_b x)"
  using assms
proof (transfer, goal_cases)
  case (1 x)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  from 1 have [simp]: "c = 0"
    by auto
  from 1 have "a = 1 \<and> d = 1 \<or> a = -1 \<and> d = -1"
    by (auto simp: modgrp_rel_def zmult_eq_1_iff)
  thus ?case
    by (auto simp: modgrp_rel_def)
qed

lemma is_singular_modgrp_inverse [simp]: "is_singular_modgrp (inverse x) \<longleftrightarrow> is_singular_modgrp x"
  by transfer auto

lemma is_singular_modgrp_S_left_iff [simp]: "is_singular_modgrp (S_modgrp * f) \<longleftrightarrow> modgrp_a f \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_S_right_iff [simp]: "is_singular_modgrp (f * S_modgrp) \<longleftrightarrow> modgrp_d f \<noteq> 0"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_T_left_iff [simp]:
  "is_singular_modgrp (T_modgrp * f) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_T_right_iff [simp]:
  "is_singular_modgrp (f * T_modgrp) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_shift_left_iff [simp]:
  "is_singular_modgrp (shift_modgrp n * f) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma is_singular_modgrp_shift_right_iff [simp]:
  "is_singular_modgrp (f * shift_modgrp n) \<longleftrightarrow> is_singular_modgrp f"
  by transfer (auto simp: modgrp_rel_def split: if_splits)

lemma pole_modgrp_inverse [simp]: "pole_modgrp (inverse x) = pole_image_modgrp x"
  by transfer auto

lemma pole_image_modgrp_inverse [simp]: "pole_image_modgrp (inverse x) = pole_modgrp x"
  by transfer auto

lemma pole_image_modgrp_in_Reals: "pole_image_modgrp x \<in> (\<real> :: 'a :: {real_field, field} set)"
  by transfer (auto intro!: Reals_divide)

lemma apply_modgrp_inverse_eqI:
  fixes x y :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp f \<or> y \<noteq> pole_modgrp f" "apply_modgrp f y = x"
  shows   "apply_modgrp (inverse f) x = y"
proof -
  have "apply_modgrp (inverse f) x = apply_modgrp (inverse f * f) y"
    using assms by (subst apply_modgrp_mult) auto
  also have "\<dots> = y"
    by simp
  finally show ?thesis .
qed

lemma apply_modgrp_eq_iff [simp]:
  fixes x y :: "'a :: field_char_0"
  assumes "\<not>is_singular_modgrp f \<or> x \<noteq> pole_modgrp f \<and> y \<noteq> pole_modgrp f"
  shows   "apply_modgrp f x = apply_modgrp f y \<longleftrightarrow> x = y"
  using assms by (metis apply_modgrp_inverse_eqI)

lemma is_singular_modgrp_times_aux:
  assumes det: "a * d - b * c = 1" "a' * d' - b' * (c' :: int) = 1"
  shows   "(c * a' + d * c' \<noteq> 0) \<longleftrightarrow> ((c = 0 \<longrightarrow> c' \<noteq> 0) \<and> (c = 0 \<or> c' = 0 \<or> -d * c' \<noteq> a' * c))"
  using assms by Groebner_Basis.algebra

lemma is_singular_modgrp_times_iff:
   "is_singular_modgrp (x * y) \<longleftrightarrow>
      (is_singular_modgrp x \<or> is_singular_modgrp y) \<and>
      (\<not>is_singular_modgrp x \<or> \<not>is_singular_modgrp y \<or> pole_modgrp x \<noteq> (pole_image_modgrp y :: real))"
proof (transfer, goal_cases)
  case (1 x y)
  obtain a b c d where [simp]: "x = (a, b, c, d)"
    using prod_cases4 by blast
  obtain a' b' c' d' where [simp]: "y = (a', b', c', d')"
    using prod_cases4 by blast
  show ?case
    using is_singular_modgrp_times_aux[of a d b c a' d' b' c'] 1
    by (auto simp: modgrp_rel_def field_simps simp flip: of_int_mult of_int_add of_int_minus of_int_diff)
qed

lemma shift_modgrp_1: "shift_modgrp 1 = T_modgrp"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_eq_iff: "shift_modgrp n = shift_modgrp m \<longleftrightarrow> n = m"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_neq_S [simp]: "shift_modgrp n \<noteq> S_modgrp"
  by transfer (auto simp: modgrp_rel_def)

lemma S_neq_shift_modgrp [simp]: "S_modgrp \<noteq> shift_modgrp n"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_eq_T_iff [simp]: "shift_modgrp n = T_modgrp \<longleftrightarrow> n = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma T_eq_shift_modgrp_iff [simp]: "T_modgrp = shift_modgrp n \<longleftrightarrow> n = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_0 [simp]: "shift_modgrp 0 = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_add: "shift_modgrp (m + n) = shift_modgrp m * shift_modgrp n"
  by transfer (auto simp: modgrp_rel_def)

lemma shift_modgrp_minus: "shift_modgrp (-m) = inverse (shift_modgrp m)"
proof -
  have "1 = shift_modgrp (m + (-m))"
    by simp
  also have "shift_modgrp (m + (-m)) = shift_modgrp m * shift_modgrp (-m)"
    by (subst shift_modgrp_add) auto
  finally show ?thesis
    by (simp add: modgrp.inverse_unique)
qed

lemma shift_modgrp_power: "shift_modgrp n ^ m = shift_modgrp (n * m)"
  by (induction m) (auto simp: algebra_simps shift_modgrp_add)

lemma shift_modgrp_power_int: "shift_modgrp n powi m = shift_modgrp (n * m)"
  by (cases "m \<ge> 0")
     (auto simp: power_int_def shift_modgrp_power simp flip: shift_modgrp_minus)

lemma shift_shift_modgrp: "shift_modgrp n * (shift_modgrp m * x) = shift_modgrp (n + m) * x"
  by (simp add: mult.assoc shift_modgrp_add)


lemma shift_modgrp_conv_T_power: "shift_modgrp n = T_modgrp powi n"
  by (simp flip: shift_modgrp_1 add: shift_modgrp_power_int)

lemma modgrp_S_S [simp]: "S_modgrp * S_modgrp = 1"
  by transfer (auto simp: modgrp_rel_def)

lemma inverse_S_modgrp [simp]: "inverse S_modgrp = S_modgrp"
  using modgrp_S_S modgrp.inverse_unique by metis

lemma modgrp_S_S_' [simp]: "S_modgrp * (S_modgrp * x) = x"
  by (subst mult.assoc [symmetric], subst modgrp_S_S) simp

lemma modgrp_S_power: "S_modgrp ^ n = (if even n then 1 else S_modgrp)"
  by (induction n) auto

lemma modgrp_S_S_power_int: "S_modgrp powi n = (if even n then 1 else S_modgrp)"
  by (auto simp: power_int_def modgrp_S_power even_nat_iff)


lemma not_is_singular_1_modgrp [simp]: "\<not>is_singular_modgrp 1"
  by transfer auto

lemma not_is_singular_T_modgrp [simp]: "\<not>is_singular_modgrp T_modgrp"
  by transfer auto

lemma not_is_singular_shift_modgrp [simp]: "\<not>is_singular_modgrp (shift_modgrp n)"
  by transfer auto

lemma is_singular_S_modgrp [simp]: "is_singular_modgrp S_modgrp"
  by transfer auto

lemma pole_modgrp_S [simp]: "pole_modgrp S_modgrp = 0"
  by transfer auto

lemma pole_modgrp_1 [simp]: "pole_modgrp 1 = 0"
  by transfer auto

lemma pole_modgrp_T [simp]: "pole_modgrp T_modgrp = 0"
  by transfer auto

lemma pole_modgrp_shift [simp]: "pole_modgrp (shift_modgrp n) = 0"
  by transfer auto

lemma pole_image_modgrp_1 [simp]: "pole_image_modgrp 1 = 0"
  by transfer auto

lemma pole_image_modgrp_T [simp]: "pole_image_modgrp T_modgrp = 0"
  by transfer auto

lemma pole_image_modgrp_shift [simp]: "pole_image_modgrp (shift_modgrp n) = 0"
  by transfer auto

lemma pole_image_modgrp_S [simp]: "pole_image_modgrp S_modgrp = 0"
  by transfer auto

lemma minus_minus_power2_eq: "(-x - y :: 'a :: ring_1) ^ 2 = (x + y) ^ 2"
  by (simp add: algebra_simps power2_eq_square)

lift_definition deriv_modgrp :: "modgrp \<Rightarrow> 'a :: field \<Rightarrow> 'a" is
  "\<lambda>(a,b,c,d) x. inverse ((of_int c * x + of_int d) ^ 2)"
  by (auto simp: modgrp_rel_def minus_minus_power2_eq)

lemma deriv_modgrp_nonzero:
  assumes "\<not>is_singular_modgrp f \<or> (x :: 'a :: field_char_0) \<noteq> pole_modgrp f"
  shows   "deriv_modgrp f x \<noteq> 0"
  using assms
  by transfer (auto simp: modgrp_rel_def add_eq_0_iff split: if_splits)

lemma deriv_modgrp_altdef:
  "deriv_modgrp f z = inverse (of_int (modgrp_c f) * z + of_int (modgrp_d f)) ^ 2"
  by transfer (auto simp: minus_minus_power2_eq power_inverse)

lemma moebius_has_field_derivative:
  assumes "c = 0 \<or> x \<noteq> -d / c" "c \<noteq> 0 \<or> d \<noteq> 0"
  shows   "(moebius a b c d has_field_derivative (a * d - b * c) / (c * x + d) ^ 2) (at x within A)"
  unfolding moebius_def
  apply (rule derivative_eq_intros refl)+
  using assms
   apply (auto simp: divide_simps add_eq_0_iff power2_eq_square split: if_splits)
  apply (auto simp: algebra_simps)?
  done

lemma apply_modgrp_has_field_derivative [derivative_intros]:
  assumes "\<not>is_singular_modgrp f \<or> x \<noteq> pole_modgrp f"
  shows   "(apply_modgrp f has_field_derivative deriv_modgrp f x) (at x within A)"
  using assms
proof (transfer, goal_cases)
  case (1 f x A)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  have "(moebius (of_int a) (of_int b) (of_int c) (of_int d) has_field_derivative
           (of_int (a * d - b * c) / ((of_int c * x + of_int d)\<^sup>2)))
           (at x within A)"
    unfolding of_int_mult of_int_diff
    by (rule moebius_has_field_derivative) (use 1 in \<open>auto simp: modgrp_rel_def\<close>)
  also have "a * d - b * c = 1"
    using 1 by (simp add: modgrp_rel_def)
  finally show ?case
    by (simp add: field_simps)
qed

lemma apply_modgrp_has_field_derivative' [derivative_intros]:
  assumes "(g has_field_derivative g') (at x within A)"
  assumes "\<not>is_singular_modgrp f \<or> g x \<noteq> pole_modgrp f"
  shows   "((\<lambda>x. apply_modgrp f (g x)) has_field_derivative deriv_modgrp f (g x) * g')
              (at x within A)"
proof -
  have "((apply_modgrp f \<circ> g) has_field_derivative deriv_modgrp f (g x) * g') (at x within A)"
    by (intro DERIV_chain assms derivative_intros)
  thus ?thesis
    by (simp add: o_def)
qed


definition modgrp_factor :: "modgrp \<Rightarrow> complex \<Rightarrow> complex" where
  "modgrp_factor g z = of_int (modgrp_c g) * z + of_int (modgrp_d g)"

lemma modgrp_factor_shift [simp]: "modgrp_factor (shift_modgrp n) z = 1"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_T [simp]: "modgrp_factor T_modgrp z = 1"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_S [simp]: "modgrp_factor S_modgrp z = z"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_shift_right [simp]:
  "modgrp_factor (f * shift_modgrp n) z = modgrp_factor f (z + of_int n)"
  unfolding modgrp_factor_def
  by transfer (auto simp: algebra_simps)

lemma modgrp_c_shift_left [simp]:
  "modgrp_c (shift_modgrp n * f) = modgrp_c f"
  unfolding modgrp_factor_def by transfer auto

lemma modgrp_d_shift_left [simp]:
  "modgrp_d (shift_modgrp n * f) = modgrp_d f"
  unfolding modgrp_factor_def by transfer auto

lemma modgrp_factor_shift_left [simp]:
  "modgrp_factor (shift_modgrp n * f) z = modgrp_factor f z"
  by (simp add: modgrp_factor_def)

lemma modgrp_factor_T_right [simp]:
  "modgrp_factor (f * T_modgrp) z = modgrp_factor f (z + 1)"
  unfolding shift_modgrp_1 [symmetric] by (subst modgrp_factor_shift_right) auto

lemma modgrp_factor_T_left [simp]:
  "modgrp_factor (T_modgrp * f) z = modgrp_factor f z"
  unfolding shift_modgrp_1 [symmetric] by (subst modgrp_factor_shift_left) auto

lemma has_field_derivative_modgrp_factor [derivative_intros]:
  assumes "(f has_field_derivative f') (at x)"
  shows   "((\<lambda>x. modgrp_factor g (f x)) has_field_derivative (of_int (modgrp_c g) * f')) (at x)"
  unfolding modgrp_factor_def by (auto intro!: derivative_eq_intros assms)

lemma modgrp_factor_analytic [analytic_intros]: "modgrp_factor g analytic_on A"
  unfolding modgrp_factor_def by (auto simp: modgrp_factor_def intro!: analytic_intros)

lemma modgrp_factor_nonzero [simp]:
  assumes "Im z \<noteq> 0"
  shows   "modgrp_factor g z \<noteq> 0"
proof -
  define c d where "c = modgrp_c g" and "d = modgrp_d g"
  have "c \<noteq> 0 \<or> d \<noteq> 0"
    unfolding c_def d_def using modgrp_c_nz_or_d_nz by blast
  have "of_int c * z + of_int d \<noteq> 0"
    using assms \<open>c \<noteq> 0 \<or> d \<noteq> 0\<close> by (auto simp: complex_eq_iff)
  thus ?thesis
    by (simp add: modgrp_factor_def c_def d_def)
qed

lemma tendsto_modgrp_factor [tendsto_intros]:
  "(f \<longlongrightarrow> c) F \<Longrightarrow> ((\<lambda>x. modgrp_factor g (f x)) \<longlongrightarrow> modgrp_factor g c) F"
  unfolding modgrp_factor_def by (auto intro!: tendsto_intros)

lemma modgrp_a_1 [simp]: "modgrp_a 1 = 1"
  and modgrp_b_1 [simp]: "modgrp_b 1 = 0"
  and modgrp_c_1 [simp]: "modgrp_c 1 = 0"
  and modgrp_d_1 [simp]: "modgrp_d 1 = 1"
  by (transfer; simp; fail)+

lemma modgrp_factor_1 [simp]: "modgrp_factor 1 z = 1"
  by (auto simp: modgrp_factor_def)

lemma modgrp_c_0: 
  assumes "a * d = 1"
  shows   "modgrp a b 0 d = shift_modgrp (if a > 0 then b else -b)"
  using assms by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

lemma not_singular_modgrpD:
  assumes "\<not>is_singular_modgrp f"
  shows   "f = shift_modgrp (modgrp_b f)"
  using assms by transfer (auto simp: modgrp_rel_def zmult_eq_1_iff)

lemma S_conv_modgrp: "S_modgrp = modgrp 0 (-1) 1 0"
  and T_conv_modgrp: "T_modgrp = modgrp 1 1 0 1"
  and shift_conv_modgrp: "shift_modgrp n = modgrp 1 n 0 1"
  and one_conv_modgrp: "1 = modgrp 1 0 0 1"
  by (transfer; simp add: modgrp_rel_def)+

lemma modgrp_rel_reflI: "(case x of (a,b,c,d) \<Rightarrow> a * d - b * c = 1) \<Longrightarrow> x = y \<Longrightarrow> modgrp_rel x y"
  by (simp add: modgrp_rel_def case_prod_unfold)

lemma modgrp_times:
  assumes "a * d - b * c = 1"
  assumes "a' * d' - b' * c' = 1"
  shows "modgrp a b c d * modgrp a' b' c' d' =
         modgrp (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')"
  using assms by transfer (auto simp: modgrp_rel_def algebra_simps)

lemma modgrp_inverse:
  assumes "a * d - b * c = 1"
  shows   "inverse (modgrp a b c d) = modgrp d (-b) (-c) a"
  by (intro modgrp.inverse_unique, subst modgrp_times)
     (use assms in \<open>auto simp: algebra_simps one_conv_modgrp\<close>)

lemma apply_modgrp_altdef:
  "(apply_modgrp x :: 'a :: field \<Rightarrow> _) =
   moebius (of_int (modgrp_a x)) (of_int (modgrp_b x)) (of_int (modgrp_c x)) (of_int (modgrp_d x))"
proof (transfer, goal_cases)
  case (1 x)
  thus ?case
    by (auto simp: case_prod_unfold moebius_uminus')
qed

lemma modgrp_a_mult_shift [simp]: "modgrp_a (f * shift_modgrp m) = modgrp_a f"
  by transfer auto

lemma modgrp_b_mult_shift [simp]: "modgrp_b (f * shift_modgrp m) = modgrp_a f * m + modgrp_b f"
  by transfer auto

lemma modgrp_c_mult_shift [simp]: "modgrp_c (f * shift_modgrp m) = modgrp_c f"
  by transfer auto

lemma modgrp_d_mult_shift [simp]: "modgrp_d (f * shift_modgrp m) = modgrp_c f * m + modgrp_d f"
  by transfer auto

lemma coprime_modgrp_c_d: "coprime (modgrp_c f) (modgrp_d f)"
proof -
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have "[a * 0 - b * c = a * d - b * c] (mod d)"
    by (intro cong_diff cong_refl cong_mult) (auto simp: cong_def)
  also have "a * d - b * c = 1"
    unfolding a_b_c_d_def modgrp_abcd_det[of f] by simp
  finally have "[c * (-b) = 1] (mod d)"
    by (simp add: mult_ac)
  thus "coprime c d"
    by (subst coprime_iff_invertible_int) (auto intro!: exI[of _ "-b"])
qed

context unimodular_transform
begin

lift_definition as_modgrp :: modgrp is "(a, b, c, d)"
  using unimodular by (auto simp: modgrp_rel_def)

lemma as_modgrp_altdef: "as_modgrp = modgrp a b c d"
  using unimodular by transfer (auto simp: modgrp_rel_def)

lemma \<phi>_as_modgrp: "\<phi> = apply_modgrp as_modgrp"
  unfolding \<phi>_def by transfer simp

end

interpretation modgrp: unimodular_transform "modgrp_a x" "modgrp_b x" "modgrp_c x" "modgrp_d x"
  rewrites "modgrp.as_modgrp = x" and "modgrp.\<phi> = apply_modgrp x"
proof -
  show *: "unimodular_transform (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
    by unfold_locales (rule modgrp_abcd_det)
  show "unimodular_transform.as_modgrp (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = x"
    by (subst unimodular_transform.as_modgrp_altdef[OF *]) auto
  show "unimodular_transform.\<phi> (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x) = apply_modgrp x"
    by (subst unimodular_transform.\<phi>_def[OF *], subst apply_modgrp_altdef) auto
qed


subsection \<open>Writing an element of the modular group as a product of powers of generators\<close>

definition modgrp_from_gens :: "int option list \<Rightarrow> modgrp" where
  "modgrp_from_gens xs = prod_list (map (\<lambda>x. case x of None \<Rightarrow> S_modgrp | Some n \<Rightarrow> shift_modgrp n) xs)"

lemma modgrp_from_gens_Nil [simp]:
        "modgrp_from_gens [] = 1"
  and modgrp_from_gens_append [simp]:
        "modgrp_from_gens (xs @ ys) = modgrp_from_gens xs * modgrp_from_gens ys"
  and modgrp_from_gens_Cons1 [simp]:
        "modgrp_from_gens (None # xs) = S_modgrp * modgrp_from_gens xs"
  and modgrp_from_gens_Cons2 [simp]:
        "modgrp_from_gens (Some n # xs) = shift_modgrp n * modgrp_from_gens xs"
  and modgrp_from_gens_Cons:
        "modgrp_from_gens (x # xs) =
            (case x of None \<Rightarrow> S_modgrp | Some n \<Rightarrow> shift_modgrp n) * modgrp_from_gens xs"
  by (simp_all add: modgrp_from_gens_def)

definition invert_modgrp_gens :: "int option list \<Rightarrow> int option list"
  where "invert_modgrp_gens = rev \<circ> map (map_option uminus)"

lemma invert_modgrp_gens_Nil [simp]:
        "invert_modgrp_gens [] = []"
  and invert_modgrp_gens_append [simp]:
        "invert_modgrp_gens (xs @ ys) = invert_modgrp_gens ys @ invert_modgrp_gens xs"
  and invert_modgrp_gens_Cons1 [simp]:
        "invert_modgrp_gens (None # xs) = invert_modgrp_gens xs @ [None]"
  and invert_modgrp_gens_Cons2 [simp]:
        "invert_modgrp_gens (Some n # xs) = invert_modgrp_gens xs @ [Some (-n)]"
  and invert_modgrp_gens_Cons:
        "invert_modgrp_gens (x # xs) = invert_modgrp_gens xs @ [map_option uminus x]"
  by (simp_all add: invert_modgrp_gens_def)

lemma modgrp_from_gens_invert [simp]:
  "modgrp_from_gens (invert_modgrp_gens xs) = inverse (modgrp_from_gens xs)"
  by (induction xs)
     (auto simp: invert_modgrp_gens_Cons map_option_case algebra_simps 
                 modgrp.inverse_distrib_swap shift_modgrp_minus split: option.splits)

function modgrp_genseq :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int option list" where
  "modgrp_genseq a b c d =
     (if c = 0 then let b' = (if a > 0 then b else -b) in [Some b']
      else modgrp_genseq (-a * (d div c) + b) (-a) (d mod c) (-c) @ [None, Some (d div c)])"
  by auto
termination
  by (relation "Wellfounded.measure (nat \<circ> abs \<circ> (\<lambda>(_,_,c,_) \<Rightarrow> c))") (auto simp: abs_mod_less)

lemmas [simp del] = modgrp_genseq.simps

lemma modgrp_genseq_c_0: "modgrp_genseq a b 0 d = (let b' = (if a > 0 then b else -b) in [Some b'])"
  and modgrp_genseq_c_nz:
        "c \<noteq> 0 \<Longrightarrow> modgrp_genseq a b c d =
           (let q = d div c in modgrp_genseq (-a * q + b) (-a) (d mod c) (-c) @ [None, Some q])"
  by (subst modgrp_genseq.simps; simp add: Let_def)+  

lemma modgrp_genseq_code [code]:
  "modgrp_genseq a b c d =
     (if c = 0 then [Some (if a > 0 then b else -b)]
      else (let q = d div c in modgrp_genseq (-a * q + b) (-a) (d mod c) (-c) @ [None, Some q]))"
  by (subst modgrp_genseq.simps) (auto simp: Let_def)

lemma modgrp_genseq_correct:
  assumes "a * d - b * c = 1"
  shows   "modgrp_from_gens (modgrp_genseq a b c d) = modgrp a b c d"
  using assms
proof (induction a b c d rule: modgrp_genseq.induct)
  case (1 a b c d)
  write S_modgrp ("S")
  write shift_modgrp ("T")

  show ?case
  proof (cases "c = 0")
    case [simp]: True
    thus ?thesis using 1
      by (auto simp: modgrp_genseq_c_0 modgrp_c_0)
  next
    case False
    define q r where "q = d div c" and "r = d mod c"
    have "q * c + r = d"
      by (simp add: q_def r_def)
    with \<open>a * d - b * c = 1\<close> have det': "a * r - (b - a * q) * c = 1"
      by Groebner_Basis.algebra

    have "modgrp_from_gens (modgrp_genseq a b c d) = modgrp (-a * q + b) (-a) r (-c) * (S * T q)"
      using False "1.IH" det' by (simp add: modgrp_genseq_c_nz Let_def q_def r_def)
    also have "S * T q = modgrp 0 (- 1) 1 q"
      unfolding S_conv_modgrp shift_conv_modgrp by (subst modgrp_times) simp_all
    also have "modgrp (-a * q + b) (-a) r (-c) * \<dots> = modgrp (- a) (- b) (- c) (-r - c * q)"
      using det' by (subst modgrp_times) simp_all
    also have "\<dots> = modgrp a b c (q * c + r)"
      using det' by (intro modgrp_cong) (auto simp: algebra_simps modgrp_rel_def)
    also have "q * c + r = d"
      by (simp add: q_def r_def)
    finally show ?thesis .
  qed
qed

lemma filterlim_apply_modgrp_at:
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "filterlim (apply_modgrp g) (at (apply_modgrp g z)) (at (z :: 'a :: real_normed_field))"
proof -
  have "\<forall>\<^sub>F x in at z. x \<in> (if is_singular_modgrp g then -{pole_modgrp g} else UNIV) - {z}"
    by (intro eventually_at_in_open) (use assms in auto)
  hence "\<forall>\<^sub>F x in at z. apply_modgrp g x \<noteq> apply_modgrp g z"
    by eventually_elim (use assms in \<open>auto split: if_splits\<close>)
  thus ?thesis
    using assms by (auto simp: filterlim_at intro!: tendsto_eq_intros)
qed

lemma apply_modgrp_neq_pole_image [simp]:
  "is_singular_modgrp g \<Longrightarrow> z \<noteq> pole_modgrp g \<Longrightarrow>
     apply_modgrp g (z :: 'a :: field_char_0) \<noteq> pole_image_modgrp g"
  by transfer (auto simp: field_simps add_eq_0_iff moebius_def modgrp_rel_def
                    simp flip: of_int_add of_int_mult of_int_diff)

lemma image_apply_modgrp_conv_vimage:
  fixes A :: "'a :: field_char_0 set"
  assumes "\<not>is_singular_modgrp f \<or> pole_modgrp f \<notin> A"
  defines "S \<equiv> (if is_singular_modgrp f then -{pole_image_modgrp f :: 'a} else UNIV)"
  shows   "apply_modgrp f ` A = apply_modgrp (inverse f) -` A \<inter> S"
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> (apply_modgrp (inverse f) -` A) \<inter> S"
  thus "z \<in> apply_modgrp f ` A" using assms
    by (auto elim!: rev_image_eqI simp flip: apply_modgrp_mult simp: S_def split: if_splits)
next
  fix z assume z: "z \<in> apply_modgrp f ` A"
  then obtain x where x: "x \<in> A" "z = apply_modgrp f x"
    by auto
  have "apply_modgrp (inverse f) (apply_modgrp f x) \<in> A"
    using x assms by (subst apply_modgrp_mult [symmetric]) auto
  moreover have "apply_modgrp f x \<noteq> pole_image_modgrp f" if "is_singular_modgrp f"
    using x assms that by (intro apply_modgrp_neq_pole_image) auto
  ultimately show "z \<in> (apply_modgrp (inverse f) -` A) \<inter> S"
    using x by (auto simp: S_def)
qed

lemma apply_modgrp_open_map:
  fixes A :: "'a :: real_normed_field set"
  assumes "open A" "\<not>is_singular_modgrp f \<or> pole_modgrp f \<notin> A"
  shows   "open (apply_modgrp f ` A)"
proof -
  define S :: "'a set" where "S = (if is_singular_modgrp f then -{pole_image_modgrp f} else UNIV)"
  have "open S"
    by (auto simp: S_def)
  have "apply_modgrp f ` A = apply_modgrp (inverse f) -` A \<inter> S"
    using image_apply_modgrp_conv_vimage[of f A] assms by (auto simp: S_def)
  also have "apply_modgrp (inverse f) -` A \<inter> S = S \<inter> apply_modgrp (inverse f) -` A"
    by (simp only: Int_commute)
  also have "open \<dots>"
    using assms by (intro continuous_open_preimage continuous_intros assms \<open>open S\<close>)
                   (auto simp: S_def)
  finally show ?thesis .
qed

lemma filtermap_at_apply_modgrp:
  fixes z :: "'a :: real_normed_field"
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "filtermap (apply_modgrp g) (at z) = at (apply_modgrp g z)"
proof (rule filtermap_fun_inverse)
  show "filterlim (apply_modgrp g) (at (apply_modgrp g z)) (at z)"
    using assms by (intro filterlim_apply_modgrp_at) auto
next
  have "filterlim (apply_modgrp (inverse g)) (at (apply_modgrp (inverse g) (apply_modgrp g z)))
           (at (apply_modgrp g z))"
    using assms by (intro filterlim_apply_modgrp_at) auto
  also have "apply_modgrp (inverse g) (apply_modgrp g z) = z"
    using assms by (simp flip: apply_modgrp_mult)
  finally show "filterlim (apply_modgrp (inverse g)) (at z) (at (apply_modgrp g z))" .
next
  have "eventually (\<lambda>x. x \<in> (if is_singular_modgrp g then -{pole_image_modgrp g} else UNIV))
           (at (apply_modgrp g z))"
    by (intro eventually_at_in_open') (use assms in auto)
  thus "\<forall>\<^sub>F x in at (apply_modgrp g z). apply_modgrp g (apply_modgrp (inverse g) x) = x"
    by eventually_elim (auto simp flip: apply_modgrp_mult split: if_splits)
qed

lemma zorder_moebius_zero:
  assumes "a \<noteq> 0" "a * d - b * c \<noteq> 0"
  shows   "zorder (moebius a b c d) (-b / a) = 1"
proof (rule zorder_eqI)
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define A where "A = (if c = 0 then UNIV else -{-d/c})"
  show "open A"
    by (auto simp: A_def)
  show "-b/a \<in> A"
    using assms by (auto simp: A_def field_simps)
  show "(\<lambda>x. a / (c * x + d)) holomorphic_on A"
  proof (intro holomorphic_intros)
    fix x assume "x \<in> A"
    thus "c * x + d \<noteq> 0"
      unfolding A_def using assms
      by (auto simp: A_def field_simps add_eq_0_iff split: if_splits)
  qed
  show "a / (c * (-b / a) + d) \<noteq> 0"
    using assms by (auto simp: field_simps)
  show "moebius a b c d w = a / (c * w + d) * (w - - b / a) powi 1"
    if "w \<in> (if c = 0 then UNIV else - {- d / c})" "w \<noteq> - b / a" for w
    using that assms by (auto simp: divide_simps moebius_def split: if_splits)
qed

lemma zorder_moebius_pole:
  assumes "c \<noteq> 0" "a * d - b * c \<noteq> 0"
  shows   "zorder (moebius a b c d) (-d / c) = -1"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  have "zorder (moebius a b c d) (-d / c) =
          zorder (\<lambda>x. (a * x + b) / c / (x - (-d / c)) ^ 1) (-d / c)"
  proof (rule zorder_cong)
    have "eventually (\<lambda>z. z \<noteq> -d/c) (at (-d/c))"
      by (simp add: eventually_neq_at_within)
    thus "\<forall>\<^sub>F z in at (- d / c). moebius a b c d z = (a * z + b) / c / (z - - d / c) ^ 1"
      by eventually_elim (use assms in \<open>auto simp: moebius_def divide_simps mult_ac\<close>)
  qed auto
  also have "zorder (\<lambda>x. (a * x + b) / c / (x - (-d / c)) ^ 1) (-d / c) = -int 1"
  proof (rule zorder_nonzero_div_power)
    show "(\<lambda>w. (a * w + b) / c) holomorphic_on UNIV"
      using assms by (intro holomorphic_intros)
    show "(a * (-d / c) + b) / c \<noteq> 0"
      using assms by (auto simp: field_simps)
  qed auto
  finally show ?thesis by simp
qed

lemma zorder_moebius:
  assumes "c = 0 \<or> z \<noteq> -d / c" "a * d - b * c \<noteq> 0"
  shows   "zorder (\<lambda>x. moebius a b c d x - moebius a b c d z) z = 1"
proof (rule zorder_eqI)
  define S where "S = (if c = 0 then UNIV else -{-d/c})"
  define g where "g = (\<lambda>w. (a * d - b * c) / ((c * w + d) * (c * z + d)))"
  show "open S" "z \<in> S"
    using assms by (auto simp: S_def)
  show "g holomorphic_on S"
    unfolding g_def using assms
    by (intro holomorphic_intros no_zero_divisors)
       (auto simp: S_def field_simps add_eq_0_iff split: if_splits)
  show "(a * d - b * c) / ((c * z + d) * (c * z + d)) \<noteq> 0"
    using assms by (auto simp: add_eq_0_iff split: if_splits)
  show "moebius a b c d w - moebius a b c d z =
         (a * d - b * c) / ((c * w + d) * (c * z + d)) * (w - z) powi 1" if "w \<in> S" for w
    by (subst moebius_diff_eq) (use that assms in \<open>auto simp: S_def split: if_splits\<close>)
qed

lemma zorder_apply_modgrp:
  assumes "\<not>is_singular_modgrp g \<or> z \<noteq> pole_modgrp g"
  shows   "zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z = 1"
  using assms
proof (transfer, goal_cases)
  case (1 f z)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  show ?case using 1 zorder_moebius[of c z d a b]
    by (auto simp: modgrp_rel_def simp flip: of_int_mult)
qed

lemma zorder_fls_modgrp_pole:
  assumes "is_singular_modgrp f"
  shows   "zorder (apply_modgrp f) (pole_modgrp f) = -1"
  using assms
proof (transfer, goal_cases)
  case (1 f)
  obtain a b c d where [simp]: "f = (a, b, c, d)"
    using prod_cases4 .
  show ?case using 1 zorder_moebius_pole[of c a d b]
    by (auto simp: modgrp_rel_def simp flip: of_int_mult)
qed


subsection \<open>Induction rules in terms of generators\<close>

text \<open>Theorem 2.1\<close>
lemma modgrp_induct_S_shift [case_names id S shift]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (S_modgrp * x)"
          "\<And>x n. P x \<Longrightarrow> P (shift_modgrp n * x)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have "P (modgrp_from_gens xs)"
    by (induction xs) (auto intro: assms simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct [case_names id S T inv_T]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (S_modgrp * x)"
          "\<And>x. P x \<Longrightarrow> P (T_modgrp * x)"
          "\<And>x. P x \<Longrightarrow> P (inverse T_modgrp * x)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have *: "P (T_modgrp ^ n * x)" if "P x" for n x
    by (induction n) (auto simp: mult.assoc shift_modgrp_1 intro: assms that)
  have **: "P (inverse T_modgrp ^ n * x)" if "P x" for n x
    by (induction n) (auto simp: shift_modgrp_add mult.assoc shift_modgrp_1 intro: assms that) 
  have ***: "P (shift_modgrp n * x)" if "P x" for n x
    using *[of x "nat n"] **[of x "nat (-n)"] that
    by (auto simp: shift_modgrp_conv_T_power power_int_def)
  have "P (modgrp_from_gens xs)"
    by (induction xs) (auto intro: assms *** simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct_S_shift' [case_names id S shift]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (x * S_modgrp)"
          "\<And>x n. P x \<Longrightarrow> P (x * shift_modgrp n)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have "P (modgrp_from_gens xs)"
    by (induction xs rule: rev_induct) (auto intro: assms simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma modgrp_induct' [case_names id S T inv_T]:
  assumes "P 1"
          "\<And>x. P x \<Longrightarrow> P (x * S_modgrp)"
          "\<And>x. P x \<Longrightarrow> P (x * T_modgrp)"
          "\<And>x. P x \<Longrightarrow> P (x * inverse T_modgrp)"
  shows   "P x"
proof -
  define xs where "xs = modgrp_genseq (modgrp_a x) (modgrp_b x) (modgrp_c x) (modgrp_d x)"
  have *: "P (x * T_modgrp ^ n)" if "P x" for n x
    using assms(3)[of "x * T_modgrp ^ n" for n]
    by (induction n)  (auto intro: that simp: algebra_simps power_commuting_commutes)
  have **: "P (x * inverse T_modgrp ^ n)" if "P x" for n x
    using assms(4)[of "x * inverse T_modgrp ^ n" for n]
    by (induction n) (auto intro: that simp: algebra_simps power_commuting_commutes) 
  have ***: "P (x * shift_modgrp n)" if "P x" for n x
    using *[of x "nat n"] **[of x "nat (-n)"] that
    by (auto simp: shift_modgrp_conv_T_power power_int_def)
  have "P (modgrp_from_gens xs)"
    by (induction xs rule: rev_induct)
       (auto intro: assms *** simp: modgrp_from_gens_Cons split: option.splits)
  thus ?thesis using modgrp_abcd_det[of x]
    by (simp add: xs_def modgrp_genseq_correct)
qed

lemma moebius_uminus1: "moebius (-a) b c d = moebius a (-b) (-c) (-d)"
  by (auto simp add: moebius_def fun_eq_iff divide_simps) (auto simp: algebra_simps add_eq_0_iff)

lemma moebius_shift:
  "moebius a b c d (z + of_int n) = moebius a (a * of_int n + b) c (c * of_int n + d) z"
  by (simp add: moebius_def algebra_simps)

lemma moebius_eq_shift: "moebius 1 (of_int n) 0 1 z = z + of_int n"
  by (simp add: moebius_def)

lemma moebius_S:
  assumes "a * d - b * c \<noteq> 0" "z \<noteq> 0"
  shows   "moebius a b c d (-(1 / z)) = moebius b (- a) d (- c) (z :: 'a :: field)"
  using assms by (auto simp: divide_simps moebius_def)

lemma moebius_eq_S: "moebius 0 1 (-1) 0 z = -1 / z"
  by (simp add: moebius_def)


section \<open>Code generation\<close>

code_datatype modgrp

lemma one_modgrp_code [code]:   "1 = modgrp 1 0 0 1"
  and S_modgrp_code [code]:     "S_modgrp = modgrp 0 (-1) 1 0"
  and T_modgrp_code [code]:     "T_modgrp = modgrp 1 1 0 1"
  and shift_modgrp_code [code]: "shift_modgrp n = modgrp 1 n 0 1"
  by (simp_all add: one_conv_modgrp S_conv_modgrp T_conv_modgrp shift_conv_modgrp)

lemma inverse_modgrp_code [code]: "inverse (modgrp a b c d) = modgrp d (-b) (-c) a"
  by (cases "a * d - b * c = 1")
     (auto simp: modgrp_inverse modgrp_wrong algebra_simps)

lemma times_modgrp_code [code]:
  "modgrp a b c d * modgrp a' b' c' d' = (
     if a * d - b * c \<noteq> 1 then modgrp a' b' c' d'
     else if a' * d' - b' * c' \<noteq> 1 then modgrp a b c d
     else  modgrp (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d'))"
  by (simp add: modgrp_times modgrp_wrong)

lemma modgrp_a_code [code]:
  "modgrp_a (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -a else a else 1)"
  by transfer auto

lemma modgrp_b_code [code]:
  "modgrp_b (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -b else b else 0)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_c_code [code]:
  "modgrp_c (modgrp a b c d) = (if a * d - b * c = 1 then \<bar>c\<bar> else 0)"
  by transfer (auto simp: modgrp_rel_def)

lemma modgrp_d_code [code]:
  "modgrp_d (modgrp a b c d) = (if a * d - b * c = 1 then if c < 0 \<or> c = 0 \<and> d < 0 then -d else d else 1)"
  by transfer auto

lemma apply_modgrp_code [code]:
  "apply_modgrp (modgrp a b c d) z =
     (if a * d - b * c \<noteq> 1 then z else (of_int a * z + of_int b) / (of_int c * z + of_int d))"
  by transfer (auto simp: moebius_def)

lemma is_singular_modgrp_code [code]:
  "is_singular_modgrp (modgrp a b c d) \<longleftrightarrow> a * d - b * c = 1 \<and> c \<noteq> 0"
  by transfer auto

lemma pole_modgrp_code [code]:
  "pole_modgrp (modgrp a b c d) = (if a * d - b * c = 1 then -of_int d / of_int c else 0)"
  by transfer auto

lemma pole_image_modgrp_code [code]:
  "pole_image_modgrp (modgrp a b c d) =
    (if a * d - b * c = 1 \<and> c \<noteq> 0 then of_int a / of_int c else 0)"
  by transfer auto


section \<open>Subgroups\<close>

locale modgrp_subgroup =
  fixes G :: "modgrp set"
  assumes one_in_G [simp, intro]: "1 \<in> G"
  assumes times_in_G [simp, intro]: "x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> x * y \<in> G"
  assumes inverse_in_G [simp, intro]: "x \<in> G \<Longrightarrow> inverse x \<in> G"
begin

lemma divide_in_G [intro]: "f \<in> G \<Longrightarrow> g \<in> G \<Longrightarrow> f / g \<in> G"
  unfolding divide_modgrp_def by (intro times_in_G inverse_in_G)

lemma power_in_G [intro]: "f \<in> G \<Longrightarrow> f ^ n \<in> G"
  by (induction n) auto

lemma power_int_in_G [intro]: "f \<in> G \<Longrightarrow> f powi n \<in> G"
  by (auto simp: power_int_def)

lemma prod_list_in_G [intro]: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> G) \<Longrightarrow> prod_list xs \<in> G"
  by (induction xs) auto

lemma inverse_in_G_iff [simp]: "inverse f \<in> G \<longleftrightarrow> f \<in> G"
  by (metis inverse_in_G modgrp.inverse_inverse)

definition rel :: "complex \<Rightarrow> complex \<Rightarrow> bool" where
  "rel x y \<longleftrightarrow> Im x > 0 \<and> Im y > 0 \<and> (\<exists>f\<in>G. apply_modgrp f x = y)"

definition orbit :: "complex \<Rightarrow> complex set" where
  "orbit x = {y. rel x y}"

lemma Im_nonpos_imp_not_rel: "Im x \<le> 0 \<or> Im y \<le> 0 \<Longrightarrow> \<not>rel x y"
  by (auto simp: rel_def)

lemma orbit_empty: "Im x \<le> 0 \<Longrightarrow> orbit x = {}"
  by (auto simp: orbit_def Im_nonpos_imp_not_rel)

lemma rel_imp_Im_pos [dest]:
  assumes "rel x y"
  shows   "Im x > 0" "Im y > 0"
  using assms by (auto simp: rel_def)

lemma rel_refl [simp]: "rel x x \<longleftrightarrow> Im x > 0"
  by (auto simp: rel_def intro!: bexI[of _ 1])

lemma rel_sym:
  assumes "rel x y"
  shows   "rel y x"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from this have "apply_modgrp (inverse f) y = x"
    using pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (intro apply_modgrp_inverse_eqI) (auto simp: complex_is_Real_iff)
  moreover have "inverse f \<in> G"
    using f by auto
  ultimately show ?thesis
    using f by (auto simp: rel_def)
qed

lemma rel_commutes: "rel x y = rel y x"
  using rel_sym by blast

lemma rel_trans [trans]:
  assumes "rel x y" "rel y z"
  shows   "rel x z"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from assms obtain g where g: "Im z > 0" "g \<in> G" "apply_modgrp g y = z"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  have "apply_modgrp (g * f) x = z"
    using f g pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (subst apply_modgrp_mult) (auto simp: complex_is_Real_iff)
  with f g show ?thesis
    unfolding rel_def by blast
qed

lemma relI1 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel x (apply_modgrp f y)"
  using modgrp.Im_transform_pos_iff rel_def rel_trans by blast

lemma relI2 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel (apply_modgrp f x) y"
  by (meson relI1 rel_commutes rel_def)

lemma rel_apply_modgrp_left_iff [simp]:
  assumes "f \<in> G"
  shows   "rel (apply_modgrp f x) y \<longleftrightarrow> Im x > 0 \<and> rel x y"
proof safe
  assume "rel (apply_modgrp f x) y"
  thus "rel x y"
    by (meson assms modgrp.Im_transform_pos_iff rel_def rel_trans)
next
  assume "rel x y" "Im x > 0"
  thus "rel (apply_modgrp f x) y"
    by (meson assms relI2 rel_trans)
qed auto

lemma rel_apply_modgrp_right_iff [simp]:
  assumes "f \<in> G"
  shows   "rel y (apply_modgrp f x) \<longleftrightarrow> Im x > 0 \<and> rel y x"
  using assms by (metis rel_apply_modgrp_left_iff rel_sym)

lemma orbit_refl_iff: "x \<in> orbit x \<longleftrightarrow> Im x > 0"
  by (auto simp: orbit_def)

lemma orbit_refl: "Im x > 0 \<Longrightarrow> x \<in> orbit x"
  by (auto simp: orbit_def)

lemma orbit_cong: "rel x y \<Longrightarrow> orbit x = orbit y"
  using rel_trans rel_commutes unfolding orbit_def by blast

lemma orbit_empty_iff [simp]: "orbit x = {} \<longleftrightarrow> Im x \<le> 0" "{} = orbit x \<longleftrightarrow> Im x \<le> 0"
  using orbit_refl orbit_empty by force+

lemmas [simp] = orbit_refl_iff

lemma orbit_eq_iff: "orbit x = orbit y \<longleftrightarrow> Im x \<le> 0 \<and> Im y \<le> 0 \<or> rel x y"
  (* TODO cleanup *)
  apply (cases "Im y \<le> 0"; cases "Im x \<le> 0")
     apply (simp_all add: orbit_empty orbit_empty_iff)
    apply (auto simp: not_le)
  using orbit_def apply fastforce
  using orbit_cong apply blast+
  done 

lemma orbit_apply_modgrp [simp]: "f \<in> G \<Longrightarrow> orbit (apply_modgrp f z) = orbit z"
  by (subst orbit_eq_iff) auto  

lemma apply_modgrp_in_orbit_iff [simp]: "f \<in> G \<Longrightarrow> apply_modgrp f z \<in> orbit y \<longleftrightarrow> z \<in> orbit y"
  by (auto simp: orbit_def rel_commutes)

lemma orbit_imp_Im_pos: "x \<in> orbit y \<Longrightarrow> Im x > 0"
  by (auto simp: orbit_def)

end

interpretation modular_group: modgrp_subgroup UNIV
  by unfold_locales auto

notation modular_group.rel (infixl "\<sim>\<^sub>\<Gamma>" 49)

lemma (in modgrp_subgroup) rel_imp_rel: "rel x y \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y"
  unfolding rel_def modular_group.rel_def by auto

lemma modular_group_rel_plus_int_iff_right1 [simp]:
  assumes "z \<in> \<int>"
  shows   "x \<sim>\<^sub>\<Gamma> y + z \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  from assms obtain n where n: "z = of_int n"
    by (elim Ints_cases)
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp (shift_modgrp n) y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by (simp add: n)
qed

lemma
  assumes "z \<in> \<int>"
  shows   modular_group_rel_plus_int_iff_right2 [simp]: "x \<sim>\<^sub>\<Gamma> z + y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left1 [simp]:  "z + x \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left2 [simp]:  "x + z \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_plus_int_iff_right1[OF assms] modular_group.rel_commutes add.commute
  by metis+

lemma modular_group_rel_S_iff_right [simp]: "x \<sim>\<^sub>\<Gamma> -(1/y) \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp S_modgrp y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by simp
qed

lemma modular_group_rel_S_iff_left [simp]: "-(1/x) \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_S_iff_right[of y x] by (metis modular_group.rel_commutes)


subsection \<open>Subgroups containing shifts\<close>

definition modgrp_subgroup_period :: "modgrp set \<Rightarrow> nat" where
  "modgrp_subgroup_period G = nat (Gcd {n. shift_modgrp n \<in> G})"

lemma of_nat_modgrp_subgroup_period:
  "of_nat (modgrp_subgroup_period G) = Gcd {n. shift_modgrp n \<in> G}"
  unfolding modgrp_subgroup_period_def by simp

(* TODO: Move to distribution *)
lemma ideal_int_conv_Gcd:
  fixes A :: "int set"
  assumes "0 \<in> A"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x + y \<in> A"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> x * y \<in> A"
  shows   "A = {n. Gcd A dvd n}"
proof
  show "A \<subseteq> {n. Gcd A dvd n}"
    by auto
next
  have "Gcd A \<in> A"
  proof (cases "A = {0}")
    case False
    define x :: int where "x = int (LEAST x. int x \<in> A \<and> x > 0)"
    have ex: "\<exists>x. int x \<in> A \<and> x > 0"
    proof -
      from False obtain x where "x \<in> A - {0}"
        using assms(1) by auto
      with assms(3)[of x "-1"] show ?thesis
        by (intro exI[of _ "if x > 0 then nat x else nat (-x)"]) auto
    qed
    have x: "x \<in> A \<and> x > 0"
      unfolding x_def using LeastI_ex[OF ex] by auto
    have x': "x \<le> y" if y: "y \<in> A" "y > 0" for y
      using y unfolding x_def
      by (metis of_nat_le_iff wellorder_Least_lemma(2) zero_less_imp_eq_int)
    have "x dvd Gcd A"
    proof (rule Gcd_greatest)
      fix y assume y: "y \<in> A"
      have "y = (y div x) * x + (y mod x)"
        by simp
      have "y + x * (-1) * (y div x) \<in> A"
        by (intro assms) (use x y in auto)
      also have "y + x * (-1) * (y div x) = y mod x"
        by (simp add: algebra_simps)
      finally have "y mod x \<in> A" .
      moreover have "y mod x \<ge> 0" "y mod x < x"
        using x by simp_all
      ultimately have "y mod x = 0"
        using x'[of "y mod x"] by (cases "y mod x = 0") auto
      thus "x dvd y"
        by presburger
    qed
    thus "Gcd A \<in> A"
      using assms(3) x by (auto elim!: dvdE)
  qed auto
  thus "{n. Gcd A dvd n} \<subseteq> A"
    by (auto elim!: dvdE intro!: assms)
qed


locale modgrp_subgroup_periodic = modgrp_subgroup +
  assumes periodic': "\<exists>n>0. shift_modgrp n \<in> G"
begin

lemma modgrp_subgroup_period_pos: "modgrp_subgroup_period G > 0"
proof -
  have "Gcd {n. shift_modgrp n \<in> G} \<noteq> 0"
    using periodic' by (auto intro!: Nat.gr0I simp: Gcd_0_iff)
  moreover have "Gcd {n. shift_modgrp n \<in> G} \<ge> 0"
    by simp
  ultimately show ?thesis
    unfolding modgrp_subgroup_period_def by linarith
qed

lemma shift_modgrp_in_G_iff: "shift_modgrp n \<in> G \<longleftrightarrow> int (modgrp_subgroup_period G) dvd n"
proof -
  let ?A = "{n. shift_modgrp n \<in> G}"
  have "?A = {n. int (modgrp_subgroup_period G) dvd n}"
    unfolding of_nat_modgrp_subgroup_period
    by (rule ideal_int_conv_Gcd) (auto simp: shift_modgrp_add simp flip: shift_modgrp_power_int)
  thus ?thesis
    by auto
qed

lemma shift_modgrp_in_G_period [intro, simp]:
  "shift_modgrp (int (modgrp_subgroup_period G)) \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

lemma shift_modgrp_in_G [intro]:
  "int (modgrp_subgroup_period G) dvd n \<Longrightarrow> shift_modgrp n \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

end

interpretation modular_group: modgrp_subgroup_periodic UNIV
  rewrites "modgrp_subgroup_period UNIV = Suc 0"
  by unfold_locales (auto intro: exI[of _ 1] simp: modgrp_subgroup_period_def)

lemma modgrp_subgroup_period_UNIV [simp]: "modgrp_subgroup_period UNIV = Suc 0"
  by (simp add: modgrp_subgroup_period_def)

subsection \<open>Fundamental regions\<close>

subsubsection \<open>Definition\<close>

locale fundamental_region = modgrp_subgroup +
  fixes R :: "complex set"
  assumes "open": "open R"
  assumes subset: "R \<subseteq> {z. Im z > 0}"
  assumes unique: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> rel x y \<Longrightarrow> x = y"
  assumes equiv_in_closure: "\<And>x. Im x > 0 \<Longrightarrow> \<exists>y\<in>closure R. rel x y "
begin

text \<open>The uniqueness property can be extended to the closure of \<open>R\<close>:\<close>
lemma unique':
  assumes "x \<in> R" "y \<in> closure R" "rel x y" "Im y > 0"
  shows   "x = y"
proof (cases "y \<in> R")
  case False
  show ?thesis
  proof (rule ccontr)
    assume xy: "x \<noteq> y"
    from assms have "rel y x"
      by (simp add: rel_commutes)
    then obtain f where f: "x = apply_modgrp f y" "f \<in> G"
      unfolding rel_def by blast
  
    have "continuous_on {z. Im z > 0} (apply_modgrp f)"
      by (intro continuous_intros) auto
    hence "isCont (apply_modgrp f) y"
      using open_halfspace_Im_gt[of 0] assms continuous_on_eq_continuous_at by blast
    hence lim: "apply_modgrp f \<midarrow>y\<rightarrow> x"
      using f by (simp add: isCont_def)

    define \<epsilon> where "\<epsilon> = dist x y / 2"
    have \<epsilon>: "\<epsilon> > 0"
      using xy by (auto simp: \<epsilon>_def)

    have "eventually (\<lambda>w. w \<in> ball x \<epsilon> \<inter> R) (nhds x)"
      by (intro eventually_nhds_in_open) (use assms \<epsilon> "open" in auto)
    from this and lim have "eventually (\<lambda>z. apply_modgrp f z \<in> ball x \<epsilon> \<inter> R) (at y)"
      by (rule eventually_compose_filterlim)
    moreover have "eventually (\<lambda>z. z \<in> ball y \<epsilon>) (nhds y)"
      using assms \<epsilon> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>z. z \<in> ball y \<epsilon>) (at y)"
      unfolding eventually_at_filter by eventually_elim auto
    ultimately have "eventually (\<lambda>z. z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) (at y)"
      by eventually_elim auto
    moreover have "y islimpt R"
      using \<open>y \<in> closure R\<close> \<open>y \<notin> R\<close> by (auto simp: closure_def)
    hence "frequently (\<lambda>z. z \<in> R) (at y)"
      using islimpt_conv_frequently_at by blast
    ultimately have "frequently (\<lambda>z.
                        (z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) \<and> z \<in> R) (at y)"
      by (intro frequently_eventually_conj)
    hence "frequently (\<lambda>z. False) (at y)"
    proof (rule frequently_elim1)
      fix z assume z: "(z \<in> ball y \<epsilon> \<and> apply_modgrp f z \<in> R \<inter> ball x \<epsilon>) \<and> z \<in> R"
      have "ball y \<epsilon> \<inter> ball x \<epsilon> = {}"
        by (intro disjoint_ballI) (auto simp: \<epsilon>_def dist_commute)
      with z have "apply_modgrp f z \<noteq> z"
        by auto
      with z f subset show False
        using unique[of z "apply_modgrp f z"] by auto
    qed
    thus False
      by simp
  qed
qed (use assms unique in auto)

lemma
  pole_modgrp_not_in_region [simp]: "pole_modgrp f \<notin> R" and
  pole_image_modgrp_not_in_region [simp]: "pole_image_modgrp f \<notin> R"
  using subset by force+


end


subsubsection \<open>The standard fundamental region for \<open>\<Gamma>\<close>\<close>

text \<open>
  The standard fundamental region \<open>\<R>\<^sub>\<Gamma>\<close> consists of all the points \<open>z\<close> in the upper half plane
  with \<open>|z| > 1\<close> and $\text{Re}(z) \leq \frac{1}{2}$.
\<close>
definition std_fund_region :: "complex set" ("\<R>\<^sub>\<Gamma>") where
  "\<R>\<^sub>\<Gamma> = -cball 0 1 \<inter> Re -` {-1/2<..<1/2} \<inter> {z. Im z > 0}"

text \<open>
  The following version of \<open>\<R>\<^sub>\<Gamma>\<close> is what Apostol refers to as the closure of \<open>\<R>\<^sub>\<Gamma>\<close>, but it is
  actually only part of the closure: since each point at the border of the fundamental region
  is equivalent to its mirror image w.r.t.\ the \<open>Im(z) = 0\<close> axis, we only want one of these copies
  to be in \<open>\<R>\<^sub>\<Gamma>'\<close>, and we choose the left one.

  So \<open>\<R>\<^sub>\<Gamma>'\<close> is actually \<open>\<R>\<^sub>\<Gamma>\<close> plus all the points on the left border plus all points on the
  left half of the semicircle.
\<close>
definition std_fund_region' :: "complex set" ("\<R>\<^sub>\<Gamma>''") where
  "\<R>\<^sub>\<Gamma>' = \<R>\<^sub>\<Gamma> \<union> (-ball 0 1 \<inter> Re -` {-1/2..0} \<inter> {z. Im z > 0})"

lemma std_fund_region_altdef:
  "\<R>\<^sub>\<Gamma> = {z. norm z > 1 \<and> norm (z + cnj z) < 1 \<and> Im z > 0}"
  by (auto simp: std_fund_region_def complex_add_cnj)

lemma in_std_fund_region_iff:
  "z \<in> \<R>\<^sub>\<Gamma> \<longleftrightarrow> norm z > 1 \<and> Re z \<in> {-1/2<..<1/2} \<and> Im z > 0"
  by (auto simp: std_fund_region_def field_simps)

lemma in_std_fund_region'_iff:
  "z \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> Im z > 0 \<and> ((norm z > 1 \<and> Re z \<in> {-1/2..<1/2}) \<or> (norm z = 1 \<and> Re z \<in> {-1/2..0}))"
  by (auto simp: std_fund_region'_def std_fund_region_def field_simps)

lemma open_std_fund_region [simp, intro]: "open \<R>\<^sub>\<Gamma>"
  unfolding std_fund_region_def
  by (intro open_Int open_vimage continuous_intros open_halfspace_Im_gt) auto

lemma Im_std_fund_region: "z \<in> \<R>\<^sub>\<Gamma> \<Longrightarrow> Im z > 0"
  by (auto simp: std_fund_region_def)

subsubsection \<open>The closure of the standard fundamental region\<close>

context
  fixes S S' :: "(real \<times> real) set" and T :: "complex set"
  fixes f :: "real \<times> real \<Rightarrow> complex" and g :: "complex \<Rightarrow> real \<times> real"
  defines "f \<equiv> (\<lambda>(x,y). Complex x (y + sqrt (1 - x ^ 2)))"
  defines "g \<equiv> (\<lambda>z. (Re z, Im z - sqrt (1 - Re z ^ 2)))"
  defines "S \<equiv> ({-1/2<..<1/2} \<times> {0<..})"
  defines "S' \<equiv> ({-1/2..1/2} \<times> {0..})"
  defines "T \<equiv> {z. norm z \<ge> 1 \<and> Re z \<in> {-1/2..1/2} \<and> Im z \<ge> 0}"
begin

lemma image_subset_std_fund_region: "f ` S \<subseteq> \<R>\<^sub>\<Gamma>"
  unfolding subset_iff in_std_fund_region_iff S_def
proof safe
  fix a b :: real
  assume ab: "a \<in> {-1/2<..<1/2}" "b > 0"
  have "\<bar>a\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using ab by (intro power_mono) auto
  hence "a ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "a ^ 2 \<le> 1"
    by simp

  show "Im (f (a, b)) > 0"
    using ab \<open>a ^ 2 \<le> 1 / 4\<close> by (auto simp: f_def intro: add_pos_nonneg)

  show "Re (f (a, b)) \<in> {-1/2<..<1/2}"
    using ab by (simp add: f_def)

  have "1 ^ 2 = a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2"
    using \<open>a ^ 2 \<le> 1 / 4\<close> by (simp add: power2_eq_square algebra_simps)
  also have "a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2 < a\<^sup>2 + (b + sqrt (1 - a\<^sup>2)) ^ 2"
    using ab \<open>a ^ 2 \<le> 1\<close> by (intro add_strict_left_mono power2_mono power2_strict_mono) auto
  also have "\<dots> = norm (f (a, b)) ^ 2"
    by (simp add: f_def norm_complex_def)
  finally show "norm (f (a, b)) > 1"
    by (rule power2_less_imp_less) auto
qed

lemma image_std_fund_region_subset: "g ` \<R>\<^sub>\<Gamma> \<subseteq> S"
  unfolding subset_iff g_def S_def
proof safe
  fix z :: complex
  assume "z \<in> \<R>\<^sub>\<Gamma>"
  hence z: "norm z > 1" "Re z \<in> {-1/2<..<1/2}" "Im z > 0"
    by (auto simp: in_std_fund_region_iff)

  have "\<bar>Re z\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using z by (intro power_mono) auto
  hence "Re z ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "Re z ^ 2 \<le> 1"
    by simp

  from z show "Re z \<in> {- 1 / 2<..<1 / 2}"
    by auto

  have "sqrt (1 - Re z ^ 2) ^ 2 = 1 - Re z ^ 2"
    using \<open>Re z ^ 2 \<le> 1\<close> by simp
  also have "\<dots> < Im z ^ 2"
    using z by (simp add: norm_complex_def algebra_simps)
  finally have "sqrt (1 - Re z ^ 2) < Im z"
    by (rule power2_less_imp_less) (use z in auto)
  thus "Im z - sqrt (1 - Re z ^ 2) > 0"
    by simp
qed

lemma std_fund_region_map_inverses: "f (g x) = x" "g (f y) = y"
  by (simp_all add: f_def g_def case_prod_unfold)

lemma bij_betw_std_fund_region1: "bij_betw f S \<R>\<^sub>\<Gamma>"
  using image_std_fund_region_subset image_subset_std_fund_region
  by (intro bij_betwI[of _ _ _ g]) (auto simp: std_fund_region_map_inverses)

lemma bij_betw_std_fund_region2: "bij_betw g \<R>\<^sub>\<Gamma> S"
  using image_std_fund_region_subset image_subset_std_fund_region
  by (intro bij_betwI[of _ _ _ f]) (auto simp: std_fund_region_map_inverses)

lemma image_subset_std_fund_region': "f ` S' \<subseteq> T"
  unfolding subset_iff S'_def T_def
proof safe
  fix a b :: real
  assume ab: "a \<in> {-1/2..1/2}" "b \<ge> 0"
  have "\<bar>a\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using ab by (intro power_mono) auto
  hence "a ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "a ^ 2 \<le> 1"
    by simp

  show "Im (f (a, b)) \<ge> 0"
    using ab \<open>a ^ 2 \<le> 1 / 4\<close> by (auto simp: f_def intro: add_pos_nonneg)

  show "Re (f (a, b)) \<in> {-1/2..1/2}"
    using ab by (simp add: f_def)

  have "1 ^ 2 = a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2"
    using \<open>a ^ 2 \<le> 1 / 4\<close> by (simp add: power2_eq_square algebra_simps)
  also have "a\<^sup>2 + (0 + sqrt (1 - a\<^sup>2)) ^ 2 \<le> a\<^sup>2 + (b + sqrt (1 - a\<^sup>2)) ^ 2"
    using ab \<open>a ^ 2 \<le> 1\<close> by (intro add_left_mono power2_mono power2_strict_mono) auto
  also have "\<dots> = norm (f (a, b)) ^ 2"
    by (simp add: f_def norm_complex_def)
  finally show "norm (f (a, b)) \<ge> 1"
    by (rule power2_le_imp_le) auto
qed

lemma image_std_fund_region_subset': "g ` T \<subseteq> S'"
  unfolding subset_iff g_def S'_def
proof safe
  fix z :: complex
  assume "z \<in> T"
  hence z: "norm z \<ge> 1" "Re z \<in> {-1/2..1/2}" "Im z \<ge> 0"
    by (auto simp: T_def)

  have "\<bar>Re z\<bar> ^ 2 \<le> (1 / 2) ^ 2"
    using z by (intro power_mono) auto
  hence "Re z ^ 2 \<le> 1 / 4"
    by (simp add: power2_eq_square)
  hence "Re z ^ 2 \<le> 1"
    by simp

  from z show "Re z \<in> {-1/2..1/2}"
    by auto

  have "sqrt (1 - Re z ^ 2) ^ 2 = 1 - Re z ^ 2"
    using \<open>Re z ^ 2 \<le> 1\<close> by simp
  also have "\<dots> \<le> Im z ^ 2"
    using z by (simp add: norm_complex_def algebra_simps)
  finally have "sqrt (1 - Re z ^ 2) \<le> Im z"
    by (rule power2_le_imp_le) (use z in auto)
  thus "Im z - sqrt (1 - Re z ^ 2) \<ge> 0"
    by simp
qed

lemma bij_betw_std_fund_region1': "bij_betw f S' T"
  using image_std_fund_region_subset' image_subset_std_fund_region'
  by (intro bij_betwI[of _ _ _ g]) (auto simp: std_fund_region_map_inverses)

lemma bij_betw_std_fund_region2': "bij_betw g T S'"
  using image_std_fund_region_subset' image_subset_std_fund_region'
  by (intro bij_betwI[of _ _ _ f]) (auto simp: std_fund_region_map_inverses)

theorem closure_std_fund_region: "closure \<R>\<^sub>\<Gamma> = T"
proof -
  have homeo: "homeomorphism S \<R>\<^sub>\<Gamma> f g"
    using image_std_fund_region_subset image_subset_std_fund_region
    by (intro homeomorphismI)
       (auto simp: g_def f_def case_prod_unfold intro!: continuous_intros)

  have "closure \<R>\<^sub>\<Gamma> = closure (f ` S)"
    using bij_betw_std_fund_region1 by (simp add: bij_betw_def)
  also have "\<dots> = f ` closure S"
    using bij_betw_std_fund_region1 homeo
  proof (rule closure_bij_homeomorphic_image_eq)
    show "continuous_on UNIV f" "continuous_on UNIV g"
      by (auto simp: f_def g_def case_prod_unfold intro!: continuous_intros)
  qed (auto simp: std_fund_region_map_inverses)
  also have "closure S = {-1 / 2..1 / 2} \<times> {0..}"
    by (simp add: S_def closure_Times)
  also have "\<dots> = S'"
    by (simp add: S'_def)
  also have "f ` S' = T"
    using bij_betw_std_fund_region1' by (simp add: bij_betw_def)
  finally show ?thesis .
qed

lemma in_closure_std_fund_region_iff:
  "x \<in> closure \<R>\<^sub>\<Gamma> \<longleftrightarrow> norm x \<ge> 1 \<and> Re x \<in> {-1/2..1/2} \<and> Im x \<ge> 0"
  by (simp add: closure_std_fund_region T_def)

lemma frontier_std_fund_region:
  "frontier \<R>\<^sub>\<Gamma> =
     {z. norm z \<ge> 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> = 1 / 2} \<union>
     {z. norm z = 1 \<and> Im z > 0 \<and> \<bar>Re z\<bar> \<le> 1 / 2}" (is "_ = ?rhs")
proof -
  have [simp]: "x ^ 2 \<ge> 1 \<longleftrightarrow> x \<ge> 1 \<or> x \<le> -1" for x :: real
    using abs_le_square_iff[of 1 x] by auto
  have "frontier \<R>\<^sub>\<Gamma> = closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>"
    unfolding frontier_def by (subst interior_open) simp_all
  also have "\<dots> = ?rhs"
    unfolding closure_std_fund_region unfolding std_fund_region_def
    by (auto simp: cmod_def T_def)
  finally show ?thesis .
qed

lemma std_fund_region'_subset_closure: "\<R>\<^sub>\<Gamma>' \<subseteq> closure \<R>\<^sub>\<Gamma>"
  by (auto simp: in_std_fund_region'_iff in_closure_std_fund_region_iff)

lemma std_fund_region'_superset: "\<R>\<^sub>\<Gamma> \<subseteq> \<R>\<^sub>\<Gamma>'"
  by (auto simp: in_std_fund_region'_iff in_std_fund_region_iff)

lemma in_std_fund_region'_not_on_frontier_iff:
  assumes "z \<notin> frontier \<R>\<^sub>\<Gamma>"
  shows   "z \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> z \<in> \<R>\<^sub>\<Gamma>"
proof
  assume "z \<in> \<R>\<^sub>\<Gamma>'"
  hence "z \<in> closure \<R>\<^sub>\<Gamma>"
    using std_fund_region'_subset_closure by blast
  thus "z \<in> \<R>\<^sub>\<Gamma>"
    using assms by (auto simp: frontier_def interior_open)
qed (use std_fund_region'_superset in auto)

lemma simply_connected_std_fund_region: "simply_connected \<R>\<^sub>\<Gamma>"
proof (rule simply_connected_retraction_gen)
  show "simply_connected S"
    unfolding S_def by (intro convex_imp_simply_connected convex_Times) auto
  show "continuous_on S f"
    unfolding f_def S_def case_prod_unfold by (intro continuous_intros)
  show "continuous_on \<R>\<^sub>\<Gamma> g"
    unfolding g_def case_prod_unfold by (intro continuous_intros)
  show "f ` S = \<R>\<^sub>\<Gamma>"
    using bij_betw_std_fund_region1 by (simp add: bij_betw_def)
  show "g \<in> \<R>\<^sub>\<Gamma> \<rightarrow> S"
    using bij_betw_std_fund_region2 bij_betw_imp_funcset by blast
  show "f (g x) = x" for x
    by (simp add: f_def g_def)
qed

lemma simply_connected_closure_std_fund_region: "simply_connected (closure \<R>\<^sub>\<Gamma>)"
proof (rule simply_connected_retraction_gen)
  show "simply_connected S'"
    unfolding S'_def by (intro convex_imp_simply_connected convex_Times) auto
  show "continuous_on S' f"
    unfolding f_def S'_def case_prod_unfold by (intro continuous_intros)
  show "continuous_on (closure \<R>\<^sub>\<Gamma>) g"
    unfolding g_def case_prod_unfold by (intro continuous_intros)
  show "f ` S' = closure \<R>\<^sub>\<Gamma>"
    using bij_betw_std_fund_region1' by (simp add: bij_betw_def closure_std_fund_region)
  show "g \<in> closure \<R>\<^sub>\<Gamma> \<rightarrow> S'"
    using bij_betw_std_fund_region2' bij_betw_imp_funcset closure_std_fund_region by blast
  show "f (g x) = x" for x
    by (simp add: f_def g_def)
qed

lemma std_fund_region'_subset: "\<R>\<^sub>\<Gamma>' \<subseteq> closure \<R>\<^sub>\<Gamma>"
  unfolding std_fund_region'_def closure_std_fund_region T_def unfolding std_fund_region_def
  by auto

lemma closure_std_fund_region_Im_pos: "closure \<R>\<^sub>\<Gamma> \<subseteq> {z. Im z > 0}"
  unfolding closure_std_fund_region
  by (auto intro!: neq_le_trans simp: norm_complex_def field_simps power2_ge_1_iff T_def)

lemma closure_std_fund_region_Im_ge: "closure \<R>\<^sub>\<Gamma> \<subseteq> {z. Im z \<ge> sqrt 3 / 2}"
proof
  fix z assume "z \<in> closure \<R>\<^sub>\<Gamma>"
  hence *: "norm z \<ge> 1" "\<bar>Re z\<bar> \<le> 1 / 2" "Im z \<ge> 0"
    by (auto simp: closure_std_fund_region T_def)
  have "1 \<le> norm z ^ 2"
    using * by simp
  also have "norm z ^ 2 \<le> (1 / 2) ^ 2 + Im z ^ 2"
    unfolding cmod_power2 by (intro add_right_mono power2_mono) (use * in auto)
  finally have "Im z ^ 2 \<ge> (sqrt 3 / 2) ^ 2"
    by (simp add: power2_eq_square)
  hence "Im z \<ge> sqrt 3 / 2"
    by (subst (asm) abs_le_square_iff [symmetric]) (use * in auto)
  thus "z \<in> {z. Im z \<ge> sqrt 3 / 2}"
    by simp
qed  

lemma std_fund_region'_minus_std_fund_region:
  "\<R>\<^sub>\<Gamma>' - \<R>\<^sub>\<Gamma> =
      {z. norm z = 1 \<and> Im z > 0 \<and> Re z \<in> {-1/2..0}} \<union> {z. Re z = -1 / 2 \<and> Im z \<ge> sqrt 3 / 2}"
  (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> ?lhs"
  from z have "Im z \<ge> sqrt 3 / 2"
    using closure_std_fund_region_Im_ge std_fund_region'_subset by auto
  thus "z \<in> ?rhs" using z
    by (auto simp: std_fund_region'_def std_fund_region_def not_less)
next
  fix z assume z: "z \<in> ?rhs"
  have "sqrt 3 / 2 > 0"
    by simp
  have "Im z > 0"
    using z less_le_trans[OF \<open>sqrt 3 / 2 > 0\<close>, of "Im z"] by auto
  moreover have "norm z \<ge> 1"
    using z
  proof
    assume "z \<in> {z. Re z = - 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
    hence "norm z ^ 2 \<ge> (-1/2) ^ 2 + (sqrt 3 / 2) ^ 2"
      unfolding cmod_power2 by (intro add_mono power2_mono) auto
    also have "(-1/2) ^ 2 + (sqrt 3 / 2) ^ 2 = 1"
      by (simp add: field_simps power2_eq_square)
    finally show "norm z \<ge> 1"
      by (simp add: power2_nonneg_ge_1_iff)
  qed auto
  ultimately show "z \<in> ?lhs" using z
    by (auto simp: std_fund_region'_def std_fund_region_def)
qed

lemma closure_std_fund_region_minus_std_fund_region':
  "closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>' =
      {z. norm z = 1 \<and> Im z > 0 \<and> Re z \<in> {0<..1/2}} \<union> {z. Re z = 1 / 2 \<and> Im z \<ge> sqrt 3 / 2}"
  (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix z assume z: "z \<in> closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>'"
  have "norm z \<ge> 1"
    using z by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  from z have "Im z > 0" "Im z \<ge> sqrt 3 / 2"
    using closure_std_fund_region_Im_pos closure_std_fund_region_Im_ge by blast+
  thus "z \<in> ?rhs" using z
    by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
next
  fix z assume "z \<in> ?rhs"
  thus "z \<in> ?lhs"
  proof
    assume "z \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> Re z \<in> {0<..1 / 2}}"
    thus "z \<in> ?lhs"
      by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  next
    assume z: "z \<in> {z. Re z = 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
    have "0 < sqrt 3 / 2"
      by simp
    also have "\<dots> \<le> Im z"
      using z by auto
    finally have "Im z > 0" .
    have "norm z ^ 2 \<ge> (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
      unfolding cmod_power2 by (intro add_mono power2_mono) (use z in auto)
    also have "(1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2 = 1"
      by (simp add: power2_eq_square)
    finally have "norm z \<ge> 1"
      by (simp add: power2_nonneg_ge_1_iff)
    from this and \<open>Im z > 0\<close> and z show "z \<in> ?lhs"
      by (auto simp: closure_std_fund_region in_std_fund_region'_iff not_le T_def)
  qed  
qed

lemma cis_in_std_fund_region'_iff:
  assumes "\<phi> \<in> {0..pi}"
  shows   "cis \<phi> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> \<phi> \<in> {pi/2..2*pi/3}"
proof
  assume \<phi>: "\<phi> \<in> {pi/2..2*pi/3}"
  have "\<phi> > 0"
    by (rule less_le_trans[of _ "pi / 2"]) (use \<phi> in auto)
  moreover have "\<phi> < pi"
    by (rule le_less_trans[of _ "2 * pi / 3"]) (use \<phi> in auto)
  ultimately have "sin \<phi> > 0"
    by (intro sin_gt_zero) auto
  moreover have "cos \<phi> \<ge> cos (2 * pi / 3)"
    using \<phi> by (intro cos_monotone_0_pi_le) auto
  moreover have "cos \<phi> \<le> cos (pi / 2)"
    using \<phi> by (intro cos_monotone_0_pi_le) auto
  ultimately show "cis \<phi> \<in> \<R>\<^sub>\<Gamma>'"
    by (auto simp: in_std_fund_region'_iff cos_120)
next
  assume "cis \<phi> \<in> \<R>\<^sub>\<Gamma>'"
  hence *: "cos \<phi> \<ge> cos (2 * pi / 3)" "cos \<phi> \<le> cos (pi / 2)"
    by (auto simp: in_std_fund_region'_iff cos_120)
  have "\<phi> \<le> 2 * pi / 3"
    using *(1) assms by (subst (asm) cos_mono_le_eq) auto
  moreover have "\<phi> \<ge> pi / 2"
    using *(2) assms by (subst (asm) cos_mono_le_eq) auto
  ultimately show "\<phi> \<in> {pi/2..2*pi/3}"
    by auto
qed

lemma imag_axis_in_std_fund_region'_iff: "y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> y \<ge> 1"
  by (auto simp: in_std_fund_region'_iff)

lemma vertical_left_in_std_fund_region'_iff:
  "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>' \<longleftrightarrow> y \<ge> sqrt 3 / 2"
proof
  assume y: "y \<ge> sqrt 3 / 2"
  have "1 = (1 / 2) ^ 2 + (sqrt 3 / 2) ^ 2"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> (1 / 2) ^ 2 + y ^ 2"
    using y by (intro add_mono power2_mono) auto
  also have "\<dots> = norm (y *\<^sub>R \<i> - 1 / 2) ^ 2"
    unfolding cmod_power2 by simp
  finally have "norm (y *\<^sub>R \<i> - 1 / 2) \<ge> 1"
    by (simp add: power2_nonneg_ge_1_iff)
  moreover have "y > 0"
    by (rule less_le_trans[OF _ y]) auto
  ultimately show "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>'"
    using y by (auto simp: in_std_fund_region'_iff)
next
  assume *: "-1 / 2 + y *\<^sub>R \<i> \<in> \<R>\<^sub>\<Gamma>'"
  hence "y > 0"
    by (auto simp: in_std_fund_region'_iff)
  from * have "1 \<le> norm (y *\<^sub>R \<i> - 1 / 2)"
    by (auto simp: in_std_fund_region'_iff)
  hence "1 \<le> norm (y *\<^sub>R \<i> - 1 / 2) ^ 2"
    by (simp add: power2_nonneg_ge_1_iff)
  also have "\<dots> = (1 / 2) ^ 2 + y ^ 2"
    unfolding cmod_power2 by simp
  finally have "y ^ 2 \<ge> (sqrt 3 / 2) ^ 2"
    by (simp add: algebra_simps power2_eq_square)
  hence "y \<ge> sqrt 3 / 2"
    by (rule power2_le_imp_le) (use \<open>y > 0\<close> in auto)
  thus "y \<ge> sqrt 3 / 2" using *
    by (auto simp: in_std_fund_region'_iff)
qed

lemma std_fund_region'_border_aux1:
  "{z. norm z = 1 \<and> 0 < Im z \<and> Re z \<in> {-1/2..0}} = cis ` {pi / 2..2 / 3 * pi}"
proof safe
  fix z :: complex assume z: "norm z = 1" "Im z > 0" "Re z \<in> {-1/2..0}"
  show "z \<in> cis ` {pi/2..2/3*pi}"
  proof (rule rev_image_eqI)
    from z have [simp]: "z \<noteq> 0"
      by auto
    have [simp]: "Arg z \<ge> 0"
      using z by (auto simp: Arg_less_0)
    have z_eq: "cis (Arg z) = z"
      using z by (auto simp: cis_Arg complex_sgn_def)
    thus "z = cis (Arg z)"
      by simp
    have "Re (cis (Arg z)) \<ge> -1/2"
      using z by (subst z_eq) auto
    hence "cos (Arg z) \<ge> cos (2/3*pi)"
      by (simp add: cos_120 cos_120')
    hence "Arg z \<le> 2 / 3 * pi"
      using Arg_le_pi by (subst (asm) cos_mono_le_eq) auto
    moreover have "Re (cis (Arg z)) \<le> 0"
      using z by (subst z_eq) auto
    hence "cos (Arg z) \<le> cos (pi / 2)"
      by simp
    hence "Arg z \<ge> pi / 2"
      using Arg_le_pi by (subst (asm) cos_mono_le_eq) auto
    ultimately show "Arg z \<in> {pi/2..2/3*pi}"
      by simp
  qed
next
  fix t :: real assume t: "t \<in> {pi/2..2/3*pi}"
  have "t > 0"
    by (rule less_le_trans[of _ "pi/2"]) (use t in auto)
  have "t < pi"
    by (rule le_less_trans[of _ "2/3*pi"]) (use t in auto)
  have "sin t > 0"
    using \<open>t > 0\<close> \<open>t < pi\<close> by (intro sin_gt_zero) auto
  moreover have "cos t \<le> cos (pi / 2)"
    using t \<open>t < pi\<close> by (intro cos_monotone_0_pi_le) auto
  moreover have "cos t \<ge> cos (2*pi/3)"
    using t by (intro cos_monotone_0_pi_le) auto
  ultimately show "norm (cis t) = 1" "Im (cis t) > 0" "Re (cis t) \<in> {-1/2..0}"
    by (auto simp: cos_120 cos_120')
qed

lemma std_fund_region'_border_aux2:
  "{z. Re z = - 1 / 2 \<and> sqrt 3 / 2 \<le> Im z} = (\<lambda>x. - 1 / 2 + x *\<^sub>R \<i>) ` {sqrt 3 / 2..}"
  by (auto simp: complex_eq_iff)

lemma compact_std_fund_region:
  assumes "B > 1"
  shows "compact (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
  unfolding compact_eq_bounded_closed
proof
  show "closed (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
    by (intro closed_Int closed_halfspace_Im_le) auto
next
  show "bounded (closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B})"
  proof -
    have "closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> B} \<subseteq> cbox (-1/2) (1/2 + \<i> * B)"
      by (auto simp: in_closure_std_fund_region_iff in_cbox_complex_iff)
    moreover have "bounded (cbox (-1/2) (1/2 + \<i> * B))"
      by simp
    ultimately show ?thesis
      using bounded_subset by blast
  qed
qed

end


subsubsection \<open>Proving that the standard region is fundamental\<close>

lemma (in gen_lattice) closest_lattice_point_exists:
  assumes "X \<subseteq> \<Omega>" "X \<noteq> {}"
  obtains x where "x \<in> X" "\<And>y. y \<in> X \<Longrightarrow> norm x \<le> norm y"
proof -
  obtain x0 where x0: "x0 \<in> X"
    using assms by auto
  have "\<not>z islimpt X" for z
    using not_islimpt_omega assms(1) islimpt_subset by blast
  hence "finite (cball 0 (norm x0) \<inter> X)"
    by (intro finite_not_islimpt_in_compact) auto
  moreover have "x0 \<in> cball 0 (norm x0) \<inter> X"
    using x0 by auto
  ultimately obtain x where x: "is_arg_min norm (\<lambda>x. x \<in> cball 0 (norm x0) \<inter> X) x"
    using ex_is_arg_min_if_finite[of "cball 0 (norm x0) \<inter> X" norm] by blast
  thus ?thesis
    by (intro that[of x]) (auto simp: is_arg_min_def)
qed

lemma (in gen_lattice) noncollinear_lattice_point_exists:
  assumes "x \<in> \<Omega>*"
  obtains y where "y \<in> \<Omega>*" "y / x \<notin> \<real>"
proof -
  from assms obtain m n where x: "x = of_\<omega>12_coords (of_int m, of_int n)" and "x \<noteq> 0"
    by (auto simp: omega_altdef omega_minus_zero_def elim!: Ints_cases)
  define y where "y = of_\<omega>12_coords (of_int (-n), of_int m)"
  have "y \<in> \<Omega>"
    by (auto simp: y_def)
  moreover have "y \<noteq> 0"
    using \<open>x \<noteq> 0\<close> by (auto simp: x y_def of_\<omega>12_coords_eq_0_iff prod_eq_iff)
  moreover have "y / x \<notin> \<real>"
  proof
    assume "y / x \<in> \<real>"
    then obtain a where "y / x = of_real a"
      by (elim Reals_cases)
    hence y: "y = a *\<^sub>R x"
      using assms \<open>x \<noteq> 0\<close> by (simp add: field_simps scaleR_conv_of_real)
    have "of_\<omega>12_coords (-real_of_int n, real_of_int m) =
          of_\<omega>12_coords (a * real_of_int m, a * real_of_int n)"
      using y by (simp add: x y_def algebra_simps flip: of_\<omega>12_coords_scaleR)
    hence eq: "-real_of_int n = a * real_of_int m" "real_of_int m = a * real_of_int n"
      unfolding of_\<omega>12_coords_eq_iff prod_eq_iff fst_conv snd_conv by blast+
    have "m \<noteq> 0 \<or> n \<noteq> 0"
      using \<open>x \<noteq> 0\<close> by (auto simp: x)
    with eq[symmetric] have nz: "m \<noteq> 0" "n \<noteq> 0"
      by auto
    have "a ^ 2 * real_of_int m = a * (a * real_of_int m)"
      by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = (-1) * real_of_int m"
      by (simp flip: eq)
    finally have "a ^ 2 = -1"
      using \<open>m \<noteq> 0\<close> by (subst (asm) mult_right_cancel) auto
    moreover have "a ^ 2 \<ge> 0"
      by simp
    ultimately show False
      by linarith
  qed
  ultimately show ?thesis
    by (intro that) (auto simp: omega_minus_zero_def)
qed


lemma norm_open_segment_less:
  fixes x y z :: "'a :: euclidean_space"
  assumes "norm x \<le> norm y" "z \<in> open_segment x y"
  shows   "norm z < norm y"
  using assms
  by (metis (no_types, opaque_lifting) diff_zero dist_decreases_open_segment
         dist_norm norm_minus_commute order_less_le_trans)


text \<open>Lemma 1\<close>
lemma (in gen_lattice) std_fund_region_fundamental_lemma1:
  obtains \<omega>1' \<omega>2' :: complex and a b c d :: int
  where "\<bar>a * d - b * c\<bar> = 1"
        "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
        "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
        "Im (\<omega>2' / \<omega>1') \<noteq> 0"
        "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
proof -
  have "\<Omega>* \<subseteq> \<Omega>" "\<Omega>* \<noteq> {}"
    using omegaI1 omega_omega_minus_zero omega_omega_minus_zero by blast+
  then obtain \<omega>1' where \<omega>1': "\<omega>1' \<in> \<Omega>*" "\<And>y. y \<in> \<Omega>* \<Longrightarrow> norm \<omega>1' \<le> norm y"
    using closest_lattice_point_exists by blast

  define X where "X = {y. y \<in> \<Omega>* \<and> y / \<omega>1' \<notin> \<real>}"
  have "X \<subseteq> \<Omega>"
    by (auto simp: X_def omega_minus_zero_def)
  moreover have  "X \<noteq> {}"
    using noncollinear_lattice_point_exists[of \<omega>1'] \<omega>1'(1) unfolding X_def by force
  ultimately obtain \<omega>2' where \<omega>2': "\<omega>2' \<in> X" "\<And>z. z \<in> X \<Longrightarrow> norm \<omega>2' \<le> norm z"
    using closest_lattice_point_exists by blast

  have [simp]: "\<omega>1' \<noteq> 0" "\<omega>2' \<noteq> 0"
    using \<omega>1' \<omega>2' by (auto simp: omega_minus_zero_def X_def)
  have noncollinear: "\<omega>2' / \<omega>1' \<notin> \<real>"
    using \<omega>2' by (auto simp: X_def)
  have Im_nz: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
    using noncollinear by (auto simp: complex_is_Real_iff)

  have "norm \<omega>1' \<le> norm \<omega>2'"
    by (intro \<omega>1') (use \<omega>2' in \<open>auto simp: X_def\<close>)

  have triangle: "z \<notin> \<Omega>" if z: "z \<in> triangle \<omega>1' \<omega>2'" "z \<notin> {0, \<omega>1', \<omega>2'}" for z
  proof
    assume "z \<in> \<Omega>"
    hence "z \<in> \<Omega>*"
      using z by (auto simp: omega_minus_zero_def)
    from that obtain a b where ab: "a \<ge> 0" "b \<ge> 0" "a + b \<le> 1" "z = a *\<^sub>R \<omega>1' + b *\<^sub>R \<omega>2'"
      by (auto simp: triangle_def scaleR_conv_of_real)

    have "norm z \<le> norm (a *\<^sub>R \<omega>1') + norm (b *\<^sub>R \<omega>2')"
      unfolding ab using norm_triangle_ineq by blast
    also have "\<dots> = a * norm \<omega>1' + b * norm \<omega>2'"
      using ab by simp
    finally have norm_z_le: "norm z \<le> a * norm \<omega>1' + b * norm \<omega>2'" .

    also have "\<dots> \<le> a * norm \<omega>2' + b * norm \<omega>2'"
      using ab \<open>norm \<omega>1' \<le> norm \<omega>2'\<close> by (intro add_mono mult_left_mono) auto
    also have "\<dots> = (a + b) * norm \<omega>2'"
      by (simp add: algebra_simps)
    finally have norm_z_le': "norm z \<le> (a + b) * norm \<omega>2'" .

    have "z / \<omega>1' \<notin> \<real>"
    proof
      assume real: "z / \<omega>1' \<in> \<real>"
      show False
      proof (cases "b = 0")
        case False
        hence "\<omega>2' / \<omega>1' = (z / \<omega>1' - of_real a) / of_real b"
          by (simp add: ab field_simps scaleR_conv_of_real)
        also have "\<dots> \<in> \<real>"
          using real by (auto intro: Reals_divide Reals_diff)
        finally show False
          using noncollinear by contradiction
      next
        case True
        hence "z = a *\<^sub>R \<omega>1'"
          using ab by simp
        from this and z have "a \<noteq> 1"
          by auto
        hence "a < 1"
          using ab by simp
        have "norm z = a * norm \<omega>1'"
          using \<open>z = a *\<^sub>R \<omega>1'\<close> \<open>a \<ge> 0\<close> by simp
        also have "\<dots> < 1 * norm \<omega>1'"
          using \<open>a < 1\<close> by (intro mult_strict_right_mono) auto
        finally have "norm z < norm \<omega>1'"
          by simp
        moreover have "norm z \<ge> norm \<omega>1'"
          by (intro \<omega>1') (use z \<open>z \<in> \<Omega>*\<close> in auto)
        ultimately show False
          by simp
      qed
    qed
    hence "z \<in> X"
      using \<open>z \<in> \<Omega>*\<close> by (auto simp: X_def)
    hence "norm z \<ge> norm \<omega>2'"
      by (intro \<omega>2')

    moreover have "norm z \<le> norm \<omega>2'"
    proof -
      have "norm z \<le> (a + b) * norm \<omega>2'"
        by (rule norm_z_le')
      also have "\<dots> \<le> 1 * norm \<omega>2'"
        using ab by (intro mult_right_mono) auto
      finally show "norm z \<le> norm \<omega>2'"
        by simp
    qed

    ultimately have norm_z: "norm z = norm \<omega>2'"
      by linarith

    have "\<not>(a + b < 1)"
    proof
      assume *: "a + b < 1"
      have "norm z \<le> (a + b) * norm \<omega>2'"
        by (rule norm_z_le')
      also have "\<dots> < 1 * norm \<omega>2'"
        by (intro mult_strict_right_mono *) auto
      finally show False
        using norm_z by simp
    qed
    with ab have b_eq: "b = 1 - a"
      by linarith

    have "norm z < norm \<omega>2'"
    proof (rule norm_open_segment_less)
      have "a \<noteq> 0" "a \<noteq> 1"
        using z ab by (auto simp: b_eq)
      hence "\<exists>u. u > 0 \<and> u < 1 \<and> z = (1 - u) *\<^sub>R \<omega>1' + u *\<^sub>R \<omega>2'"
        using ab by (intro exI[of _ b]) (auto simp: b_eq)
      thus "z \<in> open_segment \<omega>1' \<omega>2'"
        using z ab noncollinear unfolding in_segment by auto
    next
      show "norm \<omega>1' \<le> norm \<omega>2'"
        by fact
    qed
    with norm_z show False
      by simp
  qed
  hence "Complex_Lattices.triangle \<omega>1' \<omega>2' \<inter> \<Omega> = {0, \<omega>1', \<omega>2'}"
    using \<omega>1' \<omega>2' by (auto simp: X_def omega_minus_zero_def)

  hence "fundamental_pair \<omega>1' \<omega>2'"
    unfolding fundamental_pair_iff_triangle using Im_nz by blast
  hence "are_equivalent \<omega>1 \<omega>2 \<omega>1' \<omega>2'"
    using fundamental_pair_equivalent by blast
  then obtain a b c d :: int where abcd:
    "a * d - b * c = 1 \<or> a * d - b * c = -1"
    "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
    unfolding are_equivalent_iff[OF ratio_notin_real Im_nz] by blast
  from abcd(1) have det: "\<bar>a * d - b * c\<bar> = 1"
    by linarith

  have *: "norm (\<omega>1' + of_int n * \<omega>2') \<ge> norm \<omega>2'" if n: "n \<noteq> 0" for n
  proof (rule \<omega>2')
    define z where "z = \<omega>1' + of_int n * \<omega>2'"
    have "z \<in> \<Omega>"
      unfolding z_def using \<omega>1'(1) \<omega>2'(1)
      by (auto simp: X_def omega_add omega_mult_left omega_minus_zero_def)
    moreover have "z / \<omega>1' \<notin> \<real>"
    proof
      assume "z / \<omega>1' \<in> \<real>"
      hence "(z / \<omega>1' - 1) / of_int n \<in> \<real>"
        by auto
      also have "(z / \<omega>1' - 1) / of_int n = \<omega>2' / \<omega>1'"
        using n by (simp add: field_simps z_def)
      finally show False
        using noncollinear by contradiction
    qed
    moreover from this have "z \<noteq> 0"
      by auto
    ultimately show "z \<in> X"
      by (auto simp: X_def omega_minus_zero_def)
  qed
  have norms: "norm (\<omega>1' + \<omega>2') \<ge> norm \<omega>2'" "norm (\<omega>1' - \<omega>2') \<ge> norm \<omega>2'"
    using *[of 1] and *[of "-1"] by simp_all

  show ?thesis
    using det norms abcd noncollinear \<open>norm \<omega>1' \<le> norm \<omega>2'\<close>
    by (intro that[of a d b c \<omega>2' \<omega>1']) (simp_all add: complex_is_Real_iff)
qed

lemma (in gen_lattice) std_fund_region_fundamental_lemma2:
  obtains \<omega>1' \<omega>2' :: complex and a b c d :: int
  where "a * d - b * c = 1"
        "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
        "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
        "Im (\<omega>2' / \<omega>1') \<noteq> 0"
        "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
proof -
  obtain \<omega>1' \<omega>2' a b c d
    where abcd: "\<bar>a * d - b * c\<bar> = 1"
      and eq: "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1" "\<omega>1' = of_int c * \<omega>2 + of_int d * \<omega>1"
      and nz: "Im (\<omega>2' / \<omega>1') \<noteq> 0"
      and norms: "norm \<omega>1' \<le> norm \<omega>2'" "norm \<omega>2' \<le> norm (\<omega>1' + \<omega>2')" "norm \<omega>2' \<le> norm (\<omega>1' - \<omega>2')"
    using std_fund_region_fundamental_lemma1 .

  show ?thesis
  proof (cases "a * d - b * c = 1")
    case True
    thus ?thesis
      by (intro that[of a d b c \<omega>2' \<omega>1'] eq nz norms)
  next
    case False
    show ?thesis
    proof (intro that[of a "-d" b "-c" \<omega>2' "-\<omega>1'"])
      from False have "a * d - b * c = -1"
        using abcd by linarith
      thus "a * (-d) - b * (-c) = 1"
        by simp
    next
      show "\<omega>2' = of_int a * \<omega>2 + of_int b * \<omega>1"
           "-\<omega>1' = of_int (- c) * \<omega>2 + of_int (- d) * \<omega>1"
        using eq by (simp_all add: algebra_simps)
    qed (use norms nz in \<open>auto simp: norm_minus_commute add.commute\<close>)
  qed
qed

text \<open>Theorem 2.2\<close>
theorem std_fund_region_fundamental_aux1:
  assumes "Im \<tau>' > 0"
  obtains \<tau> where "Im \<tau> > 0" "\<tau> \<sim>\<^sub>\<Gamma> \<tau>'" "norm \<tau> \<ge> 1" "norm (\<tau> + 1) \<ge> norm \<tau>" "norm (\<tau> - 1) \<ge> norm \<tau>"
proof -
  interpret std_lattice \<tau>'
    using assms by unfold_locales (auto simp: complex_is_Real_iff)
  obtain \<omega>1 \<omega>2 a b c d
    where abcd: "a * d - b * c = 1"
      and eq: "\<omega>2 = of_int a * \<tau>' + of_int b * 1" "\<omega>1 = of_int c * \<tau>' + of_int d * 1"
      and nz: "Im (\<omega>2 / \<omega>1) \<noteq> 0"
      and norms: "norm \<omega>1 \<le> norm \<omega>2" "norm \<omega>2 \<le> norm (\<omega>1 + \<omega>2)" "norm \<omega>2 \<le> norm (\<omega>1 - \<omega>2)"
    using std_fund_region_fundamental_lemma2 .
  from nz have [simp]: "\<omega>1 \<noteq> 0" "\<omega>2 \<noteq> 0"
    by auto

  interpret unimodular_transform a b c d
    by unfold_locales fact

  define \<tau> where "\<tau> = \<omega>2 / \<omega>1"
  have \<tau>_eq: "\<tau> = \<phi> \<tau>'"
    by (simp add: moebius_def \<tau>_def eq add_ac \<phi>_def)

  show ?thesis
  proof (rule that[of \<tau>])
    show "Im \<tau> > 0"
      using assms \<tau>_eq by (simp add: Im_transform_pos)
  next
    show "norm \<tau> \<ge> 1" "norm (\<tau> + 1) \<ge> norm \<tau>" "norm (\<tau> - 1) \<ge> norm \<tau>"
      using norms by (simp_all add: \<tau>_def norm_divide field_simps norm_minus_commute)
  next
    have "\<tau> = apply_modgrp as_modgrp \<tau>'"
      using \<tau>_eq by (simp add: \<phi>_as_modgrp)
    thus "\<tau> \<sim>\<^sub>\<Gamma> \<tau>'" using \<open>Im \<tau>' > 0\<close>
      by auto
  qed
qed

lemma std_fund_region_fundamental_aux2:
  assumes "norm (z + 1) \<ge> norm z" "norm (z - 1) \<ge> norm z"
  shows   "Re z \<in> {-1/2..1/2}"
proof -
  have "0 \<le> norm (z + 1) ^ 2 - norm z ^ 2"
    using assms by simp
  also have "\<dots> = (Re z + 1)\<^sup>2 - (Re z)\<^sup>2"
    unfolding norm_complex_def by simp
  also have "\<dots> = 1 + 2 * Re z"
    by (simp add: algebra_simps power2_eq_square)
  finally have "Re z \<ge> -1/2"
    by simp

  have "0 \<le> norm (z - 1) ^ 2 - norm z ^ 2"
    using assms by simp
  also have "\<dots> = (Re z - 1)\<^sup>2 - (Re z)\<^sup>2"
    unfolding norm_complex_def by simp
  also have "\<dots> = 1 - 2 * Re z"
    by (simp add: algebra_simps power2_eq_square)
  finally have "Re z \<le> 1/2"
    by simp

  with \<open>Re z \<ge> -1/2\<close> show ?thesis
    by simp
qed

lemma std_fund_region_fundamental_aux3:
  fixes x y :: complex
  assumes xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>"
  assumes f: "y = apply_modgrp f x"
  defines "c \<equiv> modgrp_c f"
  defines "d \<equiv> modgrp_d f"
  assumes c: "c \<noteq> 0"
  shows   "Im y < Im x"
proof -
  have ineq1: "norm (c * x + d) ^ 2 > c ^ 2 - \<bar>c * d\<bar> + d ^ 2"
  proof -
    have "of_int \<bar>c\<bar> * 1 < of_int \<bar>c\<bar> * norm x"
      using xy c by (intro mult_strict_left_mono) (auto simp: std_fund_region_def)
    hence "of_int c ^ 2 < (of_int c * norm x) ^ 2"
      by (intro power2_strict_mono) auto
    also have "\<dots> - \<bar>c * d\<bar> * 1 + d ^ 2 \<le>
          (of_int c * norm x) ^ 2 - \<bar>c * d\<bar> * (2 * \<bar>Re x\<bar>) + d ^ 2"
      using xy unfolding of_int_add of_int_mult of_int_power of_int_diff
      by (intro add_mono diff_mono mult_left_mono) (auto simp: std_fund_region_def)
    also have "\<dots> = c ^ 2 * norm x ^ 2 - \<bar>2 * c * d * Re x\<bar> + d ^ 2"
      by (simp add: power_mult_distrib abs_mult)
    also have "\<dots> \<le> c ^ 2 * norm x ^ 2 + 2 * c * d * Re x + d ^ 2"
      by linarith
    also have "\<dots> = norm (c * x + d) ^ 2"
      unfolding cmod_power2 by (simp add: algebra_simps power2_eq_square)
    finally show "norm (c * x + d) ^ 2 > c ^ 2 - \<bar>c * d\<bar> + d ^ 2" 
      by simp
  qed

  have "Im y = Im x / norm (c * x + d) ^ 2"
    using f by (simp add: modgrp.Im_transform c_def d_def)

  also have "norm (c * x + d) ^ 2 > 1"
  proof (cases "d = 0")
    case [simp]: True
    have "0 < c ^ 2"
      using c by simp
    hence "1 \<le> real_of_int (c ^ 2) * 1"
      by linarith
    also have "\<dots> < of_int (c ^ 2) * norm x ^ 2"
      using xy c by (intro mult_strict_left_mono) (auto simp: std_fund_region_def)
    also have "\<dots> = norm (c * x + d) ^ 2"
      by (simp add: norm_mult power_mult_distrib)
    finally show ?thesis .
  next
    case False
    have "0 < \<bar>c * d\<bar>"
      using c False by auto
    hence "1 \<le> \<bar>c * d\<bar>"
      by linarith
    also have "\<dots> \<le> \<bar>c * d\<bar> + (\<bar>c\<bar> - \<bar>d\<bar>) ^ 2"
      by simp
    also have "\<dots> = c ^ 2 - \<bar>c * d\<bar> + d ^ 2"
      by (simp add: algebra_simps power2_eq_square abs_mult)
    finally have "1 \<le> real_of_int (c ^ 2 - \<bar>c * d\<bar> + d ^ 2)"
      by linarith
    also have "\<dots> < norm (c * x + d) ^ 2"
      using ineq1 False by simp
    finally show ?thesis .
  qed

  hence "Im x / norm (c * x + d) ^ 2 < Im x / 1"
    using xy by (intro divide_strict_left_mono) (auto simp: std_fund_region_def)
  finally show ?thesis
    by simp
qed

lemma std_fund_region_fundamental_aux4:
  fixes x y :: complex
  assumes xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>"
  assumes f: "y = apply_modgrp f x"
  shows   "f = 1"
proof -
  define a where "a = modgrp_a f"
  define b where "b = modgrp_b f"
  define c where "c = modgrp_c f"
  define d where "d = modgrp_d f"

  have c: "c = 0"
  proof (rule ccontr)
    assume c: "c \<noteq> 0"
    have "Im y < Im x" using xy f c
      by (intro std_fund_region_fundamental_aux3[where f = f]) (auto simp: c_def)
    moreover have "Im y > Im x"
    proof (rule std_fund_region_fundamental_aux3[where f = "inverse f"])
      have "Im x > 0"
        using xy by (auto simp: std_fund_region_def)
      hence "x \<noteq> pole_modgrp f"
        using pole_modgrp_in_Reals[of f, where ?'a = complex]
        by (auto simp: complex_is_Real_iff)
      with f have "apply_modgrp (inverse f) y = x"
        by (intro apply_modgrp_inverse_eqI) auto
      thus "x = apply_modgrp (inverse f) y" ..
    next
      have "is_singular_modgrp f"
        using c by (simp add: is_singular_modgrp_altdef c_def)
      hence "is_singular_modgrp (inverse f)"
        by simp
      thus "modgrp_c (inverse f) \<noteq> 0"
        unfolding is_singular_modgrp_altdef by simp      
    qed (use xy c in \<open>auto simp: c_def\<close>)
    ultimately show False
      by simp
  qed

  define n where "n = sgn a * b"
  from c have "\<not>is_singular_modgrp f"
    by (auto simp: is_singular_modgrp_altdef c_def)
  hence f_eq: "f = shift_modgrp n"
    using not_is_singular_modgrpD[of f] by (simp add: n_def a_def b_def)
  from xy f have "n = 0"
    by (auto simp: std_fund_region_def f_eq)
  thus "f = 1"
    by (simp add: f_eq)
qed

text \<open>Theorem 2.3\<close>
interpretation std_fund_region: fundamental_region UNIV std_fund_region
proof
  show "std_fund_region \<subseteq> {z. Im z > 0}"
    using Im_std_fund_region by blast
next
  fix x y :: complex
  assume xy: "x \<in> \<R>\<^sub>\<Gamma>" "y \<in> \<R>\<^sub>\<Gamma>" "x \<sim>\<^sub>\<Gamma> y"
  then obtain f where f: "y = apply_modgrp f x"
    by (auto simp: modular_group.rel_def)
  with xy have "f = 1"
    using std_fund_region_fundamental_aux4 by blast
  with f xy show "x = y"
    by simp
next
  fix x :: complex
  assume x: "Im x > 0"
  obtain y where y: "Im y > 0" "y \<sim>\<^sub>\<Gamma> x"
    "norm y \<ge> 1" "norm (y + 1) \<ge> norm y" "norm (y - 1) \<ge> norm y"
    using std_fund_region_fundamental_aux1[OF x] by blast
  from y have "Re y \<in> {-1/2..1/2}"
    by (intro std_fund_region_fundamental_aux2)
  with y show "\<exists>y\<in>closure std_fund_region. x \<sim>\<^sub>\<Gamma> y"
    using x unfolding closure_std_fund_region by (auto simp: modular_group.rel_commutes)
qed auto

theorem std_fund_region_no_fixed_point:
  assumes "z \<in> \<R>\<^sub>\<Gamma>"
  assumes "apply_modgrp f z = z"
  shows   "f = 1"
  using std_fund_region_fundamental_aux4[of z "apply_modgrp f z" f] assms by auto

lemma std_fund_region_no_fixed_point':
  assumes "z \<in> \<R>\<^sub>\<Gamma>"
  assumes "apply_modgrp f z = apply_modgrp g z"
  shows   "f = g"
proof -
  have z: "Im z > 0"
    using assms by (auto simp: in_std_fund_region_iff)
  have "apply_modgrp (inverse f) (apply_modgrp g z) = apply_modgrp (inverse f) (apply_modgrp f z)"
    by (simp only: assms(2))
  also have "\<dots> = z"
    using z by (intro apply_modgrp_inverse_eqI) auto
  also have "apply_modgrp (inverse f) (apply_modgrp g z) = apply_modgrp (inverse f * g) z"
    by (rule apply_modgrp_mult [symmetric]) (use z in auto)
  finally have "inverse f * g = 1"
    using assms by (intro std_fund_region_no_fixed_point) auto
  thus ?thesis
    by (metis modgrp.left_cancel modgrp.left_inverse)
qed

lemma equiv_point_in_std_fund_region':
  assumes "Im z > 0"
  obtains z' where "z \<sim>\<^sub>\<Gamma> z'" "z' \<in> \<R>\<^sub>\<Gamma>'"
proof -
  obtain z1 where z1: "z \<sim>\<^sub>\<Gamma> z1" "z1 \<in> closure \<R>\<^sub>\<Gamma>"
    using std_fund_region.equiv_in_closure assms by blast
  show ?thesis
  proof (cases "z1 \<in> \<R>\<^sub>\<Gamma>'")
    case True
    thus ?thesis
      using z1 by (intro that[of z1]) auto
  next
    case False
    hence "z1 \<in> closure \<R>\<^sub>\<Gamma> - \<R>\<^sub>\<Gamma>'"
      using z1 by blast
    thus ?thesis
      unfolding closure_std_fund_region_minus_std_fund_region'
    proof
      assume z1': "z1 \<in> {z. cmod z = 1 \<and> 0 < Im z \<and> Re z \<in> {0<..1 / 2}}"
      define z2 where "z2 = apply_modgrp S_modgrp z1"
      show ?thesis
      proof (rule that [of z2])
        show "z \<sim>\<^sub>\<Gamma> z2"
          unfolding z2_def using z1
          by (subst modular_group.rel_apply_modgrp_right_iff) auto
        have "-cnj z1 \<in> \<R>\<^sub>\<Gamma>'"
          using z1' by (auto simp: z2_def in_std_fund_region'_iff)
        also have "-cnj z1 = z2"
          using z1' by (auto simp: z2_def divide_conv_cnj)
        finally show "z2 \<in> \<R>\<^sub>\<Gamma>'" .
      qed
    next
      assume z1': "z1 \<in> {z. Re z = 1 / 2 \<and> sqrt 3 / 2 \<le> Im z}"
      define z2 where "z2 = apply_modgrp (shift_modgrp (-1)) z1"
      show ?thesis
      proof (rule that [of z2])
        show "z \<sim>\<^sub>\<Gamma> z2"
          unfolding z2_def using z1
          by (subst modular_group.rel_apply_modgrp_right_iff) auto
        have "-cnj z1 \<in> \<R>\<^sub>\<Gamma>'"
          using z1' z1 by (auto simp: z2_def in_std_fund_region'_iff in_closure_std_fund_region_iff)
        also have "-cnj z1 = z2"
          using z1' by (auto simp: z2_def complex_eq_iff)
        finally show "z2 \<in> \<R>\<^sub>\<Gamma>'" .
      qed
    qed
  qed
qed


text \<open>
  The image of the fundamental region under a unimodular transformation is again a
  fundamental region.
\<close>
locale std_fund_region_image =
  fixes f :: modgrp and R :: "complex set"
  defines "R \<equiv> apply_modgrp f ` \<R>\<^sub>\<Gamma>"
begin

lemma R_altdef: "R = {z. Im z > 0} \<inter> apply_modgrp (inverse f) -` \<R>\<^sub>\<Gamma>"
(* TODO cleanup *)
  apply (auto simp: R_def apply_modgrp_mult [symmetric] Im_std_fund_region)
   apply (subst apply_modgrp_mult [symmetric])
  apply (auto simp: R_def apply_modgrp_mult [symmetric] Im_std_fund_region)
  by (metis Im_pole_modgrp apply_modgrp_inverse_eqI image_iff less_numeral_extra(3) modgrp.inverse_inverse)

lemma R_altdef': "R = apply_modgrp (inverse f) -` \<R>\<^sub>\<Gamma>"
  unfolding R_altdef by (auto simp: in_std_fund_region_iff)

sublocale fundamental_region UNIV R
proof
  show "open R"
    unfolding R_altdef 
    by (intro continuous_open_preimage continuous_intros) (auto simp: open_halfspace_Im_gt )
  show "R \<subseteq> {z. 0 < Im z}"
    unfolding R_altdef by auto
  show "x = y" if "x \<in> R" "y \<in> R" "x \<sim>\<^sub>\<Gamma> y" for x y
    using that unfolding R_def by (auto dest: std_fund_region.unique)
  show "\<exists>y\<in>closure R. x \<sim>\<^sub>\<Gamma> y" if "Im x > 0" for x
  proof -
    define x' where "x' = apply_modgrp (inverse f) x"
    have x': "Im x' > 0"
      using that by (simp add: x'_def)
    then obtain y where y: "y \<in> closure \<R>\<^sub>\<Gamma>" "x' \<sim>\<^sub>\<Gamma> y"
      using std_fund_region.equiv_in_closure[of x'] by blast
    define y' where "y' = apply_modgrp f y"
    have "y islimpt \<R>\<^sub>\<Gamma>"
      using y by (meson islimpt_closure_open limpt_of_closure open_std_fund_region)
    then obtain h :: "nat \<Rightarrow> complex" where h: "\<And>n. h n \<in> \<R>\<^sub>\<Gamma> - {y}" "h \<longlonglongrightarrow> y"
      unfolding islimpt_sequential by blast
    have "(apply_modgrp f \<circ> h) n \<in> R - {y'}" for n
    proof -
      have Ims: "Im y > 0" "Im (h n) > 0"
        using y h(1)[of n] by (auto simp: in_std_fund_region_iff)
      have "apply_modgrp f (h n) \<in> R" "h n \<noteq> y"
        using h(1)[of n] by (auto simp: R_def)
      moreover have "apply_modgrp f (h n) \<noteq> y'"
        unfolding y'_def using y \<open>h n \<noteq> y\<close> Ims by (subst apply_modgrp_eq_iff) auto
      ultimately show ?thesis
        by auto
    qed
    moreover have "(apply_modgrp f \<circ> h) \<longlonglongrightarrow> y'"
      unfolding y'_def using y by (auto intro!: tendsto_compose_at[OF h(2)] tendsto_eq_intros)+
    ultimately have "y' islimpt R"
      unfolding islimpt_sequential by blast
    hence "y' \<in> closure R"
      by (simp add: closure_def)
 
    moreover have "x \<sim>\<^sub>\<Gamma> y'"
      using x' that y unfolding y'_def x'_def
      by (auto simp: modular_group.rel_commutes)
    ultimately show ?thesis
      by blast
  qed
qed

end



subsection \<open>Some important points\<close>

lemma cos_120: "cos (2 * pi / 3) = -1/2"
  and sin_120: "sin (2 * pi / 3) = sqrt 3 / 2"
  using sin_double[of "pi / 3"] cos_double[of "pi / 3"]
  by (simp_all add: power2_eq_square sin_60 cos_60)

definition modfun_rho ("\<^bold>\<rho>") where
  "\<^bold>\<rho> = cis (2 / 3 * pi)"

lemma modfun_rho_altdef: "\<^bold>\<rho> = -1 / 2 + sqrt 3 / 2 * \<i>"
  by (simp add: complex_eq_iff modfun_rho_def Re_exp Im_exp sin_120 cos_120)

lemma Re_modfun_rho [simp]: "Re \<^bold>\<rho> = -1 / 2"
  and Im_modfun_rho [simp]: "Im \<^bold>\<rho> = sqrt 3 / 2"
  by (simp_all add: modfun_rho_altdef)

lemma norm_modfun_rho [simp]: "norm \<^bold>\<rho> = 1"
  by (simp add: modfun_rho_def)

lemma modfun_rho_plus_1_eq: "\<^bold>\<rho> + 1 = exp (pi / 3 * \<i>)"
  by (simp add: modfun_rho_altdef complex_eq_iff Re_exp Im_exp sin_60 cos_60)

lemma norm_modfun_rho_plus_1 [simp]: "norm (\<^bold>\<rho> + 1) = 1"
  by (simp add: modfun_rho_plus_1_eq)

lemma cnj_modfun_rho: "cnj \<^bold>\<rho> = -\<^bold>\<rho> - 1"
  and cnj_modfun_rho_plus1: "cnj (\<^bold>\<rho> + 1) = -\<^bold>\<rho>"
  by (auto simp: complex_eq_iff)

lemma modfun_rho_cube: "\<^bold>\<rho> ^ 3 = 1"
  by (simp add: modfun_rho_def Complex.DeMoivre)

lemma modfun_rho_power_mod3_reduce: "\<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (n mod 3)"
proof -
  have "\<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (3 * (n div 3) + (n mod 3))"
    by simp
  also have "\<dots> = (\<^bold>\<rho> ^ 3) ^ (n div 3) * \<^bold>\<rho> ^ (n mod 3)"
    by (subst power_add) (simp add: power_mult)
  also have "\<dots> = \<^bold>\<rho> ^ (n mod 3)"
    by (simp add: modfun_rho_cube)
  finally show ?thesis .
qed

lemma modfun_rho_power_mod3_reduce': "n \<ge> 3 \<Longrightarrow> \<^bold>\<rho> ^ n = \<^bold>\<rho> ^ (n mod 3)"
  by (rule modfun_rho_power_mod3_reduce)

lemmas [simp] = modfun_rho_power_mod3_reduce' [of "numeral num" for num]

lemma modfun_rho_square: "\<^bold>\<rho> ^ 2 = -\<^bold>\<rho> - 1"
  by (simp add: modfun_rho_altdef power2_eq_square field_simps flip: of_real_mult)

lemma modfun_rho_not_real [simp]: "\<^bold>\<rho> \<notin> \<real>"
  by (simp add: modfun_rho_altdef complex_is_Real_iff)

lemma modfun_rho_nonzero [simp]: "\<^bold>\<rho> \<noteq> 0"
  by (simp add: modfun_rho_def)

lemma modfun_rho_not_one [simp]: "\<^bold>\<rho> \<noteq> 1"
  by (simp add: complex_eq_iff modfun_rho_altdef)

lemma i_neq_modfun_rho [simp]: "\<i> \<noteq> \<^bold>\<rho>"
  and i_neq_modfun_rho_plus1 [simp]: "\<i> \<noteq> \<^bold>\<rho> + 1"
  and modfun_rho_neg_i [simp]: "\<^bold>\<rho> \<noteq> \<i>"
  and modfun_rho_plus1_neg_i [simp]: "\<^bold>\<rho> + 1 \<noteq> \<i>"
  by (auto simp: complex_eq_iff)

lemma i_in_closure_std_fund_region [intro, simp]: "\<i> \<in> closure \<R>\<^sub>\<Gamma>"
  and i_in_std_fund_region' [intro, simp]: "\<i> \<in> \<R>\<^sub>\<Gamma>'"
  and modfun_rho_in_closure_std_fund_region [intro, simp]: "\<^bold>\<rho> \<in> closure \<R>\<^sub>\<Gamma>"
  and modfun_rho_in_std_fund_region' [intro, simp]: "\<^bold>\<rho> \<in> \<R>\<^sub>\<Gamma>'"
  and modfun_rho_plus_1_notin_closure_std_fund_region [intro, simp]: "\<^bold>\<rho> + 1 \<in> closure \<R>\<^sub>\<Gamma>"
  and modfun_rho_plus_1_notin_std_fund_region' [intro, simp]: "\<^bold>\<rho> + 1 \<notin> \<R>\<^sub>\<Gamma>'"
  by (simp_all add: closure_std_fund_region std_fund_region'_def in_std_fund_region_iff)

end