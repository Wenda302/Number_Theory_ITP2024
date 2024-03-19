theory More_Zeta_Laurent_Expansion
  imports "Zeta_Function.Zeta_Laurent_Expansion"
begin

definition fps_pre_zeta_1 :: "complex fps" where
  "fps_pre_zeta_1 = Abs_fps (\<lambda>n. (-1)^n * stieltjes_gamma n / fact n)"

lemma pre_zeta_1_has_fps_expansion_1 [fps_expansion_intros]:
  "(\<lambda>z. pre_zeta 1 (1 + z)) has_fps_expansion fps_pre_zeta_1"
proof -
  have "(\<lambda>z. pre_zeta 1 (1 + z)) has_fps_expansion fps_expansion (pre_zeta 1) 1"
    by (intro analytic_at_imp_has_fps_expansion analytic_intros analytic_pre_zeta) auto
  also have "\<dots> = fps_pre_zeta_1"
    by (simp add: fps_expansion_pre_zeta_1_1 fps_pre_zeta_1_def)
  finally show ?thesis .
qed

definition fls_zeta_1 :: "complex fls" where
  "fls_zeta_1 = fls_X_intpow (-1) + fps_to_fls fps_pre_zeta_1"

lemma zeta_has_laurent_expansion_1 [laurent_expansion_intros]:
  "(\<lambda>z. zeta (1 + z)) has_laurent_expansion fls_zeta_1"
proof -
  have "(\<lambda>z. z powi (-1) + pre_zeta 1 (1 + z)) has_laurent_expansion fls_zeta_1"
    unfolding fls_zeta_1_def
    by (intro laurent_expansion_intros fps_expansion_intros has_laurent_expansion_fps)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro has_laurent_expansion_cong)
       (auto simp: eventually_at_filter zeta_def hurwitz_zeta_def divide_inverse)
  finally show ?thesis .
qed

end
