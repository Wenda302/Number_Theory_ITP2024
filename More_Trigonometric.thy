theory More_Trigonometric 
  imports "Winding_Number_Eval.Missing_Transcendental"
begin

(*ALL MIGRATED TO THE REPOSITORY*)

  lemma tan_eq_0_cos_sin: "tan x = 0 \<longleftrightarrow> cos x = 0 \<or> sin x = 0"
    by (auto simp: tan_def)
  
  lemma tan_eq_0_Ex:
    assumes "tan x = 0"
    obtains k::int where "x = (k/2) * pi"
    using assms
    by (metis cos_zero_iff_int mult.commute sin_zero_iff_int tan_eq_0_cos_sin times_divide_eq_left) 
  
  lemma arctan_tan_eq_abs_pi:
    assumes "cos \<theta> \<noteq> 0"
    obtains k where "arctan (tan \<theta>) = \<theta> - of_int k * pi"
    by (metis add.commute assms cos_zero_iff_int2 eq_diff_eq tan_eq_arctan_Ex)
  
  lemma tan_eq:
    assumes "tan x = tan y" "tan x \<noteq> 0"
    obtains k::int where "x = y + k * pi"
  proof -
    obtain k0 where k0: "x = arctan (tan y) + real_of_int k0 * pi"
      using assms tan_eq_arctan_Ex[of x "tan y"] by auto
    obtain k1 where k1: "arctan (tan y) = y - of_int k1 * pi"
      using arctan_tan_eq_abs_pi assms tan_eq_0_cos_sin by auto
    have "x = y + (k0-k1)*pi"
      using k0 k1 by (auto simp: algebra_simps)
    with that show ?thesis
      by blast
  qed

end