theory More_Topology 
  imports "Winding_Number_Eval.Missing_Topology" "HOL-Analysis.Analysis"
begin

lemma compact_minkowski_sum_cball:
  fixes A :: "'a :: heine_borel set"
  assumes "compact A"
  shows   "compact (\<Union>x\<in>A. cball x r)"
proof (cases "A = {}")
  case False
  show ?thesis
  unfolding compact_eq_bounded_closed
  proof safe
    have "open (-(\<Union>x\<in>A. cball x r))"
      unfolding open_dist
    proof safe
      fix x assume x: "x \<notin> (\<Union>x\<in>A. cball x r)"
      have "\<exists>x'\<in>{x}. \<exists>y\<in>A. dist x' y = setdist {x} A"
        using \<open>A \<noteq> {}\<close> assms
        by (intro setdist_compact_closed) (auto simp: compact_imp_closed)
      then obtain y where y: "y \<in> A" "dist x y = setdist {x} A"
        by blast
      with x have "setdist {x} A > r"
        by (auto simp: dist_commute)
      moreover have "False" if "dist z x < setdist {x} A - r" "u \<in> A" "z \<in> cball u r" for z u
        by (smt (verit, del_insts) mem_cball setdist_Lipschitz setdist_sing_in_set that)
      ultimately
      show "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> - (\<Union>x\<in>A. cball x r)"
        by (force intro!: exI[of _ "setdist {x} A - r"])
    qed
    thus "closed (\<Union>x\<in>A. cball x r)"
      using closed_open by blast
  next
    from assms have "bounded A"
      by (simp add: compact_imp_bounded)
    then obtain x c where c: "\<And>y. y \<in> A \<Longrightarrow> dist x y \<le> c"
      unfolding bounded_def by blast
    have "\<forall>y\<in>(\<Union>x\<in>A. cball x r). dist x y \<le> c + r"
    proof safe
      fix y z assume *: "y \<in> A" "z \<in> cball y r"
      thus "dist x z \<le> c + r"
        using * c[of y] cball_trans mem_cball by blast
    qed
    thus "bounded (\<Union>x\<in>A. cball x r)"
      unfolding bounded_def by blast
  qed
qed auto

end