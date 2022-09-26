theory Realisation
  imports ZFC_Extras Graph_Theory.Graph_Theory
begin

abbreviation parents :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "parents G s \<equiv> {u. u \<rightarrow>\<^bsub>G\<^esub> s}"

abbreviation ancestors :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ancestors G s \<equiv> {u. u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> s}"

lemma (in fin_digraph) finite_parents[intro]: "finite (parents G s)"
  using reachable_in_verts
  by (auto intro: rev_finite_subset[where ?A="parents G s", OF finite_verts])

lemma (in fin_digraph) small_parents[intro]: "small (parents G s)"
  using finite_imp_small finite_parents by blast

lemma (in fin_digraph) finite_ancestors[intro]: "finite (ancestors G s)"
  using reachable_in_verts
  by (auto intro: rev_finite_subset[where ?A="ancestors G s", OF finite_verts])

lemma (in fin_digraph) small_ancestors[intro]: "small (ancestors G s)"
  using finite_imp_small finite_ancestors by blast

lemma (in wf_digraph) in_ancestors_if_dominates[simp, intro]:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "s \<in> ancestors G t"
  using assms by blast

lemma (in wf_digraph) ancestors_mono:
  assumes "s \<in> ancestors G t"
  shows "ancestors G s \<subseteq> ancestors G t"
  using assms by fastforce

locale dag = digraph G for G +
  assumes acyclic: "\<nexists>c. cycle c"
begin

lemma ancestors_asym:
  assumes "s \<in> ancestors G t"
  shows "t \<notin> ancestors G s"
proof
  assume "t \<in> ancestors G s"
  then obtain p1 p2 where "awalk t p1 s" "p1 \<noteq> []" "awalk s p2 t" "p2 \<noteq> []"
    using assms reachable1_awalk by auto
  then have "closed_w (p1 @ p2)"
    unfolding closed_w_def by auto
  with closed_w_imp_cycle acyclic show False
    by blast
qed

lemma ancestors_strict_mono:
  assumes "s \<in> ancestors G t"
  shows "ancestors G s \<subset> ancestors G t"
  using assms ancestors_mono ancestors_asym by blast

lemma card_ancestors_strict_mono:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "card (ancestors G s) < card (ancestors G t)"
  using assms finite_ancestors ancestors_strict_mono
  by (metis in_ancestors_if_dominates psubset_card_mono)

end

locale realisation = dag G for G +
  fixes P T :: "'a set"
  fixes I :: "'a \<Rightarrow> V"
  assumes P_T_partition_verts: "P \<inter> T = {}" "verts G = P \<union> T"
begin

lemma
  shows finite_P: "finite P"
    and finite_T: "finite T"
    and finite_P_un_T: "finite (P \<union> T)"
  using finite_verts P_T_partition_verts by auto
 
function height :: "'a \<Rightarrow> nat" where
  "t \<in> P \<Longrightarrow> height t = 0"
| "t \<notin> P \<Longrightarrow> \<forall>s. \<not> s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = 0"
| "t \<notin> P \<Longrightarrow> s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = Max (height ` parents G t) + 1"
  by auto
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma height_cases':
  obtains (P_0) "t \<in> P" "height t = 0"
    | (nP_0) "t \<notin> P" "\<forall>s. \<not> s \<rightarrow>\<^bsub>G\<^esub> t" "height t = 0"
    | (nP_Suc) s where "t \<notin> P" "s \<rightarrow>\<^bsub>G\<^esub> t" "height t = height s + 1"
proof(cases t rule: height.cases)
  case (3 t s)
  note Max_in[OF finite_imageI[where ?h=height, OF finite_parents]]
  with 3 that show ?thesis
    by auto
qed simp_all

function realise :: "'a \<Rightarrow> V" where
  "x \<in> P \<Longrightarrow> realise x = vset {I x}"
| "t \<in> T \<Longrightarrow> realise t = vset (realise ` parents G t)"
| "x \<notin> P \<union> T \<Longrightarrow> realise x = 0"
  using P_T_partition_verts by auto
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma small_realisation_parents[simp, intro!]: "small (realise ` parents G t)"
  using small_parents by auto

lemma lemma1_1:
  assumes "s \<in> P \<union> T" "t \<in> T" "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "height s < height t"
  using assms
proof(cases t rule: height.cases)
  case (3 t u)
  note Max_ge[OF finite_imageI[where ?h=height, OF finite_parents], of "height s" t]
  with assms 3 show ?thesis
    by auto
qed (use P_T_partition_verts in auto)


lemma dominates_if_mem_realisation:
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realise y"
  assumes "s \<in> P \<union> T" "t \<in> P \<union> T"
  assumes "realise s \<in> elts (realise t)"
  obtains s' where "s' \<rightarrow>\<^bsub>G\<^esub> t" "realise s = realise s'"
  using assms(2-)
proof(induction t rule: realise.induct)
  case (1 x)
  with assms(1) show ?case 
    by (metis all_not_in_conv elts_of_set insert_iff mem_not_sym realise.simps(1))
qed auto

lemma lemma1_2':
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realise y"
  assumes "t1 \<in> P \<union> T" "t2 \<in> P \<union> T" "realise t1 = realise t2"
  shows "height t1 \<le> height t2"
proof -
  from assms(3,4) consider "t1 \<in> P" | "t1 \<in> T" "t2 \<in> P" | "t1 \<in> T" "t2 \<in> T"
    using P_T_partition_verts by blast
  then show ?thesis
  proof cases
    case 1
    with assms show ?thesis by auto
  next
    case 2
    then show ?thesis
    proof(cases t1 rule: height.cases)
      case (3 t s)
      have "small (realise ` parents G t1)"
        by blast+
      with 2 3 assms(5) have "realise ` parents G t1 = {I t2}"
        using \<open>small (realise ` parents G t1)\<close> by force
      moreover from 3 adj_in_verts P_T_partition_verts have "s \<in> P \<union> T"
        by simp
      then have "I t2 \<noteq> realise s"
        using 2 3 assms(2,3,5) by metis
      ultimately show ?thesis
        using 3 by (metis ex_in_conv imageI insert_iff mem_Collect_eq)
    qed auto
  next
    case 3
    with P_T_partition_verts have "t1 \<in> T" "t2 \<in> T"
      by simp_all
    then show ?thesis
      using assms(5)
    proof(induction "height t2" arbitrary: t1 t2 rule: less_induct)
      case less
      then show ?case
      proof(cases "height t2")
        case 0
        with less.prems assms(2) show ?thesis
          using P_T_partition_verts(1)
          apply(cases t2 rule: height_cases'; cases t1 rule: height_cases')
          by (auto simp: vset_eq_0_iff[OF small_realisation_parents])
      next
        case (Suc x)
        then have "t2 \<notin> P"
          using less.prems(2) by fastforce
        then show ?thesis
        proof(cases t1 rule: height_cases')
          case (nP_Suc s)
          with P_T_partition_verts adj_in_verts(1) have "s \<in> P \<union> T"
            by blast
          from nP_Suc less.prems(1) have "realise s \<in> elts (realise t1)"
            by auto
          then obtain s' where s': "realise s' = realise s" "s' \<rightarrow>\<^bsub>G\<^esub> t2"
            using dominates_if_mem_realisation \<open>s \<in> P \<union> T\<close> less.prems assms(2)
            by (metis Un_iff)
          then have "s' \<in> P \<union> T"
            using P_T_partition_verts(2) adj_in_verts(1) by blast

          note lemma1_1[OF this(1) less.prems(2) \<open>s' \<rightarrow>\<^bsub>G\<^esub> t2\<close>]
          from less(1)[OF this _ _ s'(1)[symmetric]] have "height s \<le> height s'" if "s \<in> T" "s' \<in> T"
            using that P_T_partition_verts(2) adj_in_verts(1) nP_Suc(2) s'(2) by blast
          with nP_Suc have ?thesis if "s \<in> T" "s' \<in> T"
            using that \<open>height s' < height t2\<close> by linarith

          moreover have "height s \<le> height s'" if "s \<in> T" "s' \<notin> T"
          proof -
            from that \<open>s' \<in> P \<union> T\<close> P_T_partition_verts have "s' \<in> P"
              by simp
            with that show ?thesis
            proof(cases s rule: height.cases)
              case (3 _ u)
              then have "u \<in> P \<union> T"
                using P_T_partition_verts(2) adj_in_verts(1) by blast
              with 3 that have "realise u \<in> elts (realise s)"
                by auto
              then obtain u' where "u' \<rightarrow>\<^bsub>G\<^esub> s'" "realise u' = realise u"
                using dominates_if_mem_realisation
                by (metis \<open>s' \<in> P \<union> T\<close> \<open>u \<in> P \<union> T\<close> assms(2) s'(1))

              then show ?thesis
                using \<open>realise u \<in> elts (realise s)\<close> \<open>s' \<in> P\<close> assms(2) s'(1)
                by (metis P_T_partition_verts(2)
                    adj_in_verts(1) elts_of_set mem_not_refl realise.simps(1)
                    singletonD small_empty small_insert)
            qed auto
          qed
          with nP_Suc have ?thesis if "s \<in> T" "s' \<notin> T"
            using that \<open>height s' < height t2\<close> by linarith
          ultimately show ?thesis
            using nP_Suc Suc \<open>s \<in> P \<union> T\<close> by auto
        qed auto
      qed
    qed
  qed
qed

lemma lemma1_2:
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realise y"
  assumes "t1 \<in> P \<union> T" "t2 \<in> P \<union> T" "realise t1 = realise t2"
  shows "height t1 = height t2"
  using assms lemma1_2' le_antisym unfolding inj_on_def by metis

lemma lemma1_3:
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realise y"
  assumes "s \<in> P \<union> T" "t \<in> P \<union> T" "realise s \<in> elts (realise t)"
  shows "height s < height t"
proof -
  from assms dominates_if_mem_realisation obtain s' where
    s': "realise s' = realise s" "s' \<rightarrow>\<^bsub>G\<^esub> t" by metis
  then have "s' \<in> P \<union> T"
    using adj_in_verts P_T_partition_verts by blast
  from assms(2-5) have "t \<in> T"
    by (metis elts_of_set mem_not_sym realise.cases realise.simps(1) singletonD
              small_empty small_insert)
  with lemma1_1[OF \<open>s' \<in> P \<union> T\<close>] assms s' have "height s' < height t"
    by auto
  moreover from lemma1_2[OF _ _ \<open>s' \<in> P \<union> T\<close> _ s'(1)] have "height s' = height s"
    using assms by blast
  ultimately show ?thesis
    by linarith
qed

lemma card_realisation_T_less_card_verts:
  "t \<in> T \<Longrightarrow> card (elts (realise t)) < card (P \<union> T)"
proof(induction t rule: realise.induct)
  case (2 t)
  then have "t \<in> verts G"
    using P_T_partition_verts by simp
  then have "parents G t \<subset> verts G"
    using adj_not_same by auto
  from psubset_card_mono[OF _ this] have "card (parents G t) < card (verts G)"
    by simp
  then have "card (realise ` parents G t) < card (verts G)"
    using card_image_le[OF finite_parents, where ?f=realise and ?s1=t] by linarith 
  with 2 show ?case
    using P_T_partition_verts(2) by auto
qed (use P_T_partition_verts in auto)

lemma card_realisation_P:
  "p \<in> P \<Longrightarrow> card (elts (realise p)) = 1"
  by simp

lemma card_elts_realisation_T:
  assumes "t \<in> T" "x \<in> elts (realise t)"
  shows "card (elts x) < card (P \<union> T)"
proof -
  obtain s where s: "x = realise s" "s \<in> parents G t"
    using assms by force
  then have "s \<in> P \<union> T"
    using P_T_partition_verts(2) adj_in_verts(1) by blast
  with s have "{s, t} \<subseteq> P \<union> T" "s \<noteq> t"
    using assms(1) adj_not_same s(2) by blast+
  with finite_P_un_T have "card (P \<union> T) \<ge> 2"
    by (metis card_2_iff card_mono)
  with \<open>s \<in> P \<union> T\<close> s show ?thesis
    using card_realisation_T_less_card_verts
    by auto
qed

end

end