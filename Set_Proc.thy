theory Set_Proc                
  imports Main Logic ZFC_in_HOL.ZFC_in_HOL Graph_Theory.Graph_Theory "HOL-Library.Sublist"
    "HOL-Eisbach.Eisbach"
begin

abbreviation "vset \<equiv> ZFC_in_HOL.set"

hide_const (open) ZFC_in_HOL.set

datatype 'a pset_term = 
  Empty (\<open>\<emptyset>\<close>)| Var 'a |
  Union "'a pset_term" "'a pset_term" (infixr \<open>\<squnion>\<^sub>s\<close> 60) |
  Inter "'a pset_term" "'a pset_term" (infixr \<open>\<sqinter>\<^sub>s\<close> 70) |
  Diff "'a pset_term" "'a pset_term"  (infixl \<open>-\<^sub>s\<close> 80) |
  Single "'a pset_term"

datatype 'a pset_atom =
  Elem "'a pset_term" "'a pset_term" (infix \<open>\<in>\<^sub>s\<close> 55) | 
  Equal "'a pset_term" "'a pset_term" (infix \<open>\<approx>\<^sub>s\<close> 55)

type_synonym 'a pset_literal = "bool \<times> 'a pset_atom"

definition "vdiff s1 s2 \<equiv> vset (elts s1 - elts s2)"

fun I\<^sub>s\<^sub>t :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_term \<Rightarrow> V" where
  "I\<^sub>s\<^sub>t v \<emptyset> = 0"
| "I\<^sub>s\<^sub>t v (Var x) = v x"
| "I\<^sub>s\<^sub>t v (s1 \<squnion>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<squnion> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 \<sqinter>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<sqinter> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 -\<^sub>s s2) = vdiff (I\<^sub>s\<^sub>t v s1) (I\<^sub>s\<^sub>t v s2)"
| "I\<^sub>s\<^sub>t v (Single s) = vset {I\<^sub>s\<^sub>t v s}"

fun I\<^sub>s\<^sub>a :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>a v (t1 \<in>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<in> elts (I\<^sub>s\<^sub>t v t2)"
| "I\<^sub>s\<^sub>a v (t1 \<approx>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 = I\<^sub>s\<^sub>t v t2"

definition I\<^sub>s\<^sub>l :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_literal \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>l v \<equiv> (\<lambda>(b, a). b \<longleftrightarrow> I\<^sub>s\<^sub>a v a)"

type_synonym 'a pset_fm = "'a pset_literal fm"

abbreviation ancestors1 :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ancestors1 G s \<equiv> {u. u \<rightarrow>\<^bsub>G\<^esub> s}"

abbreviation ancestors :: "('a,'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "ancestors G s \<equiv> {u. u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> s}"

lemma (in fin_digraph) finite_ancestors1[intro]: "finite (ancestors1 G s)"
  using reachable_in_verts
  by (auto intro: rev_finite_subset[where ?A="ancestors1 G s", OF finite_verts])

lemma (in fin_digraph) small_ancestors1[intro]: "small (ancestors1 G s)"
  using finite_imp_small finite_ancestors1 by blast

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

lemma ancestors_not_comm:
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
  using assms ancestors_mono ancestors_not_comm by blast

lemma card_ancestors_strict_mono:
  assumes "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "card (ancestors G s) < card (ancestors G t)"
  using assms finite_ancestors ancestors_strict_mono
  by (metis in_ancestors_if_dominates psubset_card_mono)

end

locale realization = dag G for G +
  fixes P T :: "'a set"
  fixes I :: "'a \<Rightarrow> V"
  assumes P_T_partition_verts: "P \<inter> T = {}" "verts G = P \<union> T"
begin
 
function height :: "'a \<Rightarrow> nat" where
  "t \<in> P \<Longrightarrow> height t = 0"
| "t \<notin> P \<Longrightarrow> \<forall>s. \<not> s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = 0"
| "t \<notin> P \<Longrightarrow> s \<rightarrow>\<^bsub>G\<^esub> t \<Longrightarrow> height t = Max (height ` ancestors1 G t) + 1"
  by auto
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma height_cases':
  obtains (P_0) "t \<in> P" "height t = 0"
    | (nP_0) "t \<notin> P" "\<forall>s. \<not> s \<rightarrow>\<^bsub>G\<^esub> t" "height t = 0"
    | (nP_Suc) s where "t \<notin> P" "s \<rightarrow>\<^bsub>G\<^esub> t" "height t = height s + 1"
proof(cases t rule: height.cases)
  case (3 t s)
  note Max_in[OF finite_imageI[where ?h=height, OF finite_ancestors1]]
  with 3 that show ?thesis
    by auto
qed simp_all

function realization :: "'a \<Rightarrow> V" where
  "x \<in> P \<Longrightarrow> realization x = vset {I x}"
| "t \<in> T \<Longrightarrow> realization t = vset (realization ` ancestors1 G t)"
| "x \<notin> P \<union> T \<Longrightarrow> realization x = 0"
  using P_T_partition_verts by auto
termination
  by (relation "measure (\<lambda>t. card (ancestors G t))") (simp_all add: card_ancestors_strict_mono)

lemma small_realization_ancestors1[iff]: "small (realization ` ancestors1 G t)"
  using small_ancestors1 by auto

lemma lemma1_1:
  assumes "s \<in> P \<union> T" "t \<in> T" "s \<rightarrow>\<^bsub>G\<^esub> t"
  shows "height s < height t"
  using assms
proof(cases t rule: height.cases)
  case (3 t u)
  note Max_ge[OF finite_imageI[where ?h=height, OF finite_ancestors1], of "height s" t]
  with assms 3 show ?thesis
    by auto
qed (use P_T_partition_verts in auto)

lemma dominates_if_mem_realization:
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<union> T \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> realization y"
  assumes "s \<in> P \<union> T" "t \<in> P \<union> T"
  assumes "realization s \<in> elts (realization t)"
  obtains s' where "s' \<rightarrow>\<^bsub>G\<^esub> t" "realization s = realization s'"
  using assms(2-)
proof(induction t rule: realization.induct)
  case (1 x)
  with assms(1)[OF \<open>x \<in> P\<close>] show ?case 
    apply(simp)
    by (metis "1.prems"(4) mem_not_sym)
qed auto

lemma lemma1_2':
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> I y"
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<union> T \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> realization y"
  assumes "t1 \<in> P \<union> T" "t2 \<in> P \<union> T" "realization t1 = realization t2"
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
      have "small (realization ` ancestors1 G t1)"
        by blast+
      with 2 3 assms(5) have "realization ` ancestors1 G t1 = {I t2}"
        using \<open>small (realization ` ancestors1 G t1)\<close> by force
      moreover from 3 adj_in_verts P_T_partition_verts have "s \<in> P \<union> T"
        by simp
      then have "I t2 \<noteq> realization s"
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
        with 0 less.prems assms(2) show ?thesis
          using P_T_partition_verts(1)
          apply(cases t2 rule: height_cases'; cases t1 rule: height_cases')
            apply(auto)
          by (metis (no_types, lifting) Collect_empty_eq elts_of_set empty_is_image less.prems(3)
                  realization.simps(2) small_realization_ancestors1)
      next
        case (Suc x)
        then have "t2 \<notin> P"
          using less.prems(2) by fastforce
        then show ?thesis
        proof(cases t1 rule: height_cases')
          case (nP_Suc s)
          with P_T_partition_verts adj_in_verts(1) have "s \<in> P \<union> T"
            by blast
          from nP_Suc less.prems(1) have "realization s \<in> elts (realization t1)"
            by auto
          then obtain s' where s': "realization s' = realization s" "s' \<rightarrow>\<^bsub>G\<^esub> t2"
            using dominates_if_mem_realization \<open>s \<in> P \<union> T\<close> less.prems assms(2)
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
              with 3 that have "realization u \<in> elts (realization s)"
                by auto
              then obtain u' where "u' \<rightarrow>\<^bsub>G\<^esub> s'" "realization u' = realization u"
                using dominates_if_mem_realization
                by (metis \<open>s' \<in> P \<union> T\<close> \<open>u \<in> P \<union> T\<close> assms(2) s'(1))

              then show ?thesis
                using \<open>realization u \<in> elts (realization s)\<close> \<open>s' \<in> P\<close> assms(2) s'(1)
                by (metis P_T_partition_verts(2)
                    adj_in_verts(1) elts_of_set mem_not_refl realization.simps(1)
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
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> I y"
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<union> T \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> realization y"
  assumes "t1 \<in> P \<union> T" "t2 \<in> P \<union> T" "realization t1 = realization t2"
  shows "height t1 = height t2"
  using assms lemma1_2' le_antisym by metis
    
lemma lemma1_3:
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> I y"
  assumes "\<And>x y. x \<in> P \<Longrightarrow> y \<in> P \<union> T \<Longrightarrow> x \<noteq> y \<Longrightarrow> I x \<noteq> realization y"
  assumes "s \<in> P \<union> T" "t \<in> P \<union> T" "realization s \<in> elts (realization t)"
  shows "height s < height t"
proof -
  from assms dominates_if_mem_realization obtain s' where
    s': "realization s' = realization s" "s' \<rightarrow>\<^bsub>G\<^esub> t" by metis
  then have "s' \<in> P \<union> T"
    using adj_in_verts P_T_partition_verts by blast
  from assms(2-5) have "t \<in> T"
    by (metis elts_of_set mem_not_sym realization.cases realization.simps(1) singletonD
              small_empty small_insert)
  with lemma1_1[OF \<open>s' \<in> P \<union> T\<close>] assms s' have "height s' < height t"
    by auto
  moreover from lemma1_2[OF _ _ \<open>s' \<in> P \<union> T\<close> _ s'(1)] have "height s' = height s"
    using assms by blast
  ultimately show ?thesis
    by linarith
qed

lemma ancestors1_subs_verts: "t \<in> verts G \<Longrightarrow> ancestors1 G t \<subset> verts G"
  using adj_not_same by auto

lemma card_realization_less_card_verts:
  "t \<in> T \<Longrightarrow> card (elts (realization t)) < card (P \<union> T)"
proof(induction t rule: realization.induct)
  case (2 t)
  then have "t \<in> verts G"
    using P_T_partition_verts by simp
  then have "ancestors1 G t \<subset> verts G"
    using adj_not_same by auto
  from psubset_card_mono[OF _ this] have "card (ancestors1 G t) < card (verts G)"
    by simp
  then have "card (realization ` ancestors1 G t) < card (verts G)"
    using card_image_le[OF finite_ancestors1, where ?f=realization and ?s1=t] by linarith 
  with 2 show ?case
    using P_T_partition_verts(2) by auto
qed (use P_T_partition_verts in auto)

end



type_synonym 'a branch = "'a pset_fm list"

definition vars_fm :: "'a pset_fm \<Rightarrow> 'a set" where
  "vars_fm \<phi> \<equiv> \<Union>((\<lambda>(b, a). set_pset_atom a) ` atoms \<phi>)"

lemma vars_fm_simps:
  "vars_fm (Atom x) = set_pset_atom (snd x)"
  "vars_fm (And p q) = vars_fm p \<union> vars_fm q"
  "vars_fm (Or p q) = vars_fm p \<union> vars_fm q"
  "vars_fm (Neg p) = vars_fm p"
  unfolding vars_fm_def
     apply(auto)
  done

definition vars_branch :: "'a branch \<Rightarrow> 'a set" where
  "vars_branch b \<equiv> \<Union>(vars_fm ` set b)"

lemma vars_branch_simps:
  "vars_branch [] = {}"
  "vars_branch (x # xs) = vars_fm x \<union> vars_branch xs"
  unfolding vars_branch_def by auto

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_literal list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((True, s' \<in>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_literal list \<Rightarrow> bool" where
  "member_cycle ((True, s \<in>\<^sub>s t) # cs) = member_seq s ((True, s \<in>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

abbreviation "AT a \<equiv> Atom (True, a)"
abbreviation "AF a \<equiv> Atom (False, a)"

fun subterms where
  "subterms \<emptyset> = {\<emptyset>}"
| "subterms (Var i) = {Var i}"
| "subterms (t1 \<squnion>\<^sub>s t2) = {t1 \<squnion>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 \<sqinter>\<^sub>s t2) = {t1 \<sqinter>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 -\<^sub>s t2) = {t1 -\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (Single t) = {Single t} \<union> subterms t"

fun subterms_literal where
  "subterms_literal (_, t1 \<in>\<^sub>s t2) = subterms t1 \<union> subterms t2"
| "subterms_literal (_, t1 \<approx>\<^sub>s t2) = subterms t1 \<union> subterms t2"

fun subterms_fm where
  "subterms_fm (Atom a) = subterms_literal a"
| "subterms_fm (Neg f) = subterms_fm f"
| "subterms_fm (Or f1 f2) = subterms_fm f1 \<union> subterms_fm f2"
| "subterms_fm (And f1 f2) = subterms_fm f1 \<union> subterms_fm f2"

definition "subterms_branch b \<equiv> \<Union>(subterms_fm ` set b)"

lemma subterms_branch_simps:
  "subterms_branch [] = {}"
  "subterms_branch (x # xs) = subterms_fm x \<union> subterms_branch xs"
  unfolding subterms_branch_def by auto

fun tlvl_terms_literal where
  "tlvl_terms_literal (_, t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms_literal (_, t1 \<approx>\<^sub>s t2) = {t1, t2}"

fun subst_tlvl_literal where
  "subst_tlvl_literal t1 t2 (b, s1 \<in>\<^sub>s s2) =
    (b, (if s1 = t1 then t2 else s1) \<in>\<^sub>s (if s2 = t1 then t2 else s2))"
| "subst_tlvl_literal t1 t2 (b, s1 \<approx>\<^sub>s s2) =
    (b, (if s1 = t1 then t2 else s1) \<approx>\<^sub>s (if s2 = t1 then t2 else s2))"

inductive lextends_fm :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "And p q \<in> set branch \<Longrightarrow> lextends_fm (p # q # branch) branch"
| "Neg (Or p q) \<in> set branch \<Longrightarrow> lextends_fm (Neg p # Neg q # branch) branch"
| "\<lbrakk> Or p q \<in> set branch; Neg p \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm (q # branch) branch"
| "\<lbrakk> Or p q \<in> set branch; Neg q \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm (p # branch) branch"
| "\<lbrakk> Neg (And p q) \<in> set branch; p \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm (Neg q # branch) branch"
| "\<lbrakk> Neg (And p q) \<in> set branch; q \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm (Neg p # branch) branch"

inductive lextends_un :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_un (AF (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un (AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un (AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_un (AT (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_un (AT (s \<in>\<^sub>s t1) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un (AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch"

inductive lextends_int :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_int (AT (s \<in>\<^sub>s t1) # AT (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int (AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t2) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int (AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_int (AF (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_int (AF (s \<in>\<^sub>s t1) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; AT (s \<in>\<^sub>s t2) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int (AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch"

inductive lextends_diff :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_diff (AT (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff (AF (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff (AF (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_diff (AT (s \<in>\<^sub>s t2) # branch) branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_diff (AF (s \<in>\<^sub>s t1) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff (AT (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch"

inductive lextends_single :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "Single t1 \<in> subterms_fm (last branch) \<Longrightarrow> lextends_single (AT (t1 \<in>\<^sub>s Single t1) # branch) branch"
| "AT (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> lextends_single (AT (s \<approx>\<^sub>s t1) # branch) branch"
| "AF (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> lextends_single (AF (s \<approx>\<^sub>s t1) # branch) branch"

inductive lextends_eq :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; Atom l \<in> set branch; t1 \<in> tlvl_terms_literal l \<rbrakk>
    \<Longrightarrow> lextends_eq (Atom (subst_tlvl_literal t1 t2 l) # branch) branch"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; Atom l \<in> set branch; t2 \<in> tlvl_terms_literal l \<rbrakk>
    \<Longrightarrow> lextends_eq (Atom (subst_tlvl_literal t2 t1 l) # branch) branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t) \<in> set branch;  AF (s' \<in>\<^sub>s t) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_eq (AF (s \<approx>\<^sub>s s') # branch) branch"

inductive lextends :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "lextends_fm b' b \<Longrightarrow> lextends b' b"
| "lextends_un b' b \<Longrightarrow> lextends b' b"
| "lextends_int b' b \<Longrightarrow> lextends b' b"
| "lextends_diff b' b \<Longrightarrow> lextends b' b"
| "lextends_single b' b \<Longrightarrow> lextends b' b"
| "lextends_eq b' b \<Longrightarrow> lextends b' b"

lemma lextends_induct[consumes 1]:
  assumes "lextends b' b"
  shows "
    (\<And>p q branch. And p q \<in> set branch \<Longrightarrow> P (p # q # branch) branch) \<Longrightarrow>
    (\<And>p q branch. Neg (Or p q) \<in> set branch \<Longrightarrow> P (Neg p # Neg q # branch) branch) \<Longrightarrow>
    (\<And>p q branch. Or p q \<in> set branch \<Longrightarrow> Neg p \<in> set branch \<Longrightarrow> P (q # branch) branch) \<Longrightarrow>
    (\<And>p q branch. Or p q \<in> set branch \<Longrightarrow> Neg q \<in> set branch \<Longrightarrow> P (p # branch) branch) \<Longrightarrow>
    (\<And>p q branch. Neg (And p q) \<in> set branch \<Longrightarrow> p \<in> set branch \<Longrightarrow> P (Neg q # branch) branch) \<Longrightarrow>
    (\<And>p q branch. Neg (And p q) \<in> set branch \<Longrightarrow> q \<in> set branch \<Longrightarrow> P (Neg p # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AF (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P (AT (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AT (s \<in>\<^sub>s t1) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AT (s \<in>\<^sub>s t1) # AT (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P (AF (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AF (s \<in>\<^sub>s t1) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AT (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AF (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AF (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P (AT (s \<in>\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P (AF (s \<in>\<^sub>s t1) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P (AT (s \<in>\<^sub>s t1 -\<^sub>s t2) # branch) branch) \<Longrightarrow>
    (\<And>t1 branch. Single t1 \<in> subterms_fm (last branch) \<Longrightarrow> P (AT (t1 \<in>\<^sub>s Single t1) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch. AT (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> P (AT (s \<approx>\<^sub>s t1) # branch) branch) \<Longrightarrow>
    (\<And>s t1 branch. AF (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> P (AF (s \<approx>\<^sub>s t1) # branch) branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> Atom l \<in> set branch \<Longrightarrow> t1 \<in> tlvl_terms_literal l \<Longrightarrow> P (Atom (subst_tlvl_literal t1 t2 l) # branch) branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> Atom l \<in> set branch \<Longrightarrow> t2 \<in> tlvl_terms_literal l \<Longrightarrow> P (Atom (subst_tlvl_literal t2 t1 l) # branch) branch) \<Longrightarrow>
    (\<And>s t branch s'. AT (s \<in>\<^sub>s t) \<in> set branch \<Longrightarrow> AF (s' \<in>\<^sub>s t) \<in> set branch \<Longrightarrow> P (AF (s \<approx>\<^sub>s s') # branch) branch) \<Longrightarrow> P b' b"
  using assms
  apply(induction rule: lextends.induct)
  subgoal apply(induction rule: lextends_fm.induct) by metis+
  subgoal apply(induction rule: lextends_un.induct) by metis+
  subgoal apply(induction rule: lextends_int.induct) by metis+
  subgoal apply(induction rule: lextends_diff.induct) by metis+
  subgoal apply(induction rule: lextends_single.induct) by metis+
  subgoal apply(induction rule: lextends_eq.induct) by metis+
  done

lemma lextends_strict_suffix:
  "lextends b1 b2 \<Longrightarrow> strict_suffix b2 b1"
  by (induction rule: lextends_induct) (auto simp: strict_suffix_def suffix_def)

lemma subterms_refl[simp]:
  "t \<in> subterms t"
  by (induction t) auto

lemma subterms_subterms_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms v \<Longrightarrow> s \<in> subterms v"
  apply(induction v)
       apply(auto)
  done

lemma subterms_subterms_literal_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_literal v \<Longrightarrow> s \<in> subterms_literal v"
  apply(cases v rule: subterms_literal.cases)
  using subterms_subterms_trans by auto

lemma subterms_subterms_fm_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_fm \<phi> \<Longrightarrow> s \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
  using subterms_subterms_literal_trans by (force)+

lemma subterms_subterms_branch_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_branch b \<Longrightarrow> s \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_subterms_fm_trans by blast

lemma tlvl_terms_literal_subs_subterms_literal:
  "tlvl_terms_literal l \<subseteq> subterms_literal l"
  apply(cases l rule: tlvl_terms_literal.cases)  by auto

lemma subterms_literal_subst_tlvl_subs:
  "subterms_literal (subst_tlvl_literal t1 t2 l) \<subseteq> subterms t2 \<union> subterms_literal l"
  apply(cases "(t1, t2, l)" rule: subst_tlvl_literal.cases)
    apply(auto)
  done

lemmas lextends_mono = strict_suffix_set_subset[OF lextends_strict_suffix]

definition "lin_sat branch \<equiv> (\<nexists>branch'. lextends branch' branch \<and> set branch \<subset> set branch')"

inductive bclosed :: "'a branch \<Rightarrow> bool" where
  contr: "\<lbrakk> \<phi> \<in> set branch; Neg \<phi> \<in> set branch \<rbrakk> \<Longrightarrow> bclosed branch"
| elemEmpty: "AT (t \<in>\<^sub>s \<emptyset>) \<in> set branch \<Longrightarrow> bclosed branch"
| neqSelf: "AF (t \<approx>\<^sub>s t) \<in> set branch \<Longrightarrow> bclosed branch"
| memberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set branch) \<rbrakk> \<Longrightarrow> bclosed branch"

abbreviation "bopen branch \<equiv> \<not> bclosed branch"

inductive extends :: "'a branch list \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set branch;
     p \<notin> set branch; Neg p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends [p # branch, Neg p # branch] branch"
| "\<lbrakk> Neg (And p q) \<in> set branch;
     Neg p \<notin> set branch; p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends [Neg p # branch, p # branch] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t1) \<notin> set branch; AF (s \<in>\<^sub>s t1) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends [AT (s \<in>\<^sub>s t1) # branch, AF (s \<in>\<^sub>s t1) # branch] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends [AT (s \<in>\<^sub>s t2) # branch, AF (s \<in>\<^sub>s t2) # branch] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends [AT (s \<in>\<^sub>s t2) # branch, AF (s \<in>\<^sub>s t2) # branch] branch"
| "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set branch; t1 \<in> subterms_fm (last branch); t2 \<in> subterms_fm (last branch);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set branch \<and> AF (x \<in>\<^sub>s t2) \<in> set branch;
     \<nexists>x. AF (x \<in>\<^sub>s t1) \<in> set branch \<and> AT (x \<in>\<^sub>s t2) \<in> set branch;
     x \<notin> vars_branch branch \<rbrakk>
    \<Longrightarrow> extends [AT (Var x \<in>\<^sub>s t1) # AF (Var x \<in>\<^sub>s t2) # branch, AF (Var x \<in>\<^sub>s t1) # AT (Var x \<in>\<^sub>s t2) # branch] branch"


lemma extends_strict_suffix:
  "extends bs b \<Longrightarrow> b' \<in> set bs \<Longrightarrow> strict_suffix b b'"
  apply(induction rule: extends.induct)
                      apply(auto simp: strict_suffix_def suffix_def)
  done

lemmas extends_mono = strict_suffix_set_subset[OF extends_strict_suffix]

inductive extendss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "lextends b1 b2 \<Longrightarrow> extendss b2 b3 \<Longrightarrow> extendss b1 b3"
| "extends bs b2 \<Longrightarrow> b1 \<in> set bs \<Longrightarrow> extendss b2 b3 \<Longrightarrow> extendss b1 b3"
| "lextends b1 b2 \<Longrightarrow> extendss b1 b2"
| "extends bs b \<Longrightarrow> b1 \<in> set bs \<Longrightarrow> extendss b1 b"

lemma extendss_strict_suffix:
  "extendss b1 b2 \<Longrightarrow> strict_suffix b2 b1"
  apply(induction rule: extendss.induct)
     apply(use lextends_strict_suffix extends_strict_suffix in \<open>force+\<close>)
  done

lemmas extendss_mono = strict_suffix_set_subset[OF extendss_strict_suffix]

inductive closeable :: "'a branch \<Rightarrow> bool" where
  "bclosed b \<Longrightarrow> closeable b"
| "lextends b' b \<Longrightarrow> closeable b' \<Longrightarrow> closeable b"
| "extends bs b \<Longrightarrow> \<forall>b' \<in> set bs. closeable b' \<Longrightarrow> closeable b"

definition "sat branch \<equiv> lin_sat branch \<and> (\<nexists>branches. extends branches branch)"

definition "params branch \<equiv> vars_branch branch - vars_fm (last branch)"

definition "params' b \<equiv>
  {c \<in> params b. \<forall>t \<in> subterms_fm (last b).
    AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b }"

definition "subterms_branch' branch \<equiv>
  subterms_fm (last branch) \<union> Var ` (params branch - params' branch)"

definition "bgraph branch \<equiv>
  let
    vs = Var ` params branch \<union> subterms_branch' branch
  in
    \<lparr> verts = vs,
      arcs = {(s, t) \<in> vs \<times> vs. AT (s \<in>\<^sub>s t) \<in> set branch},
      tail = fst,
      head = snd \<rparr>"

lemma vars_fm_Atom[simp]: "vars_fm (Atom (b, a)) = set_pset_atom a"
  unfolding vars_fm_def by simp

lemma Un_set_pset_term_subterms_eq_set_pset_term:
  "\<Union>(set_pset_term ` subterms t) = set_pset_term t"
  by (induction t) auto

lemma Un_set_pset_term_subterms_fm_eq_vars_fm:
  "\<Union>(set_pset_term ` subterms_fm \<phi>) = vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom x)
  then show ?case
    by (cases x rule: subterms_literal.cases)
       (auto simp: Un_set_pset_term_subterms_eq_set_pset_term vars_fm_simps)
qed (fastforce simp: vars_fm_simps)+

lemma Un_set_pset_term_subterms_branch_eq_vars_branch:
  "\<Union>(set_pset_term ` subterms_branch b) = vars_branch b"
  using Un_set_pset_term_subterms_fm_eq_vars_fm
  unfolding vars_branch_def subterms_branch_def
  by force

lemma subs_vars_branch_if_subs_subterms_branch:
  "subterms_branch b1 \<subseteq> subterms_branch b2 \<Longrightarrow> vars_branch b1 \<subseteq> vars_branch b2"
  using Un_set_pset_term_subterms_branch_eq_vars_branch
  by (metis complete_lattice_class.Sup_subset_mono subset_image_iff)

lemma subterms_branch_eq_if_vars_branch_eq:
  "subterms_branch b1 = subterms_branch b2 \<Longrightarrow> vars_branch b1 = vars_branch b2"
  using subs_vars_branch_if_subs_subterms_branch by blast

lemma mem_pset_term_if_mem_subterms:
  "x \<in> set_pset_term s \<Longrightarrow> s \<in> subterms t \<Longrightarrow> x \<in> set_pset_term t"
  apply(induction t)
       apply(auto intro: pset_term.set_intros)
  done

lemma mem_pset_fm_if_mem_subterm_fm:
  "x \<in> set_pset_term s \<Longrightarrow> s \<in> subterms_fm \<phi> \<Longrightarrow> x \<in> vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom x)
  then show ?case
    by (cases x rule: subterms_literal.cases)
       (auto simp: mem_pset_term_if_mem_subterms vars_fm_simps)
qed (auto simp: vars_fm_def)


lemma set_pset_term_subs_subterms:
  "v \<in> set_pset_term t \<Longrightarrow> Var v \<in> subterms t"
  apply(induction t)
       apply(auto)
  done

lemma set_pset_atom_subs_subterms_literal:
  "v \<in> set_pset_atom a \<Longrightarrow> Var v \<in> subterms_literal (b, a)"
  apply(cases "(b, a)" rule: subterms_literal.cases)
   apply(auto simp: set_pset_term_subs_subterms)
  done

lemma vars_fm_subs_subterms_fm:
  "v \<in> vars_fm \<phi> \<Longrightarrow> Var v \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
     apply(auto simp: set_pset_atom_subs_subterms_literal vars_fm_simps)
  done

lemma vars_branch_subs_subterms_branch:
  "Var ` vars_branch b \<subseteq> subterms_branch b"
  unfolding vars_branch_def subterms_branch_def
  apply(auto simp: vars_fm_subs_subterms_fm)
  done

lemma subterms_branch_subterms_subterms_literal_trans:
  "Atom a \<in> set b \<Longrightarrow> x \<in> subterms s \<Longrightarrow> s \<in> subterms_literal a \<Longrightarrow> x \<in> subterms_branch b"
  unfolding subterms_branch_def
  by (metis UN_I subterms_fm.simps(1) subterms_literal.simps subterms_subterms_literal_trans)

lemma subterms_branch_subterms_subterms_fm_trans:
  "b \<noteq> [] \<Longrightarrow> x \<in> subterms t \<Longrightarrow> t \<in> subterms_fm (last b) \<Longrightarrow> x \<in> subterms_branch b"
  using subterms_branch_def subterms_subterms_fm_trans by fastforce

method subterms_trans =
  (match conclusion in "X \<in> subterms_branch B" for X B \<Rightarrow> \<open>
    match premises in X: "X \<in> subterms T" for T \<Rightarrow> \<open>
        (match premises in not_Nil: "B \<noteq> []" and T: "T \<in> subterms_fm (last B)" \<Rightarrow> \<open>
          (rule subterms_branch_subterms_subterms_fm_trans[OF not_Nil X T]) 
        \<close>)
      | (match premises in T: "Atom (b, ?C T) \<in> set B" for b \<Rightarrow> \<open>
          (rule subterms_branch_subterms_subterms_literal_trans[OF T X]; simp; fail)
        \<close>)
    \<close>
  \<close>)

lemmas subterms_simps =
  subterms_branch_simps subterms_fm.simps subterms_literal.simps

method solve_subterms = (unfold subterms_simps, safe; subterms_trans)

lemma lextends_subterms_branch_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms_branch b' = subterms_branch b"
proof(induction rule: lextends.induct)
  case (1 b' b)
  then show ?case
    apply(induction rule: lextends_fm.induct)
    apply(auto simp: subterms_branch_def)
    done
next
  case (2 b' b)
  then show ?case
    apply(induction rule: lextends_un.induct)
         apply(solve_subterms+)
    done

next
  case (3 b' b)
  then show ?case
    apply(induction rule: lextends_int.induct)
         apply(solve_subterms+)
    done
next
  case (4 b' b)
  then show ?case
    apply(induction rule: lextends_diff.induct)
         apply(solve_subterms+)
    done
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (1 t1 branch)
    then show ?case
      apply(auto simp: subterms_branch_simps)
      by (metis subterms_refl UnCI subterms_branch_subterms_subterms_fm_trans subterms.simps(6))+
  qed solve_subterms+
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lextends_eq.induct)
    case (1 t1 t2 branch l)
    then show ?case
      by (auto simp: subterms_branch_def subterms_branch_subterms_subterms_literal_trans
               dest!: subsetD[OF subterms_literal_subst_tlvl_subs])
  next
    case (2 t1 t2 branch l)
    then show ?case
      by (auto simp: subterms_branch_def subterms_branch_subterms_subterms_literal_trans
               dest!: subsetD[OF subterms_literal_subst_tlvl_subs])
  next
    case (3 s t branch s')
    then show ?case
      by (auto simp: subterms_branch_simps subterms_branch_subterms_subterms_literal_trans)
  qed
qed

lemma lextends_vars_branch_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars_branch b' = vars_branch b"
  using lextends_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma lextends_last_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  using lextends_strict_suffix unfolding strict_suffix_def suffix_def by force

lemma extends_last_eq:
  "extends bs b \<Longrightarrow> b' \<in> set bs \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  using extends_strict_suffix unfolding strict_suffix_def suffix_def by force

lemma lextends_params_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> params b' = params b"
  using lextends_last_eq lextends_vars_branch_eq unfolding params_def by force

lemma lextends_fm_params'_eq:
  assumes "lextends_fm b' b" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_Atom \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  shows "params' b' = params' b"
  using assms
  apply(induction rule: lextends_fm.induct)
       apply(fastforce simp: params'_def params_def vars_branch_def vars_fm_simps)+
  done

lemma lextends_params'_subs:
  assumes "lextends b' b" "b \<noteq> []"
  shows "params' b' \<subseteq> params' b"
  using assms lextends_params_eq[OF assms]
  by (induction rule: lextends_induct) (auto simp: params'_def)

lemma subterms_fm_intros:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "Single t \<in> subterms_fm \<phi> \<Longrightarrow> t \<in> subterms_fm \<phi>"
  by (metis UnCI subterms.simps subterms_refl subterms_subterms_fm_trans)+

lemma subterms_branch_intros:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "Single t \<in> subterms_branch b \<Longrightarrow> t \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_fm_intros by fast+

definition "no_new_subterms b \<equiv>
  (\<forall>t. t \<in> subterms_branch b \<and> t \<notin> Var ` params b \<longrightarrow> t \<in> subterms_fm (last b))"

lemma no_new_subtermsI:
  assumes "\<And>t. t \<in> subterms_branch b \<Longrightarrow> t \<notin> Var ` params b \<Longrightarrow> t \<in> subterms_fm (last b)"
  shows "no_new_subterms b"
  using assms unfolding no_new_subterms_def by blast

lemma Var_in_subterms_branch_and_not_in_params:
  assumes "Var v \<in> subterms_branch b" "v \<notin> params b"
  shows "v \<in> vars_fm (last b)"
  using assms unfolding params_def no_new_subterms_def
  by (auto simp: image_set_diff[unfolded inj_on_def] image_UN
                 Un_set_pset_term_subterms_branch_eq_vars_branch[symmetric])

lemma subterms_branch_cases:
  assumes "t \<in> subterms_branch b" "t \<notin> Var ` params b"
  obtains
    (Empty) "t = \<emptyset>"
  | (Union) t1 t2 where "t = t1 \<squnion>\<^sub>s t2"
  | (Inter) t1 t2 where "t = t1 \<sqinter>\<^sub>s t2"
  | (Diff) t1 t2 where "t = t1 -\<^sub>s t2"
  | (Single) t1 where "t = Single t1"
  | (Var) v where "t = Var v" "v \<in> vars_fm (last b)"
proof(cases t)
  case (Var x)
  with assms have "x \<in> vars_fm (last b)"
    using Var_in_subterms_branch_and_not_in_params by (metis imageI)
  with Var that show ?thesis by blast
qed (use assms that in auto)

lemma no_new_subterms_casesI[case_names Empty Union Inter Diff Single]:
  assumes "\<emptyset> \<in> subterms_branch b \<Longrightarrow> \<emptyset> \<in> subterms_fm (last b)"
  assumes "\<And>t1 t2. t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b)"
  assumes "\<And>t1 t2. t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b)"
  assumes "\<And>t1 t2. t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
  assumes "\<And>t. Single t \<in> subterms_branch b \<Longrightarrow> Single t \<in> subterms_fm (last b)"
  shows "no_new_subterms b"
proof(intro no_new_subtermsI)
  fix t assume "t \<in> subterms_branch b" "t \<notin> Var ` params b"
  with this assms show "t \<in> subterms_fm (last b)"
    by (cases t rule: subterms_branch_cases) (auto simp: vars_fm_subs_subterms_fm)
qed

lemma no_new_subtermsE:
  assumes "no_new_subterms b"
  shows "\<emptyset> \<in> subterms_branch b \<Longrightarrow> \<emptyset> \<in> subterms_fm (last b)"
        "\<And>t1 t2. t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b)"
        "\<And>t1 t2. t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b)"
        "\<And>t1 t2. t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
        "\<And>t. Single t \<in> subterms_branch b \<Longrightarrow> Single t \<in> subterms_fm (last b)"
  using assms unfolding no_new_subterms_def by auto
 
lemma mem_in_subterms_branch_if_in_atoms_branch:
  assumes "(p, t1 \<in>\<^sub>s t2) \<in> \<Union>(atoms ` set b)"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(p, t1 \<in>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

lemma eq_in_subterms_branch_if_in_atoms_branch:
  assumes "(p, t1 \<approx>\<^sub>s t2) \<in> \<Union>(atoms ` set b)"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(p, t1 \<approx>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

lemma lextends_no_new_subterms:
  assumes "lextends b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  shows "no_new_subterms b'"
  using assms unfolding no_new_subterms_def
  by (simp add: lextends_last_eq lextends_params_eq lextends_subterms_branch_eq[OF assms(1,2)])

lemma subterms_branch_subterms_literalI:
  assumes "Atom l \<in> set branch" "t \<in> subterms_literal l"
  shows "t \<in> subterms_branch branch"
  using assms unfolding subterms_branch_def  
  by (cases l rule: subterms_literal.cases) (metis UnionI imageI subterms_fm.simps(1))+

lemma vars_branch_vars_fmI:
  assumes "\<phi> \<in> set branch" "v \<in> vars_fm \<phi>"
  shows "v \<in> vars_branch branch"
  using assms vars_branch_def vars_fm_def by fastforce

lemma extends_no_new_subterms:
  assumes "extends bs b" "b \<noteq> []"
  assumes "b' \<in> set bs"
  assumes "no_new_subterms b"
  shows "no_new_subterms b'"
  using assms
proof(induction rule: extends.induct)
  case (1 p q branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps intro!: no_new_subterms_casesI)
    apply (metis UN_I UnCI subterms_branch_def subterms_fm.simps)+
    done
next
  case (2 p q branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps intro!: no_new_subterms_casesI)
    apply (metis UN_I UnCI subterms_branch_def subterms_fm.simps)+
    done
next
  case (3 s t1 t2 branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_literal_trans
               intro!: no_new_subterms_casesI)
    done
next
  case (4 s t1 branch t2)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_literal_trans
               intro: subterms_subterms_fm_trans[OF _ subterms_fm_intros(4)]
               intro!: no_new_subterms_casesI)
    done
next
  case (5 s t1 branch t2)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_literal_trans
               intro: subterms_subterms_fm_trans[OF _ subterms_fm_intros(6)]
               intro!: no_new_subterms_casesI)
    done
next
  case (6 t1 t2 branch x)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_literal_trans
               intro!: no_new_subterms_casesI)
    done
qed

lemmas subterms_branch_subterms_fm_lastI =
  subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]

definition "params_subterms b \<equiv> Var ` params b \<union> subterms_fm (last b)"

lemma subterms_branch_eq_if_no_new_subterms:
  assumes "no_new_subterms b" "b \<noteq> []"
  shows "params_subterms b = subterms_branch b"
  using assms no_new_subtermsE[OF assms(1)]
proof -
  note simps = params_def no_new_subterms_def params_subterms_def
    subterms_branch_simps vars_branch_simps
  with assms show ?thesis
    by (auto simp: simps vars_fm_subs_subterms_fm
                   vars_branch_subs_subterms_branch[unfolded image_subset_iff]
             intro: subterms_branch_subterms_fm_lastI)
qed

lemma aux:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_Atom \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-) lextends_params_eq[OF assms(2,3)]
  by (induction rule: lextends_induct)
     (auto simp: disjoint_iff P_def vars_fm_simps)

lemma params_subterms_last_disjnt: "Var ` params b \<inter> subterms_fm (last b) = {}"
  by (auto simp: params_def intro!: mem_pset_fm_if_mem_subterm_fm)

lemma lemma_2_lextends:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b)"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_Atom \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b. P b c t"
  shows "\<forall>c \<in> params' b'. \<forall>t \<in> params_subterms b'. P b' c t"
  using assms(2-6)
  using lextends_last_eq[OF assms(2,3)] lextends_params_eq[OF assms(2,3)]
        lextends_params'_subs[OF assms(2,3)]
proof(induction rule: lextends.induct)
  case (1 b' b)

  have *: "P b' c t"
    if "\<forall>\<phi> \<in> set b' - set b. vars_fm \<phi> \<inter> params b' = {}"
    and "c \<in> params' b" "t \<in> params_subterms b'" for c t
  proof -
    from that "1.prems"(6) have "\<forall>\<phi> \<in> set b' - set b. \<phi> \<noteq> AT (Var c \<approx>\<^sub>s t) \<and> \<phi> \<noteq> AT (t \<approx>\<^sub>s Var c)"
      by (auto simp: params'_def disjoint_iff)
    with 1 that show ?thesis
      unfolding P_def params_subterms_def by (metis Diff_iff params_subterms_def)
  qed
  moreover
  note params'_eq =lextends_fm_params'_eq[OF "1"(1,2,4)] 
  with "1"(1,4,7) params'_eq have "\<forall>\<phi> \<in> set b' - set b. vars_fm \<phi> \<inter> params b' = {}"
    by (induction rule: lextends_fm.induct) (auto simp: disjoint_iff vars_fm_simps)
  ultimately show ?case
    using 1 by blast
next
  case (2 b' b)
  then show ?case
    apply(induction rule: lextends_un.induct)
         apply(auto simp: params_subterms_def P_def)
    done
next
  case (3 b' b)
  then show ?case
    apply(induction rule: lextends_int.induct)
         apply(auto simp: params_subterms_def P_def)
    done
next
  case (4 b' b)
  then show ?case
    apply(induction rule: lextends_diff.induct)
         apply(auto simp: params_subterms_def P_def)
    done
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (2 s t1 branch)
    then have "Single t1 \<in> subterms_branch branch"
      by (auto intro: subterms_branch_subterms_literalI)
    with 2 have "t1 \<in> subterms_fm (last branch)"
      by (metis subterms_fm_intros(7) no_new_subtermsE(5))
    then have "\<forall>c \<in> params' branch. Var c \<noteq> t1"
      unfolding params'_def params_def
      by (simp, meson mem_pset_fm_if_mem_subterm_fm pset_term.set_intros(1))
    moreover
    from \<open>t1 \<in> subterms_fm (last branch)\<close> have "\<forall>c \<in> params' branch. Var c \<noteq> s"
      unfolding params'_def using "2.hyps" sorry
    ultimately show ?case
      using 2 by (auto simp: P_def params_subterms_def)
  qed (auto simp: params_subterms_def P_def)
next
  case (6 b' b)
  then have "no_new_subterms b'" "b' \<noteq> []"
    using lextends_no_new_subterms[OF lextends.intros(6)] lextends_eq.simps by blast+
  note subterms_branch_eq_if_no_new_subterms[OF this]
  with 6 show ?case
  proof(induction rule: lextends_eq.induct)
    case eq_left: (1 t1 t2 branch l)
    then have t1_in_subterms_branch:
      "t1 \<in> subterms_branch (Atom (subst_tlvl_literal t1 t2 l) # branch)"
      by (auto simp: subterms_branch_simps intro: subterms_branch_subterms_literalI)
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_left have "(True, Var c \<approx>\<^sub>s x) = subst_tlvl_literal t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_left consider
          (refl) "l = (True, t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (True, Var c \<approx>\<^sub>s t1)" "t2 = x"
        | (t1_right) "l = (True, t1 \<approx>\<^sub>s x)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl_literal.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_left P_def t1_in_subterms_branch by (auto simp: params_subterms_def)
    next
      case (2 c x)
      with eq_left have "(True, x \<approx>\<^sub>s Var c) = subst_tlvl_literal t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_left consider
          (refl) "l = (True, t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (True, t1 \<approx>\<^sub>s Var c)" "t2 = x"
        | (t1_right) "l = (True, x \<approx>\<^sub>s t1)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl_literal.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_left P_def params_subterms_def t1_in_subterms_branch
        by (auto simp: params_subterms_def)
    qed
  next
    case eq_right: (2 t1 t2 branch l)
    then have t2_in_subterms_branch:
      "t2 \<in> subterms_branch (Atom (subst_tlvl_literal t2 t1 l) # branch)"
      by (auto simp: subterms_branch_simps intro: subterms_branch_subterms_literalI)
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_right have "(True, Var c \<approx>\<^sub>s x) = subst_tlvl_literal t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_right consider
          (refl) "l = (True, t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (True, Var c \<approx>\<^sub>s t2)" "t1 = x"
        | (t1_right) "l = (True, t2 \<approx>\<^sub>s x)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl_literal.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_right P_def params_subterms_def t2_in_subterms_branch
        by (auto simp: params_subterms_def)
    next
      case (2 c x)
      with eq_right have "(True, x \<approx>\<^sub>s Var c) = subst_tlvl_literal t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_right consider
          (refl) "l = (True, t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (True, t2 \<approx>\<^sub>s Var c)" "t1 = x"
        | (t1_right) "l = (True, x \<approx>\<^sub>s t2)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl_literal.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_right P_def params_subterms_def t2_in_subterms_branch
        by (auto simp: params_subterms_def)
    qed
  next
    case (3 s t branch s')
    then show ?case
      using P_def by (auto simp: params_subterms_def)
  qed
qed

lemma lemma_2_extends:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b)"
  assumes "extends bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "\<forall>t \<in> subterms_branch b. t \<in> params_subterms b"
  assumes "\<forall>\<phi>\<in>set b. \<forall>a. \<phi> \<noteq> Atom a \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b. P b c t"
  shows "\<forall>c \<in> params' b'. \<forall>t \<in> params_subterms b'. P b' c t"
  using assms(2-) extends_last_eq[OF assms(2-4)]
proof(induction rule: extends.induct)
  case (1 p q branch)
  then have "params (p # branch) = params branch" "params (Neg p # branch) = params branch"
    unfolding params_def
    by (auto simp: vars_branch_simps vars_branch_vars_fmI vars_fm_simps)
  with 1 show ?case sorry
next
  case (2 p q branch)
  then show ?case sorry
next
  case (3 s t1 t2 branch)
  then show ?case sorry
next
  case (4 s t1 branch t2)
  then show ?case sorry
next
  case (5 s t1 branch t2)
  then show ?case sorry
next
  case (6 t1 t2 branch x)
  then show ?case sorry
qed


end