theory Set_Proc                
  imports Main Logic ZFC_in_HOL.ZFC_in_HOL Graph_Theory.Graph_Theory
begin

abbreviation "vset \<equiv> ZFC_in_HOL.set"

hide_const (open) ZFC_in_HOL.set

datatype 'a pset_term = 
  Empty (\<open>\<emptyset>\<close>)| Var 'a |
  Union "'a pset_term" "'a pset_term" (infixr \<open>\<squnion>\<^sub>s\<close> 50) |
  Inter "'a pset_term" "'a pset_term" (infixr \<open>\<sqinter>\<^sub>s\<close> 60) |
  Diff "'a pset_term" "'a pset_term"  (infixl \<open>-\<^sub>s\<close> 70) |
  Single "'a pset_term"

datatype 'a pset_atom =
  Elem "'a pset_term" "'a pset_term" (infix \<open>\<in>\<^sub>s\<close> 45) | 
  Equal "'a pset_term" "'a pset_term" (infix \<open>\<approx>\<^sub>s\<close> 45) |
  Subset "'a pset_term" "'a pset_term" (infix \<open>\<sqsubseteq>\<^sub>s\<close> 45)

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
| "I\<^sub>s\<^sub>a v (t1 \<sqsubseteq>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<le> I\<^sub>s\<^sub>t v t2"

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
next
  case (2 t)
  then show ?case
    apply(auto)
     apply (metis (no_types, lifting) emptyE image_iff mem_Collect_eq)+
    done
next
  case (3 x)
  then show ?case by simp
qed

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
        have "small (realization ` ancestors1 G t)" for t
          using small_ancestors1 by simp
        with 0 less.prems assms(2) show ?thesis
          apply(cases t2 rule: height_cases')
            apply(auto)
           apply (metis Int_iff P_T_partition_verts(1) empty_iff)
          by (metis (no_types, lifting) Collect_empty_eq elts_of_set empty_is_image height.simps(1,2)
              less.prems(3) realization.simps(2))
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

end














type_synonym 'a branch = "'a pset_fm list"

definition vars :: "'a branch \<Rightarrow> 'a set" where
  "vars b \<equiv> \<Union>((\<lambda>(b, a). set_pset_atom a) ` \<Union>(atoms ` set b))"

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_literal list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((True, s' \<sqsubseteq>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_literal list \<Rightarrow> bool" where
  "member_cycle ((True, s \<sqsubseteq>\<^sub>s t) # cs) = member_seq s ((True, s \<sqsubseteq>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

abbreviation "AT a \<equiv> Atom (True, a)"
abbreviation "AF a \<equiv> Atom (False, a)"

inductive closeable :: "'a branch \<Rightarrow> bool" where
  Or: "\<lbrakk> Or \<phi>\<^sub>1 \<phi>\<^sub>2 \<in> set branch; closeable (\<phi>\<^sub>1 # branch); closeable (\<phi>\<^sub>2 # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| And: "\<lbrakk> And \<phi>\<^sub>1 \<phi>\<^sub>2 \<in> set branch; closeable (\<phi>\<^sub>1 # \<phi>\<^sub>2 # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"

| Close: "\<lbrakk> \<phi> \<in> set branch; Neg \<phi> \<in> set branch \<rbrakk> \<Longrightarrow> closeable branch"
| CloseElemEmpty: "AT (t \<sqsubseteq>\<^sub>s \<emptyset>) \<in> set branch \<Longrightarrow> closeable branch"
| CloseNegEqual: "AF (t \<approx>\<^sub>s t) \<in> set branch \<Longrightarrow> closeable branch"
| CloseMemberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set branch) \<rbrakk> \<Longrightarrow> closeable branch"

| "\<lbrakk> AT (s \<sqsubseteq>\<^sub>s t) \<in> set branch; closeable (AT (s \<approx>\<^sub>s s \<sqinter>\<^sub>s t) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (s \<sqsubseteq>\<^sub>s t) \<in> set branch; closeable (AF (s \<approx>\<^sub>s s \<sqinter>\<^sub>s t) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch; closeable (AT (s \<in>\<^sub>s t1) # AT (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch; closeable (AT (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; closeable (AF (s \<in>\<^sub>s t1) # AF (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (s \<in>\<^sub>s Set t0 ts) \<in> set branch; closeable (map (\<lambda>t. AF (s \<approx>\<^sub>s t)) (t0 # ts) @ branch) \<rbrakk>
    \<Longrightarrow> closeable branch"

| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch;
     closeable (AT (s \<in>\<^sub>s t1) # branch); closeable (AT (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch;
     closeable (AF (s \<in>\<^sub>s t1) # branch); closeable (AF (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch;
     closeable (AF (s \<in>\<^sub>s t1) # branch); closeable (AT (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AT (s \<in>\<^sub>s Set t0 ts) \<in> set branch;
     \<forall>l \<in> (\<lambda>t. AT (s \<approx>\<^sub>s t)) ` set (t0 # ts). closeable (l # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"

| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t1) \<in> set branch; closeable (AT (s \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t2) \<in> set branch; closeable (AT (s \<in>\<^sub>s t1) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set branch; c \<notin> vars branch;
     closeable (AT (Var c \<in>\<^sub>s t1) # AF (Var c \<in>\<^sub>s t2) # branch);
     closeable (AF (Var c \<in>\<^sub>s t1) # AT (Var c \<in>\<^sub>s t2) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"
| "\<lbrakk> s \<in> tlvl_terms branch; t \<in> tlvl_terms branch;
     closeable (AT (s \<in>\<^sub>s t) # branch); closeable (AF (s \<in>\<^sub>s t) # branch) \<rbrakk>
    \<Longrightarrow> closeable branch"




end