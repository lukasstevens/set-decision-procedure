theory Set_Proc                
  imports Main Logic ZFC_in_HOL.ZFC_in_HOL Graph_Theory.Graph_Theory
    "HOL-Library.Sublist"
begin

abbreviation "vset \<equiv> ZFC_in_HOL.set"

hide_const (open) ZFC_in_HOL.set

datatype 'a pset_term = 
  Empty (\<open>\<emptyset>\<close>)| is_Var: Var 'a |
  Union "'a pset_term" "'a pset_term" (infixr \<open>\<squnion>\<^sub>s\<close> 60) |
  Inter "'a pset_term" "'a pset_term" (infixr \<open>\<sqinter>\<^sub>s\<close> 70) |
  Diff "'a pset_term" "'a pset_term"  (infixl \<open>-\<^sub>s\<close> 80) |
  Single "'a pset_term"

datatype 'a pset_atom =
  Elem "'a pset_term" "'a pset_term" (infix \<open>\<in>\<^sub>s\<close> 55) | 
  Equal "'a pset_term" "'a pset_term" (infix \<open>\<approx>\<^sub>s\<close> 55)

definition "vdiff s1 s2 \<equiv> vset (elts s1 - elts s2)"

lemma small_Diff[intro]: "small s \<Longrightarrow> small (s - t)" 
  by (meson Diff_subset smaller_than_small)

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

type_synonym 'a pset_fm = "'a pset_atom fm"

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

lemma
  shows finite_P: "finite P"
    and finite_T: "finite T"
    and finite_P_un_T: "finite (P \<union> T)"
  using finite_verts P_T_partition_verts by auto
 
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

lemma small_realization_ancestors1[simp, intro!]: "small (realization ` ancestors1 G t)"
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
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realization y"
  assumes "s \<in> P \<union> T" "t \<in> P \<union> T"
  assumes "realization s \<in> elts (realization t)"
  obtains s' where "s' \<rightarrow>\<^bsub>G\<^esub> t" "realization s = realization s'"
  using assms(2-)
proof(induction t rule: realization.induct)
  case (1 x)
  with assms(1) show ?case 
    by (metis all_not_in_conv elts_of_set insert_iff mem_not_sym realization.simps(1))
qed auto

lemma lemma1_2':
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realization y"
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
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realization y"
  assumes "t1 \<in> P \<union> T" "t2 \<in> P \<union> T" "realization t1 = realization t2"
  shows "height t1 = height t2"
  using assms lemma1_2' le_antisym unfolding inj_on_def by metis

lemma lemma1_3:
  assumes "inj_on I P"
  assumes "\<forall>x \<in> P. \<forall>y \<in> P \<union> T. x \<noteq> y \<longrightarrow> I x \<noteq> realization y"
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

lemma card_realization_T_less_card_verts:
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

lemma card_realization_P:
  "p \<in> P \<Longrightarrow> card (elts (realization p)) = 1"
  by simp

lemma card_elts_realization_T:
  assumes "t \<in> T" "x \<in> elts (realization t)"
  shows "card (elts x) < card (P \<union> T)"
proof -
  obtain s where s: "x = realization s" "s \<in> ancestors1 G t"
    using assms by force
  then have "s \<in> P \<union> T"
    using P_T_partition_verts(2) adj_in_verts(1) by blast
  with s have "{s, t} \<subseteq> P \<union> T" "s \<noteq> t"
    using assms(1) adj_not_same s(2) by blast+
  with finite_P_un_T have "card (P \<union> T) \<ge> 2"
    by (metis card_2_iff card_mono)
  with \<open>s \<in> P \<union> T\<close> s show ?thesis
    using card_realization_T_less_card_verts
    by auto
qed

end

lemma Ex_set_family:
  assumes "finite P"
  shows "\<exists>I. inj_on I P \<and> (\<forall>p. card (elts (I p)) \<ge> n)"
proof -
  from \<open>finite P\<close> obtain ip where ip: "bij_betw ip P {..<card P}"
    using to_nat_on_finite by blast
  let ?I = "ord_of_nat o ((+) n) o ip"
  from ip have "inj_on ?I P"
    by (auto simp: inj_on_def bij_betw_def)
  moreover have "card (elts (?I p)) \<ge> n" for p
    by auto
  ultimately show ?thesis
    by auto
qed
    

type_synonym 'a branch = "'a pset_fm list"

definition vars_fm :: "'a pset_fm \<Rightarrow> 'a set" where
  "vars_fm \<phi> \<equiv> \<Union>(set_pset_atom ` atoms \<phi>)"

lemma vars_fm_simps[simp]:
  "vars_fm (Atom a) = set_pset_atom a"
  "vars_fm (And p q) = vars_fm p \<union> vars_fm q"
  "vars_fm (Or p q) = vars_fm p \<union> vars_fm q"
  "vars_fm (Neg p) = vars_fm p"
  unfolding vars_fm_def
     apply(auto)
  done

lemma vars_fmI:
  "x \<in> vars_fm p \<Longrightarrow> x \<in> vars_fm (And p q)"
  "x \<in> vars_fm q \<Longrightarrow> x \<in> vars_fm (And p q)"
  "x \<in> vars_fm p \<Longrightarrow> x \<in> vars_fm (Or p q)"
  "x \<in> vars_fm q \<Longrightarrow> x \<in> vars_fm (Or p q)"
  "x \<in> vars_fm p \<Longrightarrow> x \<in> vars_fm (Neg p)"
  by auto

definition vars_branch :: "'a branch \<Rightarrow> 'a set" where
  "vars_branch b \<equiv> \<Union>(vars_fm ` set b)"

lemma vars_branch_simps:
  "vars_branch [] = {}"
  "vars_branch (x # xs) = vars_fm x \<union> vars_branch xs"
  unfolding vars_branch_def by auto

lemma vars_branch_append:
  "vars_branch (b1 @ b2) = vars_branch b1 \<union> vars_branch b2"
  unfolding vars_branch_def by simp

lemma vars_fm_vars_branchI:
  "\<phi> \<in> set b \<Longrightarrow> x \<in> vars_fm \<phi> \<Longrightarrow> x \<in> vars_branch b"
  unfolding vars_branch_def by blast

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_atom list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((s' \<in>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_atom list \<Rightarrow> bool" where
  "member_cycle ((s \<in>\<^sub>s t) # cs) = member_seq s ((s \<in>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

abbreviation "AT a \<equiv> Atom a"
abbreviation "AF a \<equiv> Neg (Atom a)"

fun subfms where
  "subfms (Atom a) = {Atom a}"
| "subfms (And p q) = {And p q} \<union> subfms p \<union> subfms q"
| "subfms (Or p q) = {Or p q} \<union> subfms p \<union> subfms q"
| "subfms (Neg q) = {Neg q} \<union> subfms q"

definition "subfms_branch b \<equiv> \<Union>(subfms ` set b)"

lemma subfms_branch_simps:
  "subfms_branch [] = {}"
  "subfms_branch (x # xs) = subfms x \<union> subfms_branch xs"
  unfolding subfms_branch_def by auto

fun subterms where
  "subterms \<emptyset> = {\<emptyset>}"
| "subterms (Var i) = {Var i}"
| "subterms (t1 \<squnion>\<^sub>s t2) = {t1 \<squnion>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 \<sqinter>\<^sub>s t2) = {t1 \<sqinter>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 -\<^sub>s t2) = {t1 -\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (Single t) = {Single t} \<union> subterms t"

fun subterms_atom where
  "subterms_atom (t1 \<in>\<^sub>s t2) = subterms t1 \<union> subterms t2"
| "subterms_atom (t1 \<approx>\<^sub>s t2) = subterms t1 \<union> subterms t2"

definition "subterms_fm \<phi> \<equiv> \<Union>(subterms_atom ` atoms \<phi>)"

lemma subterms_fm_simps[simp]:
  "subterms_fm (Atom a) = subterms_atom a"
  "subterms_fm (And p q) = subterms_fm p \<union> subterms_fm q"
  "subterms_fm (Or p q) = subterms_fm p \<union> subterms_fm q"
  "subterms_fm (Neg p) = subterms_fm p"
  unfolding subterms_fm_def by auto

definition "subterms_branch b \<equiv> \<Union>(subterms_fm ` set b)"

lemma subterms_branch_simps:
  "subterms_branch [] = {}"
  "subterms_branch (x # xs) = subterms_fm x \<union> subterms_branch xs"
  unfolding subterms_branch_def by auto

lemma subterms_refl[simp]:
  "t \<in> subterms t"
  by (induction t) auto

lemma subterms_subterms_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms v \<Longrightarrow> s \<in> subterms v"
  apply(induction v)
       apply(auto)
  done

lemma subterms_subterms_atom_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_atom v \<Longrightarrow> s \<in> subterms_atom v"
  apply(cases v rule: subterms_atom.cases)
  using subterms_subterms_trans by auto

lemma subterms_subterms_fm_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_fm \<phi> \<Longrightarrow> s \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
     apply(auto simp: subterms_subterms_atom_trans)
  done

lemma subterms_fmD:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t1 \<in> subterms_fm \<phi>"
  "t1 -\<^sub>s t2 \<in> subterms_fm \<phi> \<Longrightarrow> t2 \<in> subterms_fm \<phi>"
  "Single t \<in> subterms_fm \<phi> \<Longrightarrow> t \<in> subterms_fm \<phi>"
  by (metis UnCI subterms.simps subterms_refl subterms_subterms_fm_trans)+

lemma subterms_branchD:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t1 \<in> subterms_branch b"
  "t1 -\<^sub>s t2 \<in> subterms_branch b \<Longrightarrow> t2 \<in> subterms_branch b"
  "Single t \<in> subterms_branch b \<Longrightarrow> t \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_fmD by fast+

lemma subfms_refl[simp]: "p \<in> subfms p"
  by (cases p) auto

lemma subfmsI:
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (And p q)"
  "a \<in> subfms q \<Longrightarrow> a \<in> subfms (And p q)"
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (Or p q)"
  "a \<in> subfms q \<Longrightarrow> a \<in> subfms (Or p q)"
  "a \<in> subfms p \<Longrightarrow> a \<in> subfms (Neg p)"
  by auto

lemma subfms_trans: "q \<in> subfms p \<Longrightarrow> p \<in> subfms r \<Longrightarrow> q \<in> subfms r"
  by (induction r) auto

lemma subfmsD:
  "And p q \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  "And p q \<in> subfms \<phi> \<Longrightarrow> q \<in> subfms \<phi>"
  "Or p q \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  "Or p q \<in> subfms \<phi> \<Longrightarrow> q \<in> subfms \<phi>"
  "Neg p \<in> subfms \<phi> \<Longrightarrow> p \<in> subfms \<phi>"
  using subfmsI subfms_refl subfms_trans by metis+

abbreviation "pset_atoms_branch b \<equiv> \<Union>(atoms ` set b)"

fun tlvl_terms_atom where
  "tlvl_terms_atom (t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms_atom (t1 \<approx>\<^sub>s t2) = {t1, t2}"

fun subst_tlvl where
  "subst_tlvl t1 t2 (s1 \<in>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<in>\<^sub>s (if s2 = t1 then t2 else s2)"
| "subst_tlvl t1 t2 (s1 \<approx>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<approx>\<^sub>s (if s2 = t1 then t2 else s2)"

inductive lextends_fm :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "And p q \<in> set branch \<Longrightarrow> lextends_fm [p, q] branch"
| "Neg (Or p q) \<in> set branch \<Longrightarrow> lextends_fm [Neg p, Neg q] branch"
| "\<lbrakk> Or p q \<in> set branch; Neg p \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm [q] branch"
| "\<lbrakk> Or p q \<in> set branch; Neg q \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm [p] branch"
| "\<lbrakk> Neg (And p q) \<in> set branch; p \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm [Neg q] branch"
| "\<lbrakk> Neg (And p q) \<in> set branch; q \<in> set branch \<rbrakk> \<Longrightarrow> lextends_fm [Neg p] branch"
| "Neg (Neg p) \<in> set branch \<Longrightarrow> lextends_fm [p] branch"

inductive lextends_un :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_un [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_un [AT (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_un [AT (s \<in>\<^sub>s t1)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_un [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch"

inductive lextends_int :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_int [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t2) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_int [AF (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_int [AF (s \<in>\<^sub>s t1)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; AT (s \<in>\<^sub>s t2) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_int [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch"

inductive lextends_diff :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> lextends_diff [AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch; AT (s \<in>\<^sub>s t1) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_diff [AT (s \<in>\<^sub>s t2)] branch"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_diff [AF (s \<in>\<^sub>s t1)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; AF (s \<in>\<^sub>s t2) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<rbrakk>
    \<Longrightarrow> lextends_diff [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch"

inductive lextends_single :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "Single t1 \<in> subterms_fm (last branch) \<Longrightarrow> lextends_single [AT (t1 \<in>\<^sub>s Single t1)] branch"
| "AT (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> lextends_single [AT (s \<approx>\<^sub>s t1)] branch"
| "AF (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> lextends_single [AF (s \<approx>\<^sub>s t1)] branch"

inductive lextends_eq :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AT l \<in> set branch; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> lextends_eq [AT (subst_tlvl t1 t2 l)] branch"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AF l \<in> set branch; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> lextends_eq [AF (subst_tlvl t1 t2 l)] branch"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AT l \<in> set branch; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> lextends_eq [AT (subst_tlvl t2 t1 l)] branch"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set branch; AF l \<in> set branch; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> lextends_eq [AF (subst_tlvl t2 t1 l)] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t) \<in> set branch; AF (s' \<in>\<^sub>s t) \<in> set branch \<rbrakk>
    \<Longrightarrow> lextends_eq [AF (s \<approx>\<^sub>s s')] branch"

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
    (\<And>p q branch. And p q \<in> set branch \<Longrightarrow> P [p, q] branch) \<Longrightarrow>
    (\<And>p q branch. Neg (Or p q) \<in> set branch \<Longrightarrow> P [Neg p, Neg q] branch) \<Longrightarrow>
    (\<And>p q branch. Or p q \<in> set branch \<Longrightarrow> Neg p \<in> set branch \<Longrightarrow> P [q] branch) \<Longrightarrow>
    (\<And>p q branch. Or p q \<in> set branch \<Longrightarrow> Neg q \<in> set branch \<Longrightarrow> P [p] branch) \<Longrightarrow>
    (\<And>p q branch. Neg (And p q) \<in> set branch \<Longrightarrow> p \<in> set branch \<Longrightarrow> P [Neg q] branch) \<Longrightarrow>
    (\<And>p q branch. Neg (And p q) \<in> set branch \<Longrightarrow> q \<in> set branch \<Longrightarrow> P [Neg p] branch) \<Longrightarrow>
    (\<And>p q branch. Neg (Neg p) \<in> set branch \<Longrightarrow> P [p] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AT (s \<in>\<^sub>s t1)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P [AF (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AT (s \<in>\<^sub>s t1),  AF (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AF (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t2 branch t1. AT (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>s t1 t2 branch. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] branch) \<Longrightarrow>
    (\<And>s t1 branch t2. AT (s \<in>\<^sub>s t1) \<in> set branch \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set branch \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last branch) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] branch) \<Longrightarrow>
    (\<And>t1 branch. Single t1 \<in> subterms_fm (last branch) \<Longrightarrow> P [AT (t1 \<in>\<^sub>s Single t1)] branch) \<Longrightarrow>
    (\<And>s t1 branch. AT (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> P [AT (s \<approx>\<^sub>s t1)] branch) \<Longrightarrow>
    (\<And>s t1 branch. AF (s \<in>\<^sub>s Single t1) \<in> set branch \<Longrightarrow> P [AF (s \<approx>\<^sub>s t1)] branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT l \<in> set branch \<Longrightarrow> t1 \<in> tlvl_terms_atom l \<Longrightarrow> P [AT (subst_tlvl t1 t2 l)] branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF l \<in> set branch \<Longrightarrow> t1 \<in> tlvl_terms_atom l \<Longrightarrow> P [AF (subst_tlvl t1 t2 l)] branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> AT l \<in> set branch \<Longrightarrow> t2 \<in> tlvl_terms_atom l \<Longrightarrow> P [AT (subst_tlvl t2 t1 l)] branch) \<Longrightarrow>
    (\<And>t1 t2 branch l. AT (t1 \<approx>\<^sub>s t2) \<in> set branch \<Longrightarrow> AF l \<in> set branch \<Longrightarrow> t2 \<in> tlvl_terms_atom l \<Longrightarrow> P [AF (subst_tlvl t2 t1 l)] branch) \<Longrightarrow>  
    (\<And>s t branch s'. AT (s \<in>\<^sub>s t) \<in> set branch \<Longrightarrow> AF (s' \<in>\<^sub>s t) \<in> set branch \<Longrightarrow> P [AF (s \<approx>\<^sub>s s')] branch) \<Longrightarrow> P b' b"
  using assms
  apply(induction rule: lextends.induct)
  subgoal apply(induction rule: lextends_fm.induct) by metis+
  subgoal apply(induction rule: lextends_un.induct) by metis+
  subgoal apply(induction rule: lextends_int.induct) by metis+
  subgoal apply(induction rule: lextends_diff.induct) by metis+
  subgoal apply(induction rule: lextends_single.induct) by metis+
  subgoal apply(induction rule: lextends_eq.induct) by metis+
  done


lemma subterms_subterms_branch_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_branch b \<Longrightarrow> s \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_subterms_fm_trans by blast

lemma tlvl_terms_atom_subs_subterms_atom:
  "tlvl_terms_atom a \<subseteq> subterms_atom a"
  apply(cases a rule: tlvl_terms_atom.cases)  by auto

lemma subterms_atom_subst_tlvl_subs:
  "subterms_atom (subst_tlvl t1 t2 a) \<subseteq> subterms t2 \<union> subterms_atom a"
  apply(cases "(t1, t2, a)" rule: subst_tlvl.cases)
    apply(auto)
  done

lemma subterms_branchI_if_AT_mem:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms_branch b" "t \<in> subterms_branch b"
  using assms unfolding subterms_branch_def by force+

lemma subterms_branchI_if_AF_mem:
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms_branch b" "t \<in> subterms_branch b"
  using assms unfolding subterms_branch_def by force+

lemma subterms_branchI_if_AT_eq:
  assumes "AT (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms_branch b" "t \<in> subterms_branch b"
  using assms unfolding subterms_branch_def by force+

lemma subterms_branchI_if_AF_eq:
  assumes "AF (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> subterms_branch b" "t \<in> subterms_branch b"
  using assms unfolding subterms_branch_def by force+


definition "lin_sat branch \<equiv> (\<forall>branch'. lextends branch' branch \<longrightarrow> set branch' \<subseteq> set branch)"

lemma lin_satD:
  assumes "lin_sat b"
  assumes "lextends b' b"
  assumes "x \<in> set b'"
  shows "x \<in> set b"
  using assms unfolding lin_sat_def by auto

inductive bclosed :: "'a branch \<Rightarrow> bool" where
  contr: "\<lbrakk> \<phi> \<in> set branch; Neg \<phi> \<in> set branch \<rbrakk> \<Longrightarrow> bclosed branch"
| elemEmpty: "AT (t \<in>\<^sub>s \<emptyset>) \<in> set branch \<Longrightarrow> bclosed branch"
| neqSelf: "AF (t \<approx>\<^sub>s t) \<in> set branch \<Longrightarrow> bclosed branch"
| memberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set branch) \<rbrakk> \<Longrightarrow> bclosed branch"

lemma bclosed_mono: "bclosed b \<Longrightarrow> set b \<subseteq> set b' \<Longrightarrow> bclosed b'"
proof(induction rule: bclosed.induct)
  case (memberCycle cs branch)
  then show ?case
    by (meson Atoms_mono bclosed.memberCycle subset_trans)
qed (auto simp: bclosed.simps)

abbreviation "bopen branch \<equiv> \<not> bclosed branch"

inductive extends_noparam :: "'a branch list \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set branch;
     p \<notin> set branch; Neg p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam [[p], [Neg p]] branch"
| "\<lbrakk> Neg (And p q) \<in> set branch;
     Neg p \<notin> set branch; p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam [[Neg p], [p]] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t1) \<notin> set branch; AF (s \<in>\<^sub>s t1) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam [[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam [[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]] branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam [[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]] branch"

inductive extends_param ::
  "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a \<Rightarrow> 'a branch list \<Rightarrow> 'a branch \<Rightarrow> bool" for t1 t2 x where
  "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set branch; t1 \<in> subterms_fm (last branch); t2 \<in> subterms_fm (last branch);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set branch \<and> AF (x \<in>\<^sub>s t2) \<in> set branch;
     \<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set branch \<and> AF (x \<in>\<^sub>s t1) \<in> set branch;
     x \<notin> vars_branch branch \<rbrakk>
    \<Longrightarrow> extends_param t1 t2 x [[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
                               [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]] branch"

inductive_cases extends_param_cases[consumes 1]: "extends_param t1 t2 x bs b"

lemma extends_paramD:
  assumes "extends_param t1 t2 x bs b"
  shows "bs = [[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
               [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]]"
        "AF (t1 \<approx>\<^sub>s t2) \<in> set b" "t1 \<in> subterms_fm (last b)" "t2 \<in> subterms_fm (last b)"
        "\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b"
        "\<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b"
        "x \<notin> vars_branch b"
  using extends_param.cases[OF assms] by metis+

inductive extends :: "'a branch list \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "extends_noparam bs b \<Longrightarrow> extends bs b"
| "extends_param t1 t2 x bs b \<Longrightarrow> extends bs b"


lemma extends_disjnt:
  assumes "extends bs' b" "b' \<in> set bs'"
  shows "set b \<inter> set b' = {}"
  using assms
proof(induction bs' b rule: extends.induct)
  case (1 bs b)
  then show ?case
    by (induction rule: extends_noparam.induct) (auto intro: list.set_intros(1))
next
  case (2 t1 t2 x bs b)
  then show ?case
  proof(induction rule: extends_param.induct)
    case (1 branch)
    from \<open>x \<notin> vars_branch branch\<close>
    have "AT (Var x \<in>\<^sub>s t1) \<notin> set branch" "AF (Var x \<in>\<^sub>s t1) \<notin> set branch"
      unfolding vars_branch_def by auto
    with 1 show ?case
      by (auto intro: list.set_intros(1) simp: disjnt_iff vars_fm_vars_branchI)
  qed
qed

lemma extends_branch_not_Nil:
  assumes "extends bs' b" "b' \<in> set bs'"
  shows "b' \<noteq> []"
  using assms
proof(induction bs' b rule: extends.induct)
  case (1 bs b)
  then show ?case
    by (induction rule: extends_noparam.induct) auto
next
  case (2 t1 t2 x bs b)
  then show ?case
    by (induction rule: extends_param.induct) auto
qed

lemma extends_not_Nil: "extends bs' b \<Longrightarrow> bs' \<noteq> []"
proof(induction rule: extends.induct)
  case (1 bs b)
  then show ?case by (induction rule: extends_noparam.induct) auto
next
  case (2 t1 t2 x bs b)
  then show ?case by (induction rule: extends_param.induct) auto
qed

lemma extends_strict_mono:
  assumes "extends bs' b" "b' \<in> set bs'"
  shows "set b \<subset> set (b' @ b)"
  using extends_disjnt[OF assms] extends_branch_not_Nil[OF assms]
  by (simp add: less_le) (metis Un_Int_eq(1) set_empty2)

inductive_cases extends_cases[consumes 1, case_names no_param param]: "extends bs b"

inductive extendss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "extendss b b"
| "lextends b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"
| "extends bs b2 \<Longrightarrow> b3 \<in> set bs \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"

lemma extendss_trans: "extendss b3 b2 \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss b3 b1"
  by (induction rule: extendss.induct) (auto simp: extendss.intros)

lemma extendss_suffix:
  "extendss b1 b2 \<Longrightarrow> suffix b2 b1"
  apply(induction rule: extendss.induct)
    apply(auto simp: suffix_appendI)
  done

lemmas extendss_mono = set_mono_suffix[OF extendss_suffix]

lemma extendss_strict_mono_if_neq:
  "extendss b' b \<Longrightarrow> b' \<noteq> b \<Longrightarrow> set b \<subset> set b'"
  apply(induction rule: extendss.induct)
  using extends_strict_mono by blast+

lemma extendss_last_eq[simp]:
  "extendss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  by (metis extendss_suffix last_appendR suffix_def)

inductive closeable :: "'a branch \<Rightarrow> bool" where
  "bclosed b \<Longrightarrow> closeable b"
| "lextends b' b \<Longrightarrow> set b \<subset> set (b' @ b) \<Longrightarrow> closeable (b' @ b) \<Longrightarrow> closeable b"
| "extends bs b \<Longrightarrow> lin_sat b \<Longrightarrow> \<forall>b' \<in> set bs. closeable (b' @ b) \<Longrightarrow> closeable b"

definition "sat branch \<equiv> lin_sat branch \<and> (\<nexists>branches. extends branches branch)"

lemma satD:
  assumes "sat b"
  shows "lin_sat b" "\<nexists>b'. extends b' b"
  using assms unfolding sat_def by auto

definition "wf_branch b \<equiv> (\<exists>\<phi>. extendss b [\<phi>])"
                            
definition "params branch \<equiv> vars_branch branch - vars_fm (last branch)"

definition "params' b \<equiv>
  {c \<in> params b. \<forall>t \<in> subterms_fm (last b).
    AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b}"

lemma params_singleton[simp]: "params [\<phi>] = {}"
  unfolding params_def vars_branch_simps by simp

lemma params'_singleton[simp]: "params' [\<phi>] = {}"
  unfolding params'_def by auto

lemma params_mono: "set b1 \<subseteq> set b2 \<Longrightarrow> last b1 = last b2 \<Longrightarrow> params b1 \<subseteq> params b2"
  unfolding params_def
  by (auto simp: vars_branch_def)

lemma params'D:
  assumes "c \<in> params' b"
  shows "c \<in> params b"
        "t \<in> subterms_fm (last b) \<Longrightarrow> AT (Var c \<approx>\<^sub>s t) \<notin> set b"
        "t \<in> subterms_fm (last b) \<Longrightarrow> AT (t \<approx>\<^sub>s Var c) \<notin> set b"
  using assms unfolding params'_def by auto

lemma params'I:
  assumes "c \<in> params b"
  assumes "\<And>t. t \<in> subterms_fm (last b) \<Longrightarrow> AT (Var c \<approx>\<^sub>s t) \<notin> set b"
  assumes "\<And>t. t \<in> subterms_fm (last b) \<Longrightarrow> AT (t \<approx>\<^sub>s Var c) \<notin> set b"
  shows "c \<in> params' b"
  using assms unfolding params'_def by blast

definition "subterms_branch' branch \<equiv>
  subterms_fm (last branch) \<union> Var ` (params branch - params' branch)"

definition "bgraph branch \<equiv>
  let
    vs = Var ` params' branch \<union> subterms_branch' branch
  in
    \<lparr> verts = vs,
      arcs = {(s, t). AT (s \<in>\<^sub>s t) \<in> set branch},
      tail = fst,
      head = snd \<rparr>"

lemma Un_set_pset_term_subterms_eq_set_pset_term:
  "\<Union>(set_pset_term ` subterms t) = set_pset_term t"
  by (induction t) auto

lemma Un_set_pset_term_subterms_fm_eq_vars_fm:
  "\<Union>(set_pset_term ` subterms_fm \<phi>) = vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom a)
  then show ?case
    by (cases a) (auto simp: Un_set_pset_term_subterms_eq_set_pset_term)
qed (fastforce)+

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

lemma mem_set_pset_term_if_mem_subterms:
  "x \<in> set_pset_term s \<Longrightarrow> s \<in> subterms t \<Longrightarrow> x \<in> set_pset_term t"
  apply(induction t)
       apply(auto intro: pset_term.set_intros)
  done

lemma mem_vars_fm_if_mem_subterm_fm:
  "x \<in> set_pset_term s \<Longrightarrow> s \<in> subterms_fm \<phi> \<Longrightarrow> x \<in> vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom a)
  then show ?case
    by (cases a) (auto simp: mem_set_pset_term_if_mem_subterms)
qed (auto simp: vars_fm_def)


lemma set_pset_term_subs_subterms:
  "v \<in> set_pset_term t \<Longrightarrow> Var v \<in> subterms t"
  apply(induction t)
       apply(auto)
  done

lemma set_pset_atom_subs_subterms_atom:
  "v \<in> set_pset_atom a \<Longrightarrow> Var v \<in> subterms_atom a"
  apply(cases a)
   apply(auto simp: set_pset_term_subs_subterms)
  done

lemma vars_fm_subs_subterms_fm:
  "v \<in> vars_fm \<phi> \<Longrightarrow> Var v \<in> subterms_fm \<phi>"
  apply(induction \<phi>)
     apply(auto simp: set_pset_atom_subs_subterms_atom)
  done

lemma vars_branch_subs_subterms_branch:
  "Var ` vars_branch b \<subseteq> subterms_branch b"
  unfolding vars_branch_def subterms_branch_def
  apply(auto simp: vars_fm_subs_subterms_fm)
  done

lemma subterms_branch_subterms_subterms_atom_trans:
  "Atom a \<in> set b \<Longrightarrow> x \<in> subterms s \<Longrightarrow> s \<in> subterms_atom a \<Longrightarrow> x \<in> subterms_branch b"
  unfolding subterms_branch_def
  by (metis UN_I subterms_fm_simps(1) subterms_subterms_atom_trans)

lemma subterms_branch_subterms_subterms_fm_trans:
  "b \<noteq> [] \<Longrightarrow> x \<in> subterms t \<Longrightarrow> t \<in> subterms_fm (last b) \<Longrightarrow> x \<in> subterms_branch b"
  using subterms_branch_def subterms_subterms_fm_trans by fastforce

lemma lextends_subterms_branch_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms_branch (b' @ b) = subterms_branch b"
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
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_subterms_branch_trans
          dest: subterms_branchD subterms_branchI_if_AT_mem subterms_branchI_if_AF_mem)
    done
next
  case (3 b' b)
  then show ?case
    apply(induction rule: lextends_int.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_subterms_branch_trans
          dest: subterms_branchD subterms_branchI_if_AT_mem subterms_branchI_if_AF_mem)
    done
next
  case (4 b' b)
  then show ?case
    apply(induction rule: lextends_diff.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_subterms_branch_trans
          dest: subterms_branchD subterms_branchI_if_AT_mem subterms_branchI_if_AF_mem)
    done
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (1 t1 branch)
    then show ?case
      using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
      apply(auto simp: subterms_branch_simps
            dest: subterms_fmD intro: subterms_subterms_branch_trans)
      done
  qed (auto simp: subterms_branch_simps subterms_branch_subterms_subterms_atom_trans
       dest: subterms_branchD subterms_branchI_if_AF_mem 
       intro: subterms_subterms_branch_trans)
next
  case (6 b' b)
  then show ?case
  by (induction rule: lextends_eq.induct)
     (auto simp: subterms_branch_def subterms_branch_subterms_subterms_atom_trans
            dest!: subsetD[OF subterms_atom_subst_tlvl_subs])
qed

lemma lextends_vars_branch_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars_branch (b' @ b) = vars_branch b"
  using lextends_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma extends_noparam_subterms_branch_eq:
  "extends_noparam bs b \<Longrightarrow> b' \<in> set bs \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms_branch (b' @ b) = subterms_branch b"
proof(induction rule: extends_noparam.induct)
  case (3 s t1 t2 branch)
  then show ?case
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
next
  case (4 s t1 branch t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "4"(2)]
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
next
  case (5 s t1 branch t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "5"(2)]
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
qed (use subterms_branch_def in \<open>(fastforce simp: subterms_branch_simps)+\<close>)


lemma extends_noparam_vars_branch_eq:
  "extends_noparam bs b \<Longrightarrow> b' \<in> set bs \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars_branch (b' @ b) = vars_branch b"
  using extends_noparam_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma lextends_params_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> params (b' @ b) = params b"
  using lextends_vars_branch_eq unfolding params_def by force

lemma extends_noparam_params_eq:
  assumes "extends_noparam bs b" "b' \<in> set bs" "b \<noteq> []" 
  shows "params (b' @ b) = params b"
  using extends_noparam_vars_branch_eq[OF assms] assms(3)
  unfolding params_def by simp

lemma extends_param_vars_branch_eq:
  assumes "extends_param t1 t2 x bs b" "b' \<in> set bs" "b \<noteq> []"
  shows "vars_branch (b' @ b) = insert x (vars_branch b)"
  using assms extends_paramD[OF assms(1)]
  by (auto simp: mem_vars_fm_if_mem_subterm_fm vars_branch_simps vars_fm_vars_branchI)

lemma extends_param_params_eq:
  assumes "extends_param t1 t2 x bs b" "b' \<in> set bs" "b \<noteq> []"
  shows "params (b' @ b) = insert x (params b)"
  using assms extends_paramD[OF assms(1)]
  unfolding params_def
  by (auto simp: mem_vars_fm_if_mem_subterm_fm vars_branch_simps vars_branch_def)

lemma params_append_mono: "b \<noteq> [] \<Longrightarrow> params b \<subseteq> params (b' @ b)"
  unfolding params_def by (auto simp: vars_branch_def)

lemma lextends_params'_subs:
  assumes "lextends b' b" "b \<noteq> []"
  shows "params' (b' @ b) \<subseteq> params' b"
  using assms lextends_params_eq[OF assms]
  by (induction rule: lextends_induct) (auto simp: params'_def)


lemma subterms_branch'D:
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t1 \<in> subterms_branch' b"
  "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t2 \<in> subterms_branch' b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t1 \<in> subterms_branch' b"
  "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t2 \<in> subterms_branch' b"
  "t1 -\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t1 \<in> subterms_branch' b"
  "t1 -\<^sub>s t2 \<in> subterms_branch' b \<Longrightarrow> t2 \<in> subterms_branch' b"
  "Single t \<in> subterms_branch' b \<Longrightarrow> t \<in> subterms_branch' b"
  unfolding subterms_branch'_def using subterms_fmD by fast+

lemma subterms_branch'_if_subterms_fm_last:
  "t \<in> subterms_fm (last b) \<Longrightarrow> t \<in> subterms_branch' b"
  by (simp add: subterms_branch'_def)

definition "no_new_subterms b \<equiv>
  (\<forall>t \<in> subterms_branch b. t \<notin> Var ` params b \<longrightarrow> t \<in> subterms_fm (last b))"

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
  assumes "(t1 \<in>\<^sub>s t2) \<in> \<Union>(atoms ` set b)"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(t1 \<in>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

lemma eq_in_subterms_branch_if_in_atoms_branch:
  assumes "(t1 \<approx>\<^sub>s t2) \<in> \<Union>(atoms ` set b)"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(t1 \<approx>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

lemma lextends_no_new_subterms:
  assumes "lextends b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms unfolding no_new_subterms_def
  by (simp add: lextends_params_eq lextends_subterms_branch_eq[OF assms(1,2)])

lemma subterms_branch_subterms_atomI:
  assumes "Atom l \<in> set branch" "t \<in> subterms_atom l"
  shows "t \<in> subterms_branch branch"
  using assms unfolding subterms_branch_def  
  apply (cases l rule: subterms_atom.cases)
   apply (metis subterms_branch_def subterms_branch_subterms_subterms_atom_trans subterms_refl)+
  done
  
lemma extends_noparam_no_new_subterms:
  assumes "extends_noparam bs b" "b \<noteq> []" "b' \<in> set bs"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
proof(induction rule: extends_noparam.induct)
  case (1 p q branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_def subterms_fm_def
               intro!: no_new_subterms_casesI)
    apply (meson fm.set_intros)+
    done
next
  case (2 p q branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_def subterms_fm_def
               intro!: no_new_subterms_casesI)
    apply (meson fm.set_intros)+
    done
next
  case (3 s t1 t2 branch)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_atom_trans
               intro!: no_new_subterms_casesI)
    done
next
  case (4 s t1 branch t2)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_atom_trans
               intro!: no_new_subterms_casesI)
    using "4.hyps"(2) subterms_branch_subterms_subterms_fm_trans subterms_fmD(4) apply blast+
    done
next
  case (5 s t1 branch t2)
  then show ?case
    using no_new_subtermsE[OF \<open>no_new_subterms branch\<close>]
    apply(auto simp: subterms_branch_simps subterms_branch_subterms_subterms_atom_trans subterms_fm_def
               intro: subterms_subterms_fm_trans[OF _ subterms_fmD(6)]
               intro!: no_new_subterms_casesI)
    using "5.hyps"(2) subterms_branch_subterms_subterms_fm_trans subterms_fmD(6) apply blast+
    done
qed

lemma extends_param_no_new_subterms:
  assumes "extends_param t1 t2 x bs b" "b \<noteq> []" "b' \<in> set bs"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(induction rule: extends_param.induct)
  apply(auto simp: subterms_branch_simps subterms_subterms_atom_trans subterms_subterms_fm_trans
                   no_new_subtermsE
             intro!: no_new_subterms_casesI)
  done

lemma extends_no_new_subterms:
  assumes "extends bs b" "b \<noteq> []" "b' \<in> set bs"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(cases rule: extends.cases)
  using extends_noparam_no_new_subterms extends_param_no_new_subterms by metis+

lemma extendss_no_new_subterms:
  assumes "extendss b' b" "b \<noteq> []" "no_new_subterms b"
  shows "no_new_subterms b'"
  using assms
  apply(induction b' b rule: extendss.induct)
  using extendss_suffix suffix_bot.extremum_uniqueI
  using lextends_no_new_subterms extends_no_new_subterms
  by blast+

lemmas subterms_branch_subterms_fm_lastI =
  subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]

definition "params_subterms b \<equiv> Var ` params b \<union> subterms_fm (last b)"

lemma subterms_branch_eq_if_no_new_subterms:
  assumes "no_new_subterms b" "b \<noteq> []"
  shows "subterms_branch b = params_subterms b"
  using assms no_new_subtermsE[OF assms(1)]
proof -
  note simps = params_def no_new_subterms_def params_subterms_def
    subterms_branch_simps vars_branch_simps
  with assms show ?thesis
    by (auto simp: simps vars_fm_subs_subterms_fm
                   vars_branch_subs_subterms_branch[unfolded image_subset_iff]
             intro: subterms_branch_subterms_fm_lastI)
qed

lemma params_subterms_last_disjnt: "Var ` params b \<inter> subterms_fm (last b) = {}"
  by (auto simp: params_def intro!: mem_vars_fm_if_mem_subterm_fm)

lemma params'_subterms_branch'_disjnt: "Var ` params' b \<inter> subterms_branch' b = {}"
  unfolding subterms_branch'_def params'_def
  using params_subterms_last_disjnt by fastforce

lemma params_subterms_eq_subterms_branch':
  "params_subterms b = Var ` params' b \<union> subterms_branch' b"
  unfolding params_subterms_def subterms_branch'_def
  by (auto simp: params'D(1))

fun is_literal where
  "is_literal (Atom _) = True"
| "is_literal (Neg (Atom _)) = True"
| "is_literal _ = False"

lemma lextends_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-) lextends_params_eq[OF assms(2,3)]
  by (induction rule: lextends_induct)(auto simp: disjoint_iff P_def)

lemma extends_noparam_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "extends_noparam bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: extends_noparam.induct)
     (auto simp: Int_def P_def params_def vars_fm_vars_branchI vars_fm_simps)

lemma extends_param_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "extends_param t1 t2 x bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: extends_param.induct)
     (auto simp: Int_def P_def params_def vars_fm_vars_branchI vars_fm_simps)

lemma extends_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "extends bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  apply(cases bs b rule: extends_cases)
  using extends_param_no_params_if_not_literal extends_noparam_no_params_if_not_literal
  using P_def by fast+

lemma extendss_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "extendss b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-)
  apply (induction rule: extendss.induct)
  using lextends_no_params_if_not_literal extends_no_params_if_not_literal
     apply (metis P_def extendss_suffix suffix_bot.extremum_uniqueI)+
  done

lemma lextends_fm_params'_eq:
  assumes "lextends_fm b' b" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  shows "params' (b' @ b) = params' b"
  using assms
  apply(induction rule: lextends_fm.induct)
       apply(fastforce simp: params'_def params_def vars_branch_def)+
  done


lemma lextends_un_params'_eq:
  assumes "lextends_un b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b.
    AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "params' (b' @ b) = params' b"
proof -
  note lextends.intros(2)[OF assms(1)]
  note lextends_params_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> params' (b' @ b)" if "x \<in> params' b" for x
    using that
    apply(induction rule: lextends_un.induct)
         apply(auto simp: params_subterms_def params'D intro!: params'I)
    done
  with lextends_params'_subs[OF \<open>lextends b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma lextends_int_params'_eq:
  assumes "lextends_int b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b.
    AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "params' (b' @ b) = params' b"
proof -
  note lextends.intros(3)[OF assms(1)]
  note lextends_params_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> params' (b' @ b)" if "x \<in> params' b" for x
    using that
    apply(induction rule: lextends_int.induct)
         apply(auto simp: params_subterms_def params'D intro!: params'I)
    done
  with lextends_params'_subs[OF \<open>lextends b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma lextends_diff_params'_eq:
  assumes "lextends_diff b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b.
    AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "params' (b' @ b) = params' b"
proof -
  note lextends.intros(4)[OF assms(1)]
  note lextends_params_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> params' (b' @ b)" if "x \<in> params' b" for x
    using that
    apply(induction rule: lextends_diff.induct)
         apply(auto simp: params_subterms_def params'D intro!: params'I)
    done
  with lextends_params'_subs[OF \<open>lextends b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma extends_noparam_params'_eq:
  assumes "extends_noparam bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  shows "params' (b' @ b) = params' b"
  using assms
proof -
  from assms have "x \<in> params' (b' @ b)" if "x \<in> params' b" for x
    using that extends_noparam_params_eq[OF assms(1-3)]
    by (induction rule: extends_noparam.induct)
       (intro params'I; fastforce simp: params'D)+
  moreover from assms have "params' (b' @ b) \<subseteq> params' b"
    unfolding params'_def
    using extends_noparam_params_eq by fastforce
  ultimately show ?thesis by blast
qed

lemma extends_param_params'_eq:
  assumes "extends_param t1 t2 x bs b" "b' \<in> set bs" "b \<noteq> []"
  shows "params' (b' @ b) = insert x (params' b)"
  using assms(2,3) extends_paramD[OF assms(1)]
  unfolding params'_def unfolding extends_param_params_eq[OF assms] 
  by (auto simp: vars_fm_vars_branchI)

lemma lemma_2_lextends:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b)"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b. P b c t"
  shows "\<forall>c \<in> params' (b' @ b). \<forall>t \<in> params_subterms (b' @ b). P (b' @ b) c t"
  using assms(2-6)
  using lextends_params_eq[OF assms(2,3)]
        lextends_params'_subs[OF assms(2,3)]
proof(induction rule: lextends.induct)
  case (1 b' b)

  have *: "P (b' @ b) c t"
    if "\<forall>\<phi> \<in> set b'. vars_fm \<phi> \<inter> params (b' @ b) = {}"
    and "c \<in> params' b" "t \<in> params_subterms (b' @ b)" for c t
  proof -
    from that "1.prems"(5)
    have "\<forall>\<phi> \<in> set b'. \<phi> \<noteq> AT (Var c \<approx>\<^sub>s t) \<and> \<phi> \<noteq> AT (t \<approx>\<^sub>s Var c) \<and> \<phi> \<noteq> AT (t \<in>\<^sub>s Var c)"
      by (auto simp: params'_def disjoint_iff)
    with 1 that show ?thesis
      unfolding P_def params_subterms_def
      by (metis Un_iff last_appendR set_append)
  qed
  moreover
  note params'_eq = lextends_fm_params'_eq[OF "1"(1,2,4)] 
  with "1"(1,4,6) params'_eq have "\<forall>\<phi> \<in> set b'. vars_fm \<phi> \<inter> params (b' @ b) = {}"
    by (induction rule: lextends_fm.induct) (auto simp: disjoint_iff)
  ultimately show ?case
    using 1 by blast
next
  case (2 b' b)
  then show ?case
    using lextends_un_params'_eq[OF "2"(1,2,5)[unfolded P_def]]
    using lextends_no_new_subterms[OF lextends.intros(2), OF "2"(1,2) \<open>no_new_subterms b\<close>]
  proof(induction rule: lextends_un.induct)
    case (4 s t1 t2 branch)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch branch"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms branch\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  next
    case (5 s t1 t2 branch)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch branch"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms branch\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (1 s t1 t2 branch)
    then have "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch branch"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms branch\<close> have "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  next
    case (6 s t1 branch t2)
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 6 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (1 s t1 t2 branch)
    then have "t1 -\<^sub>s t2 \<in> subterms_branch branch"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms branch\<close> have "t1 -\<^sub>s t2 \<in> subterms_fm (last branch)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  next
    case (4 s t1 t2 branch)
    then have "t1 -\<^sub>s t2 \<in> subterms_branch branch"
      unfolding subterms_branch_def
      by (metis subterms_branchI_if_AF_mem(2) subterms_branch_def)
    with \<open>no_new_subterms branch\<close> have "t1 -\<^sub>s t2 \<in> subterms_fm (last branch)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (2 s t1 branch)
    then have "Single t1 \<in> subterms_branch branch"
      by (auto intro: subterms_branch_subterms_atomI)
    with 2 have "t1 \<in> subterms_fm (last branch)"
      by (metis subterms_fmD(7) no_new_subtermsE(5))
    then have "\<forall>c \<in> params' branch. Var c \<noteq> t1"
      unfolding params'_def params_def
      using params_def params_subterms_last_disjnt by fastforce
    with \<open>t1 \<in> subterms_fm (last branch)\<close> show ?case
      using 2
      unfolding P_def
      by (auto simp: params_subterms_last_disjnt[unfolded disjoint_iff] params_subterms_def subsetD
               dest: params'D(2))
  qed (auto simp: params_subterms_def P_def)
next
  case (6 b' b)
  then have "no_new_subterms (b' @ b)" "b' @ b \<noteq> []"
    using lextends_no_new_subterms[OF lextends.intros(6)] by blast+
  note subterms_branch_eq_if_no_new_subterms[OF this]
  with 6 show ?case
  proof(induction rule: lextends_eq.induct)
    case eq_left: (1 t1 t2 branch l)
    then have t1_in_subterms_branch: "t1 \<in> subterms_branch branch"
      by (metis subterms_branchI_if_AT_eq(1))
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_left have "(Var c \<approx>\<^sub>s x) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_left consider
          (refl) "l = (t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (Var c \<approx>\<^sub>s t1)" "t2 = x"
        | (t1_right) "l = (t1 \<approx>\<^sub>s x)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_left P_def t1_in_subterms_branch
        by (auto simp: subterms_branch_eq_if_no_new_subterms)
    next
      case (2 c x)
      with eq_left have "(x \<approx>\<^sub>s Var c) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_left consider
          (refl) "l = (t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (t1 \<approx>\<^sub>s Var c)" "t2 = x"
        | (t1_right) "l = (x \<approx>\<^sub>s t1)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_left P_def t1_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms)
    next
      case (3 c x)
      with eq_left have "(x \<in>\<^sub>s Var c) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 3 eq_left consider
          (refl) "l = (t1 \<in>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (t1 \<in>\<^sub>s Var c)" "t2 = x"
        | (t1_right) "l = (x \<in>\<^sub>s t1)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 3 eq_left P_def t1_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms)
    qed
  next
    case eq_left: (2 t1 t2 branch l)
    then have t1_in_subterms_branch: "t1 \<in> subterms_branch branch"
      by (metis subterms_branchI_if_AT_eq(1))
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_left have "(Var c \<approx>\<^sub>s x) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_left consider
          (refl) "l = (t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (Var c \<approx>\<^sub>s t1)" "t2 = x"
        | (t1_right) "l = (t1 \<approx>\<^sub>s x)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_left P_def t1_in_subterms_branch
        by (auto simp: subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    next
      case (2 c x)
      with eq_left have "(x \<approx>\<^sub>s Var c) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_left consider
          (refl) "l = (t1 \<approx>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (t1 \<approx>\<^sub>s Var c)" "t2 = x"
        | (t1_right) "l = (x \<approx>\<^sub>s t1)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_left P_def t1_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    next
      case (3 c x)
      with eq_left have "(x \<in>\<^sub>s Var c) = subst_tlvl t1 t2 l"
        using P_def by (auto simp: params_subterms_def)
      with 3 eq_left consider
          (refl) "l = (t1 \<in>\<^sub>s t1)" "t2 = Var c" "x = Var c"
        | (t1_left) "l = (t1 \<in>\<^sub>s Var c)" "t2 = x"
        | (t1_right) "l = (x \<in>\<^sub>s t1)" "t2 = Var c"
        apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 3 eq_left P_def t1_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    qed
  next
    case eq_right: (3 t1 t2 branch l)
    then have t2_in_subterms_branch: "t2 \<in> subterms_branch branch"
      by (metis subterms_branchI_if_AT_eq(2))
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_right have "(Var c \<approx>\<^sub>s x) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_right consider
          (refl) "l = (t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (Var c \<approx>\<^sub>s t2)" "t1 = x"
        | (t1_right) "l = (t2 \<approx>\<^sub>s x)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_right P_def t2_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms)
    next
      case (2 c x)
      with eq_right have "(x \<approx>\<^sub>s Var c) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_right consider
          (refl) "l = (t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (t2 \<approx>\<^sub>s Var c)" "t1 = x"
        | (t1_right) "l = (x \<approx>\<^sub>s t2)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_right P_def t2_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms)
    next
      case (3 c x)
      with eq_right have "(x \<in>\<^sub>s Var c) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 3 eq_right consider
          (refl) "l = (t2 \<in>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (t2 \<in>\<^sub>s Var c)" "t1 = x"
        | (t1_right) "l = (x \<in>\<^sub>s t2)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 3 eq_right P_def t2_in_subterms_branch
        by (simp_all add: in_mono subterms_branch_eq_if_no_new_subterms)
    qed
  next
    case eq_right: (4 t1 t2 branch l)
    then have t2_in_subterms_branch: "t2 \<in> subterms_branch branch"
      by (metis subterms_branchI_if_AT_eq(2))
    show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with eq_right have "(Var c \<approx>\<^sub>s x) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 1 eq_right consider
          (refl) "l = (t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (Var c \<approx>\<^sub>s t2)" "t1 = x"
        | (t1_right) "l = (t2 \<approx>\<^sub>s x)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 1 eq_right P_def t2_in_subterms_branch
        by (simp_all add: subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    next
      case (2 c x)
      with eq_right have "(x \<approx>\<^sub>s Var c) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 2 eq_right consider
          (refl) "l = (t2 \<approx>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (t2 \<approx>\<^sub>s Var c)" "t1 = x"
        | (t1_right) "l = (x \<approx>\<^sub>s t2)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 2 eq_right P_def t2_in_subterms_branch
        by (simp_all add: subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    next
      case (3 c x)
      with eq_right have "(x \<in>\<^sub>s Var c) = subst_tlvl t2 t1 l"
        using P_def by (auto simp: params_subterms_def)
      with 3 eq_right consider
          (refl) "l = (t2 \<in>\<^sub>s t2)" "t1 = Var c" "x = Var c"
        | (t1_left) "l = (t2 \<in>\<^sub>s Var c)" "t1 = x"
        | (t1_right) "l = (x \<in>\<^sub>s t2)" "t1 = Var c"
        apply(cases "(t2, t1, l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        using 3 eq_right P_def t2_in_subterms_branch
        by (simp_all add: subterms_branch_eq_if_no_new_subterms params_subterms_def subsetD)
    qed
  next
    case (5 s t branch s')
    then show ?case
      using P_def by (auto simp: params_subterms_def)
  qed
qed

lemma lemma_2_extends:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b
                      \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b)"
  assumes "extends bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b. P b c t"
  shows "\<forall>c \<in> params' (b' @ b). \<forall>t \<in> params_subterms (b' @ b). P (b' @ b) c t"
  using assms(2-) extends_no_new_subterms[OF assms(2,4,3,5)]
proof(induction rule: extends.induct)
  case (1 bs b)
  then show ?case
    using extends_noparam_params_eq[OF "1"(1-3)] extends_noparam_params'_eq[OF "1"(1-3,5)]
  proof(induction rule: extends_noparam.induct)
    case (1 p q branch)
    then show ?case
      unfolding P_def params_subterms_def
      by (fastforce dest: params'D)
  next
    case (2 p q branch)
    then show ?case
      unfolding P_def params_subterms_def
      by (fastforce dest: params'D)
  next
    case (3 s t1 t2 branch)
    then have "t1 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 3 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)

  next
    case (4 s t1 branch t2)
    then have "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)
  next
    case (5 s t1 branch t2)
    then have "t2 \<notin> Var ` params branch"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)
  qed
next
  case (2 t1 t2 x bs branch)
  from extends_paramD[OF "2"(1)] have "t1 \<notin> Var ` params branch" "t2 \<notin> Var ` params branch"
    by (meson disjoint_iff_not_equal params_subterms_last_disjnt)+
  then have not_in_params': "t1 \<notin> Var ` params' branch" "t2 \<notin> Var ` params' branch"
    unfolding params'_def by auto
  with extends_paramD[OF "2"(1)] "2"(2-) show ?case
    unfolding P_def params_subterms_def
    unfolding extends_param_params'_eq[OF "2"(1-3)] extends_param_params_eq[OF "2"(1-3)]
    by (auto simp: vars_fm_vars_branchI)
qed

lemma finite_set_pset_term: "finite (set_pset_term t)"
  apply(induction t)
       apply(auto)
  done

lemma finite_set_pset_atom: "finite (set_pset_atom a)"
  apply(cases a)
   apply(auto simp: finite_set_pset_term)
  done

lemma finite_vars_fm: "finite (vars_fm \<phi>)"
  apply(induction \<phi>)
     apply(auto simp: finite_set_pset_atom)
  done

lemma finite_vars_branch: "finite (vars_branch b)"
  apply(induction b)
   apply(auto simp: vars_branch_def finite_vars_fm)
  done

lemma finite_params: "finite (params b)"
  unfolding params_def using finite_vars_branch by auto

lemma finite_params': "finite (params' b)"
proof -
  have "params' b \<subseteq> params b"
    unfolding params'_def by simp
  then show ?thesis using finite_params finite_subset by blast
qed

lemma finite_subterms: "finite (subterms l)"
  apply(induction l)
       apply(auto)
  done

lemma finite_subterms_atom: "finite (subterms_atom l)"
  apply(cases l rule: subterms_atom.cases)
   apply(auto simp: finite_subterms)
  done

lemma finite_subterms_fm: "finite (subterms_fm \<phi>)"
  apply(induction \<phi>)
     apply(auto simp: finite_subterms_atom)
  done

lemma finite_subterms_branch: "finite (subterms_branch b)"
  apply(induction b)
   apply(auto simp: subterms_branch_def finite_subterms_fm)
  done

lemma finite_subterms_branch': "finite (subterms_branch' b)"
  unfolding subterms_branch'_def using finite_subterms_fm finite_params
  by auto

lemma finite_subfms: "finite (subfms \<phi>)"
  apply(induction \<phi>)
     apply(auto)
  done

lemma finite_subfms_branch: "finite (subfms_branch b)"
  by (induction b) (auto simp: subfms_branch_simps finite_subfms)

lemma finite_atoms: "finite (atoms \<phi>)"
  by (induction \<phi>) auto

lemma finite_pset_atoms_branch: "finite (pset_atoms_branch b)"
  by (auto simp: finite_atoms)

lemma wf_branch_not_Nil[simp]: "wf_branch b \<Longrightarrow> b \<noteq> []"
  unfolding wf_branch_def
  using extendss_suffix suffix_bot.extremum_uniqueI by blast

lemma subterms_branch_eq_if_wf_branch:
  assumes "wf_branch b"
  shows "subterms_branch b = params_subterms b"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "no_new_subterms [\<phi>]"
    unfolding no_new_subterms_def params_def
    by (simp add: subterms_branch_simps)
  with \<open>extendss b [\<phi>]\<close> have "no_new_subterms b"
    using extendss_no_new_subterms by blast
  with \<open>extendss b [\<phi>]\<close> assms show ?thesis
    by (intro subterms_branch_eq_if_no_new_subterms) simp_all
qed

lemma in_subterms_branch'_if_AT_mem_in_branch:
  assumes "wf_branch branch"
  assumes "AT (s \<in>\<^sub>s t) \<in> set branch"
  shows "s \<in> Var ` params' branch \<union> subterms_branch' branch"
    and "t \<in> Var ` params' branch \<union> subterms_branch' branch"
  using assms
  using params_subterms_eq_subterms_branch' subterms_branchI_if_AT_mem subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AF_mem_in_branch:
  assumes "wf_branch branch"
  assumes "AF (s \<in>\<^sub>s t) \<in> set branch"
  shows "s \<in> Var ` params' branch \<union> subterms_branch' branch"
    and "t \<in> Var ` params' branch \<union> subterms_branch' branch"
  using assms
  using params_subterms_eq_subterms_branch' subterms_branchI_if_AF_mem subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AT_eq_in_branch:
  assumes "wf_branch branch"
  assumes "AT (s \<approx>\<^sub>s t) \<in> set branch"
  shows "s \<in> Var ` params' branch \<union> subterms_branch' branch"
    and "t \<in> Var ` params' branch \<union> subterms_branch' branch"
  using assms
  using params_subterms_eq_subterms_branch' subterms_branchI_if_AT_eq subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AF_eq_in_branch:
  assumes "wf_branch branch"
  assumes "AF (s \<approx>\<^sub>s t) \<in> set branch"
  shows "s \<in> Var ` params' branch \<union> subterms_branch' branch"
    and "t \<in> Var ` params' branch \<union> subterms_branch' branch"
  using assms
  using params_subterms_eq_subterms_branch' subterms_branchI_if_AF_eq subterms_branch_eq_if_wf_branch
  by blast+

lemma
  assumes "wf_branch b"
  shows no_new_subterms_if_wf_branch: "no_new_subterms b"
    and no_params_if_not_literal_if_wf_branch:
      "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "no_new_subterms [\<phi>]"
    by (auto simp: no_new_subterms_def params_def vars_branch_simps subterms_branch_simps)
  from extendss_no_new_subterms[OF \<open>extendss b [\<phi>]\<close> _ this] show "no_new_subterms b"
    by simp
  from extendss_no_params_if_not_literal[OF \<open>extendss b [\<phi>]\<close>]
  show "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
    unfolding params_def by simp
qed

lemma lemma_2:
  assumes "wf_branch b"
  assumes "c \<in> params' b" "t \<in> params_subterms b"
  shows "AT (Var c \<approx>\<^sub>s t) \<notin> set b" "AT (t \<approx>\<^sub>s Var c) \<notin> set b" "AT (t \<in>\<^sub>s Var c) \<notin> set b"
proof -
  from \<open>wf_branch b\<close> obtain \<phi> where "extendss b [\<phi>]"
    using wf_branch_def by blast
  have no_params_if_not_literal: "\<forall>\<phi> \<in> set b'. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b' = {}"
    if "extendss b' [\<phi>]" for b'
    using no_params_if_not_literal_if_wf_branch that unfolding wf_branch_def by blast
  have no_new_subterms: "no_new_subterms b'" if "extendss b' [\<phi>]" for b'
    using no_new_subterms_if_wf_branch that unfolding wf_branch_def by blast
  have "AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
    using \<open>extendss b [\<phi>]\<close> assms(2,3)
  proof(induction b "[\<phi>]" arbitrary: c t rule: extendss.induct)
    case 1
    then have "params' [\<phi>] = {}"
      unfolding params'_def params_def by (auto simp: vars_branch_simps)
    with 1 show ?case
      by blast
  next
    case (2 b1 b2)
    note lemma_2_lextends[OF this(1) _
        no_new_subterms[OF this(3)] no_params_if_not_literal[OF this(3)]]
    with 2 show ?case
      using wf_branch_def wf_branch_not_Nil by blast
  next
    case (3 bs b2 b1)
    note lemma_2_extends[OF this(1) _ _
        no_new_subterms[OF this(3)] no_params_if_not_literal[OF this(3)]]
    with 3 show ?case
      using wf_branch_def wf_branch_not_Nil by blast
  qed
  then show "AT (Var c \<approx>\<^sub>s t) \<notin> set b" "AT (t \<approx>\<^sub>s Var c) \<notin> set b" "AT (t \<in>\<^sub>s Var c) \<notin> set b"
    by blast+
qed

lemma mem_subterms_fm_last_if_mem_subterms_branch:
  assumes "wf_branch b"
  assumes "t \<in> subterms_branch b" "\<not> is_Var t"
  shows "t \<in> subterms_fm (last b)"
  using assms
  unfolding subterms_branch_eq_if_wf_branch[OF \<open>wf_branch b\<close>]
  unfolding subterms_branch'_def params_subterms_def by force

locale open_branch =
  fixes b :: "'a branch"
  assumes wf_branch: "wf_branch b" and bopen: "bopen b"
      and infinite_vars: "infinite (UNIV :: 'a set)"
begin

sublocale fin_digraph_bgraph: fin_digraph "bgraph b"
proof
  show "finite (verts (bgraph b))"
    using finite_params' finite_subterms_branch'
    by (auto simp: bgraph_def Let_def)

  show "finite (arcs (bgraph b))"
    using [[simproc add: finite_Collect]]
    by (auto simp: bgraph_def Let_def inj_on_def intro!: finite_vimageI)

qed (use in_subterms_branch'_if_AT_mem_in_branch[OF wf_branch]
      in \<open>(fastforce simp: bgraph_def Let_def)+\<close>)

lemma member_seq_if_cas:
  "fin_digraph_bgraph.cas t1 is t2
  \<Longrightarrow> member_seq t1 (map (\<lambda>e. tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e) is) t2"
  by (induction "is" arbitrary: t1 t2) auto

lemma member_cycle_if_cycle:
  "fin_digraph_bgraph.cycle c
  \<Longrightarrow> member_cycle (map (\<lambda>e. tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e) c)"
  unfolding pre_digraph.cycle_def
  by (cases c) (auto simp: member_seq_if_cas)

sublocale dag_bgraph: dag "bgraph b"
proof(unfold_locales, goal_cases)
   case (1 e)
  show ?case
  proof (rule notI)
    assume "tail (bgraph b) e = head (bgraph b) e"
    then obtain t where "AT (t \<in>\<^sub>s t) \<in> set b"
      using 1 unfolding bgraph_def Let_def by auto
    then have "member_cycle [(t \<in>\<^sub>s t)]" "(t \<in>\<^sub>s t) \<in> Atoms (set b)"
      by (auto simp: Atoms_def)
    then have "bclosed b"
      using memberCycle by (metis empty_iff empty_set set_ConsD subsetI)
    with bopen show "False"
      by blast
  qed
next
  case (2 e1 e2)
  then show ?case
    by (auto simp: bgraph_def Let_def arc_to_ends_def)
next
  case 3
  show ?case
  proof(rule notI)
    assume "\<exists>c. fin_digraph_bgraph.cycle c"
    then obtain c where "fin_digraph_bgraph.cycle c"
      by blast
    then have "member_cycle (map (\<lambda>e. (tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e)) c)"
      using member_cycle_if_cycle by blast
    moreover
    from \<open>fin_digraph_bgraph.cycle c\<close> have "set c \<subseteq> arcs (bgraph b)"
      by (meson fin_digraph_bgraph.cycle_def pre_digraph.awalk_def)
    then have "set (map (\<lambda>e. (tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e)) c) \<subseteq> Atoms (set b)"
      unfolding bgraph_def Let_def Atoms_def by auto
    ultimately have "bclosed b"
      using memberCycle by blast
    with bopen show False by blast
  qed
qed

definition "I \<equiv> SOME f. inj_on f (Var ` params' b)
                  \<and> (\<forall>p. card (elts (f p)) \<ge> card (Var ` params' b \<union> subterms_branch' b))"

lemma
  shows inj_on_I: "inj_on I (Var ` params' b)"
    and card_I: "card (elts (I p)) \<ge> card (Var ` params' b \<union> subterms_branch' b)"
proof -
  have "\<exists>f. inj_on f (Var ` params' b)
    \<and> (\<forall>p. card (elts (f p)) \<ge> card (Var ` params' b \<union> subterms_branch' b))"
    using Ex_set_family finite_imageI[OF finite_params'] by blast
  from someI_ex[OF this]
  show "inj_on I (Var ` params' b)"
       "card (elts (I p)) \<ge> card (Var ` params' b \<union> subterms_branch' b)"
    unfolding I_def by blast+
qed


sublocale realization "bgraph b" "Var ` params' b" "subterms_branch' b" I
  rewrites "inj_on I (Var ` params' b) \<equiv> True"
       and "(\<forall>x \<in> Var ` params' b. \<forall>y \<in> Var ` params' b \<union> subterms_branch' b.
               x \<noteq> y \<longrightarrow> I x \<noteq> realization y) \<equiv> True"
       and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
       and "\<And>P Q. (True \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> True \<Longrightarrow> PROP Q)"
proof -
  let ?r = "realization.realization (bgraph b) (pset_term.Var ` params' b) (subterms_branch' b) I"

  show real: "realization (bgraph b) (pset_term.Var ` params' b) (subterms_branch' b)"
    apply(unfold_locales)
    using params'_subterms_branch'_disjnt by (fastforce simp: bgraph_def Let_def)+
  
  have "I x \<noteq> ?r y" if "x \<in> Var ` params' b" "y \<in> Var ` params' b" "x \<noteq> y" for x y
  proof -
    from that have "{x, y} \<subseteq> Var ` params' b"
      by blast
    with \<open>x \<noteq> y\<close> realization.finite_P_un_T[OF real]
    have "card (Var ` params' b \<union> subterms_branch' b) \<ge> 2"
      by (metis Un_commute card_2_iff card_mono le_supI2)
    with card_I realization.card_realization_P[OF real that(2)] show ?thesis
      by (metis Suc_1 not_less_eq_eq)
  qed
  moreover have "I x \<noteq> ?r y"
    if "x \<in> Var ` params' b" "y \<in> subterms_branch' b" "x \<noteq> y" for x y
    using card_I realization.card_realization_T_less_card_verts[OF real that(2)]
    by (metis le_antisym nat_less_le)
  ultimately have "(\<forall>x \<in> Var ` params' b. \<forall>y \<in> Var ` params' b \<union> subterms_branch' b.
                      x \<noteq> y \<longrightarrow> I x \<noteq> ?r y)"
    by blast
  then show "(\<forall>x \<in> Var ` params' b. \<forall>y \<in> Var ` params' b \<union> subterms_branch' b.
               x \<noteq> y \<longrightarrow> I x \<noteq> ?r y) \<equiv> True"
    by simp
qed (use inj_on_I card_I in auto)

lemma in_params_subterms_if_AT_mem_branch:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms subterms_branchI_if_AT_mem subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma in_params_subterms_if_AF_mem_branch:
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms subterms_branchI_if_AF_mem subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma params_subtermsI_if_AT_eq_branch:
  assumes "AT (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms subterms_branchI_if_AT_eq subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma params_subtermsI_if_AF_eq_branch:
  assumes "AF (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms subterms_branchI_if_AF_eq subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma realization_if_AT_mem:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "realization s \<in> elts (realization t)"
proof -
  note in_params_subterms_if_AT_mem_branch[OF assms]
  with assms have "t \<noteq> Var c" if "c \<in> params' b" for c
    using lemma_2(3)[OF wf_branch that \<open>s \<in> params_subterms b\<close>] by blast
  then have "t \<in> subterms_branch' b"
    using \<open>t \<in> params_subterms b\<close> 
    unfolding subterms_branch'_def params_subterms_def by auto
  moreover
  from assms have "s \<rightarrow>\<^bsub>bgraph b\<^esub> t"
    unfolding arcs_ends_def arc_to_ends_def by (simp add: bgraph_def)
  ultimately show ?thesis
    by auto
qed

lemma realization_if_AT_eq:
  assumes "lin_sat b"
  assumes "AT (t1 \<approx>\<^sub>s t2) \<in> set b"
  shows "realization t1 = realization t2"
proof -
  note params_subtermsI_if_AT_eq_branch[OF assms(2)]
  then consider
    (t1_param') c where "t1 = Var c" "c \<in> params' b" |
    (t2_param') c where "t2 = Var c" "c \<in> params' b" |
    (subterms) "t1 \<in> subterms_branch' b" "t2 \<in> subterms_branch' b"
    by (metis Un_iff image_iff params_subterms_eq_subterms_branch')
  then show ?thesis
  proof(cases)
    case t1_param'
    with lemma_2[OF wf_branch] assms have "t1 = t2"
      by (metis \<open>t2 \<in> params_subterms b\<close>)
    then show ?thesis by simp
  next
    case t2_param'
    with lemma_2[OF wf_branch] assms have "t1 = t2"
      by (metis \<open>t1 \<in> params_subterms b\<close>)
    then show ?thesis by simp
  next
    case subterms
    have "False" if "realization t1 \<noteq> realization t2"
    proof -
      from that have "elts (realization t1) \<noteq> elts (realization t2)"
        by blast
      from that obtain a t1' t2' where
        a: "a \<in> elts (realization t1')" "a \<notin> elts (realization t2')"
        and t1'_t2': "t1' = t1 \<and> t2' = t2 \<or> t1' = t2 \<and> t2' = t1"
        by blast
      with subterms have "t1' \<in> subterms_branch' b"
        by auto
      then obtain s where s: "a = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> t1'"
        using subterms dominates_if_mem_realization a small_realization_ancestors1
        by auto
      then have "s \<noteq> t1'"
        using dag_bgraph.adj_not_same by blast
      from s have "AT (s \<in>\<^sub>s t1') \<in> set b"
        unfolding bgraph_def Let_def using dag_bgraph.adj_not_same by auto
      note lextends_eq.intros(1,3)[OF assms(2) this, THEN lextends.intros(6)]
      with \<open>lin_sat b\<close> t1'_t2' have "AT (s \<in>\<^sub>s t2') \<in> set b"
        unfolding lin_sat_def using \<open>s \<noteq> t1'\<close>
        by (auto split: if_splits)
      from realization_if_AT_mem[OF this] \<open>a = realization s\<close> have "a \<in> elts (realization t2')"
        by blast
      with \<open>a \<notin> elts (realization t2')\<close> show False
        by blast
    qed
    then show ?thesis by blast
  qed
qed

lemma I_not_in_realization:
  assumes "t \<in> subterms_branch' b"
  shows "I x \<notin> elts (realization t)"
  using assms card_elts_realization_T[OF assms] card_I
  by (metis le_antisym le_eq_less_or_eq nat_neq_iff)

lemma realization_if_AF_eq:
  assumes "sat b"
  assumes "AF (t1 \<approx>\<^sub>s t2) \<in> set b"
  shows "realization t1 \<noteq> realization t2"
proof -
  note params_subtermsI_if_AF_eq_branch[OF assms(2)]
  then consider
    (t1_param') c where "t1 = Var c" "c \<in> params' b" |
    (t2_param') c where "t2 = Var c" "c \<in> params' b" "t1 \<in> Var ` params' b \<union> subterms_branch' b" |
    (subterms) "t1 \<in> subterms_branch' b" "t2 \<in> subterms_branch' b"
    by (metis Un_iff image_iff params_subterms_eq_subterms_branch')
  then show ?thesis
  proof cases
    case t1_param'
    then have "I t1 \<in> elts (realization t1)"
      by simp
    moreover from bopen assms(2) have "t1 \<noteq> t2"
      using neqSelf by blast
    then have "I t1 \<notin> elts (realization t2)"
      apply(cases t2 rule: realization.cases)
      using t1_param' inj_on_I I_not_in_realization by (auto simp: inj_on_contraD)
    ultimately show ?thesis by auto
  next
    case t2_param'
    then have "I t2 \<in> elts (realization t2)"
      by simp
    moreover from bopen assms(2) have "t1 \<noteq> t2"
      using neqSelf by blast
    then have "I t2 \<notin> elts (realization t1)"
      apply(cases t1 rule: realization.cases)
      using t2_param' inj_on_I I_not_in_realization by (auto simp: inj_on_contraD)
    ultimately show ?thesis by auto
  next
    case subterms
    define \<Delta> where "\<Delta> \<equiv> {(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> subterms_branch' b \<times> subterms_branch' b.
                            AF (\<tau>\<^sub>1 \<approx>\<^sub>s \<tau>\<^sub>2) \<in> set b \<and> realization \<tau>\<^sub>1 = realization \<tau>\<^sub>2}"
    have "finite \<Delta>"
    proof -
      have "\<Delta> \<subseteq> subterms_branch' b \<times> subterms_branch' b"
        unfolding \<Delta>_def by auto
      moreover note finite_cartesian_product[OF finite_subterms_branch' finite_subterms_branch']
      ultimately show ?thesis
        using finite_subset by blast
    qed
    let ?h = "\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). min (height \<tau>\<^sub>1) (height \<tau>\<^sub>2)"
    have False if "\<Delta> \<noteq> {}"
    proof -
      obtain t1 t2 where t1_t2: "(t1, t2) = arg_min_on ?h \<Delta>"
        by (metis surj_pair)
      have "(t1, t2) \<in> \<Delta>" "?h (t1, t2) = Min (?h ` \<Delta>)"
      proof -
        from arg_min_if_finite(1)[OF \<open>finite \<Delta>\<close> that] t1_t2 show "(t1, t2) \<in> \<Delta>"
          by metis

        have "f (arg_min_on f S) = Min (f ` S)" if "finite S" "S \<noteq> {}" for f S
          using arg_min_least[OF that] that
          by (auto intro!: Min_eqI[symmetric] intro: arg_min_if_finite(1)[OF that])
        from this[OF \<open>finite \<Delta>\<close> that] t1_t2 show "?h (t1, t2) = Min (?h ` \<Delta>)"
          by auto
      qed
      then have *: "t1 \<in> subterms_branch' b" "t2 \<in> subterms_branch' b"
        "AF (t1 \<approx>\<^sub>s t2) \<in> set b" "realization t1 = realization t2"
        unfolding \<Delta>_def by auto
      obtain t1' t2' where t1'_t2':
        "t1' \<in> subterms_fm (last b)" "t2' \<in> subterms_fm (last b)"
        "AF (t1' \<approx>\<^sub>s t2') \<in> set b" "realization t1' = realization t2'"
        "realization t1' = realization t1" "realization t2' = realization t2"
      proof -
        from * consider
          "t1 \<in> subterms_fm (last b)"
          | t1' where "t1' \<in> subterms_fm (last b)"
            "(AT (t1' \<approx>\<^sub>s t1) \<in> set b \<or> AT (t1 \<approx>\<^sub>s t1') \<in> set b)"
          unfolding subterms_branch'_def params'_def by blast
        then obtain t1'' where
          "t1'' \<in> subterms_fm (last b)" "AF (t1'' \<approx>\<^sub>s t2) \<in> set b"
          "realization t1'' = realization t1"
        proof cases
          case (2 t1')
          from bopen neqSelf \<open>AF (t1 \<approx>\<^sub>s t2) \<in> set b\<close> have "t1 \<noteq> t2"
            by blast
          with 2 \<open>sat b\<close> have "AF (t1' \<approx>\<^sub>s t2) \<in> set b"
            using lextends_eq.intros(2,4)[OF _ \<open>AF (t1 \<approx>\<^sub>s t2) \<in> set b\<close>, THEN lextends.intros(6)]
            unfolding sat_def subst_tlvl.simps tlvl_terms_atom.simps
            by (smt (verit, ccfv_SIG) insert_iff lin_satD list.set_intros(1))
          with that[OF "2"(1) this] \<open>sat b\<close>[unfolded sat_def] show ?thesis
            using realization_if_AT_eq 2 by metis
        qed (use * that[of t1] in blast)
        moreover
        from * consider
          "t2 \<in> subterms_fm (last b)"
          | t2' where "t2' \<in> subterms_fm (last b)"
            "(AT (t2' \<approx>\<^sub>s t2) \<in> set b \<or> AT (t2 \<approx>\<^sub>s t2') \<in> set b)"
          unfolding subterms_branch'_def params'_def by blast
        then obtain t2'' where
          "t2'' \<in> subterms_fm (last b)" "AF (t1'' \<approx>\<^sub>s t2'') \<in> set b"
          "realization t2'' = realization t2"
        proof cases
          case (2 t2')
          from bopen neqSelf \<open>AF (t1'' \<approx>\<^sub>s t2) \<in> set b\<close> have "t1'' \<noteq> t2"
            by blast
          with 2 \<open>sat b\<close> have "AF (t1'' \<approx>\<^sub>s t2') \<in> set b"
            using lextends_eq.intros(2,4)[OF _ \<open>AF (t1'' \<approx>\<^sub>s t2) \<in> set b\<close>, THEN lextends.intros(6)]
            unfolding sat_def subst_tlvl.simps tlvl_terms_atom.simps
            by (smt (verit, ccfv_SIG) insert_iff lin_satD list.set_intros(1))
          with that[OF "2"(1) this] \<open>sat b\<close>[unfolded sat_def] show ?thesis
            using realization_if_AT_eq 2 by metis
        qed (use \<open>AF (t1'' \<approx>\<^sub>s t2) \<in> set b\<close> that[of t2] in blast)
        ultimately show ?thesis
          using that * by metis
      qed
      then have "(t1', t2') \<in> \<Delta>"
        unfolding \<Delta>_def subterms_branch'_def by blast
      then have t1'_t2'_subterms: "t1' \<in> subterms_branch' b" "t2' \<in> subterms_branch' b"
        unfolding \<Delta>_def by blast+
      
      from t1'_t2' lemma1_2 "*"(3) have "?h (t1', t2') = ?h (t1, t2)"
        using params_subtermsI_if_AF_eq_branch(1,2) 
        by (metis case_prod_conv params_subterms_eq_subterms_branch')
 
      from finite_vars_branch infinite_vars obtain x where "x \<notin> vars_branch b"
        using ex_new_if_finite by blast
      from extends_param.intros[OF t1'_t2'(3,1,2) _ _ this] \<open>sat b\<close>[unfolded sat_def] consider
        s1 where "AT (s1 \<in>\<^sub>s t1') \<in> set b" "AF (s1 \<in>\<^sub>s t2') \<in> set b" |
        s2 where "AF (s2 \<in>\<^sub>s t1') \<in> set b" "AT (s2 \<in>\<^sub>s t2') \<in> set b"
        using extends.intros by metis 
      then show ?thesis
      proof cases
        case 1
        with \<open>realization t1' = realization t2'\<close> have "realization s1 \<in> elts (realization t2')"
          using realization_if_AT_mem by metis
        with 1 t1'_t2'(3,4) obtain s2 where
          "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2'" "realization s1 = realization s2"
          using dominates_if_mem_realization in_subterms_branch'_if_AT_mem_in_branch(1)[OF wf_branch] 
          by (metis params_subtermsI_if_AF_eq_branch(2) params_subterms_eq_subterms_branch')
        then have "AT (s2 \<in>\<^sub>s t2') \<in> set b"
          unfolding bgraph_def Let_def by auto
        with \<open>AF (s1 \<in>\<^sub>s t2') \<in> set b\<close> \<open>sat b\<close>[unfolded sat_def]
        have "AF (s2 \<approx>\<^sub>s s1) \<in> set b"
          using lextends_eq.intros(5)[THEN lextends.intros(6)] lin_satD by fastforce
        then have "s1 \<noteq> s2"
          using neqSelf bopen by blast           
        then have "s1 \<in> subterms_branch' b" "s2 \<in> subterms_branch' b"
          using \<open>realization s1 = realization s2\<close> inj_on_contraD[OF inj_on_I \<open>s1 \<noteq> s2\<close>]
          using in_subterms_branch'_if_AF_eq_in_branch[OF wf_branch \<open>AF (s2 \<approx>\<^sub>s s1) \<in> set b\<close>]
          using I_not_in_realization by auto blast+
        with \<open>realization s1 = realization s2\<close> have "(s2, s1) \<in> \<Delta>"
          unfolding \<Delta>_def using \<open>AF (s2 \<approx>\<^sub>s s1) \<in> set b\<close> by auto
        moreover have "?h (s2, s1) < ?h (t1', t2')"
          using \<open>s1 \<in> subterms_branch' b\<close> \<open>s2 \<in> subterms_branch' b\<close>
          using \<open>AF (s2 \<approx>\<^sub>s s1) \<in> set b\<close> \<open>realization s1 = realization s2\<close>
                \<open>realization s1 \<in> elts (realization t2')\<close>
          using t1'_t2'(4) t1'_t2'_subterms
          by (auto simp: min_def intro: lemma1_2 lemma1_3)

        ultimately show ?thesis
          using arg_min_least[OF \<open>finite \<Delta>\<close> \<open>\<Delta> \<noteq> {}\<close>]
          using \<open>(t1', t2') \<in> \<Delta>\<close> \<open>?h (t1', t2') = ?h (t1, t2)\<close> t1_t2
          by (metis (mono_tags, lifting) le_antisym le_eq_less_or_eq nat_neq_iff)
      next
        case 2
        with \<open>realization t1' = realization t2'\<close> have "realization s2 \<in> elts (realization t1')"
          using realization_if_AT_mem by metis
        with 2 t1'_t2'(3,4) obtain s1 where
          "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1'" "realization s1 = realization s2"
          using dominates_if_mem_realization in_subterms_branch'_if_AT_mem_in_branch(1)
          by (metis in_subterms_branch'_if_AF_eq_in_branch(1) wf_branch)
        then have "AT (s1 \<in>\<^sub>s t1') \<in> set b"
          unfolding bgraph_def Let_def by auto
        with \<open>AF (s2 \<in>\<^sub>s t1') \<in> set b\<close> \<open>sat b\<close>[unfolded sat_def]
        have "AF (s1 \<approx>\<^sub>s s2) \<in> set b"
          using lextends_eq.intros(5)[THEN lextends.intros(6)]
          using lin_satD by fastforce
        then have "s1 \<noteq> s2"
          using neqSelf bopen by blast           
        then have "s1 \<in> subterms_branch' b" "s2 \<in> subterms_branch' b"
          using \<open>realization s1 = realization s2\<close> inj_on_contraD[OF inj_on_I \<open>s1 \<noteq> s2\<close>]
          using in_subterms_branch'_if_AF_eq_in_branch[OF wf_branch \<open>AF (s1 \<approx>\<^sub>s s2) \<in> set b\<close>]
          using I_not_in_realization by auto blast+
        with \<open>realization s1 = realization s2\<close> have "(s1, s2) \<in> \<Delta>"
          unfolding \<Delta>_def using \<open>AF (s1 \<approx>\<^sub>s s2) \<in> set b\<close> by auto
        moreover have "?h (s1, s2) < ?h (t1', t2')"
          using \<open>s1 \<in> subterms_branch' b\<close> \<open>s2 \<in> subterms_branch' b\<close>
          using \<open>AF (s1 \<approx>\<^sub>s s2) \<in> set b\<close> \<open>realization s1 = realization s2\<close>
                \<open>realization s2 \<in> elts (realization t1')\<close>
          using t1'_t2'(4) t1'_t2'_subterms
          by (auto simp: min_def intro: lemma1_2 lemma1_3)
        ultimately show ?thesis
          using arg_min_least[OF \<open>finite \<Delta>\<close> \<open>\<Delta> \<noteq> {}\<close>]
          using \<open>(t1', t2') \<in> \<Delta>\<close> \<open>?h (t1', t2') = ?h (t1, t2)\<close> t1_t2
          by (metis (mono_tags, lifting) le_antisym le_eq_less_or_eq nat_neq_iff)
      qed
    qed
    with assms subterms show ?thesis
      unfolding \<Delta>_def by blast
  qed
qed

lemma realization_if_AF_mem:
  assumes "sat b"
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "realization s \<notin> elts (realization t)"
proof
  assume "realization s \<in> elts (realization t)"
  from assms have "s \<in> Var ` params' b \<union> subterms_branch' b"
                  "t \<in> Var ` params' b \<union> subterms_branch' b"
    using in_subterms_branch'_if_AF_mem_in_branch[OF wf_branch] by blast+
  from dominates_if_mem_realization[OF this \<open>realization s \<in> elts (realization t)\<close>]
  obtain s' where "s' \<rightarrow>\<^bsub>bgraph b\<^esub> t" "realization s = realization s'"
    by blast
  then have "AT (s' \<in>\<^sub>s t) \<in> set b"
    unfolding bgraph_def Let_def by auto
  with assms lextends_eq.intros(5)[THEN lextends.intros(6)] have "AF (s' \<approx>\<^sub>s s) \<in> set b"
    unfolding sat_def using lin_satD by fastforce
  from realization_if_AF_eq[OF \<open>sat b\<close> this] \<open>realization s = realization s'\<close> show False
    by simp
qed

lemma realization_Empty:
  assumes "\<emptyset> \<in> subterms_branch b"
  shows "realization \<emptyset> = 0"
proof -
  from bopen have "AT (s \<in>\<^sub>s \<emptyset>) \<notin> set b" for s
    using bclosed.intros by blast
  then have "ancestors1 (bgraph b) \<emptyset> = {}"
    unfolding bgraph_def Let_def by auto
  moreover from assms have "\<emptyset> \<in> subterms_branch' b"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    unfolding subterms_branch'_def by simp
  then have "\<emptyset> \<in> subterms_branch' b"
    unfolding subterms_branch'_def by blast
  ultimately show "realization \<emptyset> = 0"
    by simp
qed

lemma realization_Union:
  assumes "sat b"
  assumes "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b"
  shows "realization (t1 \<squnion>\<^sub>s t2) = realization t1 \<squnion> realization t2"
  using assms
proof -
  from assms have mem_subterms_fm: "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "elts (realization (t1 \<squnion>\<^sub>s t2)) \<subseteq> elts (realization t1 \<squnion> realization t2)"
  proof
    fix e assume "e \<in> elts (realization (t1 \<squnion>\<^sub>s t2))"
    then obtain s where s: "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> (t1 \<squnion>\<^sub>s t2)"
      using dominates_if_mem_realization mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last]
      by auto
    then have "AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> consider "AT (s \<in>\<^sub>s t1) \<in> set b" | "AF (s \<in>\<^sub>s t1) \<in> set b"
      unfolding sat_def using extends_noparam.intros(3)[OF _ mem_subterms_fm, THEN extends.intros(1)]
      by blast
    then show "e \<in> elts (realization t1 \<squnion> realization t2)"
    proof(cases)
      case 1
      with s show ?thesis using realization_if_AT_mem by auto
    next
      case 2
      from \<open>sat b\<close> lextends_un.intros(4)[OF \<open>AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b\<close> this]
      have "AT (s \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD lextends.intros(2) by force
      with s show ?thesis using realization_if_AT_mem by auto
    qed
  qed
  moreover have "elts (realization t1 \<squnion> realization t2) \<subseteq> elts (realization (t1 \<squnion>\<^sub>s t2))"
  proof
    fix e assume "e \<in> elts (realization t1 \<squnion> realization t2)"
    then consider
      s1 where "e = realization s1" "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1" |
      s2 where "e = realization s2" "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realization
      using subterms_fmD(1,2)[OF mem_subterms_fm, THEN subterms_branch'_if_subterms_fm_last]
      by auto
    then show "e \<in> elts (realization (t1 \<squnion>\<^sub>s t2))"
    proof(cases)
      case 1
      then have "AT (s1 \<in>\<^sub>s t1) \<in> set b"
        unfolding bgraph_def Let_def by auto
      from \<open>sat b\<close> lextends_un.intros(2)[OF this mem_subterms_fm, THEN lextends.intros(2)]
      have "AT (s1 \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD by force
      with 1 realization_if_AT_mem[OF this] show ?thesis
        by blast
    next
      case 2
      then have "AT (s2 \<in>\<^sub>s t2) \<in> set b"
        unfolding bgraph_def Let_def by auto
      from \<open>sat b\<close> lextends_un.intros(3)[OF this mem_subterms_fm, THEN lextends.intros(2)]
      have "AT (s2 \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD by force
      with 2 realization_if_AT_mem[OF this] show ?thesis
        by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma (in -) elts_inf[simp]: "elts (s \<sqinter> t) = elts s \<inter> elts t"
  unfolding inf_V_def
  by (meson down elts_of_set inf_le2)

lemma realization_Inter:
  assumes "sat b"
  assumes "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b"
  shows "realization (t1 \<sqinter>\<^sub>s t2) = realization t1 \<sqinter> realization t2"
  using assms
proof -
  from assms have mem_subterms_fm: "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "elts (realization (t1 \<sqinter>\<^sub>s t2)) \<subseteq> elts (realization t1 \<sqinter> realization t2)"
  proof
    fix e assume "e \<in> elts (realization (t1 \<sqinter>\<^sub>s t2))"
    then obtain s where s: "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> (t1 \<sqinter>\<^sub>s t2)"
      using dominates_if_mem_realization mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last]
      by auto
    then have "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lextends_int.intros(1)[OF this, THEN lextends.intros(3)]
    have "AT (s \<in>\<^sub>s t1) \<in> set b" "AT (s \<in>\<^sub>s t2) \<in> set b"
      unfolding sat_def using lin_satD by force+
    from this[THEN realization_if_AT_mem] s show "e \<in> elts (realization t1 \<sqinter> realization t2)"
      by auto
  qed
  moreover have "elts (realization t1 \<sqinter> realization t2) \<subseteq> elts (realization (t1 \<sqinter>\<^sub>s t2))"
  proof
    fix e assume "e \<in> elts (realization t1 \<sqinter> realization t2)"
    then obtain s1 s2 where s1_s2:
      "e = realization s1" "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1"
      "e = realization s2" "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realization
      using subterms_fmD(3,4)[OF mem_subterms_fm, THEN subterms_branch'_if_subterms_fm_last]
      by auto metis+
    then have "AT (s1 \<in>\<^sub>s t1) \<in> set b" "AT (s2 \<in>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    moreover have "AT (s1 \<in>\<^sub>s t2) \<in> set b"
    proof -
      from \<open>sat b\<close> have "AT (s1 \<in>\<^sub>s t2) \<in> set b \<or> AF (s1 \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def
        using extends_noparam.intros(4)[OF \<open>AT (s1 \<in>\<^sub>s t1) \<in> set b\<close> mem_subterms_fm]
        using extends.intros(1) by blast
      moreover from \<open>sat b\<close> s1_s2 have False if "AF (s1 \<in>\<^sub>s t2) \<in> set b"
      proof -
        note lextends_eq.intros(5)[OF \<open>AT (s2 \<in>\<^sub>s t2) \<in> set b\<close> that, THEN lextends.intros(6)]
        with realization_if_AF_eq[OF \<open>sat b\<close>, of s2 s1] have "realization s2 \<noteq> realization s1"
          using \<open>sat b\<close> by (auto simp: sat_def lin_satD)
        with \<open>e = realization s1\<close> \<open>e = realization s2\<close> show False by simp
      qed
      ultimately show "AT (s1 \<in>\<^sub>s t2) \<in> set b" by blast
    qed
    ultimately have "AT (s1 \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b"
      using \<open>sat b\<close> lextends_int.intros(6)[OF _ _ mem_subterms_fm, THEN lextends.intros(3)]
      unfolding sat_def by (fastforce simp: lin_satD)
    from realization_if_AT_mem[OF this] show "e \<in> elts (realization (t1 \<sqinter>\<^sub>s t2))"
      unfolding \<open>e = realization s1\<close>
      using mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last] by simp
  qed
  ultimately show ?thesis by blast
qed

lemma realization_Diff:
  assumes "sat b"
  assumes "t1 -\<^sub>s t2 \<in> subterms_branch b"
  shows "realization (t1 -\<^sub>s t2) = vdiff (realization t1) (realization t2)"
  using assms
proof -
  from assms have mem_subterms_fm: "t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "elts (realization (t1 -\<^sub>s t2)) \<subseteq> elts (vdiff (realization t1) (realization t2))"
  proof
    fix e assume "e \<in> elts (realization (t1 -\<^sub>s t2))"
    then obtain s where s: "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> (t1 -\<^sub>s t2)"
      using dominates_if_mem_realization mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last]
      by auto
    then have "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lextends_diff.intros(1)[OF this, THEN lextends.intros(4)]
    have "AT (s \<in>\<^sub>s t1) \<in> set b" "AF (s \<in>\<^sub>s t2) \<in> set b"
      unfolding sat_def using lin_satD by force+
    with s show "e \<in> elts (vdiff (realization t1) (realization t2))"
      using \<open>sat b\<close> realization_if_AT_mem realization_if_AF_mem
      by (auto simp: vdiff_def)
  qed
  moreover have "elts (vdiff (realization t1) (realization t2)) \<subseteq> elts (realization (t1 -\<^sub>s t2))"
  proof
    fix e assume "e \<in> elts (vdiff (realization t1) (realization t2))"
    then obtain s where s:
      "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> t1" "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realization
      using subterms_fmD(5,6)[OF mem_subterms_fm, THEN subterms_branch'_if_subterms_fm_last]
      by (auto simp: vdiff_def split: if_splits) blast
    then have "AT (s \<in>\<^sub>s t1) \<in> set b"
      unfolding bgraph_def Let_def by auto
    moreover have "AF (s \<in>\<^sub>s t2) \<in> set b"
    proof -
      from \<open>sat b\<close> have "AT (s \<in>\<^sub>s t2) \<in> set b \<or> AF (s \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def using extends_noparam.intros(5)[OF \<open>AT (s \<in>\<^sub>s t1) \<in> set b\<close> mem_subterms_fm]
        using extends.intros(1) by blast
      moreover from s(3) have False if "AT (s \<in>\<^sub>s t2) \<in> set b"
        using that unfolding Let_def bgraph_def by (auto simp: arcs_ends_def arc_to_ends_def)
      ultimately show "AF (s \<in>\<^sub>s t2) \<in> set b"
        by blast
    qed
    ultimately have "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b"
      using \<open>sat b\<close> lextends_diff.intros(6)[OF _ _ mem_subterms_fm, THEN lextends.intros(4)]
      unfolding sat_def by (fastforce simp: lin_satD)
    from realization_if_AT_mem[OF this] show "e \<in> elts (realization (t1 -\<^sub>s t2))"
      unfolding \<open>e = realization s\<close>
      using mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last] by simp
  qed
  ultimately show ?thesis by blast
qed

lemma realization_Single:
  assumes "sat b"
  assumes "Single t \<in> subterms_branch b"
  shows "realization (Single t) = vset {realization t}"
  using assms
proof -
  from assms have mem_subterms_fm: "Single t \<in> subterms_fm (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "elts (realization (Single t)) \<subseteq> elts (vset {realization t})"
  proof
    fix e assume "e \<in> elts (realization (Single t))"
    then obtain s where s: "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> Single t"
      using dominates_if_mem_realization mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last]
      by auto
    then have "AT (s \<in>\<^sub>s Single t) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lextends_single.intros(2)[OF this, THEN lextends.intros(5)]
    have "AT (s \<approx>\<^sub>s t) \<in> set b"
      unfolding sat_def using lin_satD by fastforce
    with s show "e \<in> elts (vset {realization t})"
      using realization_if_AT_eq \<open>sat b\<close>[unfolded sat_def]
      by auto
  qed
  moreover have "elts (vset {realization t}) \<subseteq> elts (realization (Single t))"
  proof
    fix e assume "e \<in> elts (vset {realization t})"
    then have "e = realization t"
      by simp
    from lextends_single.intros(1)[OF mem_subterms_fm, THEN lextends.intros(5)] \<open>sat b\<close>
    have "AT (t \<in>\<^sub>s Single t) \<in> set b"
      unfolding sat_def using lin_satD by fastforce
    from realization_if_AT_mem[OF this] \<open>e = realization t\<close>
    show "e \<in> elts (realization (Single t))"
      using mem_subterms_fm[THEN subterms_branch'_if_subterms_fm_last]
      by simp
  qed
  ultimately show ?thesis by blast
qed

lemmas realization_simps =
  realization_Empty realization_Union realization_Inter realization_Diff realization_Single

end

lemma subterms_nonempty[simp]: "subterms t \<noteq> {}"
  by (induction t) auto

lemma subterms_atom_nonempty[simp]: "subterms_atom l \<noteq> {}"
  by (cases l rule: subterms_atom.cases) auto

lemma subterms_fm_nonempty[simp]: "subterms_fm \<phi> \<noteq> {}"
  by (induction \<phi>) auto

lemma Ex_extends_params_if_in_params:
  assumes "wf_branch b"
  assumes "x \<in> params b"
  obtains t1 t2 bs b2 b1 where
    "extendss b (b2 @ b1)" "extends_param t1 t2 x bs b1" "b2 \<in> set bs" "extendss b1 [last b]"
    "x \<notin> params b1" "params (b2 @ b1) = insert x (params b1)"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "last b = \<phi>"
    by simp
  from \<open>extendss b [\<phi>]\<close> \<open>x \<in> params b\<close> that show ?thesis
    unfolding \<open>last b = \<phi>\<close>
  proof(induction b "[\<phi>]" rule: extendss.induct)
    case 1
    then show ?case by simp
  next
    case (2 b2 b1)
    with extendss_mono have "b1 \<noteq> []"
      by fastforce
    with lextends_params_eq[OF \<open>lextends b2 b1\<close> this] 2 show ?case
      by (metis (no_types, lifting) extendss.intros(2))
  next
    case (3 bs _ b2)
    then show ?case
    proof(induction rule: extends.induct)
      case (1 bs b1)
      with extendss_mono have "b1 \<noteq> []"
        by fastforce
      with extends_noparam_params_eq[OF \<open>extends_noparam bs b1\<close> \<open>b2 \<in> set bs\<close> this] 1 show ?case
        by (metis extends.intros(1) extendss.intros(3))
    next
      case (2 t1 t2 y bs b1)
      show ?case
      proof(cases "x \<in> params b1")
        case True
        from 2 have "extendss (b2 @ b1) b1"
          using extendss.intros(3)[OF _ "2.prems"(1)] extends.intros(2)[OF "2.hyps"]
          by (metis extendss.intros(1))
        with True 2 show ?thesis
          using extendss_trans by blast
      next
        case False
        from 2 have "b1 \<noteq> []"
          using extendss_mono by fastforce
        with extends_paramD[OF "2"(1)] "2"(2-) have "params (b2 @ b1) = insert y (params b1)"
          unfolding params_def
          apply (auto simp: vars_branch_simps mem_vars_fm_if_mem_subterm_fm)
          apply (metis extendss_last_eq last.simps last_in_set list.distinct(1) vars_fm_vars_branchI)+
          done
        moreover from \<open>y \<notin> vars_branch b1\<close> have "y \<notin> params b1"
          unfolding params_def by simp
        moreover from calculation have "y = x"
          using False 2 by simp
        ultimately show ?thesis
          using 2 by (metis extendss.intros(1))
      qed
    qed
  qed
qed

lemma card_params_ub_if_wf_branch:
  assumes "wf_branch b"
  shows "card (params b) \<le> (card (subterms_fm (last b)))^2"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  with wf_branch_not_Nil[OF assms] have [simp]: "last b = \<phi>"
    using extendss_last_eq by force
  have False if card_gt: "card (params b) > (card (subterms_fm \<phi>))^2"
  proof -
    define ts where "ts \<equiv> (\<lambda>x. SOME (t1, t2). \<exists>bs b2 b1.
       extendss b (b2 @ b1) \<and> b2 \<in> set bs \<and> extends_param t1 t2 x bs b1  \<and> extendss b1 [\<phi>])"
    from \<open>extendss b [\<phi>]\<close> \<open>last b = \<phi>\<close>
    have "\<exists>t1 t2 bs b2 b1.
      extendss b (b2 @ b1) \<and> b2 \<in> set bs \<and> extends_param t1 t2 x bs b1 \<and> extendss b1 [\<phi>]"
      if "x \<in> params b" for x
      using that Ex_extends_params_if_in_params[OF \<open>wf_branch b\<close> that] by metis
    then have ts_wd:
      "\<exists>bs b2 b1. extendss b (b2 @ b1) \<and> b2 \<in> set bs \<and> extends_param t1 t2 x bs b1 \<and> extendss b1 [\<phi>]"
      if "ts x = (t1, t2)" "x \<in> params b" for t1 t2 x
      using that unfolding ts_def
      by (smt (verit, ccfv_SIG) prod.case someI)
    with \<open>last b = \<phi>\<close> \<open>extendss b [\<phi>]\<close> have in_subterms_fm:
      "t1 \<in> subterms_fm \<phi>" "t2 \<in> subterms_fm \<phi>"
      if "ts x = (t1, t2)" "x \<in> params b" for t1 t2 x
      using that extends_paramD
      by (metis extendss_last_eq list.discI)+
    have "\<not> inj_on ts (params b)"
    proof -
      from in_subterms_fm have "ts ` params b \<subseteq> subterms_fm \<phi> \<times> subterms_fm \<phi>"
        by (intro subrelI) (metis imageE mem_Sigma_iff)
      then have "card (ts ` params b) \<le> card (subterms_fm \<phi> \<times> subterms_fm \<phi>)"
        by (intro card_mono) (simp_all add: finite_subterms_fm)
      moreover have "card (subterms_fm \<phi> \<times> subterms_fm \<phi>) = (card (subterms_fm \<phi>))^2"
        unfolding card_cartesian_product by algebra
      ultimately show "\<not> inj_on ts (params b)"
        using card_gt by (metis card_image linorder_not_less)
    qed
  
    from \<open>\<not> inj_on ts (params b)\<close> obtain x t1 t2 xb1 xbs2 xb2 y yb1 ybs2 yb2 where x_y:
      "x \<noteq> y" "x \<in> params b" "y \<in> params b"
      "extendss xb1 [\<phi>]" "extends_param t1 t2 x xbs2 xb1" "xb2 \<in> set xbs2" "extendss b (xb2 @ xb1)"
      "extendss yb1 [\<phi>]" "extends_param t1 t2 y ybs2 yb1" "yb2 \<in> set ybs2" "extendss b (yb2 @ yb1)"
      unfolding inj_on_def by (metis ts_wd prod.exhaust)
    have "xb2 \<noteq> yb2"
      using x_y(5)[THEN extends_paramD(1)] x_y(9)[THEN extends_paramD(1)] x_y(1,6,10) 
      by auto
    moreover from x_y have "suffix (xb2 @ xb1) (yb2 @ yb1) \<or> suffix (yb2 @ yb1) (xb2 @ xb1)"
      using extendss_suffix suffix_same_cases by blast 
    then have "suffix (xb2 @ xb1) yb1 \<or> suffix (yb2 @ yb1) xb1"
      using x_y(5)[THEN extends_paramD(1)] x_y(9)[THEN extends_paramD(1)] x_y(1,6,10)
      by (auto simp: suffix_Cons)
    ultimately show False
      using extends_paramD(1,5,6)[OF x_y(5)] extends_paramD(1,5,6)[OF x_y(9)] x_y(6,10)
      by (auto dest!: set_mono_suffix)
  qed
  then show ?thesis
    using linorder_not_le \<open>last b = \<phi>\<close> by blast
qed

lemma mem_subterms_fm_last_or_params_if_wf_branch:
  assumes "wf_branch b" "t \<in> subterms_branch b"
  shows "t \<in> subterms_fm (last b) \<or> t \<in> Var ` params b"
  using assms no_new_subterms_if_wf_branch
  unfolding no_new_subterms_def by blast

lemma card_subterms_branch_ub_if_wf_branch:
  assumes "wf_branch b"
  shows "card (subterms_branch b) \<le> card (subterms_fm (last b)) + card (params b)"
  using subterms_branch_eq_if_wf_branch[OF assms, unfolded params_subterms_def]
  by (simp add: assms card_Un_disjoint card_image_le finite_params finite_subterms_fm
                params_subterms_last_disjnt)

lemma card_Atoms_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card {a \<in> set b. is_literal a}
       \<le> 2 * (2 * (card (subterms_fm (last b)) + card (params b))^2)"
proof -
  have "card {a \<in> set b. is_literal a}
      \<le> card (pset_atoms_branch b) + card (pset_atoms_branch b)" (is "card ?A \<le> _")
  proof -
    have "?A = {AT a |a. AT a \<in> set b}
             \<union> {AF a |a. AF a \<in> set b}" (is "_ = ?ATs \<union> ?AFs")
      by auto (metis is_literal.elims(2))
    moreover have
      "?ATs \<subseteq> AT ` pset_atoms_branch b" "?AFs \<subseteq> AF ` pset_atoms_branch b"
      by force+
    moreover from calculation have "finite ?ATs" "finite ?AFs"
      by (simp_all add: finite_surj[OF finite_pset_atoms_branch])
    moreover have "?ATs \<inter> ?AFs = {}"
      by auto
    ultimately show ?thesis
      by (simp add: add_mono card_Un_disjoint finite_pset_atoms_branch surj_card_le)
  qed
  then have "card ?A \<le> 2 * card (pset_atoms_branch b)"
    by simp
  moreover
  have "atoms \<phi> \<subseteq>
    case_prod Elem ` (subterms_fm \<phi> \<times> subterms_fm \<phi>)
    \<union> case_prod Equal ` (subterms_fm \<phi> \<times> subterms_fm \<phi>)" for \<phi>
  proof(induction \<phi>)
    case (Atom x)
    then show ?case by (cases x) auto
  qed auto
  then have "pset_atoms_branch b \<subseteq>
    case_prod Elem ` (subterms_branch b \<times> subterms_branch b)
    \<union> case_prod Equal ` (subterms_branch b \<times> subterms_branch b)" (is "_ \<subseteq> ?Els \<union> ?Eqs")
    unfolding subterms_branch_def
    by force
  have "card (pset_atoms_branch b)
    \<le> (card (subterms_branch b))^2 + (card (subterms_branch b))^2"
  proof -
    from finite_subterms_branch have "finite (subterms_branch b \<times> subterms_branch b)"
      using finite_cartesian_product by auto
    then have "finite ?Els" "finite ?Eqs"
      by blast+
    moreover have "inj_on (case_prod Elem) A" "inj_on (case_prod Equal) A" for A
      unfolding inj_on_def by auto
    ultimately have "card ?Els = (card (subterms_branch b))^2" "card ?Eqs = (card (subterms_branch b))^2"
      using card_image[where ?A="subterms_branch b \<times> subterms_branch b"] card_cartesian_product
      unfolding power2_eq_square by metis+
    with card_mono[OF _ \<open>pset_atoms_branch b \<subseteq> ?Els \<union> ?Eqs\<close>] show ?thesis
      using \<open>finite ?Els\<close> \<open>finite ?Eqs\<close>
      by (metis card_Un_le finite_UnI sup.boundedE sup_absorb2)
  qed
  then have "card (pset_atoms_branch b) \<le> 2 * (card (subterms_branch b))^2"
    by simp
  ultimately show ?thesis
    using card_subterms_branch_ub_if_wf_branch[OF assms]
    by (meson dual_order.trans mult_le_mono2 power2_nat_le_eq_le)
qed

lemma lextends_not_Atom_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi>. \<psi> \<in> set b \<and> \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  apply(induction b' b rule: lextends_induct)
                      apply(fastforce simp: P_def dest: subfmsD)+
  done

lemma extends_not_Atom_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi>. \<psi> \<in> set b \<and> \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "extends bs b" "b' \<in> set bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
proof(induction bs b rule: extends.induct)
  case (1 bs b)
  then show ?case
    apply(induction rule: extends_noparam.induct)
        apply(fastforce simp: P_def dest: subfmsD)+
    done
next
  case (2 t1 t2 x bs b)
  then show ?case
    apply(induction rule: extends_param.induct)
    apply(fastforce simp: P_def dest: subfmsD)+
    done
qed

lemma extendss_not_Atom_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi>. \<psi> \<in> set b \<and> \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "extendss b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-)
proof(induction b' b rule: extendss.induct)
  case (2 b3 b2 b1)
  then have "b2 \<noteq> []"
    using extendss_suffix suffix_bot.extremum_uniqueI by blast
  with 2 show ?case
    using lextends_not_Atom_mem_subfms_last unfolding P_def by blast
next
  case (3 bs b2 b3 b1)
  then have "b2 \<noteq> []"
    using extendss_suffix suffix_bot.extremum_uniqueI by blast
  with 3 show ?case
    using extends_not_Atom_mem_subfms_last unfolding P_def by blast
qed simp

lemma card_not_Atoms_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card {\<phi> \<in> set b. \<not> is_literal \<phi>} \<le> 2 * card (subfms (last b))"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have [simp]: "last b = \<phi>"
    by simp
  have "{\<psi> \<in> set b. \<not> is_literal \<psi>} \<subseteq> subfms \<phi> \<union> Neg ` subfms \<phi>"
    using extendss_not_Atom_mem_subfms_last[OF \<open>extendss b [\<phi>]\<close>]
    by auto
  from card_mono[OF _ this] have
    "card {\<psi> \<in> set b. \<not> is_literal \<psi>} \<le> card (subfms \<phi> \<union> Neg ` subfms \<phi>)"
    using finite_subfms finite_imageI by fast
  also have "\<dots> \<le> card (subfms \<phi>) + card (Neg ` subfms \<phi>)"
    using card_Un_le by blast
  also have "\<dots> \<le> 2 * card (subfms \<phi>)"
    unfolding mult_2 by (simp add: card_image_le finite_subfms)
  finally show ?thesis
    by simp
qed

lemma card_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card (set b)
      \<le> 2 * card (subfms (last b)) + 16 * (card (subterms_fm (last b)))^4"
proof -
  let ?csts = "card (subterms_fm (last b))"
  have "set b = {\<psi> \<in> set b. \<not> is_literal \<psi>} \<union> {\<psi> \<in> set b. is_literal \<psi>}"
    by auto
  then have "card (set b)
    = card ({\<psi> \<in> set b. \<not> is_literal \<psi>}) + card ({\<psi> \<in> set b. is_literal \<psi>})"
    using card_Un_disjoint finite_Un
    by (metis (no_types, lifting) List.finite_set disjoint_iff mem_Collect_eq)
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 4 * (?csts + card (params b))^2"
    using assms card_Atoms_branch_if_wf_branch card_not_Atoms_branch_if_wf_branch
    by fastforce
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 4 * (?csts + ?csts^2)^2"
    using assms card_params_ub_if_wf_branch by auto
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 16 * ?csts^4"
  proof -
    have "1 \<le> ?csts"
      using finite_subterms_fm[THEN card_0_eq] subterms_fm_nonempty
      by (auto intro: Suc_leI)
    then have "(?csts + ?csts^2)^2 = ?csts^2 + 2 * ?csts^3 + ?csts^4"
      by algebra
    also have "\<dots> \<le> ?csts^2 + 2 * ?csts^4 + ?csts^4"
      using power_increasing[OF _ \<open>1 \<le> ?csts\<close>] by simp
    also have "\<dots> \<le> ?csts^4 + 2 * ?csts^4 + ?csts^4"
      using power_increasing[OF _ \<open>1 \<le> ?csts\<close>] by simp
    also have "\<dots> \<le> 4 * ?csts^4"
      by simp
    finally show ?thesis
      by simp
  qed
  finally show ?thesis .
qed


function (domintros) mlss_proc_branch where
  "\<not> lin_sat b
  \<Longrightarrow> mlss_proc_branch b = mlss_proc_branch ((SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)) @ b)"
| "\<lbrakk> \<not> sat b; bopen b; lin_sat b \<rbrakk>
  \<Longrightarrow> mlss_proc_branch b = list_all (\<lambda>b'. mlss_proc_branch (b' @ b)) (SOME bs. extends bs b)"
| "\<lbrakk> lin_sat b; sat b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = bclosed b"
| "\<lbrakk> lin_sat b; bclosed b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = True"
  by auto

lemma mlss_proc_branch_dom_if_wf_branch:
  assumes "wf_branch (b::'a branch)"
  shows "mlss_proc_branch_dom b"
proof -
  define card_ub where
    "card_ub \<equiv> \<lambda>b::'a branch. 2 * card (subfms (last b)) + 16 * (card (subterms_fm (last b)))^4"
  from assms show ?thesis
  proof(induction "card_ub b - card (set b)"
      arbitrary: b rule: less_induct)
    case less
    have less': "mlss_proc_branch_dom b'" if "set b \<subset> set b'" "extendss b' b" for b'
    proof -
      note extendss_last_eq[OF \<open>extendss b' b\<close> wf_branch_not_Nil[OF \<open>wf_branch b\<close>]] 
      then have "card_ub b' = card_ub b"
        unfolding card_ub_def by simp
      moreover from that \<open>wf_branch b\<close> have "wf_branch b'"
        by (meson extendss_trans wf_branch_def)
      ultimately have "mlss_proc_branch_dom b'" if "card (set b') > card (set b)"
        using less(1)[OF _ \<open>wf_branch b'\<close>] card_branch_if_wf_branch that
        by (metis (no_types, lifting) card_ub_def diff_less_mono2 order_less_le_trans)
      with that show ?thesis
        by (simp add: psubset_card_mono)
    qed
    then show ?case
    proof(cases "sat b")
      case False
      then consider
        b' where  "\<not> lin_sat b" "lextends b' b" "set b \<subset> set (b' @ b)"|
        bs' where "lin_sat b" "\<not> sat b" "extends bs' b" "bs' \<noteq> []"
                  "\<forall>b' \<in> set bs'. set b \<subset> set (b' @ b)"
        unfolding sat_def lin_sat_def
        using extends_strict_mono extends_not_Nil
        by (metis (no_types, opaque_lifting) inf_sup_aci(5) psubsetI set_append sup_ge1)
      then show ?thesis
      proof(cases)
        case 1
        then have "\<exists>b'. lextends b' b \<and> set b \<subset> set b' \<union> set b"
          by auto
        from someI_ex[OF this] 1 show ?thesis 
          using less' mlss_proc_branch.domintros(1)
          by (metis (mono_tags, lifting) extendss.intros(1,2) set_append)
      next
        case 2
        then show ?thesis
          using less' mlss_proc_branch.domintros(2,4)
          by (metis (mono_tags, lifting) extends_strict_mono extendss.intros(1,3) someI_ex)
      qed
    qed (use mlss_proc_branch.domintros sat_def in metis)
  qed
qed

definition "mlss_proc \<phi> \<equiv> mlss_proc_branch [\<phi>]"

lemma not_lin_satD: "\<not> lin_sat b \<Longrightarrow> \<exists>b'. lextends b' b \<and> set b \<subset> set (b' @ b)"
  unfolding lin_sat_def by auto

lemma not_satD_if_lin_sat: "\<not> sat b \<Longrightarrow> lin_sat b \<Longrightarrow> \<exists>bs'. extends bs' b"
  unfolding sat_def by blast

lemma not_satD: "\<not> sat b \<Longrightarrow> \<exists>b'. extendss b' b \<and> set b \<subset> set b'"
  using not_lin_satD extends_strict_mono
  by (metis extends_not_Nil extendss.simps last_in_set sat_def)

lemma closeable_if_mlss_proc_branch:
  assumes "wf_branch b"
  assumes "mlss_proc_branch b"
  shows "closeable b"
  using assms(1)[THEN mlss_proc_branch_dom_if_wf_branch] assms(2)
proof(induction b rule: mlss_proc_branch.pinduct)
  case (1 b)
  then show ?case
    using not_lin_satD[THEN someI_ex] closeable.intros(2)
    by (force simp: mlss_proc_branch.psimps)
next
  case (2 b)
  then have "\<exists>bs'. extends bs' b"
    unfolding sat_def by blast
  from 2 this[THEN someI_ex] show ?case
    by (simp add: mlss_proc_branch.psimps)
       (metis (mono_tags, lifting) Ball_set closeable.intros(3))
qed (use closeable.intros mlss_proc_branch.psimps in \<open>force+\<close>)

inductive lextendss where
  "lextendss b b"
| "lextends b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> lextendss b2 b1 \<Longrightarrow> lextendss (b3 @ b2) b1"

lemma lextendss_trans: "lextendss b3 b2 \<Longrightarrow> lextendss b2 b1 \<Longrightarrow> lextendss b3 b1"
  apply(induction rule: lextendss.induct)
   apply(auto simp: lextendss.intros)
  done

lemma lextendss_suffix:
  "lextendss b' b \<Longrightarrow> suffix b b'"
  apply(induction rule: lextendss.induct)
  apply(auto simp: suffix_append)
  done

lemmas lextendss_mono = set_mono_suffix[OF lextendss_suffix]

lemma lextendss_strict_mono_if_neq: "lextendss b' b \<Longrightarrow> b' \<noteq> b \<Longrightarrow> set b \<subset> set b'"
  apply(induction rule: lextendss.induct)
   apply(auto)
  done

lemma lextendss_last_eq:
  "lextendss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  using lextendss_suffix
  unfolding suffix_def by fastforce

lemma extendss_if_lextendss:
  "lextendss b' b \<Longrightarrow> extendss b' b"
  apply (induction rule: lextendss.induct)
  using extendss.intros(1,2) extendss_trans by blast+
 
lemma wf_branch_lextendss:
  "wf_branch b \<Longrightarrow> lextendss b' b \<Longrightarrow> wf_branch b'"
  by (meson extendss_if_lextendss extendss_trans wf_branch_def)

lemma wf_branch_extendss: "wf_branch b \<Longrightarrow> extendss b' b \<Longrightarrow> wf_branch b'"
  using extendss_trans wf_branch_def by blast

lemma lextendss_to_lin_sat:
  assumes "wf_branch b"
  shows "\<exists>b'. lextendss b' b \<and> lin_sat b' \<and> mlss_proc_branch b' = mlss_proc_branch b"
  using mlss_proc_branch_dom_if_wf_branch[OF assms] assms
proof(induction rule: mlss_proc_branch.pinduct)
  case (1 b)
  let ?b' = "SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)"
  from 1 not_lin_satD have b':
    "lextends ?b' b" "set b \<subset> set (?b' @ b)" "mlss_proc_branch (?b' @ b) = mlss_proc_branch b"
    using mlss_proc_branch.psimps(1)
    by (metis (mono_tags, lifting) someI2_ex)+
  with 1 show ?case
    using lextendss.intros lextendss_trans wf_branch_lextendss by blast
qed (use lextendss.intros(1) in \<open>blast+\<close>)

lemma lextends_if_eq_last_and_set:
  assumes "lextends b' b1"
  assumes "last b1 = last b2" "set b1 \<subseteq> set b2"
  shows "lextends b' b2"
  using assms
proof(induction rule: lextends.induct)
  case (1 b' b)
  then show ?case
    apply (induction rule: lextends_fm.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_fm.intros)+
    done
next
  case (2 b' b)
  then show ?case
    apply (induction rule: lextends_un.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_un.intros)+
    done
next
  case (3 b' b)
  then show ?case
    apply (induction rule: lextends_int.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_int.intros)+
    done
next
  case (4 b' b)
  then show ?case
     apply (induction rule: lextends_diff.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_diff.intros)+
    done
next
  case (5 b' b)
  then show ?case
     apply (induction rule: lextends_single.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_single.intros)+
    done
next
  case (6 b' b)
  then show ?case
     apply (induction rule: lextends_eq.induct)
         apply (auto simp: lextends.simps)
       apply (meson in_mono lextends_eq.intros)+
    done
qed

lemma extends_noparam_if_eq_last_and_set:
  assumes "extends_noparam b' b1"
  assumes "last b1 = last b2" "set b1 = set b2"
  shows "extends_noparam b' b2"
  using assms
  apply(induction rule: extends_noparam.induct)
  using extends_noparam.intros by fastforce+

lemma extends_param_if_eq_last_and_set:
  assumes "extends_param t1 t2 x b' b1"
  assumes "last b1 = last b2" "set b1 = set b2"
  shows "extends_param t1 t2 x b' b2"
  using assms
  apply(induction rule: extends_param.induct)
  using extends_param.intros by (metis vars_branch_def)

lemma extends_if_eq_last_and_set:
  assumes "extends b' b1"
  assumes "last b1 = last b2" "set b1 = set b2"
  shows "extends b' b2"
  using assms
  apply(induction rule: extends.induct)
  using extends_noparam_if_eq_last_and_set extends_param_if_eq_last_and_set extends.intros
  by metis+

lemma lextendss_if_eq_last_and_set:
  assumes "lextendss (b' @ ba) ba"
  assumes "last ba = last bb" "set ba = set bb"
  shows "lextendss (b' @ bb) bb"
  using assms
proof(induction "b' @ ba" ba arbitrary: b' bb rule: lextendss.induct)
  case 1
  then show ?case
    by (simp add: lextendss.intros(1))
next
  case (2 b3 b2 b1)
  then have "suffix b2 (b' @ b1)"
    by (metis suffixI)
  then obtain b'1 b'2 where b': "b' = b3 @ b'2 @ b'1" "b2 = b'1 @ b1"
    by (metis "2.hyps"(3,5) append_eq_append_conv2 append_same_eq lextendss_suffix suffix_def)
  with 2 have "lextendss (b'1 @ bb) bb"
    by blast
  moreover from b' 2 have "lextendss (b'2 @ b'1 @ bb) (b'1 @ bb)"
    by (metis append_assoc lextendss.simps same_append_eq self_append_conv2)
  moreover
  from b' 2 have "last b2 = last (b'2 @ b'1 @ bb)" "set b2 \<subseteq> set (b'2 @ b'1 @ bb)"
    by (auto simp: last_append)
  note lextends_if_eq_last_and_set[OF \<open>lextends b3 b2\<close> this]
  with 2 b' have "lextendss (b3 @ b'2 @ b'1 @ bb) (b'2 @ b'1 @ bb)"
    by (simp add: lextendss.intros)
  ultimately show ?case
    using b' by (metis append_assoc lextendss_trans)
qed

lemma lextendss_set_subs_set_lin_sat:
  assumes "lextendss ba' ba" "lextendss bb' bb"
  assumes "set ba = set bb" "last ba = last bb" "ba \<noteq> []"
  assumes "lin_sat bb'"
  shows "set ba' \<subseteq> set bb'"
  using assms
proof(induction ba' ba rule: lextendss.induct)
  case (1 b)
  then show ?case using lextendss_mono by blast
next
  case (2 b3 b2 b1)
  then show ?case
    using lextends_if_eq_last_and_set lextendss_last_eq
    by (metis le_sup_iff lin_sat_def set_append set_empty2)
qed

lemma lextendss_lin_sat_set_eq:
  assumes "lextendss ba' ba" "lextendss bb' bb"
  assumes "set ba = set bb" "last ba = last bb" "ba \<noteq> []"
  assumes "lin_sat ba'" "lin_sat bb'"
  shows "set ba' = set bb'"
  using assms lextendss_set_subs_set_lin_sat
  by (metis order_antisym_conv set_empty2)


lemma not_lin_sat_if_lextendss: "lextendss b' b \<Longrightarrow> b' \<noteq> b \<Longrightarrow> \<not> lin_sat b"
  apply(induction rule: lextendss.induct)
   apply(auto dest: lin_satD)
  done

lemma wf_branch_lextends:
  "wf_branch b \<Longrightarrow> lextends b' b \<Longrightarrow> set b \<subset> set (b' @ b) \<Longrightarrow> wf_branch (b' @ b)"
  by (metis extendss.simps wf_branch_extendss)

lemma elts_vdiff[simp]: "elts (vdiff t1 t2) = elts t1 - elts t2"
  unfolding vdiff_def by auto

lemma lextends_interp:
  assumes "lextends b' b"
  assumes "\<psi> \<in> set b'"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof(induction rule: lextends.induct)
  case (1 b' b)
  then show ?case
    apply(induction rule: lextends_fm.induct)
       apply (metis empty_iff empty_set interp.simps(2,3,4) set_ConsD)+
    done
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lextends_un.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  qed (force)+
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by (force)
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by (force)
  qed (force)+
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by (force)
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by (force)
  qed (force)+
next
  case (5 b' b)
  then show ?case
    by (induction rule: lextends_single.induct) (force)+
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lextends_eq.induct)
    case (1 t1 t2 branch l)
     with this(1,2)[THEN this(5)] show ?case
      by (cases l) (auto)
  next
    case (2 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) (auto)
  next
    case (3 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) (auto)
  next
    case (4 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) (auto)
  next
    case (5 s t branch s')
    with this(1,2)[THEN this(4)] show ?case by (force)
  qed
qed

lemma extends_noparam_interp:
  assumes "extends_noparam bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>b' \<in> set bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
  by (induction rule: extends_noparam.induct) (force)+

lemma I\<^sub>s\<^sub>t_upd_eq_if_not_mem_set_pset_term:
  assumes "x \<notin> set_pset_term t"
  shows "I\<^sub>s\<^sub>t (M(x := y)) t = I\<^sub>s\<^sub>t M t"
  using assms by (induction t) auto

lemma I\<^sub>s\<^sub>a_upd_eq_if_not_mem_set_pset_atom:
  assumes "x \<notin> set_pset_atom a"
  shows "I\<^sub>s\<^sub>a (M(x := y)) a = I\<^sub>s\<^sub>a M a"
  using assms
  by (cases a) (auto simp: I\<^sub>s\<^sub>t_upd_eq_if_not_mem_set_pset_term)

lemma interp_upd_eq_if_not_mem_vars_fm:
  assumes "x \<notin> vars_fm \<phi>"
  shows "interp I\<^sub>s\<^sub>a (M(x := y)) \<phi> = interp I\<^sub>s\<^sub>a M \<phi>"
  using assms
  by (induction \<phi>) (auto simp: I\<^sub>s\<^sub>a_upd_eq_if_not_mem_set_pset_atom)

lemma extends_param_interp:
  assumes "extends_param t1 t2 x bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> set bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof (induction rule: extends_param.induct)
  let ?bs'="[[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
             [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]]"
  case (1 b)
  with this(1)[THEN this(7)] have "I\<^sub>s\<^sub>t M t1 \<noteq> I\<^sub>s\<^sub>t M t2"
    by (auto)
  then obtain y where y:
    "y \<in> elts (I\<^sub>s\<^sub>t M t1) \<and> y \<notin> elts (I\<^sub>s\<^sub>t M t2) \<or>
     y \<in> elts (I\<^sub>s\<^sub>t M t2) \<and> y \<notin> elts (I\<^sub>s\<^sub>t M t1)"
    by (metis V_equalityI)
  have "x \<notin> set_pset_term t1" "x \<notin> set_pset_term t2"
    using 1 by (auto simp: vars_fm_vars_branchI)
  then have "I\<^sub>s\<^sub>t (M(x := y)) t1 = I\<^sub>s\<^sub>t M t1" "I\<^sub>s\<^sub>t (M(x := y)) t2 = I\<^sub>s\<^sub>t M t2"
    using I\<^sub>s\<^sub>t_upd_eq_if_not_mem_set_pset_term by metis+
  then have "\<exists>b' \<in> set ?bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using 1 y by auto
  moreover have "\<forall>\<psi> \<in> set b. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using "1"(7) \<open>x \<notin> vars_branch b\<close> interp_upd_eq_if_not_mem_vars_fm
    by (metis vars_fm_vars_branchI)
  ultimately show ?case
    by auto (metis fun_upd_same)+
qed

lemma extends_interp:
  assumes "extends bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> set bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof(induction rule: extends.induct)
  case (1 bs' b)
  with extends_noparam_interp[OF this(1)] have "\<exists>b' \<in> set bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
    by blast
  with 1 show ?case
    by auto
next
  case (2 t1 t2 x bs b)
  then show ?case using extends_param_interp by metis
qed

lemma extendss_to_bopen_and_sat_if_not_closeable:
  assumes "\<not> closeable b" "wf_branch b"
  shows "\<exists>b'. extendss b' b \<and> bopen b' \<and> sat b'"
  using mlss_proc_branch_dom_if_wf_branch[OF assms(2)] assms
proof(induction rule: mlss_proc_branch.pinduct)
  case (1 b)
  from not_lin_satD[OF \<open>\<not> lin_sat b\<close>] obtain b' where b':
    "(SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)) = b'"
    "lextends b' b" "set b \<subset> set (b' @ b)"
    by (metis (mono_tags, lifting) some_eq_imp)
    
  from \<open>\<not> closeable b\<close> b' have "\<not> closeable (b' @ b)"
    using closeable.intros(2) by blast
  moreover have "wf_branch (b' @ b)"
    using \<open>wf_branch b\<close> b' wf_branch_lextends by blast
  ultimately obtain b'' where b'':
    "extendss b'' (b' @ b)" "bopen b''" "sat b''"
    using 1 b' by blast
  with b' have "extendss b'' b"
    using extendss.intros(1) extendss.intros(2) extendss_trans by blast
  with b'' show ?case by blast
next
  case (2 b)
  from \<open>\<not> sat b\<close> \<open>lin_sat b\<close> obtain bs' where bs':
    "(SOME bs'. extends bs' b) = bs'" "extends bs' b"
    by (meson sat_def someI)

  from \<open>\<not> closeable b\<close> \<open>lin_sat b\<close> bs' obtain b' where b':
    "b' \<in> set bs'" "\<not> closeable (b' @ b)"
    using closeable.intros(3) by blast
  moreover have "wf_branch (b' @ b)"
    using \<open>wf_branch b\<close> b' bs' wf_branch_extendss by (metis extendss.simps)
  ultimately obtain b'' where b'':
    "extendss b'' (b' @ b)" "bopen b''" "sat b''"
    using 2 bs' by blast
  with bs' b' have "extendss b'' b"
    using extendss.intros(1) extendss.intros(3) extendss_trans by blast
  with b'' show ?case
    by blast
qed (use closeable.intros(1) extendss.intros(1) in \<open>blast+\<close>)

lemma (in open_branch) I\<^sub>s\<^sub>t_realization_eq_realization:
  assumes "sat b" "t \<in> subterms_branch b"
  shows "I\<^sub>s\<^sub>t (\<lambda>x. realization (Var x)) t = realization t"
  using assms
  by (induction t) (force simp: realization_simps dest: subterms_branchD)+

lemma interp_if_not_closeable:
  assumes "\<not> closeable [\<phi>]" "infinite (UNIV :: 'a set)"
  shows "\<exists>M :: 'a \<Rightarrow> V. interp I\<^sub>s\<^sub>a M \<phi>"
proof -
  from assms obtain b' where b': "extendss b' [\<phi>]" "bopen b'" "sat b'"
    using extendss_to_bopen_and_sat_if_not_closeable extendss.intros(1)
    unfolding wf_branch_def by blast
  interpret open_branch b'
    apply(unfold_locales)
    using assms b' wf_branch_def by blast+
  define M where "M \<equiv> (\<lambda>x. realization (Var x))"
  have "interp I\<^sub>s\<^sub>a M \<phi>" if "\<phi> \<in> set b'" for \<phi>
    using that
  proof(induction "size \<phi>" arbitrary: \<phi> rule: less_induct)
    case less
    then show ?case
    proof(cases \<phi>)
      case (Atom a)
      then show ?thesis
      proof(cases a)
        case (Elem s t)
        with Atom less have "s \<in> subterms_branch b'" "t \<in> subterms_branch b'"
          using subterms_branchI_if_AT_mem by blast+
        with Atom Elem less show ?thesis
          unfolding M_def
          using I\<^sub>s\<^sub>t_realization_eq_realization[OF \<open>sat b'\<close>] realization_if_AT_mem by auto
      next
        case (Equal s t)
        with Atom less have "s \<in> subterms_branch b'" "t \<in> subterms_branch b'"
          using subterms_branchI_if_AT_eq by blast+
        with Atom Equal less satD(1)[OF \<open>sat b'\<close>] show ?thesis
          unfolding M_def
          using I\<^sub>s\<^sub>t_realization_eq_realization[OF \<open>sat b'\<close>] realization_if_AT_eq by auto
      qed
    next
      case (And \<phi>1 \<phi>2)
      with \<open>\<phi> \<in> set b'\<close> \<open>sat b'\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b'" "\<phi>2 \<in> set b'"
        using lextends_fm.intros(1)[THEN lextends.intros(1)] by fastforce+
      with And less show ?thesis by simp
    next
      case (Or \<phi>1 \<phi>2)
      with \<open>\<phi> \<in> set b'\<close> \<open>sat b'\<close>[THEN satD(2)] have "\<phi>1 \<in> set b' \<or> Neg \<phi>1 \<in> set b'"
        using extends_noparam.intros(1)[THEN extends.intros(1)]
        by blast
      with less Or \<open>sat b'\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b' \<or> \<phi>2 \<in> set b'"
        using lextends_fm.intros(3)[THEN lextends.intros(1)] by fastforce
      with Or less show ?thesis
        by force
    next
      case (Neg \<phi>')
      show ?thesis
      proof(cases \<phi>')
        case (Atom a)
        then show ?thesis
        proof(cases a)
          case (Elem s t)
          with Atom Neg less have "s \<in> subterms_branch b'" "t \<in> subterms_branch b'"
            using subterms_branchI_if_AF_mem by blast+
          with Neg Atom Elem less show ?thesis
            unfolding M_def
            using I\<^sub>s\<^sub>t_realization_eq_realization realization_if_AF_mem \<open>sat b'\<close> by auto
        next
          case (Equal s t)
          with Atom Neg less have "s \<in> subterms_branch b'" "t \<in> subterms_branch b'"
            using subterms_branchI_if_AF_eq by blast+
          with Neg Atom Equal less show ?thesis
            unfolding M_def
            using I\<^sub>s\<^sub>t_realization_eq_realization realization_if_AF_eq \<open>sat b'\<close> by auto
        qed
      next
        case (And \<phi>1 \<phi>2)
        with Neg \<open>sat b'\<close>[THEN satD(2)] less have "\<phi>1 \<in> set b' \<or> Neg \<phi>1 \<in> set b'"
          using extends_noparam.intros(2)[THEN extends.intros(1)] by blast
        with \<open>sat b'\<close>[THEN satD(1), THEN lin_satD] Neg And less
        have "Neg \<phi>2 \<in> set b' \<or> Neg \<phi>1 \<in> set b'"
          using lextends_fm.intros(5)[THEN lextends.intros(1)] by fastforce
        with Neg And less show ?thesis by force
      next
        case (Or \<phi>1 \<phi>2)
        with \<open>\<phi> \<in> set b'\<close> Neg \<open>sat b'\<close>[THEN satD(1), THEN lin_satD]
        have "Neg \<phi>1 \<in> set b'" "Neg \<phi>2 \<in> set b'"
          using lextends_fm.intros(2)[THEN lextends.intros(1)] by fastforce+
        moreover have "size (Neg \<phi>1) < size \<phi>" "size (Neg \<phi>2) < size \<phi>"
          using Neg Or by simp_all
        ultimately show ?thesis using Neg Or less by force
      next
        case Neg': (Neg \<phi>'')
        with \<open>\<phi> \<in> set b'\<close> Neg \<open>sat b'\<close>[THEN satD(1), THEN lin_satD] have "\<phi>'' \<in> set b'"
          using lextends_fm.intros(7)[THEN lextends.intros(1)] by fastforce+
        with Neg Neg' less show ?thesis by simp
      qed
    qed
  qed
  with b' show ?thesis
    by (meson extendss_mono list.set_intros(1) subset_eq)
qed

inductive extendss_branches where
  "extendss_branches {b} b"
| "extendss_branches bs2 b1 \<Longrightarrow> b2 \<in> bs2 \<Longrightarrow> lextends b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2)
    \<Longrightarrow> extendss_branches ({b3 @ b2} \<union> (bs2 - {b2})) b1"
| "extendss_branches bs2 b1 \<Longrightarrow> b2 \<in> bs2 \<Longrightarrow> extends b2s b2
    \<Longrightarrow> extendss_branches ((\<lambda>b. b @ b2) ` set b2s \<union> (bs2 - {b2})) b1"

lemma extendss_if_extendss_branches:
  assumes "extendss_branches bs' b"
  assumes "b' \<in> bs'"
  shows "extendss b' b"
  using assms
  apply(induction arbitrary: b' rule: extendss_branches.induct)
  using extendss.intros by fastforce+

lemma
  assumes "extendss_branches bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> bs'. \<forall>\<phi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<phi>"
  using assms
proof(induction arbitrary: M rule: extendss_branches.induct)
  case (2 bs2 b1 b2 b3)
  then obtain M' :: "'a \<Rightarrow> V" and b' where b': "b' \<in> bs2" "\<forall>\<phi> \<in> set b'. interp I\<^sub>s\<^sub>a M' \<phi>"
    by blast
  with 2 show ?case
  proof(cases "b' = b2")
    case True
    with b' have "interp I\<^sub>s\<^sub>a M' \<phi>" if "\<phi> \<in> set b3" for \<phi>
      using that lextends_interp[OF \<open>lextends b3 b2\<close>] by simp
    with True b' show ?thesis
      by auto
  next
    case False
    with 2 b' show ?thesis by blast
  qed
next
  case (3 bs2 b1 b2 b2s)
  then obtain M' :: "'a \<Rightarrow> V" and b' where b': "b' \<in> bs2" "\<forall>\<phi> \<in> set b'. interp I\<^sub>s\<^sub>a M' \<phi>"
    by blast
  then show ?case
  proof(cases "b' = b2")
    case True
    with b' obtain M'' b2' where "b2' \<in> set b2s" "\<forall>\<phi> \<in> set (b2' @ b2). interp I\<^sub>s\<^sub>a M'' \<phi>"
      using extends_interp[OF \<open>extends b2s b2\<close>] by blast
    with True b' show ?thesis
      by (metis UnCI image_eqI)
  next
    case False
    with 3 b' show ?thesis by blast
  qed
qed blast

lemma
  assumes "closeable b"
  shows "\<exists>bs'. extendss_branches bs' b \<and> (\<forall>b' \<in> bs'. bclosed b')"
  using assms
proof(induction rule: closeable.induct)
  case (1 b)
  then show ?case
    using extendss_branches.intros(1) by blast
next
  case (2 b' b)
  then obtain bs'' where bs'': "extendss_branches bs'' (b' @ b)" "\<forall>b' \<in> bs''. bclosed b'"
    by blast
  from this(1) have "extendss_branches bs'' b"
    using \<open>lextends b' b\<close> \<open>set b \<subset> set (b' @ b)\<close>
  proof(induction "bs''" "b' @ b" arbitrary: b' b rule: extendss_branches.induct)
    case (2 bs2 b2 b3)
    then show ?case using extendss_branches.intros(2) by metis
  next
    case (3 bs2 b2 b2s)
    then show ?case using extendss_branches.intros(3) by metis
  qed (use extendss_branches.intros in fastforce)
  with bs'' show ?case by blast
next
  case (3 bs b)
  then have *: "\<exists>bs'. extendss_branches bs' (b' @ b) \<and> (\<forall>b' \<in> bs'. bclosed b')"
    if "b' \<in> set bs" for b'
    using that by blast

  then show ?case sorry
qed

lemma
  assumes "closeable b" "b \<noteq> []"
  shows "\<not> interp I\<^sub>s\<^sub>a M (last b)"
  using assms
proof(induction rule: closeable.induct)
  case (1 b)
  then show ?case sorry
next
  case (2 b' b)
  then show ?case by simp
next
  case (3 bs b)
  then show ?case
    by (auto simp: extends_not_Nil)
qed

abbreviation subst_vars_term :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a pset_term \<Rightarrow> 'a pset_term"
  where "subst_vars_term \<sigma> \<equiv> map_pset_term \<sigma>"

abbreviation subst_vars_atom :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a pset_atom \<Rightarrow> 'a pset_atom"
  where "subst_vars_atom \<sigma> \<equiv> map_pset_atom \<sigma>"

definition "subst_vars_literal \<sigma> l \<equiv> (case l of (p, a) \<Rightarrow> (p, subst_vars_atom \<sigma> a))"

abbreviation "subst_vars_fm \<sigma> \<equiv> map_fm (subst_vars_literal \<sigma>)"

abbreviation "subst_vars_branch \<sigma> b \<equiv> map (subst_vars_fm \<sigma>) b"

lemma subst_vars_literal_apply[simp]:
  "subst_vars_literal \<sigma> (p, a) = (p, subst_vars_atom \<sigma> a)"
  unfolding subst_vars_literal_def by force

lemma mem_subterms_map_pset_term:
  "t \<in> subterms s \<Longrightarrow> map_pset_term f t \<in> subterms (map_pset_term f s)"
  by (induction s) auto

lemma mem_subterms_subst_vars_literal:
  "t \<in> subterms_atom l
  \<Longrightarrow> subst_vars_term \<sigma> t \<in> subterms_atom (subst_vars_literal \<sigma> l)"
  by (cases l rule: subterms_atom.cases) (auto simp: mem_subterms_map_pset_term)

lemma mem_subterms_subst_vars_fm:
  "t \<in> subterms_fm \<phi>
  \<Longrightarrow> subst_vars_term \<sigma> t \<in> subterms_fm (subst_vars_fm \<sigma> \<phi>)"
  apply(induction \<phi>)
  using mem_subterms_subst_vars_literal by fastforce+

lemma subst_vars_term_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_term \<sigma> t1 = subst_vars_term \<sigma> t2 \<longleftrightarrow> t1 = t2"
  by (metis assms permutation_inverse_works(1) pset_term.map_comp pset_term.map_id)

lemma subst_vars_atom_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_atom \<sigma> a1 = subst_vars_atom \<sigma> a2 \<longleftrightarrow> a1 = a2"
  by (metis assms id_def permutation_inverse_works(1) pset_atom.map_comp pset_atom.map_id0)

lemma subst_vars_literal_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_literal \<sigma> l1 = subst_vars_literal \<sigma> l2 \<longleftrightarrow> l1 = l2"
  by (cases l1; cases l2) (auto simp: assms subst_vars_atom_eq_iff_if_permutation)

lemma subst_vars_fm_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_fm \<sigma> p = subst_vars_fm \<sigma> q \<longleftrightarrow> p = q"
  by (metis assms fm.inj_map_strong subst_vars_literal_eq_iff_if_permutation)

lemma subst_vars_literal_subst_tlvl:
  assumes "permutation \<sigma>"
  shows "subst_vars_literal \<sigma> (subst_tlvl t1 t2 l)
    = subst_tlvl (subst_vars_term \<sigma> t1) (subst_vars_term \<sigma> t2) (subst_vars_literal \<sigma> l)"
  using assms
  apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
   apply(auto simp: subst_vars_term_eq_iff_if_permutation)
  done

lemma tlvl_terms_atom_subst_var_literal[simp]:
  "tlvl_terms_atom (subst_vars_literal \<sigma> l) = subst_vars_term \<sigma> ` tlvl_terms_atom l"
  by (cases l rule: tlvl_terms_atom.cases) auto

lemma lextends_subst_vars_branch:
  assumes "lextends b' b" "b \<noteq> []"
  assumes "permutation \<sigma>"
  shows "lextends (subst_vars_branch \<sigma> b') (subst_vars_branch \<sigma> b)"
  using assms
proof(induction rule: lextends.induct)
  case (1 b' b)
  then show ?case
  proof(induction rule: lextends_fm.induct)
    case (3 p q branch)
    note lextends = lextends_fm.intros(3)[THEN lextends.intros(1), of "subst_vars_fm \<sigma> p"]
    from 3 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (4 p q branch)
    note lextends =
      lextends_fm.intros(4)[THEN lextends.intros(1), of _ "subst_vars_fm \<sigma> q"]
    from 4 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (5 p q branch)
    note lextends = lextends_fm.intros(5)[THEN lextends.intros(1), of "subst_vars_fm \<sigma> p"]
    from 5 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (6 p q branch)
    note lextends = lextends_fm.intros(6)[THEN lextends.intros(1), of _ "subst_vars_fm \<sigma> q"]
    from 6 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  qed (auto simp: rev_image_eqI intro!: lextends_fm.intros(1,2)[THEN lextends.intros(1)])
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lextends_un.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(1)[THEN lextends.intros(2)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(2)[THEN lextends.intros(2)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(3)[THEN lextends.intros(2)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_un.intros(4)[THEN lextends.intros(2), of _ "subst_vars_term \<sigma> t1"]
    from 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_un.intros(5)[THEN lextends.intros(2), of _ _ "subst_vars_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case 6
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(6)[THEN lextends.intros(2)]
               dest: mem_subterms_subst_vars_fm)
  qed
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(1)[THEN lextends.intros(3)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(2)[THEN lextends.intros(3)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(3)[THEN lextends.intros(3)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_int.intros(4)[THEN lextends.intros(3), of _ "subst_vars_term \<sigma> t1"]
    from 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_int.intros(5)[THEN lextends.intros(3), of _ _ "subst_vars_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (6 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(6)[THEN lextends.intros(3)]
               dest: mem_subterms_subst_vars_fm)
  qed
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(1)[THEN lextends.intros(4)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(2)[THEN lextends.intros(4)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(3)[THEN lextends.intros(4)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_diff.intros(4)[THEN lextends.intros(4), of _ "subst_vars_term \<sigma> t1"]
    with 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_diff.intros(5)[THEN lextends.intros(4), of _ _ "subst_vars_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (6 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(6)[THEN lextends.intros(4)]
               dest: mem_subterms_subst_vars_fm)
  qed

next
  case (5 b' b)
  then show ?case
    by (induction rule: lextends_single.induct)
       (auto simp: rev_image_eqI last_map
             intro!: lextends_single.intros[THEN lextends.intros(5)]
             dest: mem_subterms_subst_vars_fm)
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lextends_eq.induct)
    case (1 t1 t2 branch l)
    then show ?case
      by (auto simp: rev_image_eqI subst_vars_literal_subst_tlvl
               intro!: lextends_eq.intros(1)[THEN lextends.intros(6)])
  next
    case (2 t1 t2 branch l)
    then show ?case
      by (auto simp: rev_image_eqI subst_vars_literal_subst_tlvl
               intro!: lextends_eq.intros(2)[THEN lextends.intros(6)])
  next
    case (3 s t branch s')
    note lextends = lextends_eq.intros(3)[THEN lextends.intros(6), of _ "subst_vars_term \<sigma> t"]
    from 3 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  qed
qed

fun subst_term :: "('a \<Rightarrow> 'b pset_term) \<Rightarrow> 'a pset_term \<Rightarrow> 'b pset_term" where
"subst_term \<sigma> \<emptyset> = \<emptyset>" |
"subst_term \<sigma> (Var x) = \<sigma> x" |
"subst_term \<sigma> (t1 \<squnion>\<^sub>s t2) = subst_term \<sigma> t1 \<squnion>\<^sub>s subst_term \<sigma> t2" |
"subst_term \<sigma> (t1 \<sqinter>\<^sub>s t2) = subst_term \<sigma> t1 \<sqinter>\<^sub>s subst_term \<sigma> t2" |
"subst_term \<sigma> (t1 -\<^sub>s t2) = subst_term \<sigma> t1 -\<^sub>s subst_term \<sigma> t2" |
"subst_term \<sigma> (Single t) = Single (subst_term \<sigma> t)"

fun subst_atom :: "('a \<Rightarrow> 'b pset_term) \<Rightarrow> 'a pset_atom \<Rightarrow> 'b pset_atom" where
"subst_atom \<sigma> (t1 \<in>\<^sub>s t2) = subst_term \<sigma> t1 \<in>\<^sub>s subst_term \<sigma> t2" |
"subst_atom \<sigma> (t1 \<approx>\<^sub>s t2) = subst_term \<sigma> t1 \<approx>\<^sub>s subst_term \<sigma> t2"

definition "subst_literal \<sigma> l = (case l of (p, a) \<Rightarrow> (p, subst_atom \<sigma> a))"

abbreviation "subst_fm \<sigma> \<equiv> map_fm (subst_literal \<sigma>)"

abbreviation "subst_branch \<sigma> \<equiv> map (subst_fm \<sigma>)"

lemma subst_literal_apply[simp]:
  "subst_literal \<sigma> (p, a) = (p, subst_atom \<sigma> a)"
  unfolding subst_literal_def by force

lemma subterms_subst_term:
  "s \<in> subterms t \<Longrightarrow> subst_term \<sigma> s \<in> subterms (subst_term \<sigma> t)"
  by (induction t) auto

lemma subterms_atom_subst_atom:
  "t \<in> subterms_atom (p, a) \<Longrightarrow> subst_term \<sigma> t \<in> subterms_atom (p, subst_atom \<sigma> a)"
  apply(cases a) using subterms_subst_term by auto

lemma subterms_atom_subst_literal:
  "t \<in> subterms_atom l \<Longrightarrow> subst_term \<sigma> t \<in> subterms_atom (subst_literal \<sigma> l)"
  apply(cases l) by (simp add: subterms_atom_subst_atom)

lemma subterms_fm_subst_fm:
  "t \<in> subterms_fm \<phi> \<Longrightarrow> subst_term \<sigma> t \<in> subterms_fm (subst_fm \<sigma> \<phi>)"
proof(induction \<phi>)
  case (Atom x)
  then show ?case by (simp add: subterms_atom_subst_literal)
qed auto

(*
lemma mem_subterms_map_pset_term:
  "t \<in> subterms s \<Longrightarrow> map_pset_term f t \<in> subterms (map_pset_term f s)"
  by (induction s) auto

lemma mem_subterms_subst_vars_literal:
  "t \<in> subterms_atom l
  \<Longrightarrow> subst_vars_term \<sigma> t \<in> subterms_atom (subst_vars_literal \<sigma> l)"
  by (cases l rule: subterms_atom.cases) (auto simp: mem_subterms_map_pset_term)

lemma mem_subterms_subst_vars_fm:
  "t \<in> subterms_fm \<phi>
  \<Longrightarrow> subst_vars_term \<sigma> t \<in> subterms_fm (subst_vars_fm \<sigma> \<phi>)"
  apply(induction \<phi>)
  using mem_subterms_subst_vars_literal by fastforce+

lemma subst_vars_term_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_term \<sigma> t1 = subst_vars_term \<sigma> t2 \<longleftrightarrow> t1 = t2"
  by (metis assms permutation_inverse_works(1) pset_term.map_comp pset_term.map_id)

lemma subst_vars_atom_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_atom \<sigma> a1 = subst_vars_atom \<sigma> a2 \<longleftrightarrow> a1 = a2"
  by (metis assms id_def permutation_inverse_works(1) pset_atom.map_comp pset_atom.map_id0)

lemma subst_vars_literal_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_literal \<sigma> l1 = subst_vars_literal \<sigma> l2 \<longleftrightarrow> l1 = l2"
  by (cases l1; cases l2) (auto simp: assms subst_vars_atom_eq_iff_if_permutation)

lemma subst_vars_fm_eq_iff_if_permutation:
  assumes "permutation \<sigma>"
  shows "subst_vars_fm \<sigma> p = subst_vars_fm \<sigma> q \<longleftrightarrow> p = q"
  by (metis assms fm.inj_map_strong subst_vars_literal_eq_iff_if_permutation)

lemma subst_vars_literal_subst_tlvl:
  assumes "permutation \<sigma>"
  shows "subst_vars_literal \<sigma> (subst_tlvl t1 t2 l)
    = subst_tlvl (subst_vars_term \<sigma> t1) (subst_vars_term \<sigma> t2) (subst_vars_literal \<sigma> l)"
  using assms
  apply(cases "(t1, t2, l)" rule: subst_tlvl.cases)
   apply(auto simp: subst_vars_term_eq_iff_if_permutation)
  done

lemma tlvl_terms_atom_subst_var_literal[simp]:
  "tlvl_terms_atom (subst_vars_literal \<sigma> l) = subst_vars_term \<sigma> ` tlvl_terms_atom l"
  by (cases l rule: tlvl_terms_atom.cases) auto
*)

lemma
  assumes "t1 \<in> tlvl_terms_atom l"
  shows "subst_literal \<sigma> (subst_tlvl t1 t2 l)
  = subst_tlvl (subst_term \<sigma> t1) (subst_term \<sigma> t2) (subst_literal \<sigma> l)"
  quickcheck [timeout=60]
proof(cases "(t1, t2, l)" rule: subst_tlvl.cases)
  case (1 t1 t2 b s1 s2)
  with assms show ?thesis
    apply(simp)
    apply(safe)
    apply(auto)
next
  case (2 t1 t2 b s1 s2)
  then show ?thesis sorry
qed

lemma lextends_subst_branch:
  assumes "lextends b' b" "b \<noteq> []"
  shows "lextends (subst_branch \<sigma> b') (subst_branch \<sigma> b)"
  using assms
proof(induction rule: lextends.induct)
  case (1 b' b)
  then show ?case
  proof(induction rule: lextends_fm.induct)
    case (3 p q branch)
    note lextends = lextends_fm.intros(3)[THEN lextends.intros(1), of "subst_fm \<sigma> p"]
    from 3 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (4 p q branch)
    note lextends =
      lextends_fm.intros(4)[THEN lextends.intros(1), of _ "subst_fm \<sigma> q"]
    from 4 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (5 p q branch)
    note lextends = lextends_fm.intros(5)[THEN lextends.intros(1), of "subst_fm \<sigma> p"]
    from 5 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  next
    case (6 p q branch)
    note lextends = lextends_fm.intros(6)[THEN lextends.intros(1), of _ "subst_fm \<sigma> q"]
    from 6 show ?case
      by (auto simp: rev_image_eqI simp del: id_apply fun_upd_apply intro!: lextends)     
  qed (auto simp: rev_image_eqI intro!: lextends_fm.intros(1,2)[THEN lextends.intros(1)])
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lextends_un.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(1)[THEN lextends.intros(2)])
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(2)[THEN lextends.intros(2)]
               dest: subterms_fm_subst_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(3)[THEN lextends.intros(2)]
               dest: subterms_fm_subst_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_un.intros(4)[THEN lextends.intros(2), of _ "subst_term \<sigma> t1"]
    from 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_un.intros(5)[THEN lextends.intros(2), of _ _ "subst_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case 6
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_un.intros(6)[THEN lextends.intros(2)]
               dest: subterms_fm_subst_fm)
  qed
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(1)[THEN lextends.intros(3)])
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(2)[THEN lextends.intros(3)]
               dest: subterms_fm_subst_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(3)[THEN lextends.intros(3)]
               dest: subterms_fm_subst_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_int.intros(4)[THEN lextends.intros(3), of _ "subst_term \<sigma> t1"]
    from 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_int.intros(5)[THEN lextends.intros(3), of _ _ "subst_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (6 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_int.intros(6)[THEN lextends.intros(3)]
               dest: subterms_fm_subst_fm)
  qed
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (1 s t1 t2 branch)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(1)[THEN lextends.intros(4)]
               dest: mem_subterms_subst_vars_fm)
  next
    case (2 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(2)[THEN lextends.intros(4)]
               dest: subterms_fm_subst_fm)
  next
    case (3 s t2 branch t1)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(3)[THEN lextends.intros(4)]
               dest: subterms_fm_subst_fm)
  next
    case (4 s t1 t2 branch)
    note lextends =
      lextends_diff.intros(4)[THEN lextends.intros(4), of _ "subst_term \<sigma> t1"]
    with 4 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (5 s t1 t2 branch)
    note lextends =
      lextends_diff.intros(5)[THEN lextends.intros(4), of _ _ "subst_term \<sigma> t2"]
    from 5 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  next
    case (6 s t1 branch t2)
    then show ?case
      by (auto simp: rev_image_eqI last_map
               intro!: lextends_diff.intros(6)[THEN lextends.intros(4)]
               dest: subterms_fm_subst_fm)
  qed
next
  case (5 b' b)
  then show ?case
    by (induction rule: lextends_single.induct)
       (auto simp: rev_image_eqI last_map
             intro!: lextends_single.intros[THEN lextends.intros(5)]
             dest: subterms_fm_subst_fm)
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lextends_eq.induct)
    case (1 t1 t2 branch l)
    then have "AT (subst_term \<sigma> t1 \<approx>\<^sub>s subst_term \<sigma> t2) \<in> set (subst_branch \<sigma> branch)"
      using image_iff by fastforce
    moreover from 1 have "Atom (subst_literal \<sigma> l) \<in> set (subst_branch \<sigma> branch)"
      using image_iff by fastforce
    moreover from 1 have "subst_term \<sigma> t1 \<in> tlvl_terms_atom (subst_literal \<sigma> l)"
      apply(cases l rule: tlvl_terms_atom.cases) by auto
    ultimately have "lextends [(Atom (subst_tlvl (subst_term \<sigma> t1) (subst_term \<sigma> t2) (subst_literal \<sigma> l)))] (subst_branch \<sigma> branch)"
      using lextends_eq.intros(1)[THEN lextends.intros(6)] by blast

      thm lextends_eq.intros(1)[THEN lextends.intros(6)]
      from 1 show ?case
      apply (auto simp: rev_image_eqI subst_vars_literal_subst_tlvl
               intro!: lextends_eq.intros(1)[THEN lextends.intros(6)])

      next
    case (2 t1 t2 branch l)
    then show ?case
      by (auto simp: rev_image_eqI subst_vars_literal_subst_tlvl
               intro!: lextends_eq.intros(2)[THEN lextends.intros(6)])
  next
    case (3 s t branch s')
    note lextends = lextends_eq.intros(3)[THEN lextends.intros(6), of _ "subst_vars_term \<sigma> t"]
    from 3 show ?case
      by (auto simp: rev_image_eqI intro!: lextends)
  qed
qed


lemma not_mem_subst_vars_branch:
  assumes "\<phi> \<notin> set b"
  assumes "permutation \<sigma>"
  shows "subst_vars_fm \<sigma> \<phi> \<notin> set (subst_vars_branch \<sigma> b)"
  using assms
  by (auto simp add: subst_vars_fm_eq_iff_if_permutation vars_branch_def)

lemma vars_fm_subst_vars_fm[simp]:
  "vars_fm (subst_vars_fm \<sigma> \<phi>) = \<sigma> ` vars_fm \<phi>"
proof(induction \<phi>)
  case (Atom x)
  then show ?case
    by (cases x rule: tlvl_terms_atom.cases)
       (auto simp: vars_fm_simps pset_atom.set_map pset_term.set_map)
qed (auto simp: vars_fm_simps)

lemma vars_branch_subst_vars_branch[simp]:
  "vars_branch (subst_vars_branch \<sigma> b) = \<sigma> ` vars_branch b"
  unfolding vars_branch_def by auto

lemma extends_noparam_subst_vars_branch:
  assumes "extends_noparam bs' b" "b \<noteq> []"
  assumes "permutation \<sigma>"
  shows "extends_noparam (map (subst_vars_branch \<sigma>) bs') (subst_vars_branch \<sigma> b)"
  using assms
proof(induction rule: extends_noparam.induct)
  case (1 p q branch)
  note extends = extends_noparam.intros(1)[of _ "subst_vars_fm \<sigma> q"]
  with 1 not_mem_subst_vars_branch show ?case
    by (fastforce simp: image_iff intro!: extends)
next
  case (2 p q branch)
  note extends = extends_noparam.intros(2)[of _ "subst_vars_fm \<sigma> q"]
  with 2 not_mem_subst_vars_branch show ?case
    by (fastforce simp: image_iff intro!: extends)
next
  case (3 s t1 t2 branch)
  with 3 have not_mem:
    "subst_vars_fm \<sigma> (AT (s \<in>\<^sub>s t1)) \<notin> set (subst_vars_branch \<sigma> branch)"
    "subst_vars_fm \<sigma> (AF (s \<in>\<^sub>s t1)) \<notin> set (subst_vars_branch \<sigma> branch)"
    by (meson not_mem_subst_vars_branch)+
  note extends = extends_noparam.intros(3)[of _ _ "subst_vars_term \<sigma> t2"]
  from 3 not_mem show ?case
    by (auto simp: rev_image_eqI last_map intro!: extends dest: mem_subterms_subst_vars_fm)     
next
  case (4 s t1 branch t2)
  with 4 have not_mem:
    "subst_vars_fm \<sigma> (AT (s \<in>\<^sub>s t2)) \<notin> set (subst_vars_branch \<sigma> branch)"
    "subst_vars_fm \<sigma> (AF (s \<in>\<^sub>s t2)) \<notin> set (subst_vars_branch \<sigma> branch)"
    by (meson not_mem_subst_vars_branch)+
  note extends = extends_noparam.intros(4)[of _ "subst_vars_term \<sigma> t1"]
  from 4 not_mem show ?case
    by (auto simp: rev_image_eqI last_map intro!: extends dest: mem_subterms_subst_vars_fm)     
next
  case (5 s t1 branch t2)
  with 5 have not_mem:
    "subst_vars_fm \<sigma> (AT (s \<in>\<^sub>s t2)) \<notin> set (subst_vars_branch \<sigma> branch)"
    "subst_vars_fm \<sigma> (AF (s \<in>\<^sub>s t2)) \<notin> set (subst_vars_branch \<sigma> branch)"
    by (meson not_mem_subst_vars_branch)+
  note extends = extends_noparam.intros(5)[of _ "subst_vars_term \<sigma> t1"]
  from 5 not_mem show ?case
    by (auto simp: rev_image_eqI last_map intro!: extends dest: mem_subterms_subst_vars_fm)     
qed

lemma subst_vars_literal_comp:
  "subst_vars_literal \<sigma>\<^sub>1 o subst_vars_literal \<sigma>\<^sub>2 = subst_vars_literal (\<sigma>\<^sub>1 o \<sigma>\<^sub>2)"
  by (standard) (auto simp: subst_vars_literal_def pset_atom.map_comp)

lemma subst_vars_literal_id: "subst_vars_literal id l = l"
  by (cases l) (auto simp: pset_atom.map_id)

lemma subst_vars_fm_id: "subst_vars_fm id \<phi> = \<phi>"
  by (metis eq_id_iff fm.map_id subst_vars_literal_id)

lemma subst_vars_branch_id: "subst_vars_branch id b = b"
  by (simp add: map_idI subst_vars_fm_id)

lemma extends_param_subst_vars_branch:
  assumes "extends_param t1 t2 z bs' b" "b \<noteq> []"
  assumes "permutation \<sigma>"
  shows "extends_param (subst_vars_term \<sigma> t1) (subst_vars_term \<sigma> t2) (\<sigma> z)
    (map (subst_vars_branch \<sigma>) bs') (subst_vars_branch \<sigma> b)"
  using assms
proof(induction rule: extends_param.induct)
  case (1 branch)
  from \<open>z \<notin> vars_branch branch\<close> \<open>permutation \<sigma>\<close> have "\<sigma> z \<notin> vars_branch (subst_vars_branch \<sigma> branch)"
    by auto (metis id_apply o_apply permutation_inverse_works(1))
  moreover
  from 1 have "subst_vars_fm \<sigma> (AF (t1 \<approx>\<^sub>s t2)) \<in> set (subst_vars_branch \<sigma> branch)"
    by force
  then have "AF (subst_vars_term \<sigma> t1 \<approx>\<^sub>s subst_vars_term \<sigma> t2)
    \<in> set (subst_vars_branch \<sigma> branch)"
    by simp
  moreover note extends = extends_param.intros(1)[OF calculation(2) _ _ _ _ calculation(1)]
  from 1 show ?case
    unfolding list.map fm.map subst_vars_literal_apply pset_atom.map pset_term.map
  proof(intro extends, goal_cases)
    case 3       
    show ?case
    proof(standard, goal_cases)
      case Ex: 1
      then have "\<exists>xa.
        subst_vars_fm (inv \<sigma>) (AT (xa \<in>\<^sub>s subst_vars_term \<sigma> t1))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch)) \<and>             
        subst_vars_fm (inv \<sigma>) (AF (xa \<in>\<^sub>s subst_vars_term \<sigma> t2))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch))"
        unfolding list.set_map by blast
      then have "\<exists>xa.
        AT (subst_vars_term (inv \<sigma>) xa \<in>\<^sub>s subst_vars_term (inv \<sigma>) (subst_vars_term \<sigma> t1))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch)) \<and>             
        AF (subst_vars_term (inv \<sigma>) xa \<in>\<^sub>s subst_vars_term (inv \<sigma>) (subst_vars_term \<sigma> t2))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch))"
        by simp
      then have "\<exists>xa. (AT (xa \<in>\<^sub>s t1)) \<in> set branch \<and> (AF (xa \<in>\<^sub>s t2)) \<in> set branch"
        unfolding pset_term.map_comp list.map_comp fm.map_comp comp_def
        unfolding subst_vars_literal_comp[unfolded comp_def]
        unfolding permutation_inverse_works(1)[OF \<open>permutation \<sigma>\<close>, unfolded comp_def]
        unfolding subst_vars_branch_id pset_term.map_id by blast
      with 1 show ?case by blast
    qed
  next         
    case 4     
    show ?case
    proof(standard, goal_cases)
      case Ex: 1
      then have "\<exists>xa.
        subst_vars_fm (inv \<sigma>) (AT (xa \<in>\<^sub>s subst_vars_term \<sigma> t2))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch)) \<and>             
        subst_vars_fm (inv \<sigma>) (AF (xa \<in>\<^sub>s subst_vars_term \<sigma> t1))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch))"
        unfolding list.set_map by blast
      then have "\<exists>xa.
        AT (subst_vars_term (inv \<sigma>) xa \<in>\<^sub>s subst_vars_term (inv \<sigma>) (subst_vars_term \<sigma> t2))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch)) \<and>             
        AF (subst_vars_term (inv \<sigma>) xa \<in>\<^sub>s subst_vars_term (inv \<sigma>) (subst_vars_term \<sigma> t1))
          \<in> set (subst_vars_branch (inv \<sigma>) (subst_vars_branch \<sigma> branch))"
        by simp
      then have "\<exists>xa. (AT (xa \<in>\<^sub>s t2)) \<in> set branch \<and> (AF (xa \<in>\<^sub>s t1)) \<in> set branch"
        unfolding pset_term.map_comp list.map_comp fm.map_comp comp_def
        unfolding subst_vars_literal_comp[unfolded comp_def]
        unfolding permutation_inverse_works(1)[OF \<open>permutation \<sigma>\<close>, unfolded comp_def]
        unfolding subst_vars_branch_id pset_term.map_id by blast
      with 1 show ?case by blast
    qed                 
  qed (simp_all add: mem_subterms_subst_vars_fm last_map)    
qed

(*
lemma subst_var_if_neq[simp]: "x \<noteq> z \<Longrightarrow> subst_var x y z = z"
  by (simp add: subst_var_def)

lemma subst_var_term_if_not_mem_set[simp]:
  "x \<notin> set_pset_term t \<Longrightarrow> subst_var_term x y t = t"
  by (induction t) auto

lemma subst_var_atom_if_not_mem_set[simp]:
  "x \<notin> set_pset_atom a \<Longrightarrow> subst_var_atom x y a = a"
  by (cases a) auto

lemma subst_var_literal_if_not_mem_set[simp]:
  "x \<notin> set_pset_atom (snd l) \<Longrightarrow> subst_var_literal x y l = l"
  by (cases l rule: tlvl_terms_atom.cases) (auto simp: subst_var_literal_apply)

lemma subst_var_fm_if_not_mem_set[simp]:
  "x \<notin> vars_fm \<phi> \<Longrightarrow> subst_var_fm x y \<phi> = \<phi>"
  by (induction \<phi>) (auto intro: vars_fmI)

lemma subst_var_branch_if_not_mem_set[simp]:
  "x \<notin> vars_branch b \<Longrightarrow> subst_var_branch x y b = b"
  by (simp add: map_idI vars_branch_def)

definition "subst_vars subst vvs b \<equiv> foldr (\<lambda>(x, y) b. subst x y b) vvs b"

lemma subst_vars_simps[simp]:
  shows "subst_vars subst [] x = x"
        "subst_vars subst (vv # vvs) x = subst (fst vv) (snd vv) (subst_vars subst vvs x)"
  unfolding subst_vars_def by (simp_all add: case_prod_unfold)

lemma subst_vars_append:
  "subst_vars subst (vvs1 @ vvs2) x = subst_vars subst vvs1 (subst_vars subst vvs2 x)"
  unfolding subst_vars_def by auto

abbreviation "subst_vars_var \<equiv> subst_vars subst_var"
abbreviation "subst_vars_term \<equiv> subst_vars subst_var_term"
abbreviation "subst_vars_literal \<equiv> subst_vars subst_var_literal"
abbreviation "subst_vars_fm \<equiv> subst_vars subst_var_fm"
abbreviation "subst_vars_branch \<equiv> subst_vars subst_var_branch"

lemma subst_vars_branch_append:
  "subst_vars_branch vvs (b1 @ b2) = subst_vars_branch vvs b1 @ subst_vars_branch vvs b2"
  by (induction vvs) auto

lemma vars_branch_subst_vars_branch[simp]:
  "vars_branch (subst_vars_branch vvs b) = subst_vars_var vvs ` vars_branch b"
  by (induction vvs) (auto)

lemma set_subst_vars_branch: "set (subst_vars_branch vvs b) \<equiv> subst_vars_fm vvs ` set b"
  by (induction vvs) auto

lemma not_mem_vars_branch_subst_vars_branch:
  assumes "\<forall>ys \<in> set (suffixes (vv # vvs)) - {[]}.
    snd (hd ys) \<notin> vars_branch (subst_vars_branch (tl ys) b)"
  shows "snd vv \<notin> vars_branch (subst_vars_branch vvs b)"
  using assms
  by (simp add: insert_Diff_if)

lemma lextends_subst_vars_branch:
  assumes "lextends b' b" "b \<noteq> []"
  assumes "\<forall>ys \<in> set (suffixes vvs) - {[]}.
    snd (hd ys) \<notin> vars_branch (subst_vars_branch (tl ys) b)"
  shows "lextends (subst_vars_branch vvs b') (subst_vars_branch vvs b)"
  using assms
proof(induction vvs arbitrary: b' b)
  case (Cons vv2 vvs)
  then have "lextends (subst_vars_branch vvs b') (subst_vars_branch vvs b)"
    by auto
  moreover have "subst_vars_branch vvs b \<noteq> []"
    using \<open>b \<noteq> []\<close> by (induction vvs) (auto)
  moreover from Cons have "snd vv2 \<notin> vars_branch (subst_vars_branch vvs b)"
    by force
  moreover note lextends_subst_var_branch[OF calculation, of "fst vv2"]
  ultimately show ?case
    by simp
qed simp

lemma extends_noparam_subst_vars_branch:
  assumes "extends_noparam bs' b" "b \<noteq> []"
  assumes "\<forall>ys \<in> set (suffixes vvs) - {[]}.
    snd (hd ys) \<notin> vars_branch (subst_vars_branch (tl ys) b)"
  shows "extends_noparam (map (subst_vars_branch vvs) bs') (subst_vars_branch vvs b)"
  using assms
proof(induction vvs arbitrary: bs' b)
  case Nil
  then show ?case by simp
next
  case (Cons vv vvs)
  then have "extends_noparam (map (subst_vars_branch vvs) bs') (subst_vars_branch vvs b)"
    by simp
  moreover have "subst_vars_branch vvs b \<noteq> []"
    using \<open>b \<noteq> []\<close> by (induction vvs) (auto)
  moreover from Cons have "snd vv \<notin> vars_branch (subst_vars_branch vvs b)"
    by force
  moreover note extends_noparam_subst_var_branch[OF calculation, of "fst vv"]
  ultimately show ?case
    by (simp add: comp_def)
qed

lemma Ex_snd_eq_subst_vars_var:
  assumes "subst_vars_var vvs z \<noteq> z"
  shows "\<exists>vv \<in> set vvs. snd vv = subst_vars_var vvs z"
  using assms
proof(induction vvs)
  case (Cons vv2 vvs)
  then show ?case
  proof(cases "subst_vars_var vvs z \<noteq> z")
    case True
    with Cons obtain vv where vv: "vv \<in> set vvs" "snd vv = subst_vars_var vvs z"
      by auto
    with Cons show ?thesis
      by (cases "snd vv = subst_vars_var (vv2 # vvs) z") (auto simp: subst_var_def)
  next
    case False
    with Cons have "snd vv2 = subst_vars_var (vv2 # vvs) z"
      unfolding subst_vars_simps subst_var_def by auto
    then show ?thesis by simp
  qed
qed simp

lemma extends_param_subst_vars_branch:
  assumes "extends_param t1 t2 z bs' b" "b \<noteq> []"
  assumes "\<forall>ys \<in> set (suffixes vvs) - {[]}.
    snd (hd ys) \<notin> vars_branch (subst_vars_branch (tl ys) b)
  \<and> (\<forall>b' \<in> set bs. snd (hd ys) \<notin> vars_branch (subst_vars_branch (tl ys) b'))"
  assumes "\<forall>y \<in> snd ` set vvs. y \<noteq> z"
  assumes "distinct (map snd vvs)"
  shows "extends_param (subst_vars_term vvs t1) (subst_vars_term vvs t2) (subst_vars_var vvs z)
    (map (subst_vars_branch vvs) bs') (subst_vars_branch vvs b)"
  using assms
proof(induction vvs arbitrary: bs' b)
  case Nil
  then show ?case by simp
next
  case (Cons vv vvs)
  then have "extends_param (subst_vars_term vvs t1) (subst_vars_term vvs t2) (subst_vars_var vvs z)
    (map (subst_vars_branch vvs) bs') (subst_vars_branch vvs b)"
    by simp
  moreover have "subst_vars_branch vvs b \<noteq> []"
    using \<open>b \<noteq> []\<close> by (induction vvs) auto
  moreover from Cons have "snd vv \<notin> vars_branch (subst_vars_branch vvs b)"
    using not_mem_vars_branch_subst_vars_branch by metis
  moreover have "snd vv \<noteq> subst_vars_var vvs z"
  proof -
    have "snd vv \<noteq> subst_vars_var vvs z" if "subst_vars_var vvs z = z"
      using that by (simp add: Cons.prems)
    moreover have "snd vv \<noteq> subst_vars_var vvs z" if "subst_vars_var vvs z \<noteq> z"
      using Ex_snd_eq_subst_vars_var[OF that] Cons.prems(5)
      by (metis distinct.simps(2) imageI list.set_map list.simps(9))
    ultimately show ?thesis by blast
  qed
  moreover from extends_param_subst_var_branch[OF calculation] show ?case
    by (simp add: comp_def)
qed
*)

lemma
  fixes b :: "'a branch"
  assumes "closeable b" "b \<noteq> []"
  assumes "permutation \<sigma>"
  assumes "infinite (UNIV :: 'a set)"
  shows "closeable (subst_vars_branch \<sigma> b)"
  using assms(1-3)
proof(induction arbitrary: \<sigma> rule: closeable.induct)
  case (1 b)
  then show ?case
  proof(induction rule: bclosed.induct)
    case (contr \<phi> branch)
    then have
      "subst_vars_fm \<sigma> \<phi> \<in> set (subst_vars_branch \<sigma> branch)"
      "Neg (subst_vars_fm \<sigma> \<phi>) \<in> set (subst_vars_branch \<sigma> branch)"
      by force+
    then show ?case
      using bclosed.intros(1)[THEN closeable.intros(1)] by blast
  next
    case (elemEmpty t branch)
    with elemEmpty have "AT (subst_vars_term \<sigma> t \<in>\<^sub>s \<emptyset>) \<in> set (subst_vars_branch \<sigma> branch)"
      by force
    then show ?case
      using bclosed.intros(2)[THEN closeable.intros(1)] by blast
  next
    case (neqSelf t branch)
    with neqSelf have "AF (subst_vars_term \<sigma> t \<approx>\<^sub>s subst_vars_term \<sigma> t)
      \<in> set (subst_vars_branch \<sigma> branch)"
      by force
    then show ?case
      using bclosed.intros(3)[THEN closeable.intros(1)] by blast
  next
    case (memberCycle cs branch)
    have
      "member_seq (subst_vars_term \<sigma> s) (map (subst_vars_literal \<sigma>) cs) (subst_vars_term \<sigma> t)"
      if "member_seq s cs t" for s t
      using that
      by (induction s cs t rule: member_seq.induct) simp_all
    with memberCycle have "member_cycle (map (subst_vars_literal \<sigma>) cs)"
      by (induction cs rule: member_cycle.induct) simp_all
    moreover
    have "set (map (subst_vars_literal \<sigma>) cs) \<subseteq> Atoms (set (subst_vars_branch \<sigma> branch))"
      using \<open>set cs \<subseteq> Atoms (set branch)\<close> image_iff
      by (fastforce simp: Atoms_def)
    ultimately show ?case
      using bclosed.intros(4)[THEN closeable.intros(1)] by blast
  qed
next
  case (2 b' b)
  then have "closeable (subst_vars_branch \<sigma> (b' @ b))"
    by (simp add: lextends_vars_branch_eq)
  moreover note lextends_subst_vars_branch[OF \<open>lextends b' b\<close> "2.prems"(1,2)]
  ultimately show ?case
    using closeable.intros(2) by auto
next
  case (3 bs' b)
  then show ?case
  proof(cases rule: extends.cases)
    case 1
    with 3 have "closeable (subst_vars_branch \<sigma> (b' @ b))" if "b' \<in> set bs'" for b'
      using that by (simp add: extends_noparam_vars_branch_eq)
    moreover note extends_noparam_subst_vars_branch[OF \<open>extends_noparam bs' b\<close> "3.prems"(1,2)]
    ultimately show ?thesis
      unfolding map_append using closeable.intros(3)[OF extends.intros(1)]
      sorry
  next
    case (2 t1 t2 z)
    with 3 have "extends (map (subst_vars_branch \<sigma>) bs') (subst_vars_branch \<sigma> b)"
      by (metis extends.simps extends_param_subst_vars_branch)
    moreover have "closeable (subst_vars_branch \<sigma> (b' @ b))"
      if "b' \<in> set bs'" for b'
      using that 3 by simp
    ultimately show ?thesis
      using closeable.intros(3) by force
  qed
qed

lemma
  assumes "extends_param t1 t2 x bs' b"
  assumes "\<forall>b' \<in> set bs'. closeable (b' @ b)"
  assumes "last ba = last b" "set b \<subseteq> set ba"
  assumes "AT (t' \<in>\<^sub>s t1) \<in> set ba" "AF (t' \<in>\<^sub>s t2) \<in> set ba"
  shows "closeable ba"
proof -
  from assms have "closeable b"
    by (meson closeable.intros(3) extends.intros(2))
  then show ?thesis
    using assms(1,3-)
proof(induction b arbitrary: ba rule: closeable.induct)
  case 1
  then show ?case sorry
next
  case (2 b')
  then show ?case sorry
next
  case (3 bs)
  then show ?case sorry
qed

lemma closeable_if_last_and_set_eq:
  assumes "closeable b1"
  assumes "last b1 = last b2" "set b1 = set b2"
  shows "closeable b2"
  using assms
proof(induction arbitrary: b2 rule: closeable.induct)
  case (1 b)
  then show ?case
    using bclosed_mono closeable.intros(1) by blast
next
  case (2 b1' b1 b2)
  then show ?case
    using lextends_if_eq_last_and_set
    by (metis closeable.intros(2) dual_order.refl last_appendR set_append set_empty2)
next
  case (3 bs b)
  then show ?case
    using extends_if_eq_last_and_set
    by (metis List.set_empty closeable.intros(3) last_appendR set_append)
qed

lemma
  assumes "closeable b" "b \<noteq> []"
  assumes "lextends b' b"
  shows "closeable (b' @ b)"
  using assms
proof(induction arbitrary: b' rule: closeable.induct)
  case (1 b)
  then show ?case
    by (metis bclosed_mono closeable.intros(1) set_append sup.cobounded2)
next
  case (2 ba' b)
  then have "closeable (b' @ ba' @ b)"
    using lextends_if_eq_last_and_set
    by (metis append_is_Nil_conv last_appendR set_mono_suffix suffixI)
  then have "closeable (ba' @ b' @ b)"
    apply(rule closeable_if_last_and_set_eq)
    by (auto simp: \<open>b \<noteq> []\<close>)
  moreover have "lextends ba' (b' @ b)"
    using 2 lextends_if_eq_last_and_set
    by (metis Un_upper2 last_appendR set_append)
  ultimately show ?case
    using closeable.intros(2) by blast
next
  case (3 bas' b)
  then have *: "closeable (b' @ ba' @ b)" if "ba' \<in> set bas'" for ba'
    using that lextends_if_eq_last_and_set
    by (metis append_is_Nil_conv last_appendR set_mono_suffix suffixI)
  have "closeable (ba' @ b' @ b)" if "ba' \<in> set bas'" for ba'
    apply(rule closeable_if_last_and_set_eq[OF *[OF that]])
    using \<open>b \<noteq> []\<close> by auto
  moreover have "extends bas' (b' @ b)" sorry
  then show ?case sorry
qed

lemma closeable_mono:
  assumes "closeable b" "b \<noteq> []"
  assumes "last b = last ba" "set b \<subseteq> set ba"
  shows "closeable ba"
  using assms
proof(induction arbitrary: ba rule: closeable.induct)
  case (1 b)
  then show ?case
    using bclosed_mono closeable.intros(1) by blast
next
  case (2 b' b)
  then have "lextends b' ba"
    using lextends_if_eq_last_and_set by blast
  with 2 have "closeable (b' @ ba)"
    by (intro "2"(3)) (auto simp: last_append)
  with \<open>lextends b' ba\<close> show ?case
    using closeable.intros(2) by blast
next
  case extends: (3 bs' b)
  from extends have
    "last (b' @ b) = last (b' @ ba)" "set (b' @ b) \<subseteq> set (b' @ ba)"
    if "b' \<in> set bs'" for b'
    using that by (auto simp: last_append)
  with extends have "\<forall>b' \<in> set bs'. closeable (b' @ ba)"
    by (metis Nil_is_append_conv)
  then show ?case
  proof(cases "extends bs' ba")
    case False
    from extends(1) show ?thesis
    proof(cases rule: extends.cases)
      case 1
      then show ?thesis
      proof(cases rule: extends_noparam.cases)
        case Or: (1 p q)
        with False extends consider "p \<in> set ba" | "Neg p \<in> set ba"
          using extends_noparam.intros(1)[THEN extends.intros(1)] by blast
        with extends Or show ?thesis
          by (cases) (auto simp: last_append)
      next
        case Neg_And: (2 p q)
        with False extends consider "p \<in> set ba" | "Neg p \<in> set ba"
          using extends_noparam.intros(2)[THEN extends.intros(1)] by blast
        with extends Neg_And show ?thesis
          by (cases) (auto simp: last_append)
      next
        case Union: (3 s t1 t2)
        with False extends consider "AT (s \<in>\<^sub>s t1) \<in> set ba" | "AF (s \<in>\<^sub>s t1) \<in> set ba"
          using extends_noparam.intros(3)[THEN extends.intros(1), of s t1 t2 ba]
          by (metis subsetD)
        with extends Union show ?thesis
          by (cases) (auto simp: last_append)
      next
        case Inter: (4 s t1 t2)
        with False extends consider "AT (s \<in>\<^sub>s t2) \<in> set ba" | "AF (s \<in>\<^sub>s t2) \<in> set ba"
          using extends_noparam.intros(4)[THEN extends.intros(1), of s t1 ba t2]
          by (metis subsetD)
        with extends Inter show ?thesis
          by (cases) (auto simp: last_append)
      next
        case Diff: (5 s t1 t2)
        with False extends consider "AT (s \<in>\<^sub>s t2) \<in> set ba" | "AF (s \<in>\<^sub>s t2) \<in> set ba"
          using extends_noparam.intros(5)[THEN extends.intros(1), of s t1 ba t2]
          by (metis subsetD)
        with extends Diff show ?thesis
          by (cases) (auto simp: last_append)
      qed
    next
      case extends_param: (2 t1 t2 x)
      then show ?thesis
      proof(cases rule: extends_param.cases)
        case extends_param_case: 1
        from False have "\<not> extends_param t1 t2 x bs' ba"
          by (simp add: extends.simps)
        with extends_param_case consider
          t' where "AT (t' \<in>\<^sub>s t1) \<in> set ba" "AF (t' \<in>\<^sub>s t2) \<in> set ba" |
          t' where "AT (t' \<in>\<^sub>s t2) \<in> set ba" "AF (t' \<in>\<^sub>s t1) \<in> set ba" |
          "x \<in> vars_branch ba"
          using extends.intros(2) extends.prems(2,3) extends_param.intros[of t1 t2 ba]
          by (fastforce simp: subsetD)
        then show ?thesis
        proof(cases)
          case 1
          then show ?thesis sorry
        next
          case 2
          then show ?thesis sorry
        next
          case 3
          then show ?thesis sorry
        qed
      qed
    qed
  qed (use closeable.intros(3) in blast)
qed

lemma bclosed_if_closeable_and_sat:
  "closeable b \<Longrightarrow> sat b \<Longrightarrow> bclosed b"
proof(induction rule: closeable.induct)
  case (2 b' b)
  then have "set (b' @ b) = set b"
    unfolding sat_def lin_sat_def  by auto
  with extends_if_eq_last_and_set[OF _ _ this]
       lextends_if_eq_last_and_set[OF _ _ Set.equalityD1[OF this]] 2
  have "sat (b' @ b)"
    by (metis \<open>set (b' @ b) = set b\<close> last_appendR lin_sat_def sat_def set_empty2)
  with 2 \<open>set (b' @ b) = set b\<close> show ?case
    using bclosed_mono by blast
qed (simp_all add: sat_def)

lemma mlss_proc_branch_if_closeable:
  assumes "wf_branch b"
  assumes "closeable b"
  shows "mlss_proc_branch b"
  using mlss_proc_branch_dom_if_wf_branch[OF assms(1)] assms
proof(induction rule: mlss_proc_branch.pinduct)
  case (1 b)
  with closeable_mono have "closeable ((SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)) @ b)"
    using wf_branch_not_Nil by fastforce
  moreover have "wf_branch ((SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)) @ b)"
    using 1 wf_branch_lextends by (metis (no_types, lifting) not_lin_satD someI_ex)
  ultimately show ?case
    using 1 by (simp add: mlss_proc_branch.psimps)
next
  case (2 b)
  with closeable_mono have "closeable (b' @ b)"
    if "b' \<in> set (SOME bs'. extends bs' b)" for b'
    using that by (metis Un_upper2 last_appendR set_append wf_branch_not_Nil)
  moreover have "wf_branch (b' @ b)"
    if "b' \<in> set (SOME bs'. extends bs' b)" for b'
    using 2 that by (metis extendss.simps sat_def someI wf_branch_def)
  ultimately show ?case 
    using 2 by (simp add: Ball_set[symmetric] mlss_proc_branch.psimps)
next
  case (3 b)
  with bclosed_if_closeable_and_sat show ?case
    using mlss_proc_branch.psimps by blast
next
  case (4 b)
  then show ?case by (simp add: mlss_proc_branch.psimps)
qed

end