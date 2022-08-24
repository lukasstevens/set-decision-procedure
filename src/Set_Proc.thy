theory Set_Proc                
  imports Set_Calculus Realization
begin

section \<open>Basic Definitions\<close>

definition "lin_sat b \<equiv> \<forall>b'. lextends b' b \<longrightarrow> set b' \<subseteq> set b"

lemma lin_satD:
  assumes "lin_sat b"
  assumes "lextends b' b"
  assumes "x \<in> set b'"
  shows "x \<in> set b"
  using assms unfolding lin_sat_def by auto

lemma not_lin_satD: "\<not> lin_sat b \<Longrightarrow> \<exists>b'. lextends b' b \<and> set b \<subset> set (b' @ b)"
  unfolding lin_sat_def by auto

definition "sat b \<equiv> lin_sat b \<and> (\<nexists>bs'. fextends bs' b)"

lemma satD:
  assumes "sat b"
  shows "lin_sat b" "\<nexists>bs'. fextends bs' b"
  using assms unfolding sat_def by auto

definition "wf_branch b \<equiv> \<exists>\<phi>. extendss b [\<phi>]"

lemma wf_branch_not_Nil[simp]: "wf_branch b \<Longrightarrow> b \<noteq> []"
  unfolding wf_branch_def
  using extendss_suffix suffix_bot.extremum_uniqueI by blast

lemma wf_branch_extendss: "wf_branch b \<Longrightarrow> extendss b' b \<Longrightarrow> wf_branch b'"
  using extendss_trans wf_branch_def by blast

lemma wf_branch_lextends:
  "wf_branch b \<Longrightarrow> lextends b' b \<Longrightarrow> set b \<subset> set (b' @ b) \<Longrightarrow> wf_branch (b' @ b)"
  by (metis extendss.simps wf_branch_extendss)
                            
definition params :: "'a branch \<Rightarrow> 'a set" where
  "params b \<equiv> vars_branch b - vars_fm (last b)"

definition params' :: "'a branch \<Rightarrow> 'a set" where
  "params' b \<equiv> {c \<in> params b. \<forall>t \<in> subterms_fm (last b).
                  AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b}"

lemma params_singleton[simp]: "params [\<phi>] = {}"
  unfolding params_def vars_branch_simps by simp

lemma params'_singleton[simp]: "params' [\<phi>] = {}"
  unfolding params'_def by auto

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

lemma finite_params: "finite (params b)"
  unfolding params_def using finite_vars_branch by auto

lemma finite_params': "finite (params' b)"
proof -
  have "params' b \<subseteq> params b"
    unfolding params'_def by simp
  then show ?thesis using finite_params finite_subset by blast
qed

(* TODO: rename this *)
definition subterms_branch' :: "'a branch \<Rightarrow> 'a pset_term set" where
  "subterms_branch' b \<equiv>
    subterms_fm (last b) \<union> Var ` (params b - params' b)"

definition bgraph :: "'a branch \<Rightarrow> ('a pset_term, 'a pset_term \<times> 'a pset_term) pre_digraph" where
  "bgraph b \<equiv>
    let
      vs = Var ` params' b \<union> subterms_branch' b
    in
      \<lparr> verts = vs,
        arcs = {(s, t). AT (s \<in>\<^sub>s t) \<in> set b},
        tail = fst,
        head = snd \<rparr>"

lemma finite_subterms_branch': "finite (subterms_branch' b)"
  unfolding subterms_branch'_def using finite_subterms_fm finite_params
  by auto

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
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (3 b' b)
  then show ?case
    apply(induction rule: lextends_int.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_subterms_branch_trans
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (4 b' b)
  then show ?case
    apply(induction rule: lextends_diff.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_subterms_branch_trans
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (1 t1 b)
    then show ?case
      using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
      apply(auto simp: subterms_branch_simps
            dest: subterms_fmD intro: subterms_subterms_branch_trans)
      done
  qed (auto simp: subterms_branch_simps subterms_branch_subterms_subterms_atom_trans
       dest: subterms_branchD AF_mem_subterms_branchD 
       intro: subterms_subterms_branch_trans)
next
  case (6 b' b)
  have *: "subterms_atom (subst_tlvl t1 t2 a) \<subseteq> subterms t2 \<union> subterms_atom a"
    for t1 t2 and a :: "'a pset_atom"
    by (cases "(t1, t2, a)" rule: subst_tlvl.cases) auto
  from 6 show ?case
  by (induction rule: lextends_eq.induct)
     (auto simp: subterms_branch_def subterms_branch_subterms_subterms_atom_trans
            dest!: subsetD[OF *])
qed

lemma lextends_vars_branch_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars_branch (b' @ b) = vars_branch b"
  using lextends_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma fextends_noparam_subterms_branch_eq:
  "fextends_noparam bs' b \<Longrightarrow> b' \<in> bs' \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms_branch (b' @ b) = subterms_branch b"
proof(induction rule: fextends_noparam.induct)
  case (3 s t1 t2 b)
  then show ?case
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
next
  case (4 s t1 b t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "4"(2)]
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
next
  case (5 s t1 b t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "5"(2)]
    by (auto simp: subterms_branch_subterms_subterms_atom_trans subterms_branch_simps)
qed (use subterms_branch_def in \<open>(fastforce simp: subterms_branch_simps)+\<close>)


lemma fextends_noparam_vars_branch_eq:
  "fextends_noparam bs' b \<Longrightarrow> b' \<in> bs' \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars_branch (b' @ b) = vars_branch b"
  using fextends_noparam_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma lextends_params_eq:
  "lextends b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> params (b' @ b) = params b"
  using lextends_vars_branch_eq unfolding params_def by force

lemma fextends_noparam_params_eq:
  assumes "fextends_noparam bs' b" "b' \<in> bs'" "b \<noteq> []" 
  shows "params (b' @ b) = params b"
  using fextends_noparam_vars_branch_eq[OF assms] assms(3)
  unfolding params_def by simp

lemma fextends_param_vars_branch_eq:
  assumes "fextends_param t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "vars_branch (b' @ b) = insert x (vars_branch b)"
  using assms fextends_paramD[OF assms(1)]
  by (auto simp: mem_vars_fm_if_mem_subterm_fm vars_branch_simps vars_fm_vars_branchI)

lemma fextends_param_params_eq:
  assumes "fextends_param t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "params (b' @ b) = insert x (params b)"
  using assms fextends_paramD[OF assms(1)]
  unfolding params_def
  by (auto simp: mem_vars_fm_if_mem_subterm_fm vars_branch_simps vars_branch_def)

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
   \<forall>t \<in> subterms_branch b. t \<notin> Var ` params b \<longrightarrow> t \<in> subterms_fm (last b)"

lemma no_new_subtermsI:
  assumes "\<And>t. t \<in> subterms_branch b \<Longrightarrow> t \<notin> Var ` params b \<Longrightarrow> t \<in> subterms_fm (last b)"
  shows "no_new_subterms b"
  using assms unfolding no_new_subterms_def by blast

lemma Var_mem_subterms_branch_and_not_in_params:
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
    using Var_mem_subterms_branch_and_not_in_params by (metis imageI)
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
  
lemma fextends_noparam_no_new_subterms:
  assumes "fextends_noparam bs' b" "b' \<in> bs'" "b \<noteq> []" 
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms unfolding no_new_subterms_def
  by (simp add: fextends_noparam_params_eq fextends_noparam_subterms_branch_eq[OF assms(1,2)])

lemma fextends_param_no_new_subterms:
  assumes "fextends_param t1 t2 x bs' b" "b \<noteq> []" "b' \<in> bs'"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(induction rule: fextends_param.induct)
  apply(auto simp: subterms_branch_simps subterms_subterms_atom_trans subterms_subterms_fm_trans
             elim: no_new_subtermsE
             intro!: no_new_subterms_casesI)
  done

lemma fextends_no_new_subterms:
  assumes "fextends bs' b" "b \<noteq> []" "b' \<in> bs'"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(cases rule: fextends.cases)
  using fextends_noparam_no_new_subterms fextends_param_no_new_subterms by metis+

lemma extendss_no_new_subterms:
  assumes "extendss b' b" "b \<noteq> []" "no_new_subterms b"
  shows "no_new_subterms b'"
  using assms
  apply(induction b' b rule: extendss.induct)
  using extendss_suffix suffix_bot.extremum_uniqueI
  using lextends_no_new_subterms fextends_no_new_subterms
  by blast+

lemmas subterms_branch_subterms_fm_lastI =
  subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]

(* TODO: consider renaming this *)
definition params_subterms :: "'a branch \<Rightarrow> 'a pset_term set" where
  "params_subterms b \<equiv> Var ` params b \<union> subterms_fm (last b)"

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


section \<open>Proof of Lemma 2\<close>

fun is_literal :: "'a fm \<Rightarrow> bool" where
  "is_literal (Atom _) = True"
| "is_literal (Neg (Atom _)) = True"
| "is_literal _ = False"

(* TODO: give the invariant P a proper name *)
lemma lextends_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-) lextends_params_eq[OF assms(2,3)]
  by (induction rule: lextends_induct)(auto simp: disjoint_iff P_def)

lemma fextends_noparam_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "fextends_noparam bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: fextends_noparam.induct)
     (auto simp: Int_def P_def params_def vars_fm_vars_branchI)

lemma fextends_param_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "fextends_param t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: fextends_param.induct)
     (auto simp: Int_def P_def params_def vars_fm_vars_branchI)

lemma fextends_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "fextends bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  apply(cases bs' b rule: fextends_cases)
  using fextends_param_no_params_if_not_literal fextends_noparam_no_params_if_not_literal
  using P_def by fast+

lemma extendss_no_params_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {})"
  assumes "extendss b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-)
  apply (induction rule: extendss.induct)
  using lextends_no_params_if_not_literal fextends_no_params_if_not_literal
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

lemma fextends_noparam_params'_eq:
  assumes "fextends_noparam bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  shows "params' (b' @ b) = params' b"
  using assms
proof -
  from assms have "x \<in> params' (b' @ b)" if "x \<in> params' b" for x
    using that fextends_noparam_params_eq[OF assms(1-3)]
    by (induction rule: fextends_noparam.induct)
       (intro params'I; fastforce simp: params'D)+
  moreover from assms have "params' (b' @ b) \<subseteq> params' b"
    unfolding params'_def
    using fextends_noparam_params_eq by fastforce
  ultimately show ?thesis by blast
qed

lemma fextends_param_params'_eq:
  assumes "fextends_param t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "params' (b' @ b) = insert x (params' b)"
  using assms(2,3) fextends_paramD[OF assms(1)]
  unfolding params'_def fextends_param_params_eq[OF assms] 
  by (auto simp: vars_fm_vars_branchI)

(* TODO: give the invariant P a proper name *)
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

  have "P (b' @ b) c t"
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
  moreover from "1"(1,4,6) have "\<forall>\<phi> \<in> set b'. vars_fm \<phi> \<inter> params (b' @ b) = {}"
    by (induction rule: lextends_fm.induct) (auto simp: disjoint_iff)
  ultimately show ?case
    using 1 lextends_fm_params'_eq by blast
next
  case (2 b' b)
  then show ?case
    using lextends_un_params'_eq[OF "2"(1,2,5)[unfolded P_def]]
    using lextends_no_new_subterms[OF lextends.intros(2), OF "2"(1,2) \<open>no_new_subterms b\<close>]
  proof(induction rule: lextends_un.induct)
    case (4 s t1 t2 b)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  next
    case (5 s t1 t2 b)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms_branch b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (1 s t1 t2 b)
    then have "t1 \<sqinter>\<^sub>s t2 \<in> subterms_branch b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  next
    case (6 s t1 b t2)
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 6 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (1 s t1 t2 b)
    then have "t1 -\<^sub>s t2 \<in> subterms_branch b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps dest: params'D(1))
  next
    case (4 s t1 t2 b)
    then have "t1 -\<^sub>s t2 \<in> subterms_branch b"
      unfolding subterms_branch_def
      by (metis AF_mem_subterms_branchD(2) subterms_branch_def)
    with \<open>no_new_subterms b\<close> have "t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
      using no_new_subtermsE by blast
    then have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: params_subterms_def P_def subterms_branch_simps dest: params'D(1))
  qed (auto simp: params_subterms_def P_def)
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lextends_single.induct)
    case (2 s t1 b)
    then have "Single t1 \<in> subterms_branch b"
      by (auto intro: subterms_branch_subterms_atomI)
    with 2 have "t1 \<in> subterms_fm (last b)"
      by (metis subterms_fmD(7) no_new_subtermsE(5))
    then have "\<forall>c \<in> params' b. Var c \<noteq> t1"
      unfolding params'_def params_def
      using params_def params_subterms_last_disjnt by fastforce
    with \<open>t1 \<in> subterms_fm (last b)\<close> show ?case
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
  proof(induction rule: lextends_eq_induct')
    case (subst t1 t2 t1' t2' p l b)
    then have "t1' \<in> subterms_branch b"
      using AT_eq_subterms_branchD by blast
    then show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with subst have [simp]: "p"
        using P_def by (cases p) (auto simp: params_subterms_def)
      from 1 subst have "(Var c \<approx>\<^sub>s x) = subst_tlvl t1' t2' l"
        using P_def by (auto simp: params_subterms_def)
      with 1 subst consider
        (refl) "l = (t1' \<approx>\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1'_left) "l = (Var c \<approx>\<^sub>s t1')" "t2' = x"
        | (t1'_right) "l = (t1' \<approx>\<^sub>s x)" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 1 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    next
      case (2 c x)
      with subst have [simp]: "p"
        using P_def by (cases p) (auto simp: params_subterms_def)
      from 2 subst have "(x \<approx>\<^sub>s Var c) = subst_tlvl t1' t2' l"
        using P_def by (auto simp: params_subterms_def)
      with 2 subst consider
        (refl) "l = (t1' \<approx>\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1_left) "l = (t1' \<approx>\<^sub>s Var c)" "t2' = x"
        | (t1_right) "l = (x \<approx>\<^sub>s t1')" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 2 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    next
      case (3 c x)
      with subst have [simp]: "p"
        using P_def by (cases p) (auto simp: params_subterms_def)
      from 3 subst have "(x \<in>\<^sub>s Var c) = subst_tlvl t1' t2' l"
        using P_def by (auto simp: params_subterms_def)
      with 3 subst consider
        (refl) "l = (t1' \<in>\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1_left) "l = (t1' \<in>\<^sub>s Var c)" "t2' = x"
        | (t1_right) "l = (x \<in>\<^sub>s t1')" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 3 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    qed
  next
    case (neq s t s' b)
    then show ?case
      using P_def by (auto simp: params_subterms_def)
  qed
qed

lemma lemma_2_fextends:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c \<approx>\<^sub>s t) \<notin> set b \<and> AT (t \<approx>\<^sub>s Var c) \<notin> set b
                      \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b)"
  assumes "fextends bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars_fm \<phi> \<inter> params b = {}"
  assumes "\<forall>c \<in> params' b. \<forall>t \<in> params_subterms b. P b c t"
  shows "\<forall>c \<in> params' (b' @ b). \<forall>t \<in> params_subterms (b' @ b). P (b' @ b) c t"
  using assms(2-) fextends_no_new_subterms[OF assms(2,4,3,5)]
proof(induction rule: fextends.induct)
  case (1 bs' b)
  then show ?case
    using fextends_noparam_params_eq[OF "1"(1-3)] fextends_noparam_params'_eq[OF "1"(1-3,5)]
  proof(induction rule: fextends_noparam.induct)
    case (1 p q b)
    then show ?case
      unfolding P_def params_subterms_def
      by (fastforce dest: params'D)
  next
    case (2 p q b)
    then show ?case
      unfolding P_def params_subterms_def
      by (fastforce dest: params'D)
  next
    case (3 s t1 t2 b)
    then have "t1 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 3 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)
  next
    case (4 s t1 b t2)
    then have "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)
  next
    case (5 s t1 b t2)
    then have "t2 \<notin> Var ` params b"
      by (meson disjoint_iff params_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      unfolding P_def params_subterms_def
      by (fastforce simp: vars_branch_simps dest: params'D)
  qed
next
  case (2 t1 t2 x bs b)
  from fextends_paramD[OF "2"(1)] have "t1 \<notin> Var ` params b" "t2 \<notin> Var ` params b"
    by (meson disjoint_iff_not_equal params_subterms_last_disjnt)+
  then have not_in_params': "t1 \<notin> Var ` params' b" "t2 \<notin> Var ` params' b"
    unfolding params'_def by auto
  with fextends_paramD[OF "2"(1)] "2"(2-) show ?case
    unfolding P_def params_subterms_def
    unfolding fextends_param_params'_eq[OF "2"(1-3)] fextends_param_params_eq[OF "2"(1-3)]
    by (auto simp: vars_fm_vars_branchI)
qed

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
  assumes "wf_branch b"
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> Var ` params' b \<union> subterms_branch' b"
    and "t \<in> Var ` params' b \<union> subterms_branch' b"
  using assms
  using params_subterms_eq_subterms_branch' AT_mem_subterms_branchD subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AF_mem_in_branch:
  assumes "wf_branch b"
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> Var ` params' b \<union> subterms_branch' b"
    and "t \<in> Var ` params' b \<union> subterms_branch' b"
  using assms
  using params_subterms_eq_subterms_branch' AF_mem_subterms_branchD subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AT_eq_in_branch:
  assumes "wf_branch b"
  assumes "AT (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> Var ` params' b \<union> subterms_branch' b"
    and "t \<in> Var ` params' b \<union> subterms_branch' b"
  using assms
  using params_subterms_eq_subterms_branch' AT_eq_subterms_branchD subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms_branch'_if_AF_eq_in_branch:
  assumes "wf_branch b"
  assumes "AF (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> Var ` params' b \<union> subterms_branch' b"
    and "t \<in> Var ` params' b \<union> subterms_branch' b"
  using assms
  using params_subterms_eq_subterms_branch' AF_eq_subterms_branchD subterms_branch_eq_if_wf_branch
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
    note lemma_2_fextends[OF this(1) _ _
        no_new_subterms[OF this(3)] no_params_if_not_literal[OF this(3)]]
    with 3 show ?case
      using wf_branch_def wf_branch_not_Nil by blast
  qed
  then show "AT (Var c \<approx>\<^sub>s t) \<notin> set b" "AT (t \<approx>\<^sub>s Var c) \<notin> set b" "AT (t \<in>\<^sub>s Var c) \<notin> set b"
    by blast+
qed


section \<open>Realization of an Open Branch\<close>

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

definition I :: "'a pset_term \<Rightarrow> V" where
  "I \<equiv> SOME f. inj_on f (Var ` params' b)
             \<and> (\<forall>p. card (elts (f p)) \<ge> card (Var ` params' b \<union> subterms_branch' b))"

lemma (in -) Ex_set_family:
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

lemma AT_mem_branch_params_subtermsD:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms AT_mem_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AF_mem_branch_params_subtermsD:
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms AF_mem_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AT_eq_branch_params_subtermsD:
  assumes "AT (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms AT_eq_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AF_eq_branch_params_subtermsD:
  assumes "AF (s \<approx>\<^sub>s t) \<in> set b"
  shows "s \<in> params_subterms b" "t \<in> params_subterms b"
  using assms AF_eq_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma realization_if_AT_mem:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "realization s \<in> elts (realization t)"
proof -
  note AT_mem_branch_params_subtermsD[OF assms]
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
  note AT_eq_branch_params_subtermsD[OF assms(2)]
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
        using subterms dominates_if_mem_realization a small_realization_parents
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
  note AF_eq_branch_params_subtermsD[OF assms(2)]
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

        have "f (arg_min_on f S) = Min (f ` S)" if "finite S" "S \<noteq> {}"
          for f :: "('a pset_term \<times> 'a pset_term) \<Rightarrow> nat" and S
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
            unfolding sat_def using lin_satD by fastforce
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
            unfolding sat_def using lin_satD by fastforce
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
        using AF_eq_branch_params_subtermsD(1,2) 
        by (metis case_prod_conv params_subterms_eq_subterms_branch')
 
      from finite_vars_branch infinite_vars obtain x where "x \<notin> vars_branch b"
        using ex_new_if_finite by blast
      from fextends_param.intros[OF t1'_t2'(3,1,2) _ _ this] \<open>sat b\<close>[unfolded sat_def] consider
        s1 where "AT (s1 \<in>\<^sub>s t1') \<in> set b" "AF (s1 \<in>\<^sub>s t2') \<in> set b" |
        s2 where "AF (s2 \<in>\<^sub>s t1') \<in> set b" "AT (s2 \<in>\<^sub>s t2') \<in> set b"
        using fextends.intros(2-) by metis 
      then show ?thesis
      proof cases
        case 1
        with \<open>realization t1' = realization t2'\<close> have "realization s1 \<in> elts (realization t2')"
          using realization_if_AT_mem by metis
        with 1 t1'_t2'(3,4) obtain s2 where
          "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2'" "realization s1 = realization s2"
          using dominates_if_mem_realization in_subterms_branch'_if_AT_mem_in_branch(1)[OF wf_branch] 
          by (metis AF_eq_branch_params_subtermsD(2) params_subterms_eq_subterms_branch')
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
  then have "parents (bgraph b) \<emptyset> = {}"
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
      unfolding sat_def using fextends_noparam.intros(3)[OF _ mem_subterms_fm, THEN fextends.intros(1)]
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
        using fextends_noparam.intros(4)[OF \<open>AT (s1 \<in>\<^sub>s t1) \<in> set b\<close> mem_subterms_fm]
        using fextends.intros(1) by blast
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
  shows "realization (t1 -\<^sub>s t2) = realization t1 - realization t2"
  using assms
proof -
  from assms have mem_subterms_fm: "t1 -\<^sub>s t2 \<in> subterms_fm (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "elts (realization (t1 -\<^sub>s t2)) \<subseteq> elts (realization t1 - realization t2)"
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
    with s show "e \<in> elts (realization t1 - realization t2)"
      using \<open>sat b\<close> realization_if_AT_mem realization_if_AF_mem
      by auto
  qed
  moreover have "elts (realization t1 - realization t2) \<subseteq> elts (realization (t1 -\<^sub>s t2))"
  proof
    fix e assume "e \<in> elts (realization t1 - realization t2)"
    then obtain s where s:
      "e = realization s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> t1" "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realization
      using subterms_fmD(5,6)[OF mem_subterms_fm, THEN subterms_branch'_if_subterms_fm_last]
      by (auto split: if_splits)
    then have "AT (s \<in>\<^sub>s t1) \<in> set b"
      unfolding bgraph_def Let_def by auto
    moreover have "AF (s \<in>\<^sub>s t2) \<in> set b"
    proof -
      from \<open>sat b\<close> have "AT (s \<in>\<^sub>s t2) \<in> set b \<or> AF (s \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def using fextends_noparam.intros(5)[OF \<open>AT (s \<in>\<^sub>s t1) \<in> set b\<close> mem_subterms_fm]
        using fextends.intros(1) by blast
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


section \<open>Upper Bounding the Cardinality of a Branch\<close>

lemma Ex_fextends_params_if_in_params:
  assumes "wf_branch b"
  assumes "x \<in> params b"
  obtains t1 t2 bs b2 b1 where
    "extendss b (b2 @ b1)" "fextends_param t1 t2 x bs b1" "b2 \<in> bs" "extendss b1 [last b]"
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
    proof(induction rule: fextends.induct)
      case (1 bs b1)
      with extendss_mono have "b1 \<noteq> []"
        by fastforce
      with fextends_noparam_params_eq[OF \<open>fextends_noparam bs b1\<close> \<open>b2 \<in> bs\<close> this] 1 show ?case
        by (metis fextends.intros(1) extendss.intros(3))
    next
      case (2 t1 t2 y bs b1)
      show ?case
      proof(cases "x \<in> params b1")
        case True
        from 2 have "extendss (b2 @ b1) b1"
          using extendss.intros(3)[OF _ "2.prems"(1)] fextends.intros(2)[OF "2.hyps"]
          by (metis extendss.intros(1))
        with True 2 show ?thesis
          using extendss_trans by blast
      next
        case False
        from 2 have "b1 \<noteq> []"
          using extendss_mono by fastforce
        with fextends_paramD[OF "2"(1)] "2"(2-) have "params (b2 @ b1) = insert y (params b1)"
          unfolding params_def
          by (metis "2.hyps" fextends_param_params_eq params_def)
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
       extendss b (b2 @ b1) \<and> b2 \<in> bs \<and> fextends_param t1 t2 x bs b1  \<and> extendss b1 [\<phi>])"
    from \<open>extendss b [\<phi>]\<close> \<open>last b = \<phi>\<close>
    have "\<exists>t1 t2 bs b2 b1.
      extendss b (b2 @ b1) \<and> b2 \<in> bs \<and> fextends_param t1 t2 x bs b1 \<and> extendss b1 [\<phi>]"
      if "x \<in> params b" for x
      using that Ex_fextends_params_if_in_params[OF \<open>wf_branch b\<close> that] by metis
    then have ts_wd:
      "\<exists>bs b2 b1. extendss b (b2 @ b1) \<and> b2 \<in> bs \<and> fextends_param t1 t2 x bs b1 \<and> extendss b1 [\<phi>]"
      if "ts x = (t1, t2)" "x \<in> params b" for t1 t2 x
      using that unfolding ts_def by (smt (verit, ccfv_SIG) prod.case someI)
    with \<open>last b = \<phi>\<close> \<open>extendss b [\<phi>]\<close> have in_subterms_fm:
      "t1 \<in> subterms_fm \<phi>" "t2 \<in> subterms_fm \<phi>"
      if "ts x = (t1, t2)" "x \<in> params b" for t1 t2 x
      using that fextends_paramD
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
      "extendss xb1 [\<phi>]" "fextends_param t1 t2 x xbs2 xb1" "xb2 \<in> xbs2" "extendss b (xb2 @ xb1)"
      "extendss yb1 [\<phi>]" "fextends_param t1 t2 y ybs2 yb1" "yb2 \<in> ybs2" "extendss b (yb2 @ yb1)"
      unfolding inj_on_def by (metis ts_wd prod.exhaust)
    have "xb2 \<noteq> yb2"
      using x_y(5)[THEN fextends_paramD(1)] x_y(9)[THEN fextends_paramD(1)] x_y(1,6,10) 
      by auto
    moreover from x_y have "suffix (xb2 @ xb1) (yb2 @ yb1) \<or> suffix (yb2 @ yb1) (xb2 @ xb1)"
      using extendss_suffix suffix_same_cases by blast 
    then have "suffix (xb2 @ xb1) yb1 \<or> suffix (yb2 @ yb1) xb1"
      using x_y(5)[THEN fextends_paramD(1)] x_y(9)[THEN fextends_paramD(1)] x_y(1,6,10)
      by (auto simp: suffix_Cons)
    ultimately show False
      using fextends_paramD(1,5,6)[OF x_y(5)] fextends_paramD(1,5,6)[OF x_y(9)] x_y(6,10)
      by (auto dest!: set_mono_suffix)
  qed
  then show ?thesis
    using linorder_not_le \<open>last b = \<phi>\<close> by blast
qed

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
    \<union> case_prod Equal ` (subterms_fm \<phi> \<times> subterms_fm \<phi>)" for \<phi> :: "'a pset_fm"
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
    moreover have "inj_on (case_prod Elem) A" "inj_on (case_prod Equal) A"
      for A :: "('a pset_term \<times> 'a pset_term) set"
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

lemma lextends_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "lextends b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  apply(induction b' b rule: lextends_induct)
                      apply(fastforce simp: P_def dest: subfmsD)+
  done

lemma fextends_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "fextends bs b" "b' \<in> bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
proof(induction bs b rule: fextends.induct)
  case (1 bs' b)
  then show ?case
    apply(induction rule: fextends_noparam.induct)
        apply(fastforce simp: P_def dest: subfmsD)+
    done
next
  case (2 t1 t2 x bs' b)
  then show ?case
    apply(induction rule: fextends_param.induct)
    apply(fastforce simp: P_def dest: subfmsD)+
    done
qed

lemma extendss_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
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
    using lextends_not_literal_mem_subfms_last unfolding P_def by blast
next
  case (3 bs b2 b3 b1)
  then have "b2 \<noteq> []"
    using extendss_suffix suffix_bot.extremum_uniqueI by blast
  with 3 show ?case
    using fextends_not_literal_mem_subfms_last unfolding P_def by blast
qed simp

lemma card_not_literal_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card {\<phi> \<in> set b. \<not> is_literal \<phi>} \<le> 2 * card (subfms (last b))"
proof -
  from assms obtain \<phi> where "extendss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have [simp]: "last b = \<phi>"
    by simp
  have "{\<psi> \<in> set b. \<not> is_literal \<psi>} \<subseteq> subfms \<phi> \<union> Neg ` subfms \<phi>"
    using extendss_not_literal_mem_subfms_last[OF \<open>extendss b [\<phi>]\<close>]
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
    using assms card_Atoms_branch_if_wf_branch card_not_literal_branch_if_wf_branch
    by fastforce
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 4 * (?csts + ?csts^2)^2"
    using assms card_params_ub_if_wf_branch by auto
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 16 * ?csts^4"
  proof -
    have "1 \<le> ?csts"
      using finite_subterms_fm[THEN card_0_eq]
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


section \<open>The Decision Procedure\<close>

function (domintros) mlss_proc_branch :: "'a branch \<Rightarrow> bool" where
  "\<not> lin_sat b
  \<Longrightarrow> mlss_proc_branch b = mlss_proc_branch ((SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)) @ b)"
| "\<lbrakk> \<not> sat b; bopen b; lin_sat b \<rbrakk>
  \<Longrightarrow> mlss_proc_branch b = (\<forall>b' \<in> (SOME bs. fextends bs b). mlss_proc_branch (b' @ b))"
| "\<lbrakk> lin_sat b; sat b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = bclosed b"
| "\<lbrakk> lin_sat b; bclosed b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = True"
  by auto

lemma mlss_proc_branch_dom_if_wf_branch:
  fixes b :: "'a branch"
  assumes "wf_branch b"
  shows "mlss_proc_branch_dom b"
proof -
  define card_ub :: "'a branch \<Rightarrow> nat" where
    "card_ub \<equiv> \<lambda>b. 2 * card (subfms (last b)) + 16 * (card (subterms_fm (last b)))^4"
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
        bs' where "lin_sat b" "\<not> sat b" "fextends bs' b" "bs' \<noteq> {}"
                  "\<forall>b' \<in> bs'. set b \<subset> set (b' @ b)"
        unfolding sat_def lin_sat_def
        using fextends_strict_mono fextends_nonempty
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
          by (metis (mono_tags, lifting) fextends_strict_mono extendss.intros(1,3) someI_ex)
      qed
    qed (use mlss_proc_branch.domintros(3) sat_def in metis)
  qed
qed

definition mlss_proc :: "'a pset_fm \<Rightarrow> bool" where
  "mlss_proc \<phi> \<equiv> mlss_proc_branch [\<phi>]"


subsection \<open>Completeness\<close>

lemma (in open_branch) I\<^sub>s\<^sub>t_realization_eq_realization:
  assumes "sat b" "t \<in> subterms_branch b"
  shows "I\<^sub>s\<^sub>t (\<lambda>x. realization (Var x)) t = realization t"
  using assms
  by (induction t) (force simp: realization_simps dest: subterms_branchD)+

lemma mlss_proc_branch_complete:
  assumes "wf_branch b"
  assumes "\<not> mlss_proc_branch b"
  assumes "infinite (UNIV :: 'a set)"
  shows "\<exists>M :: 'a \<Rightarrow> V. interp I\<^sub>s\<^sub>a M (last b)"
proof -
  from mlss_proc_branch_dom_if_wf_branch[OF assms(1)] assms(1,2)
  show ?thesis
  proof(induction rule: mlss_proc_branch.pinduct)
    case (1 b)
    let ?b' = "SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)"
    from 1 have b': "lextends ?b' b" "set b \<subset> set (?b' @ b)"
      by (metis (no_types, lifting) not_lin_satD some_eq_imp)+
    with 1 have "wf_branch (?b' @ b)"
      using wf_branch_lextends by blast
    moreover from 1 b' have "\<not> mlss_proc_branch (?b' @ b)"
      by (simp add: mlss_proc_branch.psimps)
    ultimately obtain M where "interp I\<^sub>s\<^sub>a M (last (?b' @ b))"
      using 1 by blast
    with 1 show ?case
      using wf_branch_not_Nil by auto
  next
    case (2 b)
    let ?bs' = "SOME bs'. fextends bs' b"
    from 2 have bs': "fextends ?bs' b"
      by (meson sat_def tfl_some)
    with 2 obtain b' where b': "b' \<in> ?bs'" "\<not> mlss_proc_branch (b' @ b)"
      using mlss_proc_branch.psimps by blast
    with bs' have "wf_branch (b' @ b)"
      using wf_branch_extendss[OF \<open>wf_branch b\<close> extendss.intros(3)]
      using extendss.intros(1) by blast
    with 2 b' obtain M where "interp I\<^sub>s\<^sub>a M (last (b' @ b))"
      by blast
    with 2 show ?case
      using wf_branch_not_Nil by auto
  next
    case (3 b)
    then have "bopen b"
      by (simp add: mlss_proc_branch.psimps)
    interpret open_branch b
      apply(unfold_locales) using 3 assms(3) \<open>bopen b\<close> by auto
    define M where "M \<equiv> (\<lambda>x. realization (Var x))"
    have "interp I\<^sub>s\<^sub>a M \<phi>" if "\<phi> \<in> set b" for \<phi>
      using that
    proof(induction "size \<phi>" arbitrary: \<phi> rule: less_induct)
      case less
      then show ?case
      proof(cases \<phi>)
        case (Atom a)
        then show ?thesis
        proof(cases a)
          case (Elem s t)
          with Atom less have "s \<in> subterms_branch b" "t \<in> subterms_branch b"
            using AT_mem_subterms_branchD by blast+
          with Atom Elem less show ?thesis
            unfolding M_def
            using I\<^sub>s\<^sub>t_realization_eq_realization[OF \<open>sat b\<close>] realization_if_AT_mem by auto
        next
          case (Equal s t)
          with Atom less have "s \<in> subterms_branch b" "t \<in> subterms_branch b"
            using AT_eq_subterms_branchD by blast+
          with Atom Equal less satD(1)[OF \<open>sat b\<close>] show ?thesis
            unfolding M_def
            using I\<^sub>s\<^sub>t_realization_eq_realization[OF \<open>sat b\<close>] realization_if_AT_eq by auto
        qed
      next
        case (And \<phi>1 \<phi>2)
        with \<open>\<phi> \<in> set b\<close> \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b" "\<phi>2 \<in> set b"
          using lextends_fm.intros(1)[THEN lextends.intros(1)] by fastforce+
        with And less show ?thesis by simp
      next
        case (Or \<phi>1 \<phi>2)
        with \<open>\<phi> \<in> set b\<close> \<open>sat b\<close>[THEN satD(2)] have "\<phi>1 \<in> set b \<or> Neg \<phi>1 \<in> set b"
          using fextends_noparam.intros(1)[THEN fextends.intros(1)]
          by blast
        with less Or \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b \<or> \<phi>2 \<in> set b"
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
            with Atom Neg less have "s \<in> subterms_branch b" "t \<in> subterms_branch b"
              using AF_mem_subterms_branchD by blast+
            with Neg Atom Elem less show ?thesis
              unfolding M_def
              using I\<^sub>s\<^sub>t_realization_eq_realization realization_if_AF_mem \<open>sat b\<close> by auto
          next
            case (Equal s t)
            with Atom Neg less have "s \<in> subterms_branch b" "t \<in> subterms_branch b"
              using AF_eq_subterms_branchD by blast+
            with Neg Atom Equal less show ?thesis
              unfolding M_def
              using I\<^sub>s\<^sub>t_realization_eq_realization realization_if_AF_eq \<open>sat b\<close> by auto
          qed
        next
          case (And \<phi>1 \<phi>2)
          with Neg \<open>sat b\<close>[THEN satD(2)] less have "\<phi>1 \<in> set b \<or> Neg \<phi>1 \<in> set b"
            using fextends_noparam.intros(2)[THEN fextends.intros(1)] by blast
          with \<open>sat b\<close>[THEN satD(1), THEN lin_satD] Neg And less
          have "Neg \<phi>2 \<in> set b \<or> Neg \<phi>1 \<in> set b"
            using lextends_fm.intros(5)[THEN lextends.intros(1)] by fastforce
          with Neg And less show ?thesis by force
        next
          case (Or \<phi>1 \<phi>2)
          with \<open>\<phi> \<in> set b\<close> Neg \<open>sat b\<close>[THEN satD(1), THEN lin_satD]
          have "Neg \<phi>1 \<in> set b" "Neg \<phi>2 \<in> set b"
            using lextends_fm.intros(2)[THEN lextends.intros(1)] by fastforce+
          moreover have "size (Neg \<phi>1) < size \<phi>" "size (Neg \<phi>2) < size \<phi>"
            using Neg Or by simp_all
          ultimately show ?thesis using Neg Or less by force
        next
          case Neg': (Neg \<phi>'')
          with \<open>\<phi> \<in> set b\<close> Neg \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>'' \<in> set b"
            using lextends_fm.intros(7)[THEN lextends.intros(1)] by fastforce+
          with Neg Neg' less show ?thesis by simp
        qed
      qed
    qed
    then show ?case
      using last_in_set wf_branch wf_branch_not_Nil by blast
  next
    case (4 b)
    then show ?case by (simp add: mlss_proc_branch.psimps)
  qed
qed

theorem mlss_proc_complete:
  assumes "\<not> mlss_proc \<phi>"
  assumes "infinite (UNIV :: 'a set)"
  shows "\<exists>M :: 'a \<Rightarrow> V. interp I\<^sub>s\<^sub>a M \<phi>"
  using assms mlss_proc_branch_complete[of "[\<phi>]"]
  unfolding mlss_proc_def wf_branch_def
  using extendss.intros(1) by auto


subsection \<open>Soundness\<close>

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
  qed force+
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lextends_int.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  qed force+
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lextends_diff.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by force
  qed force+
next
  case (5 b' b)
  then show ?case
    by (induction rule: lextends_single.induct) force+
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lextends_eq.induct)
    case (1 t1 t2 branch l)
     with this(1,2)[THEN this(5)] show ?case
      by (cases l) auto
  next
    case (2 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) auto
  next
    case (3 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) auto
  next
    case (4 t1 t2 branch l)
    with this(1,2)[THEN this(5)] show ?case
      by (cases l) auto
  next
    case (5 s t branch s')
    with this(1,2)[THEN this(4)] show ?case by force
  qed
qed

lemma fextends_noparam_interp:
  assumes "fextends_noparam bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>b' \<in> bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
  by (induction rule: fextends_noparam.induct) force+

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

lemma fextends_param_interp:
  assumes "fextends_param t1 t2 x bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof (induction rule: fextends_param.induct)
  let ?bs'="{[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
             [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]}"
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
  then have "\<exists>b' \<in> ?bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using 1 y by auto
  moreover have "\<forall>\<psi> \<in> set b. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using "1"(7) \<open>x \<notin> vars_branch b\<close> interp_upd_eq_if_not_mem_vars_fm
    by (metis vars_fm_vars_branchI)
  ultimately show ?case
    by auto (metis fun_upd_same)+
qed

lemma fextends_interp:
  assumes "fextends bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof(induction rule: fextends.induct)
  case (1 bs' b)
  with fextends_noparam_interp[OF this(1)] have "\<exists>b' \<in> bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
    by blast
  with 1 show ?case
    by auto
next
  case (2 t1 t2 x bs b)
  then show ?case using fextends_param_interp by metis
qed

lemma wf_trancl_elts_rel: "wf ({(x, y). x \<in> elts y}\<^sup>+)"
  using foundation wf_trancl by blast

lemma trancl_elts_rel_not_refl: "(x, x) \<notin> {(x, y). x \<in> elts y}\<^sup>+"
  using wf_trancl_elts_rel by auto

lemma mem_trancl_elts_rel_if_member_seq:
  assumes "member_seq s cs t"
  assumes "cs \<noteq> []"
  assumes "\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a"
  shows "(I\<^sub>s\<^sub>t M s, I\<^sub>s\<^sub>t M t) \<in> {(x, y). x \<in> elts y}\<^sup>+"
  using assms
proof(induction rule: member_seq.induct)
  case (2 s s' u cs t)
  show ?case
  proof(cases cs)
    case Nil
    with 2 show ?thesis by auto
  next
    case (Cons c cs')
    with 2 have "(I\<^sub>s\<^sub>t M u, I\<^sub>s\<^sub>t M t) \<in> {(x, y). x \<in> elts y}\<^sup>+"
      by simp
    moreover from 2 have "I\<^sub>s\<^sub>a M (s \<in>\<^sub>s u)"
      by simp
    ultimately show ?thesis
      by (simp add: trancl_into_trancl2)
  qed
qed simp_all

lemma bclosed_interp_contr:
  assumes "bclosed b'"
  assumes "\<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
  shows "False"
  using assms
proof(induction rule: bclosed.induct)
  case (memberCycle cs b)
  then have "\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a"
    unfolding Atoms_def by fastforce
  from memberCycle obtain s where "member_seq s cs s"
    using member_cycle.elims(2) by blast
  with memberCycle \<open>\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a\<close> have "(I\<^sub>s\<^sub>t M s, I\<^sub>s\<^sub>t M s) \<in> {(x, y). x \<in> elts y}\<^sup>+"
    using mem_trancl_elts_rel_if_member_seq member_cycle.simps(2) by blast  
  with trancl_elts_rel_not_refl show ?case
    by blast
qed (use interp.simps(4) in \<open>fastforce+\<close>)

lemma mlss_proc_branch_sound:
  assumes "wf_branch b"
  assumes "\<forall>\<psi> \<in> set b. interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<not> mlss_proc_branch b"
proof
  assume "mlss_proc_branch b"
  with mlss_proc_branch_dom_if_wf_branch[OF \<open>wf_branch b\<close>]
  have "\<exists>b'. extendss b' b \<and> (\<exists>M. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>) \<and> bclosed b'"
    using assms
  proof(induction arbitrary: M rule: mlss_proc_branch.pinduct)
    case (1 b)
    let ?b' = "SOME b'. lextends b' b \<and> set b \<subset> set (b' @ b)"
    from 1 have b'_wd: "lextends ?b' b" "set b \<subset> set (?b' @ b)"
      by (metis (no_types, lifting) not_lin_satD someI_ex)+
    with \<open>wf_branch b\<close> have "wf_branch (?b' @ b)"
      using wf_branch_lextends by blast
    with 1 lextends_interp[OF b'_wd(1)] obtain b'' where
      "extendss b'' (?b' @ b)" "\<exists>M. \<forall>\<psi> \<in> set b''. interp I\<^sub>s\<^sub>a M \<psi>" "bclosed b''"
      by (fastforce simp: mlss_proc_branch.psimps)
    with 1 show ?case
      using extendss_trans extendss.intros(1,2)
      by (metis (no_types, lifting) not_lin_satD someI_ex)
  next
    case (2 b)
    let ?bs' = "SOME bs'. fextends bs' b"
    from 2 have bs'_wd: "fextends ?bs' b"
      by (meson sat_def tfl_some)
    with \<open>wf_branch b\<close> have wf_branch_b': "wf_branch (b' @ b)" if "b' \<in> ?bs'" for b'
      using that  extendss.intros(3) wf_branch_def by blast
    from fextends_interp[OF bs'_wd] 2 obtain M' b' where
      "b' \<in> ?bs'" "\<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M' \<psi>"
      by metis
    with 2 fextends_interp[OF \<open>fextends ?bs' b\<close>] wf_branch_b' obtain b'' where
      "b' \<in> ?bs'" "extendss b'' (b' @ b)"
      "\<exists>M. \<forall>\<psi> \<in> set b''. interp I\<^sub>s\<^sub>a M \<psi>" "bclosed b''"
      using mlss_proc_branch.psimps(2)[OF "2.hyps"(2-4,1)] by blast
    with 2 show ?case
      using extendss_trans extendss.intros(1,3)
      by (metis sat_def tfl_some)
  qed (use extendss.intros(1) mlss_proc_branch.psimps(3) in \<open>blast+\<close>)
  with bclosed_interp_contr show False by blast
qed

theorem mlss_proc_sound:
  assumes "interp I\<^sub>s\<^sub>a M \<phi>"
  shows "\<not> mlss_proc \<phi>"
  using assms mlss_proc_branch_sound[of "[\<phi>]"]
  unfolding mlss_proc_def wf_branch_def
  using extendss.intros(1) by auto

end