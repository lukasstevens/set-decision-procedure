theory Find_Urelems
  imports Typing Suc_Theory
begin

abbreviation "SVar \<equiv> Suc_Theory.Var"
abbreviation "SEq \<equiv> Suc_Theory.Eq"
abbreviation "SNEq \<equiv> Suc_Theory.NEq"

fun constrs_term :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_term \<Rightarrow> 'b suc_atom list" where
  "constrs_term n (Var x) = [SEq (SVar (n (Var x))) (SVar (n (Var x)))]"
| "constrs_term n (\<emptyset> k) = [SEq (SVar (n (\<emptyset> k))) (Succ (Suc k) Zero)]"
| "constrs_term n (t1 \<squnion>\<^sub>s t2) =
    [SEq (SVar (n (t1 \<squnion>\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (t1 \<sqinter>\<^sub>s t2) =
    [SEq (SVar (n (t1 \<sqinter>\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (t1 -\<^sub>s t2) =
    [SEq (SVar (n (t1 -\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (Single t) =
    [SEq (SVar (n (Single t))) (Succ 1 (SVar (n t)))]
    @ constrs_term n t"
      
fun constrs_atom :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_atom \<Rightarrow> 'b suc_atom list" where
  "constrs_atom n (t1 =\<^sub>s t2) =
    [SEq (SVar (n t1)) (SVar (n t2))]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_atom n (t1 \<in>\<^sub>s t2) =
    [SEq (SVar (n t2)) (Succ 1 (SVar (n t1)))]
    @ constrs_term n t1 @ constrs_term n t2"

fun constrs_fm :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_fm \<Rightarrow> 'b suc_atom list" where
  "constrs_fm n (Atom a) = constrs_atom n a"
| "constrs_fm n (And p q) = constrs_fm n p @ constrs_fm n q"
| "constrs_fm n (Or p q) = constrs_fm n p @ constrs_fm n q"
| "constrs_fm n (Neg p) = constrs_fm n p"

lemma is_Succ_normal_constrs_term:
  "\<forall>a \<in> set (constrs_term n t). Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  apply(induction t)
       apply(auto)
  done

lemma is_Succ_normal_constrs_atom:
  "\<forall>a \<in> set (constrs_atom n a). Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  apply(cases a)
  using is_Succ_normal_constrs_term apply(auto)
  done

lemma is_Succ_normal_constrs_fm:
  "\<forall>a \<in> set (constrs_fm n \<phi>). Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  apply(induction \<phi>)
  using is_Succ_normal_constrs_atom apply(auto)
  done

lemma is_Var_Eq_Zero_if_is_NEq_constrs_term:
  "\<forall>a \<in> set (constrs_term n t). Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  apply(induction t)
       apply(auto)
  done

lemma is_Var_Eq_Zero_if_is_NEq_constrs_atom:
  "\<forall>a \<in> set (constrs_atom n a). Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  apply(cases a)
       using is_Var_Eq_Zero_if_is_NEq_constrs_term apply(auto)
  done

lemma is_Var_Eq_Zero_if_is_NEq_constrs_fm:
  "\<forall>a \<in> set (constrs_fm n \<phi>). Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  apply(induction \<phi>)
       using is_Var_Eq_Zero_if_is_NEq_constrs_atom apply(auto)
  done

lemma type_term_eq_Some_if_All_I_atom_constrs_term:
  assumes "(\<forall>e \<in> set (constrs_term n t). Suc_Theory.I_atom v e)"
  shows "type_term (\<lambda>x. v (n (Var x))) t = Some (v (n t))"
  using assms
  apply(induction t)
       apply(auto simp: type_term.simps)
  done

lemma types_pset_atom_if_All_I_atom_constrs_atom:
  assumes "(\<forall>e \<in> set (constrs_atom n a). Suc_Theory.I_atom v e)"
  shows "(\<lambda>x. v (n (Var x))) \<turnstile> a"
  using assms
  by (cases a) (auto simp: types_pset_atom.simps type_term_eq_Some_if_All_I_atom_constrs_term)

lemma types_pset_fm_if_All_I_atom_constrs_fm:
  assumes "(\<forall>e \<in> set (constrs_fm n \<phi>). Suc_Theory.I_atom v e)"
  shows "(\<lambda>x. v (n (Var x))) \<turnstile> \<phi>"
  using assms
  by (induction \<phi>)
     (auto intro: types_fmI types_pset_atom_if_All_I_atom_constrs_atom)

lemma I_atom_constrs_term_if_type_term_eq_Some:
  assumes "inj_on n T" "subterms t \<subseteq> T"
  assumes "type_term v t = Some k"
  shows "(\<forall>e \<in> set (constrs_term n t).
    Suc_Theory.I_atom (\<lambda>x. the (type_term v (inv_into T n x))) e)"
  using assms
  apply(induction t arbitrary: T k)
       apply(auto simp: type_term.simps split: Option.bind_splits if_splits)
  apply (metis inv_into_f_eq option.sel subset_iff subterms_refl)+
  done

lemma I_atom_constrs_atom_if_types_pset_atom:
  assumes "inj_on n T" "subterms a \<subseteq> T"
  assumes "v \<turnstile> a"
  shows "(\<forall>e \<in> set (constrs_atom n a).
    Suc_Theory.I_atom (\<lambda>x. the (type_term v (inv_into T n x))) e)"
  using assms I_atom_constrs_term_if_type_term_eq_Some
  by (cases a) (force simp: types_pset_atom.simps subsetD)+

lemma I_atom_constrs_fm_if_types_pset_fm:
  assumes "inj_on n T" "subterms \<phi> \<subseteq> T"
  assumes "v \<turnstile> \<phi>"
  shows "(\<forall>e \<in> set (constrs_fm n \<phi>).
    Suc_Theory.I_atom (\<lambda>x. the (type_term v (inv_into T n x))) e)"
  using assms
  by (induction \<phi>)
     (auto dest: types_fmD simp: I_atom_constrs_atom_if_types_pset_atom)


lemma inv_into_f_eq_if_subs:
  assumes "inj_on f B" "A \<subseteq> B" "y \<in> f ` A"
  shows "inv_into B f y = inv_into A f y"
  using assms inv_into_f_eq
  by (metis f_inv_into_f inv_into_into subset_eq)

lemma aux:
  assumes "z \<in> \<Union>(set_suc_atom ` set (constrs_term n t))"
  shows "z \<in> n ` subterms t"
  using assms
  apply(induction t)
       apply(auto)
  done

lemma min_on_vars_if_min_on_set_suc_atom_constrs_term:
  assumes "inj_on n (subterms t)"
  assumes "\<And>v z. \<lbrakk> \<forall>a \<in> set (constrs_term n t). Suc_Theory.I_atom v a;
                   z \<in> \<Union> (set_suc_atom ` set (constrs_term n t)) \<rbrakk>
                 \<Longrightarrow> v_min z \<le> v z"
  assumes "type_term (\<lambda>x. v_min (n (Var x))) t = Some lt" "type_term v t = Some lt'" "z \<in> vars t"
  shows "v_min (n (Var z)) \<le> v z"
proof -
  define v' where "v' \<equiv> \<lambda>x. the (type_term v (inv_into (subterms t) n x))"
  note I_atom_constrs_term_if_type_term_eq_Some[OF assms(1) _ assms(4)]
  then have "\<forall>e \<in> set (constrs_term n t). Suc_Theory.I_atom v' e"
    unfolding v'_def by blast
  with assms(2)[OF this, unfolded v'_def] assms(1,3-) show ?thesis
  proof(induction t arbitrary: lt lt')
    case (Var x)
    then show ?case
      by (auto dest!: type_term_eq_SomeD(1))
  next
    case (Union t1 t2)
    then have "subterms t1 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)"
      by auto
    note inv_into_simps =
      this[THEN inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 \<squnion>\<^sub>s t2))\<close> _ aux]]
    with Union have "v_min z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by simp metis
    with Union show ?thesis
      by (auto simp: inj_on_subset dest!: type_term_eq_SomeD(2))
  next
    case (Inter t1 t2)
    then have "subterms t1 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)"
      by auto
    note inv_into_simps =
      this[THEN inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 \<sqinter>\<^sub>s t2))\<close> _ aux]]
    with Inter have "v_min z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by simp metis
    with Inter show ?thesis
      by (auto simp: inj_on_subset dest!: type_term_eq_SomeD(3))
  next
    case (Diff t1 t2)
    then have "subterms t1 \<subseteq> subterms (t1 -\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 -\<^sub>s t2)"
      by auto
    note inv_into_simps =
      this[THEN inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 -\<^sub>s t2))\<close> _ aux]]
    with Diff have "v_min z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by simp metis
    with Diff show ?thesis
      by (auto simp: inj_on_subset dest!: type_term_eq_SomeD(4))
  next
    case (Single t)
    then have "subterms t \<subseteq> subterms (Single t)"
      by auto
    note inv_into_simps =
      this[THEN inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (Single t))\<close> _ aux]]
    with Single have "v_min z \<le> the (type_term v (inv_into (subterms t) n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t))" for z
      using that by simp metis
    with Single show ?thesis
      by (auto simp: inj_on_subset dest!: type_term_eq_SomeD(5))
  qed simp
qed

lemma min_on_vars_if_min_on_set_suc_atom_constrs_atom:
  fixes a :: "'a pset_atom"
  assumes "inj_on n (subterms a)"
  assumes "\<And>v z. \<lbrakk> \<forall>e \<in> set (constrs_atom n a). Suc_Theory.I_atom v e;
                   z \<in> \<Union> (set_suc_atom ` set (constrs_atom n a)) \<rbrakk>
                 \<Longrightarrow> v_min z \<le> v z"
  assumes "(\<lambda>x. v_min (n (Var x))) \<turnstile> a" "v \<turnstile> a" "z \<in> vars a"
  shows "v_min (n (Var z)) \<le> v z"
proof(cases a)
  case (Elem s t)
  with assms have "inj_on n (subterms s)" "inj_on n (subterms t)"
    by (auto simp: inj_on_Un)
  note this[THEN min_on_vars_if_min_on_set_suc_atom_constrs_term]
  moreover have "v_min z \<le> v z"
    if "\<forall>e \<in> set (constrs_term n u). Suc_Theory.I_atom v e"
       "z \<in> \<Union> (set_suc_atom ` set (constrs_term n u))"
       "u \<in> {s, t}" for u v z
    using that assms(2) Elem
    apply(auto)
  
  with assms(3-) Elem show ?thesis sorry
next
  case (Equal x21 x22)
  then show ?thesis sorry
qed
  using min_on_vars_if_min_on_set_suc_atom_constrs_term
   apply(auto simp: types_pset_atom.simps )
  sledgehammer

lemma
  assumes "inj_on n (subterms \<phi>)"
  assumes "Suc_Theory.solve (Suc_Theory.elim_NEq_Zero (constrs_fm n \<phi>)) = Some ss"
  shows "(\<lambda>x. Suc_Theory.assign ss (n (Var x))) \<turnstile> \<phi>"
    and "\<And>v z. \<lbrakk> v \<turnstile> \<phi>; z \<in> vars \<phi> \<rbrakk> \<Longrightarrow> Suc_Theory.assign ss (n (Var z)) \<le> v z"
proof -
  note I_atom_assign_if_solve_elim_NEq_Zero_Some[OF _ _ assms(2)]
  then have "\<forall>e \<in> set (constrs_fm n \<phi>). Suc_Theory.I_atom (Suc_Theory.assign ss) e"
    using is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm by blast
  note types_pset_fm_if_All_I_atom_constrs_fm[OF this]
  then show "(\<lambda>x. Suc_Theory.assign ss (n (Var x))) \<turnstile> \<phi>" .

  note I_atom_assign_minimal_if_solve_elim_NEq_Zero_Some[OF _ _ assms(2)]
  then have "Suc_Theory.assign ss z \<le> v z"
    if "\<forall>a \<in> set (constrs_fm n \<phi>). Suc_Theory.I_atom v a"
       "z \<in> \<Union> (set_suc_atom ` set (constrs_fm n \<phi>))" for v z
    using that is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm by blast

  

lemma aux2:
  assumes "\<And>z. z \<in> vars t \<Longrightarrow> v_min z \<le> v z"
  assumes "type_term v_min t = Some k'" "type_term v t = Some k"
  shows "k' \<le> k"
  using assms
  apply(induction t arbitrary: k' k)
       apply(auto simp: type_term.simps split: if_splits Option.bind_splits)
  done

lemma
  assumes "inj_on n (subterms t)"
  assumes "Suc_Theory.solve (Suc_Theory.elim_NEq_Zero (constrs_term n t)) = Some ss"
  assumes "s \<in> subterms t"
  assumes "type_term v t = Some kt"
  shows "\<exists>k' k. type_term v s = Some k' \<and> type_term (\<lambda>x. Suc_Theory.assign ss (n (Var x))) s = Some k
              \<and> k \<le> k'"
proof -
  let ?v' = "\<lambda>x. the (type_term v (inv_into (subterms t) n x))"
  note All_I_atom_constrs_term_if_type_term_eq_Some[OF assms(1) _ assms(4)]
  then have "(\<forall>e \<in> set (constrs_term n t). Suc_Theory.I_atom ?v' e)"
    by blast  
  note I_atom_assign_minimal_if_solve_elim_NEq_Zero_Some[OF _ _ assms(2) this]
  then have "Suc_Theory.assign ss z \<le> ?v' z"
    if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t))" for z
    using is_Succ_normal_constrs_term is_Var_Eq_Zero_if_is_NEq_constrs_term
    using that by blast
  then have "Suc_Theory.assign ss (n (Var z)) \<le> v z"
    if "z \<in> vars t" for z
    using that \<open>inj_on n (subterms t)\<close> \<open>type_term v t = Some kt\<close>
  proof(induction t arbitrary: kt)
    case (Var x)
    then show ?case by (simp add: type_term_eq_SomeD(1))
  next
    case (Union t1 t2)
    have "subterms t1 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)"
      by auto
    note inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 \<squnion>\<^sub>s t2))\<close> _ aux]
    note this[OF \<open>subterms t1 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)\<close>] this[OF \<open>subterms t2 \<subseteq> subterms (t1 \<squnion>\<^sub>s t2)\<close>]
    with Union have "Suc_Theory.assign ss z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by auto metis+
    with Union show ?case
      by (auto simp: inj_on_Un dest: type_term_eq_SomeD)
  next
    case (Inter t1 t2)
    have "subterms t1 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)"
      by auto
    note inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 \<sqinter>\<^sub>s t2))\<close> _ aux]
    note this[OF \<open>subterms t1 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)\<close>] this[OF \<open>subterms t2 \<subseteq> subterms (t1 \<sqinter>\<^sub>s t2)\<close>]
    with Inter have "Suc_Theory.assign ss z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by auto metis+
    with Inter show ?case
      by (auto simp: inj_on_Un dest: type_term_eq_SomeD)
  next
    case (Diff t1 t2)
    have "subterms t1 \<subseteq> subterms (t1 -\<^sub>s t2)" "subterms t2 \<subseteq> subterms (t1 -\<^sub>s t2)"
      by auto
    note inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (t1 -\<^sub>s t2))\<close> _ aux]
    note this[OF \<open>subterms t1 \<subseteq> subterms (t1 -\<^sub>s t2)\<close>] this[OF \<open>subterms t2 \<subseteq> subterms (t1 -\<^sub>s t2)\<close>]
    with Diff have "Suc_Theory.assign ss z \<le> the (type_term v (inv_into (subterms t') n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t'))" "t' \<in> {t1, t2}" for z t'
      using that by auto metis+
    with Diff show ?case
      by (auto simp: inj_on_Un dest: type_term_eq_SomeD)
  next
    case (Single t)
    have "subterms t \<subseteq> subterms (Single t)"
      by auto
    note inv_into_f_eq_if_subs[OF \<open>inj_on n (subterms (Single t))\<close> this aux]
    with Single have "Suc_Theory.assign ss z \<le> the (type_term v (inv_into (subterms t) n z))"
      if "z \<in> \<Union> (set_suc_atom ` set (constrs_term n t))" for z
      using that by auto metis+
    with Single show ?case
      by (auto simp: inj_on_Un dest: type_term_eq_SomeD)
  qed simp
  with \<open>s \<in> subterms t\<close> have "Suc_Theory.assign ss (n (Var z)) \<le> v z"
    if "z \<in> vars s" for z
    using that mem_vars_term_if_mem_subterms_term by metis
  moreover obtain ks where "type_term (\<lambda>x. Suc_Theory.assign ss (n (Var x))) s = Some ks"
    using Ex_type_term_assign_if_solve_constrs_term[OF assms(2)]
    using type_term_if_mem_subterms[OF \<open>s \<in> subterms t\<close>] by blast
  moreover obtain k's where "type_term v s = Some k's"
    using type_term_if_mem_subterms[OF \<open>s \<in> subterms t\<close> assms(4)] by blast
  ultimately show ?thesis
    using aux2 by force
qed

hide_const (open) SVar SEq SNEq

end