theory Set_Calculus
  imports Set_Semantics "HOL-Library.Sublist"
begin

section \<open>Linear Extension\<close>

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_atom list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((s' \<in>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_atom list \<Rightarrow> bool" where
  "member_cycle ((s \<in>\<^sub>s t) # cs) = member_seq s ((s \<in>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

fun tlvl_terms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_atom (t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms_atom (t1 \<approx>\<^sub>s t2) = {t1, t2}"

fun subst_tlvl :: "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a pset_atom \<Rightarrow> 'a pset_atom" where
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


section \<open>Non-Linear Extension\<close>

inductive extends_noparam :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set branch;
     p \<notin> set branch; Neg p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam {[p], [Neg p]} branch"
| "\<lbrakk> Neg (And p q) \<in> set branch;
     Neg p \<notin> set branch; p \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam {[Neg p], [p]} branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set branch; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t1) \<notin> set branch; AF (s \<in>\<^sub>s t1) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam {[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]} branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} branch"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set branch; t1 -\<^sub>s t2 \<in> subterms_fm (last branch);
     AT (s \<in>\<^sub>s t2) \<notin> set branch; AF (s \<in>\<^sub>s t2) \<notin> set branch \<rbrakk>
    \<Longrightarrow> extends_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} branch"

inductive extends_param ::
  "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a \<Rightarrow> 'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" for t1 t2 x where
  "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set branch; t1 \<in> subterms_fm (last branch); t2 \<in> subterms_fm (last branch);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set branch \<and> AF (x \<in>\<^sub>s t2) \<in> set branch;
     \<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set branch \<and> AF (x \<in>\<^sub>s t1) \<in> set branch;
     x \<notin> vars_branch branch \<rbrakk>
    \<Longrightarrow> extends_param t1 t2 x {[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
                               [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]} branch"

inductive_cases extends_param_cases[consumes 1]: "extends_param t1 t2 x bs b"

lemma extends_paramD:
  assumes "extends_param t1 t2 x bs b"
  shows "bs = {[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
               [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]}"
        "AF (t1 \<approx>\<^sub>s t2) \<in> set b" "t1 \<in> subterms_fm (last b)" "t2 \<in> subterms_fm (last b)"
        "\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b"
        "\<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b"
        "x \<notin> vars_branch b"
  using extends_param.cases[OF assms] by metis+

inductive extends :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "extends_noparam bs b \<Longrightarrow> extends bs b"
| "extends_param t1 t2 x bs b \<Longrightarrow> extends bs b"

lemma extends_disjnt:
  assumes "extends bs' b" "b' \<in> bs'"
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
  assumes "extends bs' b" "b' \<in> bs'"
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

lemma extends_nonempty: "extends bs' b \<Longrightarrow> bs' \<noteq> {}"
proof(induction rule: extends.induct)
  case (1 bs b)
  then show ?case by (induction rule: extends_noparam.induct) auto
next
  case (2 t1 t2 x bs b)
  then show ?case by (induction rule: extends_param.induct) auto
qed

lemma extends_strict_mono:
  assumes "extends bs' b" "b' \<in> bs'"
  shows "set b \<subset> set (b' @ b)"
  using extends_disjnt[OF assms] extends_branch_not_Nil[OF assms]
  by (simp add: less_le) (metis Un_Int_eq(1) set_empty2)

inductive_cases extends_cases[consumes 1, case_names no_param param]: "extends bs b"


section \<open>Extension Closure\<close>

inductive extendss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "extendss b b"
| "lextends b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"
| "extends bs b2 \<Longrightarrow> b3 \<in> bs \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"

lemma extendss_trans: "extendss b3 b2 \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss b3 b1"
  by (induction rule: extendss.induct) (auto simp: extendss.intros)

lemma extendss_suffix:
  "extendss b1 b2 \<Longrightarrow> suffix b2 b1"
  apply(induction rule: extendss.induct)
    apply(auto simp: suffix_appendI)
  done

lemmas extendss_mono = set_mono_suffix[OF extendss_suffix]

lemma extendss_last_eq[simp]:
  "extendss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  by (metis extendss_suffix last_appendR suffix_def)


section \<open>Closedness\<close>

inductive bclosed :: "'a branch \<Rightarrow> bool" where
  contr: "\<lbrakk> \<phi> \<in> set branch; Neg \<phi> \<in> set branch \<rbrakk> \<Longrightarrow> bclosed branch"
| elemEmpty: "AT (t \<in>\<^sub>s \<emptyset>) \<in> set branch \<Longrightarrow> bclosed branch"
| neqSelf: "AF (t \<approx>\<^sub>s t) \<in> set branch \<Longrightarrow> bclosed branch"
| memberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set branch) \<rbrakk> \<Longrightarrow> bclosed branch"

abbreviation "bopen branch \<equiv> \<not> bclosed branch"

end