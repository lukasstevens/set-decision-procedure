theory Set_Calculus
  imports Set_Semantics "HOL-Library.Sublist"
begin

section \<open>Closedness\<close>

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_atom list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((s' \<in>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_atom list \<Rightarrow> bool" where
  "member_cycle ((s \<in>\<^sub>s t) # cs) = member_seq s ((s \<in>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

inductive bclosed :: "'a branch \<Rightarrow> bool" where
  contr: "\<lbrakk> \<phi> \<in> set b; Neg \<phi> \<in> set b \<rbrakk> \<Longrightarrow> bclosed b"
| memEmpty: "AT (t \<in>\<^sub>s \<emptyset>) \<in> set b \<Longrightarrow> bclosed b"
| neqSelf: "AF (t \<approx>\<^sub>s t) \<in> set b \<Longrightarrow> bclosed b"
| memberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set b) \<rbrakk> \<Longrightarrow> bclosed b"

abbreviation "bopen branch \<equiv> \<not> bclosed branch"

section \<open>Saturating Expansion Rules\<close>

fun tlvl_terms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_atom (t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms_atom (t1 \<approx>\<^sub>s t2) = {t1, t2}"

fun subst_tlvl :: "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a pset_atom \<Rightarrow> 'a pset_atom" where
  "subst_tlvl t1 t2 (s1 \<in>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<in>\<^sub>s (if s2 = t1 then t2 else s2)"
| "subst_tlvl t1 t2 (s1 \<approx>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<approx>\<^sub>s (if s2 = t1 then t2 else s2)"

inductive sexpands_fm :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "And p q \<in> set b \<Longrightarrow> sexpands_fm [p, q] b"
| "Neg (Or p q) \<in> set b \<Longrightarrow> sexpands_fm [Neg p, Neg q] b"
| "\<lbrakk> Or p q \<in> set b; Neg p \<in> set b \<rbrakk> \<Longrightarrow> sexpands_fm [q] b"
| "\<lbrakk> Or p q \<in> set b; Neg q \<in> set b \<rbrakk> \<Longrightarrow> sexpands_fm [p] b"
| "\<lbrakk> Neg (And p q) \<in> set b; p \<in> set b \<rbrakk> \<Longrightarrow> sexpands_fm [Neg q] b"
| "\<lbrakk> Neg (And p q) \<in> set b; q \<in> set b \<rbrakk> \<Longrightarrow> sexpands_fm [Neg p] b"
| "Neg (Neg p) \<in> set b \<Longrightarrow> sexpands_fm [p] b"

inductive sexpands_un :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> sexpands_un [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_un [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_un [AT (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_un [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"

inductive sexpands_int :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> sexpands_int [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_int [AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_int [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_int [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"

inductive sexpands_diff :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> sexpands_diff [AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_diff [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_diff [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sexpands_diff [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"

inductive sexpands_single :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "Single t1 \<in> subterms_fm (last b) \<Longrightarrow> sexpands_single [AT (t1 \<in>\<^sub>s Single t1)] b"
| "AT (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> sexpands_single [AT (s \<approx>\<^sub>s t1)] b"
| "AF (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> sexpands_single [AF (s \<approx>\<^sub>s t1)] b"

inductive sexpands_eq :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AT l \<in> set b; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sexpands_eq [AT (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AF l \<in> set b; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sexpands_eq [AF (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AT l \<in> set b; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sexpands_eq [AT (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AF l \<in> set b; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sexpands_eq [AF (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk>
    \<Longrightarrow> sexpands_eq [AF (s \<approx>\<^sub>s s')] b"

fun polarise :: "bool \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "polarise True \<phi> = \<phi>"
| "polarise False \<phi> = Neg \<phi>"

lemma sexpands_eq_induct'[consumes 1, case_names subst neq]:
  assumes "sexpands_eq b' b"
  assumes "\<And>t1 t2 t1' t2' p l b. 
      \<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; polarise p (Atom l) \<in> set b;
       (t1', t2') \<in> {(t1, t2), (t2, t1)}; t1' \<in> tlvl_terms_atom l \<rbrakk>
      \<Longrightarrow> P [polarise p (Atom (subst_tlvl t1' t2' l))] b"
  assumes "\<And>s t s' b. \<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk> \<Longrightarrow> P [AF (s \<approx>\<^sub>s s')] b"
  shows "P b' b"
  using assms(1)
  apply(induction rule: sexpands_eq.induct)
  by (metis assms(2-) insertI1 insertI2 polarise.simps)+

inductive sexpands :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "sexpands_fm b' b \<Longrightarrow> sexpands b' b"
| "sexpands_un b' b \<Longrightarrow> sexpands b' b"
| "sexpands_int b' b \<Longrightarrow> sexpands b' b"
| "sexpands_diff b' b \<Longrightarrow> sexpands b' b"
| "sexpands_single b' b \<Longrightarrow> sexpands b' b"
| "sexpands_eq b' b \<Longrightarrow> sexpands b' b"

lemma sexpands_induct[consumes 1]:
  assumes "sexpands b' b"
  shows "
    (\<And>p q b. And p q \<in> set b \<Longrightarrow> P [p, q] b) \<Longrightarrow>
    (\<And>p q b. Neg (Or p q) \<in> set b \<Longrightarrow> P [Neg p, Neg q] b) \<Longrightarrow>
    (\<And>p q b. Or p q \<in> set b \<Longrightarrow> Neg p \<in> set b \<Longrightarrow> P [q] b) \<Longrightarrow>
    (\<And>p q b. Or p q \<in> set b \<Longrightarrow> Neg q \<in> set b \<Longrightarrow> P [p] b) \<Longrightarrow>
    (\<And>p q b. Neg (And p q) \<in> set b \<Longrightarrow> p \<in> set b \<Longrightarrow> P [Neg q] b) \<Longrightarrow>
    (\<And>p q b. Neg (And p q) \<in> set b \<Longrightarrow> q \<in> set b \<Longrightarrow> P [Neg p] b) \<Longrightarrow>
    (\<And>p q b. Neg (Neg p) \<in> set b \<Longrightarrow> P [p] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1),  AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>t1 b. Single t1 \<in> subterms_fm (last b) \<Longrightarrow> P [AT (t1 \<in>\<^sub>s Single t1)] b) \<Longrightarrow>
    (\<And>s t1 b. AT (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> P [AT (s \<approx>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b. AF (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> P [AF (s \<approx>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 \<approx>\<^sub>s t2) \<in> set b \<Longrightarrow> AT l \<in> set b \<Longrightarrow> t1 \<in> tlvl_terms_atom l \<Longrightarrow> P [AT (subst_tlvl t1 t2 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 \<approx>\<^sub>s t2) \<in> set b \<Longrightarrow> AF l \<in> set b \<Longrightarrow> t1 \<in> tlvl_terms_atom l \<Longrightarrow> P [AF (subst_tlvl t1 t2 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 \<approx>\<^sub>s t2) \<in> set b \<Longrightarrow> AT l \<in> set b \<Longrightarrow> t2 \<in> tlvl_terms_atom l \<Longrightarrow> P [AT (subst_tlvl t2 t1 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 \<approx>\<^sub>s t2) \<in> set b \<Longrightarrow> AF l \<in> set b \<Longrightarrow> t2 \<in> tlvl_terms_atom l \<Longrightarrow> P [AF (subst_tlvl t2 t1 l)] b) \<Longrightarrow>  
    (\<And>s t b s'. AT (s \<in>\<^sub>s t) \<in> set b \<Longrightarrow> AF (s' \<in>\<^sub>s t) \<in> set b \<Longrightarrow> P [AF (s \<approx>\<^sub>s s')] b) \<Longrightarrow> P b' b"
  using assms
  apply(induction rule: sexpands.induct)
  subgoal apply(induction rule: sexpands_fm.induct) by metis+
  subgoal apply(induction rule: sexpands_un.induct) by metis+
  subgoal apply(induction rule: sexpands_int.induct) by metis+
  subgoal apply(induction rule: sexpands_diff.induct) by metis+
  subgoal apply(induction rule: sexpands_single.induct) by metis+
  subgoal apply(induction rule: sexpands_eq.induct) by metis+
  done


section \<open>Fulfilling Expansion Rules\<close>

(* Maybe rename noparam thing*)
inductive fexpands_noparam :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set b;
     p \<notin> set b; Neg p \<notin> set b \<rbrakk>
    \<Longrightarrow> fexpands_noparam {[p], [Neg p]} b"
| "\<lbrakk> Neg (And p q) \<in> set b;
     Neg p \<notin> set b; p \<notin> set b \<rbrakk>
    \<Longrightarrow> fexpands_noparam {[Neg p], [p]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t1) \<notin> set b; AF (s \<in>\<^sub>s t1) \<notin> set b \<rbrakk>
    \<Longrightarrow> fexpands_noparam {[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> fexpands_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> fexpands_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"

inductive fexpands_param ::
  "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a \<Rightarrow> 'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" for t1 t2 x where
  "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set b; t1 \<in> subterms_fm (last b); t2 \<in> subterms_fm (last b);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b;
     \<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b;
     x \<notin> vars_branch b \<rbrakk>
    \<Longrightarrow> fexpands_param t1 t2 x {[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
                               [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]} b"

inductive_cases fexpands_param_cases[consumes 1]: "fexpands_param t1 t2 x bs' b"

lemma fexpands_paramD:
  assumes "fexpands_param t1 t2 x bs' b"
  shows "bs' = {[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
               [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]}"
        "AF (t1 \<approx>\<^sub>s t2) \<in> set b" "t1 \<in> subterms_fm (last b)" "t2 \<in> subterms_fm (last b)"
        "\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b"
        "\<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b"
        "x \<notin> vars_branch b"
  using fexpands_param.cases[OF assms] by metis+

inductive fexpands :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "fexpands_noparam bs' b \<Longrightarrow> fexpands bs' b"
| "fexpands_param t1 t2 x bs' b \<Longrightarrow> fexpands bs' b"

lemma fexpands_disjnt:
  assumes "fexpands bs' b" "b' \<in> bs'"
  shows "set b \<inter> set b' = {}"
  using assms
proof(induction bs' b rule: fexpands.induct)
  case (1 bs b)
  then show ?case
    by (induction rule: fexpands_noparam.induct) (auto intro: list.set_intros(1))
next
  case (2 t1 t2 x bs b)
  then show ?case
  proof(induction rule: fexpands_param.induct)
    case (1 b)
    from \<open>x \<notin> vars_branch b\<close>
    have "AT (Var x \<in>\<^sub>s t1) \<notin> set b" "AF (Var x \<in>\<^sub>s t1) \<notin> set b"
      unfolding vars_branch_def by auto
    with 1 show ?case
      by (auto intro: list.set_intros(1) simp: disjnt_iff vars_fm_vars_branchI)
  qed
qed

lemma fexpands_branch_not_Nil:
  assumes "fexpands bs' b" "b' \<in> bs'"
  shows "b' \<noteq> []"
  using assms
proof(induction bs' b rule: fexpands.induct)
  case (1 bs' b)
  then show ?case
    by (induction rule: fexpands_noparam.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case
    by (induction rule: fexpands_param.induct) auto
qed

lemma fexpands_nonempty: "fexpands bs' b \<Longrightarrow> bs' \<noteq> {}"
proof(induction rule: fexpands.induct)
  case (1 bs' b)
  then show ?case by (induction rule: fexpands_noparam.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case by (induction rule: fexpands_param.induct) auto
qed

lemma fexpands_strict_mono:
  assumes "fexpands bs' b" "b' \<in> bs'"
  shows "set b \<subset> set (b' @ b)"
  using fexpands_disjnt[OF assms] fexpands_branch_not_Nil[OF assms]
  by (simp add: less_le) (metis Un_Int_eq(1) set_empty2)

inductive_cases fexpands_cases[consumes 1, case_names no_param param]: "fexpands bs b"


section \<open>Expansion Closure\<close>

inductive expandss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "expandss b b"
| "sexpands b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss (b3 @ b2) b1"
| "fexpands bs b2 \<Longrightarrow> b3 \<in> bs \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss (b3 @ b2) b1"

lemma expandss_trans: "expandss b3 b2 \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss b3 b1"
  by (induction rule: expandss.induct) (auto simp: expandss.intros)

lemma expandss_suffix:
  "expandss b1 b2 \<Longrightarrow> suffix b2 b1"
  apply(induction rule: expandss.induct)
    apply(auto simp: suffix_appendI)
  done

lemmas expandss_mono = set_mono_suffix[OF expandss_suffix]

lemma expandss_last_eq[simp]:
  "expandss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  by (metis expandss_suffix last_appendR suffix_def)

end