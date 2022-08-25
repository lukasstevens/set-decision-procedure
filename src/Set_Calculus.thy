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

section \<open>Saturation Rules\<close>

fun tlvl_terms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_atom (t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms_atom (t1 \<approx>\<^sub>s t2) = {t1, t2}"

fun subst_tlvl :: "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a pset_atom \<Rightarrow> 'a pset_atom" where
  "subst_tlvl t1 t2 (s1 \<in>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<in>\<^sub>s (if s2 = t1 then t2 else s2)"
| "subst_tlvl t1 t2 (s1 \<approx>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<approx>\<^sub>s (if s2 = t1 then t2 else s2)"

inductive sextends_fm :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "And p q \<in> set b \<Longrightarrow> sextends_fm [p, q] b"
| "Neg (Or p q) \<in> set b \<Longrightarrow> sextends_fm [Neg p, Neg q] b"
| "\<lbrakk> Or p q \<in> set b; Neg p \<in> set b \<rbrakk> \<Longrightarrow> sextends_fm [q] b"
| "\<lbrakk> Or p q \<in> set b; Neg q \<in> set b \<rbrakk> \<Longrightarrow> sextends_fm [p] b"
| "\<lbrakk> Neg (And p q) \<in> set b; p \<in> set b \<rbrakk> \<Longrightarrow> sextends_fm [Neg q] b"
| "\<lbrakk> Neg (And p q) \<in> set b; q \<in> set b \<rbrakk> \<Longrightarrow> sextends_fm [Neg p] b"
| "Neg (Neg p) \<in> set b \<Longrightarrow> sextends_fm [p] b"

inductive sextends_un :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> sextends_un [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_un [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_un [AT (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_un [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"

inductive sextends_int :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> sextends_int [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_int [AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_int [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_int [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"

inductive sextends_diff :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> sextends_diff [AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_diff [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_diff [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b) \<rbrakk>
    \<Longrightarrow> sextends_diff [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"

inductive sextends_single :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "Single t1 \<in> subterms_fm (last b) \<Longrightarrow> sextends_single [AT (t1 \<in>\<^sub>s Single t1)] b"
| "AT (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> sextends_single [AT (s \<approx>\<^sub>s t1)] b"
| "AF (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> sextends_single [AF (s \<approx>\<^sub>s t1)] b"

inductive sextends_eq :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AT l \<in> set b; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sextends_eq [AT (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AF l \<in> set b; t1 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sextends_eq [AF (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AT l \<in> set b; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sextends_eq [AT (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; AF l \<in> set b; t2 \<in> tlvl_terms_atom l \<rbrakk>
    \<Longrightarrow> sextends_eq [AF (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk>
    \<Longrightarrow> sextends_eq [AF (s \<approx>\<^sub>s s')] b"

fun polarise :: "bool \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "polarise True \<phi> = \<phi>"
| "polarise False \<phi> = Neg \<phi>"

lemma sextends_eq_induct'[consumes 1, case_names subst neq]:
  assumes "sextends_eq b' b"
  assumes "\<And>t1 t2 t1' t2' p l b. 
      \<lbrakk> AT (t1 \<approx>\<^sub>s t2) \<in> set b; polarise p (Atom l) \<in> set b;
       (t1', t2') \<in> {(t1, t2), (t2, t1)}; t1' \<in> tlvl_terms_atom l \<rbrakk>
      \<Longrightarrow> P [polarise p (Atom (subst_tlvl t1' t2' l))] b"
  assumes "\<And>s t s' b. \<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk> \<Longrightarrow> P [AF (s \<approx>\<^sub>s s')] b"
  shows "P b' b"
  using assms(1)
  apply(induction rule: sextends_eq.induct)
  by (metis assms(2-) insertI1 insertI2 polarise.simps)+

inductive sextends :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "sextends_fm b' b \<Longrightarrow> sextends b' b"
| "sextends_un b' b \<Longrightarrow> sextends b' b"
| "sextends_int b' b \<Longrightarrow> sextends b' b"
| "sextends_diff b' b \<Longrightarrow> sextends b' b"
| "sextends_single b' b \<Longrightarrow> sextends b' b"
| "sextends_eq b' b \<Longrightarrow> sextends b' b"

lemma sextends_induct[consumes 1]:
  assumes "sextends b' b"
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
  apply(induction rule: sextends.induct)
  subgoal apply(induction rule: sextends_fm.induct) by metis+
  subgoal apply(induction rule: sextends_un.induct) by metis+
  subgoal apply(induction rule: sextends_int.induct) by metis+
  subgoal apply(induction rule: sextends_diff.induct) by metis+
  subgoal apply(induction rule: sextends_single.induct) by metis+
  subgoal apply(induction rule: sextends_eq.induct) by metis+
  done


section \<open>Fulfilling Rules\<close>

(* Maybe rename noparam thing*)
inductive fextends_noparam :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set b;
     p \<notin> set b; Neg p \<notin> set b \<rbrakk>
    \<Longrightarrow> fextends_noparam {[p], [Neg p]} b"
| "\<lbrakk> Neg (And p q) \<in> set b;
     Neg p \<notin> set b; p \<notin> set b \<rbrakk>
    \<Longrightarrow> fextends_noparam {[Neg p], [p]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t1) \<notin> set b; AF (s \<in>\<^sub>s t1) \<notin> set b \<rbrakk>
    \<Longrightarrow> fextends_noparam {[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> fextends_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms_fm (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> fextends_noparam {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"

inductive fextends_param ::
  "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a \<Rightarrow> 'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" for t1 t2 x where
  "\<lbrakk> AF (t1 \<approx>\<^sub>s t2) \<in> set b; t1 \<in> subterms_fm (last b); t2 \<in> subterms_fm (last b);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b;
     \<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b;
     x \<notin> vars_branch b \<rbrakk>
    \<Longrightarrow> fextends_param t1 t2 x {[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
                               [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]} b"

inductive_cases fextends_param_cases[consumes 1]: "fextends_param t1 t2 x bs' b"

lemma fextends_paramD:
  assumes "fextends_param t1 t2 x bs' b"
  shows "bs' = {[AT (pset_term.Var x \<in>\<^sub>s t1), AF (pset_term.Var x \<in>\<^sub>s t2)],
               [AT (pset_term.Var x \<in>\<^sub>s t2), AF (pset_term.Var x \<in>\<^sub>s t1)]}"
        "AF (t1 \<approx>\<^sub>s t2) \<in> set b" "t1 \<in> subterms_fm (last b)" "t2 \<in> subterms_fm (last b)"
        "\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b"
        "\<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b"
        "x \<notin> vars_branch b"
  using fextends_param.cases[OF assms] by metis+

(* rename into ffextends (fulfilling rules) *)
inductive fextends :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "fextends_noparam bs' b \<Longrightarrow> fextends bs' b"
| "fextends_param t1 t2 x bs' b \<Longrightarrow> fextends bs' b"

lemma fextends_disjnt:
  assumes "fextends bs' b" "b' \<in> bs'"
  shows "set b \<inter> set b' = {}"
  using assms
proof(induction bs' b rule: fextends.induct)
  case (1 bs b)
  then show ?case
    by (induction rule: fextends_noparam.induct) (auto intro: list.set_intros(1))
next
  case (2 t1 t2 x bs b)
  then show ?case
  proof(induction rule: fextends_param.induct)
    case (1 b)
    from \<open>x \<notin> vars_branch b\<close>
    have "AT (Var x \<in>\<^sub>s t1) \<notin> set b" "AF (Var x \<in>\<^sub>s t1) \<notin> set b"
      unfolding vars_branch_def by auto
    with 1 show ?case
      by (auto intro: list.set_intros(1) simp: disjnt_iff vars_fm_vars_branchI)
  qed
qed

lemma fextends_branch_not_Nil:
  assumes "fextends bs' b" "b' \<in> bs'"
  shows "b' \<noteq> []"
  using assms
proof(induction bs' b rule: fextends.induct)
  case (1 bs' b)
  then show ?case
    by (induction rule: fextends_noparam.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case
    by (induction rule: fextends_param.induct) auto
qed

lemma fextends_nonempty: "fextends bs' b \<Longrightarrow> bs' \<noteq> {}"
proof(induction rule: fextends.induct)
  case (1 bs' b)
  then show ?case by (induction rule: fextends_noparam.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case by (induction rule: fextends_param.induct) auto
qed

lemma fextends_strict_mono:
  assumes "fextends bs' b" "b' \<in> bs'"
  shows "set b \<subset> set (b' @ b)"
  using fextends_disjnt[OF assms] fextends_branch_not_Nil[OF assms]
  by (simp add: less_le) (metis Un_Int_eq(1) set_empty2)

inductive_cases fextends_cases[consumes 1, case_names no_param param]: "fextends bs b"


section \<open>Extension Closure\<close>

inductive extendss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "extendss b b"
| "sextends b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"
| "fextends bs b2 \<Longrightarrow> b3 \<in> bs \<Longrightarrow> extendss b2 b1 \<Longrightarrow> extendss (b3 @ b2) b1"

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

end