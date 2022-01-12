theory Set_Proc                
  imports Main Logic ZFC_in_HOL.ZFC_in_HOL
begin

hide_const (open) ZFC_in_HOL.set

datatype 'a pset_term = 
  Empty (\<open>\<emptyset>\<close>)| Var 'a |
  Union "'a pset_term" "'a pset_term" (infixr \<open>\<squnion>\<^sub>s\<close> 50) |
  Inter "'a pset_term" "'a pset_term" (infixr \<open>\<sqinter>\<^sub>s\<close> 60) |
  Diff "'a pset_term" "'a pset_term"  (infixl \<open>-\<^sub>s\<close> 70) |
  Set "'a pset_term" "'a pset_term list"

datatype 'a pset_atom =
  Elem "'a pset_term" "'a pset_term" (infix \<open>\<in>\<^sub>s\<close> 45) | 
  Equal "'a pset_term" "'a pset_term" (infix \<open>\<approx>\<^sub>s\<close> 45) |
  Subset "'a pset_term" "'a pset_term" (infix \<open>\<sqsubseteq>\<^sub>s\<close> 45)

type_synonym 'a pset_literal = "bool \<times> 'a pset_atom"

definition "vdiff s1 s2 \<equiv> ZFC_in_HOL.set (elts s1 - elts s2)"

fun I\<^sub>s\<^sub>t :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_term \<Rightarrow> V" where
  "I\<^sub>s\<^sub>t v \<emptyset> = 0"
| "I\<^sub>s\<^sub>t v (Var x) = v x"
| "I\<^sub>s\<^sub>t v (s1 \<squnion>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<squnion> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 \<sqinter>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<sqinter> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 -\<^sub>s s2) = vdiff (I\<^sub>s\<^sub>t v s1) (I\<^sub>s\<^sub>t v s2)"
| "I\<^sub>s\<^sub>t v (Set s1 ss) = fold vinsert (map (I\<^sub>s\<^sub>t v) (s1 # ss)) 0"

fun I\<^sub>s\<^sub>a :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>a v (t1 \<in>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<in> elts (I\<^sub>s\<^sub>t v t2)"
| "I\<^sub>s\<^sub>a v (t1 \<approx>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 = I\<^sub>s\<^sub>t v t2"
| "I\<^sub>s\<^sub>a v (t1 \<sqsubseteq>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<le> I\<^sub>s\<^sub>t v t2"

definition I\<^sub>s\<^sub>l :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_literal \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>l v \<equiv> (\<lambda>(b, a). b \<longleftrightarrow> I\<^sub>s\<^sub>a v a)"

type_synonym 'a pset_fm = "'a pset_literal fm"
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

fun tlvl_terms_term :: "'a pset_term \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_term (Set t0 ts) = insert t0 (set ts)"
| "tlvl_terms_term x = {x}"

fun tlvl_terms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_atom (s \<in>\<^sub>s t) = tlvl_terms_term s \<union> tlvl_terms_term t"
| "tlvl_terms_atom (s \<approx>\<^sub>s t) = tlvl_terms_term s \<union> tlvl_terms_term t"
| "tlvl_terms_atom (s \<sqsubseteq>\<^sub>s t) = tlvl_terms_term s \<union> tlvl_terms_term t"

fun tlvl_terms_lit :: "'a pset_literal \<Rightarrow> 'a pset_term set" where
  "tlvl_terms_lit (_, a) = tlvl_terms_atom a"

definition tlvl_terms :: "'a branch \<Rightarrow> 'a pset_term set" where
  "tlvl_terms b \<equiv> \<Union>(tlvl_terms_lit ` Atoms (set b))"

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