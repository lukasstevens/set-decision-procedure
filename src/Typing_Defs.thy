theory Typing_Defs
  imports Set_Semantics
begin

fun type_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_term \<Rightarrow> nat option" where
    "type_term _ (\<emptyset> n) = Some (Suc n)"
  | "type_term v (Var x) = Some (v x)"
  | "type_term v (Single t) = map_option Suc (type_term v t)"
  | "type_term v (s \<squnion>\<^sub>s t) = do {
                              ts <- type_term v s;
                              tt <- type_term v t;
                              if ts = tt \<and> ts \<noteq> 0 then Some ts else None
                            }"
  | "type_term v (s \<sqinter>\<^sub>s t) = do {
                              ts <- type_term v s;
                              tt <- type_term v t;
                              if ts = tt \<and> ts \<noteq> 0 then Some ts else None
                            }"
  | "type_term v (s -\<^sub>s t) = do {
                              ts <- type_term v s;
                              tt <- type_term v t;
                              if ts = tt \<and> ts \<noteq> 0 then Some ts else None
                            }"

declare type_term.simps[simp del]

consts types :: "('a \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<turnstile>" 45)

inductive types_pset_atom :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "\<lbrakk> type_term v s = Some l; type_term v t = Some l \<rbrakk> \<Longrightarrow> types_pset_atom v (s =\<^sub>s t)"
| "\<lbrakk> type_term v s = Some l; type_term v t = Some (Suc l)\<rbrakk> \<Longrightarrow> types_pset_atom v (s \<in>\<^sub>s t)"

adhoc_overloading types types_pset_atom

inductive_cases types_pset_atom_Member_cases:
  "v \<turnstile> s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s t1 -\<^sub>s t2" "v \<turnstile> s \<in>\<^sub>s Single t"

definition types_pset_fm :: "('a \<Rightarrow> nat) \<Rightarrow> 'a pset_fm \<Rightarrow> bool" where
  "types_pset_fm v \<phi> \<equiv> (\<forall>a \<in> atoms \<phi>. v \<turnstile> a)"

adhoc_overloading types types_pset_fm

definition urelem :: "'a pset_fm \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "urelem \<phi> t \<equiv> (\<exists>v. v \<turnstile> \<phi> \<and> t \<in> subterms \<phi> \<and> type_term v t = Some 0)"

end