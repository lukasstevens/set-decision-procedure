theory Typing
  imports Set_Calculus
begin

section \<open>Typing\<close>

(*
datatype 'a lvl = is_GT: GT 'a | EQ 'a

fun eq_lvl :: "nat lvl \<Rightarrow> nat lvl \<Rightarrow> nat lvl option" where
  "eq_lvl (GT l) (GT k) = Some (GT (max l k))"
| "eq_lvl (GT l) (EQ k) = (if k > l then Some (EQ k) else None)"
| "eq_lvl (EQ k) (GT l) = (if k > l then Some (EQ k) else None)"
| "eq_lvl (EQ l) (EQ k) = (if l = k then Some (EQ k) else None)"

fun suc_lvl :: "nat lvl \<Rightarrow> nat lvl \<Rightarrow> bool" where
  "suc_lvl (GT l) (GT k) \<longleftrightarrow> True"
| "suc_lvl (GT l) (EQ k) \<longleftrightarrow> k \<ge> Suc (Suc l)"
| "suc_lvl (EQ l) (GT k) \<longleftrightarrow> l \<ge> k"
| "suc_lvl (EQ l) (EQ k) \<longleftrightarrow> Suc l = k"
*)

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

consts types :: "('a \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> bool" ("_ \<turnstile> _" 45)

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

lemma is_Var_if_type_term_0: "type_term v t = Some 0 \<Longrightarrow> is_Var t"
  by (induction t) (auto simp: type_term.simps split: if_splits Option.bind_splits)

lemma is_Var_if_urelem: "urelem \<phi> t \<Longrightarrow> is_Var t"
  unfolding urelem_def using is_Var_if_type_term_0 by blast

lemma types_fmD:
  "v \<turnstile> And p q \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> And p q \<Longrightarrow> v \<turnstile> q"
  "v \<turnstile> Or p q \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> Or p q \<Longrightarrow> v \<turnstile> q"
  "v \<turnstile> Neg p \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> Atom a \<Longrightarrow> v \<turnstile> a"
  unfolding types_pset_fm_def using fm.set_intros by auto

lemma types_fmI:
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> q \<Longrightarrow> v \<turnstile> And p q"
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> q \<Longrightarrow> v \<turnstile> Or p q"
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> Neg p"
  "v \<turnstile> a \<Longrightarrow> v \<turnstile> Atom a"
  unfolding types_pset_fm_def using fm.set_intros by auto


(*
lemma type_term_Elem_the_I:
  assumes "type_term v s = Some ls"
          "\<not> Option.is_none (type_term v t)" "suc_lvl ls (the (type_term v t))"
  shows "v \<turnstile> s \<in>\<^sub>s t"
  using assms types_pset_atom.intros(2)
  by (metis Option.is_none_def option.exhaust_sel) *)

(*
lemma type_term_suc_lvl_D:
  assumes "type_term v s = Some ls" "type_term v (f t1 t2) = Some lt" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  assumes "suc_lvl ls lt"
  shows "\<not> Option.is_none (type_term v t1) \<and> suc_lvl ls (the (type_term v t1))"
        "\<not> Option.is_none (type_term v t2) \<and> suc_lvl ls (the (type_term v t2))"
  using assms
  by (fastforce simp: type_term.simps dest: suc_lvlD_if_eq_lvl split: if_splits Option.bind_splits)+
*)

lemma types_pset_atom_Member_D:
  assumes "v \<turnstile> s \<in>\<^sub>s f t1 t2" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  shows "v \<turnstile> s \<in>\<^sub>s t1" "v \<turnstile> s \<in>\<^sub>s t2"
proof -
  from assms obtain ls where
    "type_term v s = Some ls" "type_term v (f t1 t2) = Some (Suc ls)"
    using types_pset_atom.simps by fastforce
  with assms have "v \<turnstile> s \<in>\<^sub>s t1 \<and> v \<turnstile> s \<in>\<^sub>s t2"
    by (auto simp: type_term.simps types_pset_atom.simps split: if_splits Option.bind_splits)
  then show "v \<turnstile> s \<in>\<^sub>s t1" "v \<turnstile> s \<in>\<^sub>s t2"
    by blast+
qed

lemmas types_pset_atom_Member_Union_D[simplified] = types_pset_atom_Member_D[where ?f="(\<squnion>\<^sub>s)"]
   and types_pset_atom_Member_Inter_D[simplified] = types_pset_atom_Member_D[where ?f="(\<sqinter>\<^sub>s)"]
   and types_pset_atom_Member_Diff_D[simplified] = types_pset_atom_Member_D[where ?f="(-\<^sub>s)"]

lemma type_term_eq_if_mem_subterms:
  fixes \<phi> :: "'a pset_fm"
  assumes "v \<turnstile> \<phi>"
  assumes "f t1 t2 \<in> subterms \<phi>" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  shows "\<not> Option.is_none (type_term v t1)"
        "type_term v t1 = type_term v t2"
proof -
  from assms obtain a :: "'a pset_atom" where atom: "v \<turnstile> a" "f t1 t2 \<in> subterms a"
    unfolding types_pset_fm_def by (induction \<phi>) auto
  then obtain g s t where "g \<in> {(\<in>\<^sub>s), (=\<^sub>s)}" "a = g s t"
    by (cases a) auto
  obtain t' l where "type_term v t' = Some l" "f t1 t2 \<in> subterms t'"
    apply(rule types_pset_atom.cases[OF \<open>v \<turnstile> a\<close>])
    using atom(2) by auto
  then have "\<not> Option.is_none (type_term v t1) \<and> type_term v t1 = type_term v t2"
  by (induction t' arbitrary: l)
     (use assms(3) in \<open>(auto simp: type_term.simps split: if_splits Option.bind_splits)\<close>)
  then show "\<not> Option.is_none (type_term v t1)" "type_term v t1 = type_term v t2"
    by blast+
qed

lemma types_if_types_Member_and_subterms:
  fixes \<phi> :: "'a pset_fm"
  assumes "v \<turnstile> s \<in>\<^sub>s t1 \<or> v \<turnstile> s \<in>\<^sub>s t2" "v \<turnstile> \<phi>"
  assumes "f t1 t2 \<in> subterms \<phi>" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  shows "v \<turnstile> s \<in>\<^sub>s f t1 t2"
proof -
  from type_term_eq_if_mem_subterms[OF assms(2-)] obtain lt where lt:
    "type_term v t1 = Some lt" "type_term v t2 = Some lt"
    by fastforce
  moreover from assms(1) lt(1,2) obtain ls where
    "type_term v s = Some ls" "lt = Suc ls"
    using types_pset_atom.simps by force
  ultimately show ?thesis
    using assms
    by (auto simp: type_term.simps types_pset_atom.simps)
qed
  
lemma types_lexpands:
  assumes "lexpands b' b" "b \<noteq> []" "\<phi> \<in> set b'"
  assumes "\<And>(\<phi> :: 'a pset_fm). \<phi> \<in> set b \<Longrightarrow> v \<turnstile> \<phi>"
  shows "v \<turnstile> \<phi>"
  using assms
proof(induction rule: lexpands.induct)
  case (1 b' b)
  then show ?case
    apply(induction rule: lexpands_fm.induct)
          apply(force dest: types_fmD intro: types_fmI(3))+
    done
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lexpands_un.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      apply(auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
                  intro: types_pset_atom_Member_Union_D)
      done
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(6) intro: types_fmI(4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(6) intro: types_fmI(4))
  next
    case (4 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Union_D)
      done
  next
    case (5 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Union_D)
      done
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(\<squnion>\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      apply(auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
      done
  qed
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lexpands_int.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      apply(auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
                  intro: types_pset_atom_Member_Inter_D)
      done
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (4 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Inter_D)
      done
  next
    case (5 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Inter_D)
      done
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(\<sqinter>\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      apply(auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
      done
  qed
next
  case (4 b' b)
  then show ?case
    proof(induction rule: lexpands_diff.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      apply(auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
                  intro: types_pset_atom_Member_Diff_D)
      done
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (4 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Diff_D)
      done
  next
    case (5 s t1 t2 b)
    then show ?case
      apply(auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
                 intro: types_pset_atom_Member_Diff_D)
      done
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(-\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      apply(auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
      done
  qed
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lexpands_single.induct)
    case (1 t1 b)
    then have "v \<turnstile> last b"
      by auto
    with \<open>Single t1 \<in> subterms (last b)\<close> obtain a :: "'a pset_atom"
      where a: "a \<in> atoms (last b)" "Single t1 \<in> subterms a" "v \<turnstile> a"
      unfolding types_pset_fm_def by (metis UN_E subterms_fm_def)
    then obtain f s t where
      "a = f s t" "f \<in> {(=\<^sub>s), (\<in>\<^sub>s)}"
      by (metis insertCI pset_atom.exhaust)
    
    then have "\<not> Option.is_none (type_term v t1)"
      
      apply(induction "last b")
      apply(auto simp: type_term.simps split: if_splits Option.bind_splits) 
    then show ?case  sorry
  next
    case (2 s t1 b)
    then show ?case sorry
  next
    case (3 s t1 b)
    then show ?case sorry
  qed
next
  case (6 b' b)
  then show ?case sorry
qed

end