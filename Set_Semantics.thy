theory Set_Semantics
  imports Logic ZFC_Extras
begin

section \<open>Syntax and Semantics\<close>

datatype 'a pset_term = 
  Empty (\<open>\<emptyset>\<close>)| is_Var: Var 'a |
  Union "'a pset_term" "'a pset_term" (infixr \<open>\<squnion>\<^sub>s\<close> 60) |
  Inter "'a pset_term" "'a pset_term" (infixr \<open>\<sqinter>\<^sub>s\<close> 70) |
  Diff "'a pset_term" "'a pset_term"  (infixl \<open>-\<^sub>s\<close> 80) |
  Single "'a pset_term"

datatype 'a pset_atom =
  Elem "'a pset_term" "'a pset_term" (infix \<open>\<in>\<^sub>s\<close> 55) | 
  Equal "'a pset_term" "'a pset_term" (infix \<open>\<approx>\<^sub>s\<close> 55)

abbreviation "AT a \<equiv> Atom a"
abbreviation "AF a \<equiv> Neg (Atom a)"

type_synonym 'a pset_fm = "'a pset_atom fm"
type_synonym 'a branch = "'a pset_fm list"

fun I\<^sub>s\<^sub>t :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_term \<Rightarrow> V" where
  "I\<^sub>s\<^sub>t v \<emptyset> = 0"
| "I\<^sub>s\<^sub>t v (Var x) = v x"
| "I\<^sub>s\<^sub>t v (s1 \<squnion>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<squnion> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 \<sqinter>\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 \<sqinter> I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (s1 -\<^sub>s s2) = I\<^sub>s\<^sub>t v s1 - I\<^sub>s\<^sub>t v s2"
| "I\<^sub>s\<^sub>t v (Single s) = vset {I\<^sub>s\<^sub>t v s}"

fun I\<^sub>s\<^sub>a :: "('a \<Rightarrow> V) \<Rightarrow> 'a pset_atom \<Rightarrow> bool" where
  "I\<^sub>s\<^sub>a v (t1 \<in>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 \<in> elts (I\<^sub>s\<^sub>t v t2)"
| "I\<^sub>s\<^sub>a v (t1 \<approx>\<^sub>s t2) \<longleftrightarrow> I\<^sub>s\<^sub>t v t1 = I\<^sub>s\<^sub>t v t2"


section \<open>Variables\<close>

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


section \<open>Subformulae and Subterms\<close>

fun subfms :: "'a fm \<Rightarrow> 'a fm set"  where
  "subfms (Atom a) = {Atom a}"
| "subfms (And p q) = {And p q} \<union> subfms p \<union> subfms q"
| "subfms (Or p q) = {Or p q} \<union> subfms p \<union> subfms q"
| "subfms (Neg q) = {Neg q} \<union> subfms q"

definition subfms_branch :: "'a fm list \<Rightarrow> 'a fm set" where
  "subfms_branch b \<equiv> \<Union>(subfms ` set b)"

lemma subfms_branch_simps:
  "subfms_branch [] = {}"
  "subfms_branch (x # xs) = subfms x \<union> subfms_branch xs"
  unfolding subfms_branch_def by auto

fun subterms :: "'a pset_term \<Rightarrow> 'a pset_term set"  where
  "subterms \<emptyset> = {\<emptyset>}"
| "subterms (Var i) = {Var i}"
| "subterms (t1 \<squnion>\<^sub>s t2) = {t1 \<squnion>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 \<sqinter>\<^sub>s t2) = {t1 \<sqinter>\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (t1 -\<^sub>s t2) = {t1 -\<^sub>s t2} \<union> subterms t1 \<union> subterms t2"
| "subterms (Single t) = {Single t} \<union> subterms t"

fun subterms_atom :: "'a pset_atom \<Rightarrow> 'a pset_term set"  where
  "subterms_atom (t1 \<in>\<^sub>s t2) = subterms t1 \<union> subterms t2"
| "subterms_atom (t1 \<approx>\<^sub>s t2) = subterms t1 \<union> subterms t2"

definition subterms_fm :: "'a pset_atom fm \<Rightarrow> 'a pset_term set" where
 "subterms_fm \<phi> \<equiv> \<Union>(subterms_atom ` atoms \<phi>)"

lemma subterms_fm_simps[simp]:
  "subterms_fm (Atom a) = subterms_atom a"
  "subterms_fm (And p q) = subterms_fm p \<union> subterms_fm q"
  "subterms_fm (Or p q) = subterms_fm p \<union> subterms_fm q"
  "subterms_fm (Neg p) = subterms_fm p"
  unfolding subterms_fm_def by auto

definition subterms_branch :: "'a pset_atom fm list \<Rightarrow> 'a pset_term set" where
  "subterms_branch b \<equiv> \<Union>(subterms_fm ` set b)"

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

abbreviation pset_atoms_branch :: "'a fm list \<Rightarrow> 'a set" where
  "pset_atoms_branch b \<equiv> \<Union>(atoms ` set b)"

lemma subterms_subterms_branch_trans:
  "s \<in> subterms t \<Longrightarrow> t \<in> subterms_branch b \<Longrightarrow> s \<in> subterms_branch b"
  unfolding subterms_branch_def using subterms_subterms_fm_trans by blast

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

lemma subterms_branchI_if_mem_mem_pset_atoms_branch:
  assumes "(t1 \<in>\<^sub>s t2) \<in> pset_atoms_branch b"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(t1 \<in>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

lemma subterms_branchI_if_eq_mem_pset_atoms_branch:
  assumes "(t1 \<approx>\<^sub>s t2) \<in> pset_atoms_branch b"
  shows "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
proof -
  from assms obtain \<phi> where phi: "\<phi> \<in> set b" "(t1 \<approx>\<^sub>s t2) \<in> atoms \<phi>"
    by blast
  from this(2) have "t1 \<in> subterms_fm \<phi> \<and> t2 \<in> subterms_fm \<phi>"
    by (induction \<phi>) (auto simp: subterms_branch_def)
  with phi show "t1 \<in> subterms_branch b" "t2 \<in> subterms_branch b"
    unfolding subterms_branch_def by blast+
qed

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

section \<open>Finiteness\<close>

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

section \<open>Non-Emptiness\<close>

lemma subterms_nonempty[simp]: "subterms t \<noteq> {}"
  by (induction t) auto

lemma subterms_atom_nonempty[simp]: "subterms_atom l \<noteq> {}"
  by (cases l rule: subterms_atom.cases) auto

lemma subterms_fm_nonempty[simp]: "subterms_fm \<phi> \<noteq> {}"
  by (induction \<phi>) auto

end