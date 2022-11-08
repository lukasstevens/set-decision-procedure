theory Suc_Theory
  imports Main "HOL-Library.Adhoc_Overloading" Fresh_Identifiers.Fresh
begin

datatype 'a suc_term = Var 'a | Zero | Succ nat "'a suc_term"

datatype 'a suc_atom = is_Eq: Eq "'a suc_term" "'a suc_term" | is_NEq: NEq "'a suc_term" "'a suc_term"

fun succ :: "nat \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "succ n (Succ k t) = succ (n + k) t"
| "succ 0 t = t"
| "succ n t = Succ n t"

fun is_suc_normal_term :: "'a suc_term \<Rightarrow> bool" where
  "is_suc_normal_term (Var _) \<longleftrightarrow> True"
| "is_suc_normal_term Zero \<longleftrightarrow> True"
| "is_suc_normal_term (Succ n Zero) \<longleftrightarrow> n \<noteq> 0"
| "is_suc_normal_term (Succ n (Var _)) \<longleftrightarrow> n \<noteq> 0"
| "is_suc_normal_term (Succ _ (Succ _ _)) \<longleftrightarrow> False"

fun is_suc_normal_atom :: "'a suc_atom \<Rightarrow> bool" where
  "is_suc_normal_atom (Eq t1 t2) \<longleftrightarrow> is_suc_normal_term t1 \<and> is_suc_normal_term t2"
| "is_suc_normal_atom (NEq t1 t2) \<longleftrightarrow> is_suc_normal_term t1 \<and> is_suc_normal_term t2"

consts is_suc_normal :: "'a \<Rightarrow> bool"
adhoc_overloading is_suc_normal is_suc_normal_term is_suc_normal_atom

fun is_Zero_free_term :: "'a suc_term \<Rightarrow> bool" where
  "is_Zero_free_term (Var _) \<longleftrightarrow> True"
| "is_Zero_free_term Zero \<longleftrightarrow> False"
| "is_Zero_free_term (Succ _ t) \<longleftrightarrow> is_Zero_free_term t"

fun is_Zero_free_atom :: "'a suc_atom \<Rightarrow> bool" where
  "is_Zero_free_atom (Eq t1 t2) \<longleftrightarrow> is_Zero_free_term t1 \<and> is_Zero_free_term t2"
| "is_Zero_free_atom (NEq t1 t2) \<longleftrightarrow> is_Zero_free_term t1 \<and> is_Zero_free_term t2"

consts is_Zero_free :: "'a \<Rightarrow> bool"
adhoc_overloading is_Zero_free is_Zero_free_term is_Zero_free_atom

fun I_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_term \<Rightarrow> nat" where
  "I_term v (Var x) = v x"
| "I_term v Zero = 0"
| "I_term v (Succ n t) = (Suc ^^ n) (I_term v t)"

fun I_atom :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_atom \<Rightarrow> bool" where
  "I_atom v (Eq t1 t2) \<longleftrightarrow> I_term v t1 = I_term v t2"
| "I_atom v (NEq t1 t2) \<longleftrightarrow> I_term v t1 \<noteq> I_term v t2"

fun subst_term :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "subst_term \<sigma> (Var x) = succ 0 (\<sigma> x)"
| "subst_term _ Zero = Zero"
| "subst_term \<sigma> (Succ n t) = succ n (subst_term \<sigma> t)"

fun subst_atom :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_atom \<Rightarrow> 'a suc_atom" where
  "subst_atom \<sigma> (Eq t1 t2) = Eq (subst_term \<sigma> t1) (subst_term \<sigma> t2)"
| "subst_atom \<sigma> (NEq t1 t2) = NEq (subst_term \<sigma> t1) (subst_term \<sigma> t2)"

lemma I_term_succ: "I_term v (succ n t) = I_term v (Succ n t)"
  apply(induction n t rule: succ.induct)
    apply(auto)
  done

lemma is_suc_normal_succ[simp]: "is_suc_normal (succ n t)"
  apply(induction n t rule: succ.induct)
    apply(auto)
  done

lemma is_suc_normal_subst_term[simp]: "is_suc_normal (subst_term \<sigma> t)"
  apply(induction t)
   apply(auto)
  done

lemma is_suc_normal_subst_atom[simp]: "is_suc_normal (subst_atom \<sigma> a)"
  by (cases a) simp_all

lemma is_Zero_free_succ[simp]: "is_Zero_free (succ n t) = is_Zero_free t"
  apply(induction n t rule: succ.induct)
      apply(auto)
  done

lemma is_Zero_free_subst_term[simp]:
  "is_Zero_free t \<Longrightarrow> is_Zero_free (subst_term (Var(x := t)) s) \<longleftrightarrow> is_Zero_free s"
  apply(induction s)
    apply(auto)
  done

lemma is_Zero_free_subst_atom[simp]:
  "is_Zero_free t \<Longrightarrow> is_Zero_free (subst_atom (Var(x := t)) a) \<longleftrightarrow> is_Zero_free a"
  by (cases a) auto

lemma is_NEq_subst_atom[simp]:
  "is_NEq (subst_atom v a) \<longleftrightarrow> is_NEq a"
  by (cases a) auto

abbreviation solve_Var_Eq_Succ where
"solve_Var_Eq_Succ solve x n y es \<equiv>
    (if x = y
      then (if n = 0 then solve es else None)
      else map_option ((#) (Eq (Var x) (succ n (Var y))))
            (solve (map (subst_atom (Var(x := succ n (Var y)))) es))
    )"

fun solve :: "'a suc_atom list \<Rightarrow> 'a suc_atom list option" where
  "solve [] = Some []"
| "solve (Eq (Var x) (Var y) # es) =
    (if x = y
      then solve es
      else map_option ((#) (Eq (Var x) (Var y))) (solve (map (subst_atom (Var(x := Var y))) es))
    )"
| "solve (Eq (Var x) (Succ n (Var y)) # es) = solve_Var_Eq_Succ solve x n y es"
| "solve (Eq (Succ n (Var y)) (Var x) # es) = solve_Var_Eq_Succ solve x n y es"
| "solve (Eq (Succ n (Var x)) (Succ k (Var y)) # es) =
    (if n \<ge> k
      then solve_Var_Eq_Succ solve y (n - k) x es
      else solve_Var_Eq_Succ solve x (k - n) y es
    )"

abbreviation "is_normal a \<equiv> \<not> is_NEq a \<and> is_Zero_free a \<and> is_suc_normal a"

lemma is_suc_normal_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "a \<in> set ss"
  shows "is_suc_normal a"
  using assms
  apply(induction es arbitrary: ss rule: solve.induct)
            apply(auto split: if_splits)
  done

lemma I_term_subst_term:
  assumes "I_atom v (Eq (Var x) t)"
  shows "I_term v (subst_term (Var(x := t)) s) = I_term v s"
  using assms
  apply(induction s)
   apply(auto simp: I_term_succ)
  done

lemma I_atom_subst_atom:
  assumes "I_atom v (Eq (Var x) t)"
  shows "I_atom v (subst_atom (Var(x := t)) a) \<longleftrightarrow> I_atom v a"
  using assms
  by (cases a) (auto simp: I_term_subst_term)

lemma I_atom_solve_None:
  assumes "solve es = None" "\<forall>a \<in> set es. is_normal a"
  shows "\<exists>a \<in> set es. \<not> I_atom v a"
proof -
  have "False" if "\<forall>a \<in> set es. I_atom v a"
    using assms that
    apply(induction es rule: solve.induct)
              apply(auto simp: I_atom_subst_atom I_term_succ split: if_splits)
    done
  then show ?thesis
    by blast
qed

lemma set_suc_term_succ[simp]: "set_suc_term (succ n t) = set_suc_term t"
  by (induction n t rule: succ.induct) auto

lemma not_mem_subst_term_self:
  assumes "x \<notin> set_suc_term t"
  shows "x \<notin> set_suc_term (subst_term (Var(x := t)) s)"
  using assms
  apply(induction s)
   apply(auto)
  done

lemma not_mem_subst_atom_self:
  assumes "x \<notin> set_suc_term t"
  shows "x \<notin> set_suc_atom (subst_atom (Var(x := t)) a)"
  using not_mem_subst_term_self[OF assms] by (cases a) simp_all

lemma not_mem_subst_term:
  assumes "z \<notin> set_suc_term t" "z \<notin> set_suc_term s"
  shows "z \<notin> set_suc_term (subst_term (Var(x := t)) s)"
  using assms 
  apply(induction s)
   apply(auto)
  done

lemma not_mem_subst_atom:
  assumes "z \<notin> set_suc_term t" "z \<notin> set_suc_atom a"
  shows "z \<notin> set_suc_atom (subst_atom (Var(x := t)) a)"
  using not_mem_subst_term[OF assms(1)] assms(2) by (cases a) simp_all

lemma not_mem_suc_atom_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "\<forall>a \<in> set es. z \<notin> set_suc_atom a"
  shows "\<forall>a \<in> set ss. z \<notin> set_suc_atom a"
  using assms
  apply(induction es arbitrary: ss rule: solve.induct)
            apply(auto simp: not_mem_subst_atom split: if_splits)
  done

lemma not_mem_suc_atom_if_solve:
  assumes "solve es = Some (Eq (Var x) t # ss)" "\<forall>a \<in> set es. is_normal a"
  shows "\<forall>a \<in> set ss. x \<notin> set_suc_atom a"
  using assms
proof(induction es arbitrary: ss rule: solve.induct)
  case (2 x y es)
  note not_mem_suc_atom_solve[where ?es="map (subst_atom (Var(x := Var y))) es" and ?z=x]
  with 2 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
next
  case (3 x n y es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(x := succ n (Var y)))) es" and ?z=x]
  with 3 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
next                                          
  case (4 n y x es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(x := succ n (Var y)))) es" and ?z=x]
  with 4 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
next
  case (5 n x k y es)
  note not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(y := succ (n - k) (Var x)))) es" and ?z=y]
   and not_mem_suc_atom_solve[
      where ?es="map (subst_atom (Var(x := succ (k - n) (Var y)))) es" and ?z=x]
  with 5 show ?case
    by (auto simp: not_mem_subst_atom_self split: if_splits)
qed auto

fun assign :: "'a suc_atom list \<Rightarrow> ('a \<Rightarrow> nat)" where
  "assign [] = (\<lambda>x. 0)"
| "assign (Eq (Var x) (Var y) # ss) = (let ass = assign ss in ass(x := ass y))"
| "assign (Eq (Var x) (Succ n (Var y)) # ss) = (let ass = assign ss in ass(x := (Suc^^n) (ass y)))"

lemma assign_succ:
  "assign (Eq (Var x) (succ n (Var y)) # ss) = assign (Eq (Var x) (Succ n (Var y)) # ss)"
  apply(cases "(n, Var y)" rule: succ.cases)
    apply(auto)
  done

lemma I_term_fun_upd:
  assumes "x \<notin> set_suc_term t"
  shows "I_term (v(x := s)) t = I_term v t"
  using assms apply(induction t) apply(auto) done

lemma I_atom_fun_upd:
  assumes "x \<notin> set_suc_atom a"
  shows "I_atom (v(x := s)) a = I_atom v a"
  using assms apply (cases a) apply(auto simp: I_term_fun_upd) done

lemma I_atom_fun_updI:
  assumes "x \<notin> set_suc_atom a" "I_atom v a"
  shows "I_atom (v(x := s)) a"
  using assms I_atom_fun_upd by metis

lemma I_atom_assign_if_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  shows "\<forall>a \<in> set ss. I_atom (assign ss) a"
  using assms
proof(induction es arbitrary: ss rule: solve.induct)
  case (2 x y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Var y) # es" and ?x=x]
  with 2 show ?case
    by (auto simp: Let_def I_atom_fun_upd split: if_splits)
next
  case (3 x n y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n (Var y)) # es" and ?x=x]
  with 3 show ?case
    by (auto simp: Let_def I_term_succ I_atom_fun_upd assign_succ split: if_splits)
next
  case (4 n y x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n (Var y)) # es" and ?x=x]
  with 4 show ?case
    by (auto simp: Let_def I_term_succ I_atom_fun_upd assign_succ split: if_splits)
next
  case (5 n x k y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Succ n (Var x)) (Succ k (Var y)) # es" and ?x=x]
   and not_mem_suc_atom_if_solve[where ?es="Eq (Succ n (Var x)) (Succ k (Var y)) # es" and ?x=y]
  with 5 show ?case
    by (auto simp: Let_def I_term_succ I_atom_fun_upd assign_succ split: if_splits)
qed auto

lemma I_atom_if_I_atom_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "\<forall>a \<in> set ss. I_atom v a"
  shows "\<forall>a \<in> set es. I_atom v a"
  using assms
proof(induction es arbitrary: ss rule: solve.induct)
  case (2 x y es)
  then show ?case
    by (auto simp: I_atom_subst_atom split: if_splits)
next
  case (3 x n y es)
  then show ?case
    by (auto simp: I_term_succ I_atom_subst_atom split: if_splits)
next
  case (4 n y x es)
  then show ?case
    by (auto simp: I_term_succ I_atom_subst_atom split: if_splits)
next
  case (5 n x k y es)
  from "5"(1,2,4-) show ?case
    by (auto simp: I_term_succ I_atom_subst_atom split: if_splits)
qed auto

lemma assign_minimal_if_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "\<forall>a \<in> set ss. I_atom v a"
  shows "assign ss z \<le> v z"
  using assms
proof(induction es arbitrary: ss z rule: solve.induct)
  case (2 x y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Var y) # es" and ?x=x]
  with 2 show ?case
    by (auto simp: Let_def split: if_splits)
next
  case (3 x n y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n (Var y)) # es" and ?x=x]
  with 3 show ?case
    by (auto simp: Let_def I_term_succ assign_succ split: if_splits)
next
  case (4 n y x es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Var x) (Succ n (Var y)) # es" and ?x=x]
  with 4 show ?case
    by (auto simp: Let_def I_term_succ assign_succ split: if_splits)
next
  case (5 n x k y es)
  note not_mem_suc_atom_if_solve[where ?es="Eq (Succ n (Var x)) (Succ k (Var y)) # es" and ?x=x]
   and not_mem_suc_atom_if_solve[where ?es="Eq (Succ n (Var x)) (Succ k (Var y)) # es" and ?x=y]
  with 5 show ?case
    by (auto simp: Let_def I_term_succ assign_succ diff_le_mono split: if_splits)
qed auto

fun elim_NEq_Zero_aux :: "('a::fresh) set \<Rightarrow> 'a suc_atom list \<Rightarrow> 'a suc_atom list" where
  "elim_NEq_Zero_aux _ [] = []"
| "elim_NEq_Zero_aux us (NEq (Var x) Zero # es) =
    (let fx = fresh us x in Eq (Var x) (Succ 1 (Var fx)) # elim_NEq_Zero_aux (insert fx us) es)"
| "elim_NEq_Zero_aux us (e # es) = e # elim_NEq_Zero_aux us es"

definition elim_NEq_Zero :: "('a::fresh) suc_atom list \<Rightarrow> 'a suc_atom list"
  where "elim_NEq_Zero es \<equiv> elim_NEq_Zero_aux (\<Union>(set_suc_atom ` set es)) es"

lemma is_normal_elim_NEq_Zero_aux:
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  shows "\<forall>a \<in> set (elim_NEq_Zero_aux us es). is_normal a"
  using assms
  apply(induction es rule: elim_NEq_Zero_aux.induct)
    apply(auto simp: Let_def)
  done

lemma is_normal_elim_NEq_Zero:
  assumes "\<forall>a \<in> set es. is_Eq a \<longrightarrow> is_normal a"
  assumes "\<forall>a \<in> set es. is_NEq a \<longrightarrow> (\<exists>x. a = NEq (Var x) Zero)"
  shows "\<forall>a \<in> set (elim_NEq_Zero es). is_normal a"
  using is_normal_elim_NEq_Zero_aux[OF assms] unfolding elim_NEq_Zero_def by blast

lemma I_atom_Var_NEq_Zero_if_I_atom_Var_Eq_Succ:
  "I_atom v (Eq (Var x) (Succ 1 (Var fx))) \<Longrightarrow> I_atom v (NEq (Var x) Zero)"
  by simp

lemma I_atom_if_I_atom_elim_NEq_Zero_aux:
  assumes "\<forall>a \<in> set (elim_NEq_Zero_aux us es). I_atom v a"
  shows "\<forall>a \<in> set es. I_atom v a"
  using assms I_atom_Var_NEq_Zero_if_I_atom_Var_Eq_Succ
  apply (induction us es rule: elim_NEq_Zero_aux.induct)
        apply(auto simp: Let_def)
  done

lemma I_atom_if_I_atom_elim_NEq_Zero:
  assumes "\<forall>a \<in> set (elim_NEq_Zero es). I_atom v a"
  shows "\<forall>a \<in> set es. I_atom v a"
  using assms I_atom_if_I_atom_elim_NEq_Zero_aux
  unfolding elim_NEq_Zero_def by blast

lemma aux:
  assumes "I_atom v (NEq (Var x) Zero)" "x \<noteq> fx"
  shows "I_atom (v(fx := nat.pred (v x))) (Eq (Var x) (Succ 1 (Var fx)))"
  using assms by auto

lemma I_term_if_eq_on_set_suc_term:
  assumes "\<forall>x \<in> set_suc_term t. v' x = v x"
  shows "I_term v' t = I_term v t"
  using assms
  apply(induction t)
    apply(auto)
  done

lemma I_atom_if_eq_on_set_suc_atom:
  assumes "\<forall>x \<in> set_suc_atom a. v' x = v x"
  shows "I_atom v' a = I_atom v a"
  using assms
  apply (cases a)
  apply(simp_all)
   apply (metis I_term_if_eq_on_set_suc_term UnI1 UnI2)+
  done

lemma
  assumes "finite us" "\<Union>(set_suc_atom ` set es) \<subseteq> us"
  assumes "a \<in> set (elim_NEq_Zero_aux us es)"
  assumes "x \<in> us"
  shows "fresh us x \<notin> set_suc_atom a"
  using assms
proof(induction us es rule: elim_NEq_Zero_aux.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 us y es)
  then have "fresh (insert (fresh us y) us) x \<notin> set_suc_atom a"
    if "a \<in> set (elim_NEq_Zero_aux (insert (fresh us y) us) es)"
    using that by (simp add: subset_insertI2)
  from 2 have "set_suc_atom a \<subseteq> insert (fresh us y) us"
        if "a \<in> set (elim_NEq_Zero_aux (insert (fresh us y) us) es)"
    using that apply(auto) 
  from "2"(2-) show ?case apply(simp) sorry
qed (use fresh_notIn in \<open>force+\<close>)

lemma
  assumes "\<Union>(set_suc_atom ` set es) \<subseteq> us" "finite us"
  assumes "\<forall>a \<in> set es. I_atom v a"
  obtains v' where "\<forall>a \<in> set (elim_NEq_Zero_aux us es). I_atom v' a"
                   "\<forall>x \<in> us. v' x = v x"
  using assms
(*
proof(induction es arbitrary: us thesis)
  case Nil
  then show ?case sorry
next
  case (Cons e es)
  consider
    x where "e = NEq (Var x) Zero" | "\<forall>x. e \<noteq> NEq (Var x) Zero"
    by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis sorry
  next
    case 2
    then show ?thesis sorry
  qed
qed
*)
proof(induction us es arbitrary: thesis rule: elim_NEq_Zero_aux.induct)
  case (1 us)
  then show ?case  sorry
next
  case (2 us x es thesis)
  then obtain v' where
    v': "\<forall>a \<in> set (elim_NEq_Zero_aux (insert (fresh us x) us) es). I_atom v' a"
        "\<forall>x \<in> insert (fresh us x) us. v' x = v x"
    by (auto simp: subset_insertI2)
  with "2.prems"(3) have "fresh us x \<notin> us" "\<forall>x \<in> us. (v'(fresh us x := nat.pred (v' x))) x = v x"
    using fresh_notIn by (metis fun_upd_apply insertCI)+
  moreover from "2.prems"(2) have "x \<in> us"
    by auto
  moreover from "2.prems"(4) have "v x \<noteq> 0"
    by simp
  with v' \<open>x \<in> us\<close> have "v' x \<noteq> 0"
    by simp
  ultimately show ?case apply(intro "2"(2)[where ?v'="v'(fresh us x := nat.pred (v' x))"])
     apply(auto simp: Let_def) apply(metis)
next
  case ("3_1" us s t es)
  then obtain v'
    where v': "\<forall>a \<in> set (elim_NEq_Zero_aux us es). I_atom v' a"
              "\<forall>x \<in> us. v' x = v x"
    by auto
  with "3_1" have "\<forall>x \<in> set_suc_atom (Eq s t). v x = v' x"
    by auto
  from I_atom_if_eq_on_set_suc_atom[OF this] have "I_atom v' (Eq s t) = I_atom v (Eq s t)"
    by blast
  with "3_1" v' show ?case
    by simp
next
  case ("3_2" us va es)
  then show ?case sorry
next
  case ("3_3" us vb vc va es)
  then show ?case sorry
next
  case ("3_4" us v vb es)
  then show ?case sorry
next
  case ("3_5" us v vb vc es)
  then show ?case sorry
qed

hide_const (open) Var subst_term subst_atom is_normal I_term I_atom is_Eq is_NEq

end