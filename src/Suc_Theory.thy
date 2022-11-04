theory Suc_Theory
  imports Main "HOL-Library.Adhoc_Overloading"
begin

datatype 'a suc_term = Var 'a | Succ nat "'a suc_term"

datatype 'a suc_atom = Eq "'a suc_term" "'a suc_term"

fun succ :: "nat \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "succ n (Succ k t) = succ (n + k) t"
| "succ 0 t = t"
| "succ n (Var x) = Succ n (Var x)"

fun is_normal_term :: "'a suc_term \<Rightarrow> bool" where
  "is_normal_term (Var _) \<longleftrightarrow> True"
| "is_normal_term (Succ n (Var _)) \<longleftrightarrow> n \<noteq> 0"
| "is_normal_term (Succ _ (Succ _ _)) \<longleftrightarrow> False"

fun is_normal_atom :: "'a suc_atom \<Rightarrow> bool" where
  "is_normal_atom (Eq t1 t2) \<longleftrightarrow> is_normal_term t1 \<and> is_normal_term t2"

consts is_normal :: "'a \<Rightarrow> bool"
adhoc_overloading is_normal is_normal_term is_normal_atom

fun I_suc_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_term \<Rightarrow> nat" where
  "I_suc_term v (Var x) = v x"
| "I_suc_term v (Succ n t) = (Suc ^^ n) (I_suc_term v t)"

fun I_suc_atom :: "('a \<Rightarrow> nat) \<Rightarrow> 'a suc_atom \<Rightarrow> bool" where
  "I_suc_atom v (Eq t1 t2) \<longleftrightarrow> I_suc_term v t1 = I_suc_term v t2"

fun subst_suc_term :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_term \<Rightarrow> 'a suc_term" where
  "subst_suc_term \<sigma> (Var x) = succ 0 (\<sigma> x)"
| "subst_suc_term \<sigma> (Succ n t) = succ n (subst_suc_term \<sigma> t)"

fun subst_suc_atom :: "('a \<Rightarrow> 'a suc_term) \<Rightarrow> 'a suc_atom \<Rightarrow> 'a suc_atom" where
  "subst_suc_atom \<sigma> (Eq t1 t2) = Eq (subst_suc_term \<sigma> t1) (subst_suc_term \<sigma> t2)"

lemma I_suc_term_succ: "I_suc_term v (succ n t) = I_suc_term v (Succ n t)"
  apply(induction n t rule: succ.induct)
    apply(auto)
  done

lemma is_normal_succ[simp]: "is_normal (succ n t)"
  apply(induction n t rule: succ.induct)
    apply(auto)
  done

lemma is_normal_subst_suc_term[simp]: "is_normal (subst_suc_term \<sigma> t)"
  apply(induction t)
   apply(auto)
  done

lemma is_normal_subst_suc_atom[simp]: "is_normal (subst_suc_atom \<sigma> a)"
  by (cases a) simp

abbreviation solve_Var_Eq_Succ where
"solve_Var_Eq_Succ solve x n y es \<equiv>
    (if x = y
      then (if n = 0 then solve es else None)
      else map_option ((#) (Eq (Var x) (succ n (Var y))))
            (solve (map (subst_suc_atom (Var(x := succ n (Var y)))) es))
    )"

fun solve :: "'a suc_atom list \<Rightarrow> 'a suc_atom list option" where
  "solve [] = Some []"
| "solve (Eq (Var x) (Var y) # es) =
    (if x = y
      then solve es
      else map_option ((#) (Eq (Var x) (Var y))) (solve (map (subst_suc_atom (Var(x := Var y))) es))
    )"
| "solve (Eq (Var x) (Succ n (Var y)) # es) = solve_Var_Eq_Succ solve x n y es"
| "solve (Eq (Succ n (Var y)) (Var x) # es) = solve_Var_Eq_Succ solve x n y es"
| "solve (Eq (Succ n (Var x)) (Succ k (Var y)) # es) =
    (if n \<ge> k
      then solve_Var_Eq_Succ solve y (n - k) x es
      else solve_Var_Eq_Succ solve x (k - n) y es
    )"

lemma is_normal_solve:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a"
  assumes "a \<in> set ss"
  shows "is_normal a"
  using assms
  apply(induction es arbitrary: ss rule: solve.induct)
            apply(auto split: if_splits)
  done

lemma I_suc_term_subst_suc_term:
  assumes "I_suc_atom v (Eq (Var x) t)"
  shows "I_suc_term v (subst_suc_term (Var(x := t)) s) = I_suc_term v s"
  using assms
  apply(induction s)
   apply(auto simp: I_suc_term_succ)
  done

lemma I_suc_atom_subst_suc_atom:
  assumes "I_suc_atom v (Eq (Var x) t)"
  shows "I_suc_atom v (subst_suc_atom (Var(x := t)) a) \<longleftrightarrow> I_suc_atom v a"
  using assms
  by (cases a) (auto simp: I_suc_term_subst_suc_term)

lemma I_suc_atom_sym: "I_suc_atom v (Eq s t) \<longleftrightarrow> I_suc_atom v (Eq t s)"
  by auto

lemma I_suc_atom_solve_Some:
  assumes "solve es = Some ss" "\<forall>a \<in> set es. is_normal a" "\<forall>a \<in> set es. I_suc_atom v a"
  assumes "a \<in> set ss"
  shows "I_suc_atom v a"
  using assms
  apply(induction es arbitrary: ss rule: solve.induct)
            apply(auto simp: I_suc_atom_subst_suc_atom I_suc_term_succ split: if_splits)
  done

lemma I_suc_atom_solve_None:
  assumes "solve es = None" "\<forall>a \<in> set es. is_normal a"
  shows "\<exists>a \<in> set es. \<not> I_suc_atom v a"
proof -
  have "False" if "\<forall>a \<in> set es. I_suc_atom v a"
    using assms that
    apply(induction es rule: solve.induct)
              apply(auto simp: I_suc_atom_subst_suc_atom I_suc_term_succ split: if_splits)
    done
  then show ?thesis
    by blast
qed

lemma
  assumes "\<forall>v. \<exists>a \<in> set es. \<not> I_suc_atom v a" "\<forall>a \<in> set es. is_normal a"
  shows "solve es = None"
  using assms
proof(induction es rule: solve.induct)
  case (2 x y es)
  then show ?case apply(auto split: if_splits) sorry
next
  case (3 x n y es)
  then show ?case sorry
next
  case (4 n y x es)
  then show ?case sorry
next
  case (5 n x k y es)
  then show ?case sorry
qed auto


(*
inductive proves_suc :: "'a suc_atom set \<Rightarrow> 'a suc_atom \<Rightarrow> bool" (infix "\<turnstile>\<^bsub>Suc\<^esub>" 60) where
  "a \<in> A \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> a"
| "A \<turnstile>\<^bsub>Suc\<^esub> Eq t t"
| "A \<turnstile>\<^bsub>Suc\<^esub> Eq t1 t2 \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> Eq t2 t1"
| "A \<turnstile>\<^bsub>Suc\<^esub> NEq t1 t2 \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> NEq t2 t1"
| "A \<turnstile>\<^bsub>Suc\<^esub> Eq t1 t2 \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> NEq t1 t2 \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> NEq Zero Zero"
| "A \<turnstile>\<^bsub>Suc\<^esub> Eq (Succ t1) (Succ t2) \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> Eq t1 t2"
| "A \<turnstile>\<^bsub>Suc\<^esub> Eq (Var x) t \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> a
  \<Longrightarrow> A \<turnstile>\<^bsub>Suc\<^esub> subst_suc_atom (\<lambda>y. if x = y then t else Var y) a"
*)

end