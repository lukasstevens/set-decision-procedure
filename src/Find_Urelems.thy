theory Find_Urelems
  imports Typing Suc_Theory
begin

abbreviation "SVar \<equiv> Suc_Theory.Var"
abbreviation "SEq \<equiv> Suc_Theory.Eq"
abbreviation "SNEq \<equiv> Suc_Theory.NEq"

fun constrs_term :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_term \<Rightarrow> 'b suc_atom list" where
  "constrs_term _ (Var _) = []"
| "constrs_term v (\<emptyset> n) = [SEq (SVar (v (\<emptyset> n))) (Succ n Zero)]"
| "constrs_term v (t1 \<squnion>\<^sub>s t2) =
    [SEq (SVar (v (t1 \<squnion>\<^sub>s t2))) (SVar (v t1)), SEq (SVar (v t1)) (SVar (v t2)), SNEq (SVar (v t1)) Zero]
    @ constrs_term v t1 @ constrs_term v t2"
| "constrs_term v (t1 \<sqinter>\<^sub>s t2) =
    [SEq (SVar (v (t1 \<sqinter>\<^sub>s t2))) (SVar (v t1)), SEq (SVar (v t1)) (SVar (v t2)), SNEq (SVar (v t1)) Zero]
    @ constrs_term v t1 @ constrs_term v t2"
| "constrs_term v (t1 -\<^sub>s t2) =
    [SEq (SVar (v (t1 -\<^sub>s t2))) (SVar (v t1)), SEq (SVar (v t1)) (SVar (v t2)), SNEq (SVar (v t1)) Zero]
    @ constrs_term v t1 @ constrs_term v t2"
| "constrs_term v (Single t) =
    [SEq (SVar (v (Single t))) (Succ 1 (SVar (v t)))]
    @ constrs_term v t"
      
fun constrs_atom :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_atom \<Rightarrow> 'b suc_atom list" where
  "constrs_atom v (t1 =\<^sub>s t2) =
    [SEq (SVar (v t1)) (SVar (v t2))]
    @ constrs_term v t1 @ constrs_term v t2"
| "constrs_atom v (t1 \<in>\<^sub>s t2) =
    [SEq (SVar (v t2)) (Succ 1 (SVar (v t1)))]
    @ constrs_term v t1 @ constrs_term v t2"

fun constrs_fm :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_fm \<Rightarrow> 'b suc_atom list" where
  "constrs_fm v (Atom a) = constrs_atom v a"
| "constrs_fm v (And p q) = constrs_fm v p @ constrs_fm v q"
| "constrs_fm v (Or p q) = constrs_fm v p @ constrs_fm v q"
| "constrs_fm v (Neg p) = constrs_fm v p"

hide_const (open) SVar SEq SNEq

end