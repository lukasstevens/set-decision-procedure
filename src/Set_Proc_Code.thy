theory Set_Proc_Code
  imports Set_Proc
begin

fun subterms_term_list :: "'a pset_term \<Rightarrow> 'a pset_term list"  where
  "subterms_term_list (\<emptyset> n) = [\<emptyset> n]"
| "subterms_term_list (Var i) = [Var i]"
| "subterms_term_list (t1 \<squnion>\<^sub>s t2) = [t1 \<squnion>\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (t1 \<sqinter>\<^sub>s t2) = [t1 \<sqinter>\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (t1 -\<^sub>s t2) = [t1 -\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (Single t) = [Single t] @ subterms_term_list t"

fun subterms_atom_list :: "'a pset_atom \<Rightarrow> 'a pset_term list"  where
  "subterms_atom_list (t1 \<in>\<^sub>s t2) = subterms_term_list t1 @ subterms_term_list t2"
| "subterms_atom_list (t1 =\<^sub>s t2) = subterms_term_list t1 @ subterms_term_list t2"

fun atoms_list :: "'a pset_fm \<Rightarrow> 'a pset_atom list" where
  "atoms_list (Atom a) = [a]"
| "atoms_list (And p q) = atoms_list p @ atoms_list q"
| "atoms_list (Or p q) = atoms_list p @ atoms_list q"
| "atoms_list (Neg p) = atoms_list p"

definition subterms_fm_list :: "'a pset_fm \<Rightarrow> 'a pset_term list" where
 "subterms_fm_list \<phi> \<equiv> concat (map subterms_atom_list (atoms_list \<phi>))"

definition subterms_branch_list :: "'a branch \<Rightarrow> 'a pset_term list" where
  "subterms_branch_list b \<equiv> concat (map subterms_fm_list b)"

lemma set_subterms_term_list[simp]:
  "set (subterms_term_list t) = subterms t"
  by (induction t) auto

lemma set_subterms_atom_list[simp]:
  "set (subterms_atom_list t) = subterms t"
  by (cases t) auto

lemma set_atoms_list[simp]:
  "set (atoms_list \<phi>) = atoms \<phi>"
  by (induction \<phi>) auto

lemma set_subterms_fm_list[simp]:
  "set (subterms_fm_list \<phi>) = subterms_fm \<phi>"
  unfolding subterms_fm_list_def subterms_fm_def by simp

lemma set_subterms_branch_list[simp]:
  "set (subterms_branch_list b) = subterms b"
  unfolding subterms_branch_list_def subterms_branch_def by simp

fun lexpand_fm1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_fm1 b (And p q) = [[p, q]]"
| "lexpand_fm1 b (Neg (Or p q)) = [[Neg p, Neg q]]"
| "lexpand_fm1 b (Or p q) =
    (if Neg p \<in> set b then [[q]] else []) @
    (if Neg q \<in> set b then [[p]] else [])"
| "lexpand_fm1 b (Neg (And p q)) =
    (if p \<in> set b then [[Neg q]] else []) @
    (if q \<in> set b then [[Neg p]] else [])"
| "lexpand_fm1 b (Neg (Neg p)) = [[p]]"
| "lexpand_fm1 b _ = []"

definition "lexpand_fm b \<equiv> concat (map (lexpand_fm1 b) b)"

lemma lexpand_fm_if_lexpands_fm:
  "lexpands_fm b' b \<Longrightarrow> b' \<in> set (lexpand_fm b)"
  apply(induction rule: lexpands_fm.induct)
        apply(force simp: lexpand_fm_def)+
  done

lemma lexpands_fm_if_lexpand_fm1: 
  "b' \<in> set (lexpand_fm1 b p) \<Longrightarrow> p \<in> set b \<Longrightarrow> lexpands_fm b' b"
  apply(induction b p rule: lexpand_fm1.induct)
        apply(auto simp: lexpands_fm.intros)
  done

lemma lexpands_fm_if_lexpand_fm:
  "b' \<in> set (lexpand_fm b) \<Longrightarrow> lexpands_fm b' b"
  using lexpands_fm_if_lexpand_fm1 unfolding lexpand_fm_def by auto

fun lexpand_un1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_un1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t \<squnion>\<^sub>s t1)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t \<squnion>\<^sub>s t1 \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 \<squnion>\<^sub>s t \<in> subterms (last b)] @ 
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow> [[AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)]]
    | _ \<Rightarrow> [])"
| "lexpand_un1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t \<squnion>\<^sub>s t2)]. t1 \<squnion>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    [[AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t)]. t1 \<squnion>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow> (if AF (s \<in>\<^sub>s t1) \<in> set b then [[AT (s \<in>\<^sub>s t2)]] else []) @
                  (if AF (s \<in>\<^sub>s t2) \<in> set b then [[AT (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_un1 _ _ = []"

definition "lexpand_un b \<equiv> concat (map (lexpand_un1 b) b)"

lemma lexpand_un_if_lexpands_un:
  "lexpands_un b' b \<Longrightarrow> b' \<in> set (lexpand_un b)"
  apply(induction rule: lexpands_un.induct)
       apply(force simp: lexpand_un_def)+
  done

lemma lexpands_un_if_lexpand_un1:
  "b' \<in> set (lexpand_un1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_un b' b"
  apply(induction b l rule: lexpand_un1.induct)
          apply(auto simp: lexpands_un.intros)
  done

lemma lexpands_un_if_lexpand_un:
  "b' \<in> set (lexpand_un b) \<Longrightarrow> lexpands_un b' b"
  unfolding lexpand_un_def using lexpands_un_if_lexpand_un1 by auto

fun lexpand_int1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_int1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t)]. AT (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 \<sqinter>\<^sub>s t \<in> subterms (last b)] @
    [[AT (s \<in>\<^sub>s t \<sqinter>\<^sub>s t2)]. AT (s' \<in>\<^sub>s t2) \<leftarrow> b, s' = s, t \<sqinter>\<^sub>s t2 \<in> subterms (last b)] @
    (case t of t1 \<sqinter>\<^sub>s t2 \<Rightarrow> [[AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)]] | _ \<Rightarrow> [])"
| "lexpand_int1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t \<sqinter>\<^sub>s t2)]. t1 \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    [[AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t)]. t1 \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of
      t1 \<sqinter>\<^sub>s t2 \<Rightarrow> (if AT (s \<in>\<^sub>s t1) \<in> set b then [[AF (s \<in>\<^sub>s t2)]] else []) @
                  (if AT (s \<in>\<^sub>s t2) \<in> set b then [[AF (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_int1 _ _ = []"

definition "lexpand_int b \<equiv> concat (map (lexpand_int1 b) b)"

lemma lexpand_int_if_lexpands_int:
  "lexpands_int b' b \<Longrightarrow> b' \<in> set (lexpand_int b)"
  apply(induction rule: lexpands_int.induct)
       apply(force simp: lexpand_int_def)+
  done

lemma lexpands_int_if_lexpand_int1:
  "b' \<in> set (lexpand_int1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_int b' b"
  apply(induction b l rule: lexpand_int1.induct)
          apply(auto simp: lexpands_int.intros)
  done

lemma lexpands_int_if_lexpand_int:
  "b' \<in> set (lexpand_int b) \<Longrightarrow> lexpands_int b' b"
  unfolding lexpand_int_def using lexpands_int_if_lexpand_int1 by auto

fun lexpand_diff1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_diff1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t -\<^sub>s t2)]. AF (s' \<in>\<^sub>s t2) \<leftarrow> b, s' = s, t -\<^sub>s t2 \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 -\<^sub>s t)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 -\<^sub>s t \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 -\<^sub>s t)]. t1 -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of t1 -\<^sub>s t2 \<Rightarrow> [[AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)]] | _ \<Rightarrow> [])"
| "lexpand_diff1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t -\<^sub>s t2)]. t1 -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    (case t of
      t1 -\<^sub>s t2 \<Rightarrow> (if AT (s \<in>\<^sub>s t1) \<in> set b then [[AT (s \<in>\<^sub>s t2)]] else []) @
                  (if AF (s \<in>\<^sub>s t2) \<in> set b then [[AF (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_diff1 _ _ = []"

definition "lexpand_diff b \<equiv> concat (map (lexpand_diff1 b) b)"

lemma lexpand_diff_if_lexpands_diff:
  "lexpands_diff b' b \<Longrightarrow> b' \<in> set (lexpand_diff b)"
  apply(induction rule: lexpands_diff.induct)
       apply(force simp: lexpand_diff_def)+
  done

lemma lexpands_diff_if_lexpand_diff1:
  "b' \<in> set (lexpand_diff1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_diff b' b"
  apply(induction b l rule: lexpand_diff1.induct)
          apply(auto simp: lexpands_diff.intros)
  done

lemma lexpands_diff_if_lexpand_diff:
  "b' \<in> set (lexpand_diff b) \<Longrightarrow> lexpands_diff b' b"
  unfolding lexpand_diff_def using lexpands_diff_if_lexpand_diff1 by auto

fun lexpand_single1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_single1 b (AT (s \<in>\<^sub>s Single t)) = [[AT (s =\<^sub>s t)]]"
| "lexpand_single1 b (AF (s \<in>\<^sub>s Single t)) = [[AF (s =\<^sub>s t)]]"
| "lexpand_single1 _ _ = []"

definition "lexpand_single b \<equiv>
  [[AT (t1 \<in>\<^sub>s Single t1)]. Single t1 \<leftarrow> subterms_fm_list (last b)] @
  concat (map (lexpand_single1 b) b)"

lemma lexpand_single_if_lexpands_single:
  "lexpands_single b' b \<Longrightarrow> b' \<in> set (lexpand_single b)"
  apply(induction rule: lexpands_single.induct)
       apply(force simp: lexpand_single_def)+
  done

lemma lexpands_single_if_lexpand_single1:
  "b' \<in> set (lexpand_single1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_single b' b"
  apply(induction b l rule: lexpand_single1.induct)
          apply(auto simp: lexpands_single.intros)
  done

lemma lexpands_single_if_lexpand_single:
  "b' \<in> set (lexpand_single b) \<Longrightarrow> lexpands_single b' b"
  unfolding lexpand_single_def using lexpands_single_if_lexpand_single1
  by (auto simp: lexpands_single.intros)

fun lexpand_eq1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_eq1 b (AT (t1 =\<^sub>s t2)) =
    [[AT (subst_tlvl t1 t2 a)]. AT a \<leftarrow> b, t1 \<in> tlvl_terms a] @
    [[AF (subst_tlvl t1 t2 a)]. AF a \<leftarrow> b, t1 \<in> tlvl_terms a] @
    [[AT (subst_tlvl t2 t1 a)]. AT a \<leftarrow> b, t2 \<in> tlvl_terms a] @
    [[AF (subst_tlvl t2 t1 a)]. AF a \<leftarrow> b, t2 \<in> tlvl_terms a]"
| "lexpand_eq1 b _ = []"

definition "lexpand_eq b \<equiv>
  [[AF (s =\<^sub>s s')]. AT (s \<in>\<^sub>s t) \<leftarrow> b, AF (s' \<in>\<^sub>s t') \<leftarrow> b, t' = t] @
  concat (map (lexpand_eq1 b) b)"

lemma lexpand_eq_if_lexpands_eq:
  "lexpands_eq b' b \<Longrightarrow> b' \<in> set (lexpand_eq b)"
  apply(induction rule: lexpands_eq.induct)
       apply(force simp: lexpand_eq_def)+
  done

lemma lexpands_eq_if_lexpand_eq1:
  "b' \<in> set (lexpand_eq1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_eq b' b"
  apply(induction b l rule: lexpand_eq1.induct)
          apply(auto simp: lexpands_eq.intros)
  done

lemma lexpands_eq_if_lexpand_eq:
  "b' \<in> set (lexpand_eq b) \<Longrightarrow> lexpands_eq b' b"
  unfolding lexpand_eq_def using lexpands_eq_if_lexpand_eq1
  by (auto simp: lexpands_eq.intros)

definition "lexpand b \<equiv>
  lexpand_fm b @
  lexpand_un b @ lexpand_int b @ lexpand_diff b @ 
  lexpand_single b @ lexpand_eq b"

lemma lexpand_if_lexpands:
  "lexpands b' b \<Longrightarrow> b' \<in> set (lexpand b)"
  apply(induction rule: lexpands.induct)
  unfolding lexpand_def
  using lexpand_fm_if_lexpands_fm
  using lexpand_un_if_lexpands_un lexpand_int_if_lexpands_int lexpand_diff_if_lexpands_diff
  using lexpand_single_if_lexpands_single lexpand_eq_if_lexpands_eq
  by fastforce+

lemma lexpands_if_lexpand:
  "b' \<in> set (lexpand b) \<Longrightarrow> lexpands b' b"
  unfolding lexpand_def
  using lexpands_fm_if_lexpand_fm
  using lexpands_un_if_lexpand_un lexpands_int_if_lexpand_int lexpands_diff_if_lexpand_diff
  using lexpands_single_if_lexpand_single lexpands_eq_if_lexpand_eq
  using lexpands.intros by fastforce


end