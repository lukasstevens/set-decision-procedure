theory Set_Proc_Code
  imports Set_Proc Typing_Urelems "Fresh_Identifiers.Fresh_Nat" "List-Index.List_Index"
begin

instantiation nat :: default
begin
definition "default_nat = (0::nat)"

instance ..
end

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

fun bexpand_nowit1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list list" where
  "bexpand_nowit1 b (Or p q) =
    (if p \<notin> set b \<and> Neg p \<notin> set b then [[[p], [Neg p]]] else [])"
| "bexpand_nowit1 b (Neg (And p q)) =
    (if Neg p \<notin> set b \<and> p \<notin> set b then [[[Neg p], [p]]] else [])"
| "bexpand_nowit1 b (AT (s \<in>\<^sub>s t)) =
    [[[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]]. t' \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t' = t,
                                       AT (s \<in>\<^sub>s t2) \<notin> set b, AF (s \<in>\<^sub>s t2) \<notin> set b] @
    [[[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]]. t' -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t' = t,
                                       AT (s \<in>\<^sub>s t2) \<notin> set b, AF (s \<in>\<^sub>s t2) \<notin> set b] @
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow>
        (if t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<and> AT (s \<in>\<^sub>s t1) \<notin> set b \<and> AF (s \<in>\<^sub>s t1) \<notin> set b
          then [[[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]]] else [])
    | _ \<Rightarrow> [])"
| "bexpand_nowit1 b _ = []"

definition "bexpand_nowit b \<equiv> concat (map (bexpand_nowit1 b) b)"

lemma bexpand_nowit_if_bexpands_nowit:
  "bexpands_nowit bs' b \<Longrightarrow> bs' \<in> set ` set (bexpand_nowit b)"
  apply(induction rule: bexpands_nowit.induct)
       apply(force simp: bexpand_nowit_def)+
  done

lemma bexpands_nowit_if_bexpand_nowit1:
  "bs' \<in> set ` set (bexpand_nowit1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> bexpands_nowit bs' b"
  apply(induction b l rule: bexpand_nowit1.induct)
          apply(auto simp: bexpands_nowit.intros)
  done

lemma bexpands_nowit_if_bexpand_nowit:
  "bs' \<in> set ` set (bexpand_nowit b) \<Longrightarrow> bexpands_nowit bs' b"
  unfolding bexpand_nowit_def using bexpands_nowit_if_bexpand_nowit1
  by (auto simp: bexpands_nowit.intros)

definition "name_subterm \<phi> \<equiv> index (subterms_fm_list \<phi>)"

lemma inj_on_name_subterm_subterms:
  "inj_on (name_subterm \<phi>) (subterms \<phi>)"
  unfolding name_subterm_def
  by (intro inj_on_index2) simp

abbreviation "solve_constraints \<phi> \<equiv>
  Suc_Theory.solve (Suc_Theory.elim_NEq_Zero (constrs_fm (name_subterm \<phi>) \<phi>))"

definition "urelem_code \<phi> t \<equiv>
  (case solve_constraints \<phi> of
    Some ss \<Rightarrow> Suc_Theory.assign ss (name_subterm \<phi> t) = 0
  | None \<Rightarrow> False)"

lemma urelem_code_if_mem_subterms:
  assumes "t \<in> subterms \<phi>"
  shows "urelem \<phi> t \<longleftrightarrow> urelem_code \<phi> t"
proof -
  note urelem_iff_assign_eq_0[OF _ assms] not_types_fm_if_solve_eq_None
  note solve_correct = this[OF inj_on_name_subterm_subterms]
  then show ?thesis
    unfolding urelem_def urelem_code_def
    by (auto split: option.splits)
qed

fun bexpand_wit1 :: "('a::{fresh,default}) branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list list" where
  "bexpand_wit1 b (AF (t1 =\<^sub>s t2)) =
    (if t1 \<in> subterms (last b) \<and> t2 \<in> subterms (last b) \<and>
        (\<forall>t \<in> set b. case t of AT (x \<in>\<^sub>s t1') \<Rightarrow> t1' = t1 \<longrightarrow> AF (x \<in>\<^sub>s t2) \<notin> set b | _ \<Rightarrow> True) \<and>
        (\<forall>t \<in> set b. case t of AT (x \<in>\<^sub>s t2') \<Rightarrow> t2' = t2 \<longrightarrow> AF (x \<in>\<^sub>s t1) \<notin> set b | _ \<Rightarrow> True) \<and>
        \<not> urelem_code (last b) t1 \<and> \<not> urelem_code (last b) t2
      then
        (let x = fresh (vars b) default
         in [[[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
              [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]]])
      else [])"
| "bexpand_wit1 b _ = []"

definition "bexpand_wit b \<equiv> concat (map (bexpand_wit1 b) b)"

lemma Not_Ex_wit_code:
  "(\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b)
    \<longleftrightarrow> (\<forall>fm \<in> set b. case fm of
                        AT (x \<in>\<^sub>s t') \<Rightarrow> t' = t1 \<longrightarrow> AF (x \<in>\<^sub>s t2) \<notin> set b
                      | _ \<Rightarrow> True)"
  by (auto split: fm.splits pset_atom.splits)

lemma bexpand_wit1_if_bexpands_wit:
  assumes "bexpands_wit t1 t2 (fresh (vars b) default) bs' b"
  shows "bs' \<in> set ` set (bexpand_wit1 b (AF (t1 =\<^sub>s t2)))"
proof -
  from bexpands_witD[OF assms] show ?thesis
    by (simp add: Let_def urelem_code_if_mem_subterms Not_Ex_wit_code[symmetric])
qed

lemma bexpand_wit_if_bexpands_wit:
  assumes "bexpands_wit t1 t2 (fresh (vars b) default) bs' b"
  shows "bs' \<in> set ` set (bexpand_wit b)"
  using assms(1)[THEN bexpand_wit1_if_bexpands_wit] bexpands_witD(2)[OF assms(1)]
  unfolding bexpand_wit_def 
  by (auto simp del: bexpand_wit1.simps(1))
  
lemma bexpands_wit_if_bexpand_wit1:
  "b' \<in> set ` set (bexpand_wit1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> (\<exists>t1 t2 x. bexpands_wit t1 t2 x b' b)"
proof(induction b l rule: bexpand_wit1.induct)
  case (1 b t1 t2)
  show ?case
    apply(rule exI[where ?x=t1], rule exI[where ?x=t2],
          rule exI[where ?x="fresh (vars b) default"])
    using 1
    by (auto simp: Let_def bexpands_wit.simps finite_vars_branch[THEN fresh_notIn]
                   Not_Ex_wit_code[symmetric] urelem_code_if_mem_subterms)
qed auto
    
lemma bexpands_wit_if_bexpand_wit:
  "bs' \<in> set ` set (bexpand_wit b) \<Longrightarrow> (\<exists>t1 t2 x. bexpands_wit t1 t2 x bs' b)"
  using bexpands_wit_if_bexpand_wit1[of bs' b]
  apply auto
  using bexpands_wit.intros
  sorry
                                
definition "bexpand b \<equiv> bexpand_nowit b @ bexpand_wit b"

lemma bexpands_if_bexpand:
  "bs' \<in> set ` set (bexpand b) \<Longrightarrow> bexpands bs' b"
  unfolding bexpand_def
  using bexpands_nowit_if_bexpand_nowit bexpands_wit_if_bexpand_wit
  using bexpands.simps by fastforce

lemma Not_bexpands_if_bexpand_empty:
  assumes "bexpand b = []"
  shows "\<not> bexpands bs' b"
proof
  assume "bexpands bs' b"
  then show False
    using assms
  proof (induction rule: bexpands.induct)
    case (1 bs' b)
    with bexpand_nowit_if_bexpands_nowit[OF this(1)] show ?case
      unfolding bexpand_def by simp
  next
    case (2 t1 t2 x bs' b)
    with bexpand_wit_if_bexpands_wit bexpands_witD[OF this(1)] show ?case
      using fresh_notIn[OF finite_vars_branch, of b]
      unfolding bexpand_def
      by (metis Nil_is_append_conv bexpands_wit.intros empty_iff empty_set)
     
  qed
qed

lemma lin_sat_code:
  "lin_sat b \<longleftrightarrow> filter (\<lambda>b'. \<not> set b' \<subseteq> set b) (lexpand b) = []"
  unfolding lin_sat_def
  using lexpand_if_lexpands lexpands_if_lexpand
  by (force simp: filter_empty_conv)

lemma sat_code:
  "sat b \<longleftrightarrow> lin_sat b \<and> bexpand b = []"
  by (meson Not_bexpands_if_bexpand_empty bexpands_if_bexpand last_in_set sat_def)

fun bclosed_code1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> bool" where
  "bclosed_code1 b (Neg \<phi>) \<longleftrightarrow>
    \<phi> \<in> set b \<or>
    (case \<phi> of Atom (t1 =\<^sub>s t2) \<Rightarrow> t1 = t2 | _ \<Rightarrow> False)"
| "bclosed_code1 b (AT (_ \<in>\<^sub>s \<emptyset> _)) \<longleftrightarrow> True"
| "bclosed_code1 _ _ \<longleftrightarrow> False"

definition "bclosed_code b \<equiv> (\<exists>t \<in> set b. bclosed_code1 b t)"

lemma bclosed_code_if_bclosed:
  assumes "bclosed b" "wf_branch b" "v \<turnstile> last b"
  shows "bclosed_code b"
  using assms
proof(induction rule: bclosed.induct)
  case (contr \<phi> b)
  then have "bclosed_code1 b (Neg \<phi>)"
    by auto
  with contr show ?case
    unfolding bclosed_code_def by blast
next
  case (memEmpty t n b)
  then have "bclosed_code1 b (AT (t \<in>\<^sub>s \<emptyset> n))"
    by auto
  with memEmpty show ?case
    unfolding bclosed_code_def by blast
next
  case (neqSelf t b)
  then have "bclosed_code1 b (AF (t =\<^sub>s t))"
    by auto
  with neqSelf show ?case
    unfolding bclosed_code_def by blast
next
  case (memberCycle cs b)
  then show ?case
    by (auto simp: bclosed_code_def dest: no_member_cycle_if_types_last)
qed

lemma bclosed_if_bclosed_code1:
  "bclosed_code1 b l \<Longrightarrow> l \<in> set b \<Longrightarrow> bclosed b"
  by (induction rule: bclosed_code1.induct)
     (auto simp: bclosed.intros split: fm.splits pset_atom.splits)

lemma bclosed_if_bclosed_code:
  "bclosed_code b \<Longrightarrow> bclosed b"
  unfolding bclosed_code_def using bclosed_if_bclosed_code1 by blast

lemma bclosed_code:
  assumes "wf_branch b" "v \<turnstile> last b"
  shows "bclosed b \<longleftrightarrow> bclosed_code b"
  using assms bclosed_if_bclosed_code bclosed_code_if_bclosed 
  by blast

definition "lexpand_safe b \<equiv>
  case filter (\<lambda>b'. \<not> set b' \<subseteq> set b) (lexpand b) of
    b' # bs' \<Rightarrow> b'
  | [] \<Rightarrow> []"

lemma lexpands_lexpand_safe:
  "\<not> lin_sat b \<Longrightarrow> lexpands (lexpand_safe b) b \<and> set b \<subset> set (lexpand_safe b @ b)"
  unfolding lexpand_safe_def
  by (auto simp: lin_sat_code intro!: lexpands_if_lexpand dest: filter_eq_ConsD split: list.splits)


lemma wf_branch_lexpand_safe:
  assumes "wf_branch b"
  shows "wf_branch (lexpand_safe b @ b)"
proof -
  from assms have "wf_branch (lexpand_safe b @ b)" if "\<not> lin_sat b"
    using that lexpands_lexpand_safe wf_branch_lexpands by metis
  moreover have "wf_branch (lexpand_safe b @ b)" if "lin_sat b"
    using assms that[unfolded lin_sat_code]
    unfolding lexpand_safe_def by simp
  ultimately show ?thesis
    by blast
qed

definition "bexpand_safe b \<equiv>
  case bexpand b of
    bs' # bss' \<Rightarrow> bs'
  | [] \<Rightarrow> {[]}"

lemma bexpands_bexpand_safe:
  "\<not> sat b \<Longrightarrow> lin_sat b \<Longrightarrow> bexpands (bexpand_safe b) b"
  unfolding bexpand_safe_def
  by (auto simp: sat_code bexpands_if_bexpand split: list.splits)

lemma wf_branch_bexpand_safe:
  assumes "wf_branch b"
  shows "\<forall>b' \<in> bexpand_safe b. wf_branch (b' @ b)"
proof -
  note wf_branch_expandss[OF assms expandss.intros(3), OF bexpands_if_bexpand]
  with assms show ?thesis
    unfolding bexpand_safe_def
    by (simp split: list.splits) (metis expandss.intros(1) list.set_intros(1))
qed

global_interpretation mlss_naive: mlss_proc lexpand_safe bexpand_safe
  apply(unfold_locales)
  using lexpands_lexpand_safe bexpands_bexpand_safe by auto


lemma types_pset_fm_code:
  "(\<exists>v. v \<turnstile> \<phi>) \<longleftrightarrow> solve_constraints \<phi> \<noteq> None"
  using not_types_fm_if_solve_eq_None types_pset_fm_assign_solve
  by (meson inj_on_name_subterm_subterms not_Some_eq)

typedef 'a wf_branch = "{b :: 'a branch. wf_branch b \<and> (\<exists>v. v \<turnstile> last b)}"
proof -
  have types: "(\<lambda>_. 0) \<turnstile> AT (\<emptyset> 0 =\<^sub>s \<emptyset> 0)"
    unfolding types_pset_fm_def 
    by (auto intro!: types_pset_atom.intros types_pset_term.intros)
  show ?thesis
    apply(rule exI[where ?x="[AT (\<emptyset> 0 =\<^sub>s \<emptyset> 0)]"])
    using types wf_branch_singleton by auto
qed
setup_lifting type_definition_wf_branch

lift_definition lin_sat_wf :: "'a wf_branch \<Rightarrow> bool" is lin_sat .
lift_definition sat_wf :: "'a wf_branch \<Rightarrow> bool" is sat .

lemma lin_sat_wf_code[code]:
  "lin_sat_wf b
  \<longleftrightarrow> filter (\<lambda>b'. \<not> set b' \<subseteq> set (Rep_wf_branch b)) (lexpand (Rep_wf_branch b)) = []"
  by transfer (use lin_sat_code in blast)

lemma sat_wf_code[code]:
  "sat_wf b \<longleftrightarrow> lin_sat_wf b \<and> bexpand (Rep_wf_branch b) = []"
  by transfer (use sat_code in blast)

lift_definition bclosed_wf :: "'a wf_branch \<Rightarrow> bool" is bclosed .
lift_definition bclosed_code_wf :: "'a wf_branch \<Rightarrow> bool" is bclosed_code .

lemma bclosed_wf_code[code]:
  "bclosed_wf b = bclosed_code_wf b"
  by transfer (use bclosed_code in blast)

lift_definition lexpand_safe_app_wf :: "'a wf_branch \<Rightarrow> 'a wf_branch"
  is "\<lambda>b. lexpand_safe b @ b"
  using wf_branch_lexpand_safe by auto

lift_definition bexpand_safe_app_wf :: "('a::{fresh,default}) wf_branch \<Rightarrow> 'a wf_branch set"
  is "\<lambda>b. (\<lambda>b'. b' @ b) ` bexpand_safe b"
  using wf_branch_bexpand_safe by auto

lift_definition mlss_proc_branch_wf :: "('a::{fresh,default}) wf_branch \<Rightarrow> bool"
  is "mlss_naive.mlss_proc_branch" .

lemma mlss_proc_branch_wf_code[code]:
  "mlss_proc_branch_wf b =
    (if \<not> lin_sat_wf b then mlss_proc_branch_wf (lexpand_safe_app_wf b)
     else if bclosed_wf b then True
     else if \<not> sat_wf b then (\<forall>b' \<in> bexpand_safe_app_wf b. mlss_proc_branch_wf b')
     else bclosed_wf b)"
  apply transfer
  apply (auto simp: mlss_naive.mlss_proc_branch_dom_if_wf_branch
                    mlss_naive.mlss_proc_branch.psimps)
  done

lemma Ball_bexpand_safe_app_wf[code_unfold]:
  "(\<forall>b' \<in> bexpand_safe_app_wf b. mlss_proc_branch_wf b')
  \<longleftrightarrow> (\<forall>b' \<in> bexpand_safe (Rep_wf_branch b). mlss_proc_branch_wf (Abs_wf_branch (b' @ b))"
  sorry

code_identifier code_module Set_Calculus \<rightharpoonup> (SML) Set_Proc_Code
export_code mlss_proc_branch_wf in SML

end