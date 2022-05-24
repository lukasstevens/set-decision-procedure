theory Logic
  imports Main
begin

datatype (atoms: 'a) fm =
  is_Atom: Atom 'a | And "'a fm" "'a fm" | Or "'a fm" "'a fm" |
  Neg "'a fm"

fun amap_fm :: "('a \<Rightarrow> 'b fm) \<Rightarrow> 'a fm \<Rightarrow> 'b fm" ("amap\<^sub>f\<^sub>m") where
  "amap\<^sub>f\<^sub>m h (Atom a) = h a" |
  "amap\<^sub>f\<^sub>m h (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (amap\<^sub>f\<^sub>m h \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m h \<phi>\<^sub>2)" |
  "amap\<^sub>f\<^sub>m h (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (amap\<^sub>f\<^sub>m h \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m h \<phi>\<^sub>2)" |
  "amap\<^sub>f\<^sub>m h (Neg \<phi>) = Neg (amap\<^sub>f\<^sub>m h \<phi>)"

fun dnf_and_fm :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "dnf_and_fm (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<psi> = Or (dnf_and_fm \<phi>\<^sub>1 \<psi>) (dnf_and_fm \<phi>\<^sub>2 \<psi>)" |
  "dnf_and_fm \<psi> (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (dnf_and_fm \<psi> \<phi>\<^sub>1) (dnf_and_fm \<psi> \<phi>\<^sub>2)" |
  "dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2 = And \<phi>\<^sub>1 \<phi>\<^sub>2"

fun dnf_fm :: "'a fm \<Rightarrow> 'a fm" where
  "dnf_fm (And \<phi>\<^sub>1 \<phi>\<^sub>2) = dnf_and_fm (dnf_fm \<phi>\<^sub>1) (dnf_fm \<phi>\<^sub>2)" |
  "dnf_fm (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (dnf_fm \<phi>\<^sub>1) (dnf_fm \<phi>\<^sub>2)" |
  "dnf_fm x = x"

fun conj_list :: "'a fm \<Rightarrow> 'a list" where
  "conj_list (And \<phi>\<^sub>1 \<phi>\<^sub>2) = conj_list \<phi>\<^sub>1 @ conj_list \<phi>\<^sub>2" |
  "conj_list (Atom a) = [a]"

fun disj_conj_list :: "'a fm \<Rightarrow> 'a list list" where
  "disj_conj_list (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = disj_conj_list \<phi>\<^sub>1 @ disj_conj_list \<phi>\<^sub>2" |
  "disj_conj_list (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [conj_list (And \<phi>\<^sub>1 \<phi>\<^sub>2)]" |
  "disj_conj_list (Atom a) = [[a]]"

definition "dnf \<equiv> disj_conj_list o dnf_fm"

lemma dnf_and_fm_induct[case_names DistribR DistribL NoDistrib]:
  fixes \<phi>\<^sub>1 \<phi>\<^sub>2 :: "'a fm"
  assumes "\<And>\<phi>\<^sub>1 \<phi>\<^sub>2 \<psi>. \<lbrakk>P \<phi>\<^sub>1 \<psi>; P \<phi>\<^sub>2 \<psi>\<rbrakk> \<Longrightarrow> P (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<psi>"
  assumes "\<And>\<psi> \<phi>\<^sub>1 \<phi>\<^sub>2. \<lbrakk>P \<psi> \<phi>\<^sub>1; P \<psi> \<phi>\<^sub>2; \<nexists>x y. \<psi> = Or x y\<rbrakk> \<Longrightarrow> P \<psi> (Or \<phi>\<^sub>1 \<phi>\<^sub>2)"
  assumes "\<And>\<phi>\<^sub>1 \<phi>\<^sub>2. \<lbrakk>\<nexists>x y. \<phi>\<^sub>1 = Or x y; \<nexists>x y. \<phi>\<^sub>2 = Or x y\<rbrakk> \<Longrightarrow> P \<phi>\<^sub>1 \<phi>\<^sub>2"
  shows "P \<phi>\<^sub>1 \<phi>\<^sub>2"
  apply(induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm.induct)
  using assms by simp_all

fun is_conj :: "'a fm \<Rightarrow> bool" where
  "is_conj (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> is_conj \<phi>\<^sub>1 \<and> is_conj \<phi>\<^sub>2" |
  "is_conj (Or _ _) \<longleftrightarrow> False" |
  "is_conj (Neg _) \<longleftrightarrow> False" |
  "is_conj (Atom _) \<longleftrightarrow> True"

fun dnormal :: "'a fm \<Rightarrow> bool" where
  "dnormal (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> dnormal \<phi>\<^sub>1 \<and> dnormal \<phi>\<^sub>2" |
  "dnormal (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> is_conj (And \<phi>\<^sub>1 \<phi>\<^sub>2)" |
  "dnormal (Neg _) \<longleftrightarrow> False" |
  "dnormal _ \<longleftrightarrow> True"

fun nfree :: "'a fm \<Rightarrow> bool" where
  "nfree (Atom \<phi>) \<longleftrightarrow> True" |
  "nfree (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> nfree \<phi>\<^sub>1 \<and> nfree \<phi>\<^sub>2" |
  "nfree (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> nfree \<phi>\<^sub>1 \<and> nfree \<phi>\<^sub>2" |
  "nfree (Neg _) \<longleftrightarrow> False"

lemma atoms_amap\<^sub>f\<^sub>m: "atoms (amap\<^sub>f\<^sub>m f \<phi>) = (\<Union>a \<in> atoms \<phi>. atoms (f a))"
  by (induction \<phi>) auto

lemma atoms_dnf_and_fm[simp]: "atoms (dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2) = atoms (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
  by (induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm.induct) auto

lemma atoms_dnf_fm[simp]: "atoms (dnf_fm \<phi>) = atoms \<phi>"
  using atoms_dnf_and_fm
  by (induction \<phi>) auto

lemma atoms_conj_list: "is_conj \<phi> \<Longrightarrow> set (conj_list \<phi>) = atoms \<phi>"
  by (induction \<phi>) auto

lemma atoms_disj_conj_list: "dnormal \<phi> \<Longrightarrow> (\<Union>A \<in> set (disj_conj_list \<phi>). set A) = atoms \<phi>"
  by (induction \<phi>) (auto simp: atoms_conj_list)

lemma nfree_amap\<^sub>f\<^sub>m: "(\<And>x. nfree (f x)) \<Longrightarrow> nfree (amap\<^sub>f\<^sub>m f \<phi>) = nfree \<phi>"
  by (induction \<phi>) auto

lemma nfree_amap\<^sub>f\<^sub>mI: "(\<And>x. nfree (f x)) \<Longrightarrow> nfree \<phi> \<Longrightarrow> nfree (amap\<^sub>f\<^sub>m f \<phi>)"
  using nfree_amap\<^sub>f\<^sub>m by blast

lemma nfree_dnf_and_fm[simp]: "nfree (dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2) = nfree (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
  apply(induction "\<phi>\<^sub>1" "\<phi>\<^sub>2" rule: dnf_and_fm.induct)
  by auto

lemma nfree_dnf_fm[simp]: "nfree (dnf_fm \<phi>) = nfree \<phi>"
  apply(induction \<phi>)
  by auto

lemma dnormal_conj: "is_conj \<phi> \<Longrightarrow> dnormal \<phi>"
  apply(induction \<phi>)
  by auto

lemma dnormal_dnf_and_fm:
  assumes "nfree \<phi>\<^sub>1" "nfree \<phi>\<^sub>2"
    and "dnormal \<phi>\<^sub>1" "dnormal \<phi>\<^sub>2"
  shows "dnormal (dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2)"
  using assms
proof(induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm_induct)
  case (DistribL \<psi> \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    apply(cases \<psi>) by auto
next
  case (NoDistrib \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    apply(cases \<phi>\<^sub>1; cases \<phi>\<^sub>2) by auto
qed simp

lemma dnormal_dnf_fm[intro]: "nfree \<phi> \<Longrightarrow> dnormal (dnf_fm \<phi>)"
  apply(induction \<phi>) by (auto simp: dnormal_dnf_and_fm)

fun "interp" :: "('model \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'model \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "interp I\<^sub>a M (Atom a) = I\<^sub>a M a" |
  "interp I\<^sub>a M (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp I\<^sub>a M \<phi>\<^sub>1 \<and> interp I\<^sub>a M \<phi>\<^sub>2)" |
  "interp I\<^sub>a M (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (interp I\<^sub>a M \<phi>\<^sub>1 \<or> interp I\<^sub>a M \<phi>\<^sub>2)" |
  "interp I\<^sub>a M (Neg \<phi>) = (\<not> interp I\<^sub>a M \<phi>)"

locale ATOM =
  fixes I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool"
begin

abbreviation I where "I \<equiv> interp I\<^sub>a"

lemma I_amap\<^sub>f\<^sub>m: "\<forall>x. I M (h x) = I\<^sub>a M x \<Longrightarrow> I M (amap\<^sub>f\<^sub>m h \<phi>) = I M \<phi>"
  by (induction \<phi>) auto

lemma I_dnf_and_fm: "nfree \<phi>\<^sub>1 \<Longrightarrow> nfree \<phi>\<^sub>2 \<Longrightarrow> I M (dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2) = I M (And \<phi>\<^sub>1 \<phi>\<^sub>2)"
  apply(induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm.induct)
  by auto

lemma I_dnf_fm: "nfree \<phi> \<Longrightarrow> I M (dnf_fm \<phi>) = I M \<phi>"
  apply(induction \<phi>)
  by (auto simp: I_dnf_and_fm)

lemma I_conj_list: "is_conj \<phi> \<Longrightarrow> (\<forall>a \<in> set (conj_list \<phi>). I\<^sub>a M a) = I M \<phi>"
  apply(induction \<phi>)
  by auto

lemma I_disj_conj_list: "dnormal \<phi> \<Longrightarrow>
  (\<exists>as \<in> set (disj_conj_list \<phi>). \<forall>a \<in> set as. I\<^sub>a M a) = I M \<phi>"
proof(induction \<phi>)
  case (And \<phi>1 \<phi>2)
  hence "is_conj (And \<phi>1 \<phi>2)" by simp
  from I_conj_list[OF this] show ?case by simp
qed auto

lemma I_dnf: "nfree \<phi> \<Longrightarrow> (\<exists>as \<in> set (dnf \<phi>). \<forall>a \<in> set as. I\<^sub>a M a) = I M \<phi>"
  unfolding dnf_def
  using I_disj_conj_list[OF dnormal_dnf_fm] I_dnf_fm by simp

end

locale nnf = ATOM I\<^sub>a for I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes aneg :: "'a \<Rightarrow> 'a fm"
  assumes nfree_aneg: "nfree (aneg a)"
  assumes I\<^sub>a_aneg: "interp I\<^sub>a M (aneg a) = (\<not> I\<^sub>a M a)"
begin

fun nnf :: "'a fm \<Rightarrow> 'a fm" where
  "nnf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
  "nnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
  "nnf (Neg (Neg \<phi>)) = (nnf \<phi>)" |
  "nnf (Neg (And \<phi>\<^sub>1 \<phi>\<^sub>2)) = (Or (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
  "nnf (Neg (Or \<phi>\<^sub>1 \<phi>\<^sub>2)) = (And (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
  "nnf (Neg (Atom a)) = aneg a" |
  "nnf \<phi> = \<phi>"

lemma nfree_nnf: "nfree (nnf \<phi>)"
  apply(induction \<phi> rule: nnf.induct)
  using nfree_aneg by auto

lemma I_nnf: "I M (nnf \<phi>) = I M \<phi>"
  by (induction rule: nnf.induct) (simp_all add: I\<^sub>a_aneg)

end

type_synonym var = int

datatype trm = Const String.literal | App trm trm | Var var

datatype prf_trm =
  PThm String.literal |
  Appt prf_trm trm |
  AppP prf_trm prf_trm |
  AbsP trm prf_trm |
  Bound trm |
  Conv trm prf_trm prf_trm

abbreviation "AppPs p ps \<equiv> foldl AppP p ps"
abbreviation "AppPThm s \<equiv> AppP (PThm s)"
abbreviation "ApptThm s \<equiv> Appt (PThm s)"
abbreviation "AppPThms s ps \<equiv> AppPs (PThm s) ps"

abbreviation "AtomConv \<equiv> AppPThm (STR ''atom_conv'')"
abbreviation "NegAtomConv \<equiv> AppPThm (STR ''neg_atom_conv'')"
abbreviation "BinopConv c1 c2 \<equiv>
  AppPThms (STR ''combination_conv'') [AppPThm (STR ''arg_conv'') c1, c2]"
abbreviation "ArgConv \<equiv> AppPThm (STR ''arg_conv'')"
abbreviation "NegNegConv \<equiv> PThm (STR ''not_not_conv'')"
abbreviation "NegAndConv \<equiv> PThm (STR ''de_Morgan_conj_conv'')"
abbreviation "NegOrConv \<equiv> PThm (STR ''de_Morgan_disj_conv'')"
abbreviation "ConjDisjDistribRConv \<equiv> PThm (STR ''conj_disj_distribR_conv'')"
abbreviation "ConjDisjDistribLConv \<equiv> PThm (STR ''conj_disj_distribL_conv'')"
abbreviation "ThenConv c1 c2 \<equiv> AppPThms (STR ''then_conv'') [c1, c2]"
abbreviation "AllConv \<equiv> PThm (STR ''all_conv'')"

fun trm_of_fm :: "('a \<Rightarrow> trm) \<Rightarrow> 'a fm \<Rightarrow> trm" where
"trm_of_fm f (Atom a) = f a" |
"trm_of_fm f (And \<phi>\<^sub>1 \<phi>\<^sub>2) = App (App (Const (STR ''conj'')) (trm_of_fm f \<phi>\<^sub>1)) (trm_of_fm f \<phi>\<^sub>2)" |
"trm_of_fm f (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = App (App (Const (STR ''disj'')) (trm_of_fm f \<phi>\<^sub>1)) (trm_of_fm f \<phi>\<^sub>2)" |
"trm_of_fm f (Neg \<phi>) = App (Const (STR ''Not'')) (trm_of_fm f \<phi>)"

fun thm_free :: "String.literal \<Rightarrow> prf_trm \<Rightarrow> bool" where
"thm_free a (PThm n) \<longleftrightarrow> a \<noteq> n" |
"thm_free a (AppP p1 p2) \<longleftrightarrow> thm_free a p1 \<and> thm_free a p2" |
"thm_free a (Appt p _) \<longleftrightarrow> thm_free a p"

abbreviation "a_conv_free \<equiv> thm_free (STR ''atom_conv'')"
abbreviation "aneg_conv_free \<equiv> thm_free (STR ''neg_atom_conv'')"

locale fm_conv_system = ATOM I\<^sub>a for I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes M :: 'model
  fixes a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool"
  fixes aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool"
begin

inductive convs :: "prf_trm \<Rightarrow> 'a fm \<Rightarrow> 'a fm \<Rightarrow> bool"
  ("_ : _ \<equiv>\<^sub>f\<^sub>m _" [] 60) where
  andC[simplified]: "p1 : A \<equiv>\<^sub>f\<^sub>m C \<Longrightarrow> p2 : B \<equiv>\<^sub>f\<^sub>m D \<Longrightarrow> BinopConv p1 p2 : And A B \<equiv>\<^sub>f\<^sub>m And C D" |
  orC[simplified]: "p1 : A \<equiv>\<^sub>f\<^sub>m C \<Longrightarrow> p2 : B \<equiv>\<^sub>f\<^sub>m D  \<Longrightarrow> BinopConv p1 p2 : Or A B \<equiv>\<^sub>f\<^sub>m Or C D" |
  negC: "p : A \<equiv>\<^sub>f\<^sub>m B  \<Longrightarrow> ArgConv p : Neg A \<equiv>\<^sub>f\<^sub>m Neg B" |
  negNegC: "NegNegConv : Neg (Neg A) \<equiv>\<^sub>f\<^sub>m A" |
  negAndC: "NegAndConv : Neg (And A B) \<equiv>\<^sub>f\<^sub>m Or (Neg A) (Neg B)" |
  negOrC: "NegOrConv : Neg (Or A B) \<equiv>\<^sub>f\<^sub>m And (Neg A) (Neg B)" |
  AtomC: "a_convs p a B\<Longrightarrow> AtomConv p : Atom a \<equiv>\<^sub>f\<^sub>m B" |
  negAtomC: "aneg_convs p a B \<Longrightarrow> NegAtomConv p : Neg (Atom a) \<equiv>\<^sub>f\<^sub>m B" |
  conjDisjDistribRC: "ConjDisjDistribRConv : And (Or A B) C \<equiv>\<^sub>f\<^sub>m Or (And A C) (And B C)" |
  conjDisjDistribLC: "ConjDisjDistribLConv : And A (Or B C) \<equiv>\<^sub>f\<^sub>m Or (And A B) (And A C)" |
  thenC[simplified]: "p1 : A \<equiv>\<^sub>f\<^sub>m B \<Longrightarrow> p2 : B \<equiv>\<^sub>f\<^sub>m C \<Longrightarrow> ThenConv p1 p2 : A \<equiv>\<^sub>f\<^sub>m C" |
  allC: "AllConv : A \<equiv>\<^sub>f\<^sub>m A"

lemma convs_sound:
  assumes "p : \<phi> \<equiv>\<^sub>f\<^sub>m \<psi>"
  assumes "\<And>ap a \<phi>\<^sub>a. a_convs ap a \<phi>\<^sub>a \<Longrightarrow> I\<^sub>a M a = I M \<phi>\<^sub>a"
  assumes "\<And>ap a \<phi>\<^sub>a. aneg_convs ap a \<phi>\<^sub>a \<Longrightarrow> \<not> (I\<^sub>a M a) = I M \<phi>\<^sub>a"
  shows "I M \<phi> = I M \<psi>"
  using assms
  apply(induction p \<phi> \<psi> rule: convs.induct) by auto

lemma convs_aneg_conv_free_sound:
  assumes "p : \<phi> \<equiv>\<^sub>f\<^sub>m \<psi>"
  assumes "aneg_conv_free p" "\<And>ap a \<phi>\<^sub>a. a_convs ap a \<phi>\<^sub>a \<Longrightarrow> I\<^sub>a M a = I M \<phi>\<^sub>a"
  shows "I M \<phi> = I M \<psi>"
  using assms
  apply (induction p \<phi> \<psi> rule: convs.induct) by auto

lemma convs_a_conv_free_sound:
  assumes "p : \<phi> \<equiv>\<^sub>f\<^sub>m \<psi>"
  assumes "a_conv_free p" "\<And>ap a \<phi>\<^sub>a. aneg_convs ap a \<phi>\<^sub>a \<Longrightarrow> \<not> (I\<^sub>a M a) = I M \<phi>\<^sub>a"
  shows "I M \<phi> = I M \<psi>"
  using assms
  apply(induction p \<phi> \<psi> rule: convs.induct) by auto

lemma convs_atom_conv_free_sound:
  assumes "p : \<phi> \<equiv>\<^sub>f\<^sub>m \<psi>"
  assumes "a_conv_free p" "aneg_conv_free p"
  shows "I M \<phi> = I M \<psi>"
  using assms
  apply(induction p \<phi> \<psi> rule: convs.induct) by auto

end

locale fm_conv = fm_conv_system I\<^sub>a M a_convs aneg_convs for
  I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" and
  M :: 'model and
  a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
  aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" +

  fixes conv :: "'a fm \<Rightarrow> 'a fm"
  fixes conv_prf :: "'a fm \<Rightarrow> prf_trm"
  assumes conv_convs: "conv_prf \<phi> : \<phi> \<equiv>\<^sub>f\<^sub>m (conv \<phi>) \<Longrightarrow> I M \<phi> = I M (conv \<phi>)"
begin
end

fun amap\<^sub>f\<^sub>m_prf :: "('a \<Rightarrow> prf_trm) \<Rightarrow> 'a fm \<Rightarrow> prf_trm" where
"amap\<^sub>f\<^sub>m_prf ap (Atom a) = AtomConv (ap a)" |
"amap\<^sub>f\<^sub>m_prf ap (And \<phi>\<^sub>1 \<phi>\<^sub>2) = BinopConv (amap\<^sub>f\<^sub>m_prf ap \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m_prf ap \<phi>\<^sub>2)" |
"amap\<^sub>f\<^sub>m_prf ap (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = BinopConv (amap\<^sub>f\<^sub>m_prf ap \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m_prf ap \<phi>\<^sub>2)" |
"amap\<^sub>f\<^sub>m_prf ap (Neg \<phi>) = ArgConv (amap\<^sub>f\<^sub>m_prf ap \<phi>)"

locale amap\<^sub>f\<^sub>m_conv = fm_conv_system I\<^sub>a M a_convs aneg_convs for
  I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" and
  M :: 'model and
  a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
  aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" +
  
  fixes atom_conv :: "'a \<Rightarrow> 'a fm"
  fixes atom_conv_prf :: "'a \<Rightarrow> prf_trm"
  assumes atom_conv_sound: "I M (atom_conv a) = I\<^sub>a M a"
  assumes aneg_conv_free_atom_conv_prf: "aneg_conv_free (atom_conv_prf a)"
  assumes atom_conv_prf_convs: "a_convs (atom_conv_prf a) a (atom_conv a)"
begin

lemma aneg_conv_free_amap\<^sub>f\<^sub>m_prf: "aneg_conv_free (amap\<^sub>f\<^sub>m_prf atom_conv_prf \<phi>)"
  using aneg_conv_free_atom_conv_prf by (induction \<phi>) auto

lemma amap\<^sub>f\<^sub>m_conv_convs: "amap\<^sub>f\<^sub>m_prf atom_conv_prf A : A \<equiv>\<^sub>f\<^sub>m amap\<^sub>f\<^sub>m atom_conv A"
  apply (induction A)
  using atom_conv_prf_convs AtomC andC orC negC by fastforce+

lemma I_amap\<^sub>f\<^sub>m_conv: "I M (amap\<^sub>f\<^sub>m atom_conv A) = I M A"
  by (simp add: ATOM.I_amap\<^sub>f\<^sub>m atom_conv_sound)

sublocale fm_conv: fm_conv I\<^sub>a M a_convs aneg_convs "amap\<^sub>f\<^sub>m atom_conv" "amap\<^sub>f\<^sub>m_prf atom_conv_prf"
  using I_amap\<^sub>f\<^sub>m_conv by unfold_locales blast

end
  

fun dnf_and_fm_prf :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> prf_trm" where
  "dnf_and_fm_prf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<psi> = ThenConv ConjDisjDistribRConv
    (BinopConv (dnf_and_fm_prf \<phi>\<^sub>1 \<psi>) (dnf_and_fm_prf \<phi>\<^sub>2 \<psi>))" |
  "dnf_and_fm_prf \<psi> (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = ThenConv ConjDisjDistribLConv
    (BinopConv (dnf_and_fm_prf \<psi> \<phi>\<^sub>1) (dnf_and_fm_prf \<psi> \<phi>\<^sub>2))" |
  "dnf_and_fm_prf \<phi>\<^sub>1 \<phi>\<^sub>2 = AllConv"

fun dnf_fm_prf :: "'a fm \<Rightarrow> prf_trm" where
  "dnf_fm_prf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = ThenConv (BinopConv (dnf_fm_prf \<phi>\<^sub>1) (dnf_fm_prf \<phi>\<^sub>2))
    (dnf_and_fm_prf (dnf_fm \<phi>\<^sub>1) (dnf_fm \<phi>\<^sub>2))" |
  "dnf_fm_prf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = BinopConv (dnf_fm_prf \<phi>\<^sub>1) (dnf_fm_prf \<phi>\<^sub>2)" |
  "dnf_fm_prf _ = AllConv"


locale dnf_fm_conv = fm_conv_system
begin

lemma dnf_and_fm_convs: "dnf_and_fm_prf \<phi>\<^sub>1 \<phi>\<^sub>2 : And \<phi>\<^sub>1 \<phi>\<^sub>2 \<equiv>\<^sub>f\<^sub>m dnf_and_fm \<phi>\<^sub>1 \<phi>\<^sub>2"
proof (induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm_induct)
  case (DistribR \<phi>\<^sub>1 \<phi>\<^sub>2 \<psi>)
  then show ?case
    using thenC[OF conjDisjDistribRC orC[OF DistribR.IH]] by simp
next
  case (DistribL \<psi> \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    using thenC[OF conjDisjDistribLC orC[OF DistribL.IH]] by (cases \<psi>) simp_all
next
  case (NoDistrib \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    apply(cases \<phi>\<^sub>1; cases \<phi>\<^sub>2) by (simp_all add: allC)
qed

lemma a_conv_free_dnf_and_fm_prf: "a_conv_free (dnf_and_fm_prf \<phi>\<^sub>1 \<phi>\<^sub>2)"
  by (induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm_prf.induct) auto

lemma aneg_conv_free_dnf_and_fm_prf: "aneg_conv_free (dnf_and_fm_prf \<phi>\<^sub>1 \<phi>\<^sub>2)"
  by (induction \<phi>\<^sub>1 \<phi>\<^sub>2 rule: dnf_and_fm_prf.induct) auto

lemma dnf_fm_convs: "dnf_fm_prf \<phi> : \<phi> \<equiv>\<^sub>f\<^sub>m dnf_fm \<phi>"
proof(induction \<phi>)
  case (And \<phi>1 \<phi>2)
  then show ?case
    using thenC[where ?B="And (dnf_fm \<phi>1) (dnf_fm \<phi>2)", OF andC]
    by (simp add: dnf_and_fm_convs)
qed (auto simp: convs.intros)

lemma a_conv_free_dnf_fm_prf: "a_conv_free (dnf_fm_prf \<phi>)"
  using a_conv_free_dnf_and_fm_prf
  by (induction \<phi> rule: dnf_fm_prf.induct) auto

lemma aneg_conv_free_dnf_fm_prf: "aneg_conv_free (dnf_fm_prf \<phi>)"
  using aneg_conv_free_dnf_and_fm_prf
  by (induction \<phi> rule: dnf_fm_prf.induct) auto

sublocale fm_conv: fm_conv I\<^sub>a M a_convs aneg_convs dnf_fm dnf_fm_prf
  apply(unfold_locales)
  using convs_atom_conv_free_sound[OF _ a_conv_free_dnf_fm_prf aneg_conv_free_dnf_fm_prf] .

end


locale nnf_conv = nnf I\<^sub>a aneg + fm_conv_system I\<^sub>a M a_convs aneg_convs for
  I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" and aneg :: "'a \<Rightarrow> 'a fm" and
  M :: 'model and
  a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
  aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" +

  fixes aneg_prf :: "'a \<Rightarrow> prf_trm"
  assumes a_conv_free_aneg_prf: "a_conv_free (aneg_prf a)"
  assumes aneg_convs: "aneg_convs (aneg_prf a) a (aneg a)"
  assumes a_convs_sound: "aneg_convs p a A \<Longrightarrow> (\<not> I\<^sub>a M a) = I M A"
begin

fun nnf_prf :: "'a fm \<Rightarrow> prf_trm" where
  "nnf_prf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = BinopConv (nnf_prf \<phi>\<^sub>1) (nnf_prf \<phi>\<^sub>2)" |
  "nnf_prf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = BinopConv (nnf_prf \<phi>\<^sub>1) (nnf_prf \<phi>\<^sub>2)" |
  "nnf_prf (Neg (Neg \<phi>)) = ThenConv NegNegConv (nnf_prf \<phi>)" |
  "nnf_prf (Neg (And \<phi>\<^sub>1 \<phi>\<^sub>2)) = ThenConv NegAndConv
    (BinopConv (nnf_prf (Neg \<phi>\<^sub>1)) (nnf_prf (Neg \<phi>\<^sub>2)))" |
  "nnf_prf (Neg (Or \<phi>\<^sub>1 \<phi>\<^sub>2)) = ThenConv NegOrConv
    (BinopConv (nnf_prf (Neg \<phi>\<^sub>1)) (nnf_prf (Neg \<phi>\<^sub>2)))" |
  "nnf_prf (Neg (Atom a)) = NegAtomConv (aneg_prf a)" |
  "nnf_prf \<phi> = AllConv"

lemma a_conv_free_nnf_prf: "a_conv_free (nnf_prf \<phi>)"
  using a_conv_free_aneg_prf
  apply(induction \<phi> rule: nnf_prf.induct) by auto

sublocale fm_conv: fm_conv I\<^sub>a M a_convs aneg_convs nnf nnf_prf
  using a_convs_sound a_conv_free_nnf_prf
  apply(unfold_locales)
  by (simp add: I_nnf)

lemma nnf_convs: "nnf_prf \<phi> : \<phi> \<equiv>\<^sub>f\<^sub>m nnf \<phi>"
proof(induction \<phi> rule: nnf.induct)
  case (3 \<phi>)
  then show ?case 
    by (auto simp: convs.intros intro: thenC[where ?B=\<phi>])
next
  case (4 \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    by (auto simp: convs.intros intro: thenC[where ?B="Or (Neg \<phi>\<^sub>1) (Neg \<phi>\<^sub>2)"])
next
  case (5 \<phi>\<^sub>1 \<phi>\<^sub>2)
  then show ?case
    by (auto simp: convs.intros intro: thenC[where ?B="And (Neg \<phi>\<^sub>1) (Neg \<phi>\<^sub>2)"])
qed (auto simp: aneg_convs convs.intros)

end

definition "Atoms A \<equiv> {a |a. Atom a \<in> A}"

lemma Atoms_Un[simp]: "Atoms (A \<union> B) = Atoms A \<union> Atoms B"
  unfolding Atoms_def by auto

lemma Atoms_mono: "A \<subseteq> B \<Longrightarrow> Atoms A \<subseteq> Atoms B"
  unfolding Atoms_def by auto

abbreviation "ConjE trm_of c d p \<equiv>
  AppPThms (STR ''conjE'') [Bound (trm_of (And c d)), AbsP (trm_of c) (AbsP (trm_of d) p)]"
abbreviation "DisjE trm_of c d p1 p2 \<equiv>
  AppPThms (STR ''disjE'') [Bound (trm_of (Or c d)), AbsP (trm_of c) p1, AbsP (trm_of d) p2]"

locale prop_fm_system = fm_conv_system I\<^sub>a M a_convs aneg_convs for 
    I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" and
    M :: 'model and
    a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
    aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" +

  fixes atom_proves :: "'a set \<Rightarrow> prf_trm \<Rightarrow> 'a fm \<Rightarrow> bool"
  fixes trm_of_atom :: "'a \<Rightarrow> trm"
  assumes atom_proves_sound: "atom_proves A ap \<phi> \<Longrightarrow> \<forall>a \<in> A. I\<^sub>a M a \<Longrightarrow> I M \<phi>"
  assumes atom_proves_weaken: "atom_proves A ap \<phi> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> atom_proves B ap \<phi>"
  assumes convs_sound: "convs cp \<phi> \<psi> \<Longrightarrow> I M \<phi> = I M \<psi>"
begin

abbreviation "trm_of \<equiv> trm_of_fm trm_of_atom"

inductive proves :: "'a fm set \<Rightarrow> prf_trm \<Rightarrow> 'a fm \<Rightarrow> bool"
  ("_ \<turnstile> _ : _" [] 50) where
  conjE[simplified]: "And c d \<in> A \<Longrightarrow> insert c (insert d A) \<turnstile> p : \<phi>
    \<Longrightarrow> A \<turnstile> ConjE trm_of c d p : \<phi>" |
  disjE[simplified]: "Or c d \<in> A \<Longrightarrow> insert c A \<turnstile> p1 : \<phi> \<Longrightarrow> insert d A \<turnstile> p2 : \<phi>
    \<Longrightarrow> A \<turnstile> DisjE trm_of c d p1 p2 : \<phi>" |
  conv[simplified]: "c \<in> A \<Longrightarrow> cp : c \<equiv>\<^sub>f\<^sub>m d \<Longrightarrow> insert d A \<turnstile> p : \<phi>
    \<Longrightarrow> A \<turnstile> Conv (trm_of c) cp p : \<phi>" |
  lift: "atom_proves (Atoms A) p \<phi> \<Longrightarrow> A \<turnstile> p : \<phi>"

lemma lift2: "atom_proves A p \<phi> \<Longrightarrow> Atom ` A \<turnstile> p : \<phi>"
  using proves.lift unfolding Atoms_def
  by (simp add: atom_proves_weaken subsetI)

lemma proves_sound: "A \<turnstile> p : \<phi> \<Longrightarrow> \<forall>\<alpha> \<in> A. I M \<alpha> \<Longrightarrow> I M \<phi>"
proof(induction A p \<phi> rule: proves.induct)
  case (conv c A d cp p \<phi>)
  then show ?case using convs_sound by fastforce
next
  case (lift A p a)
  then show ?case using atom_proves_sound unfolding Atoms_def by fastforce
qed fastforce+

lemma proves_contr:
  assumes "A \<turnstile> p : \<phi>"
  assumes "\<not> I M \<phi>"
  obtains \<psi> where "\<psi> \<in> A" "\<not> I M \<psi>"
  using assms proves_sound by blast

lemma proves_weaken_Un: "A \<turnstile> p : \<phi> \<Longrightarrow> A \<union> B \<turnstile> p : \<phi>"
proof(induction A p \<phi> arbitrary: B rule: proves.induct)
  case (lift A p \<phi>)
  then have "atom_proves (Atoms (A \<union> B)) p \<phi>"
    unfolding Atoms_def
    using atom_proves_weaken[where ?B="{a |a. Atom a \<in> A \<union> B}"] by auto
  then show ?case by (auto simp: proves.lift)
qed (fastforce intro: proves.intros)+

lemma proves_weaken: "A \<turnstile> p : \<phi> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<turnstile> p : \<phi>"
  using proves_weaken_Un unfolding subset_Un_eq by metis

end

context
  fixes trm_of_atom :: "'a \<Rightarrow> trm"
begin

fun from_conj_prf :: "prf_trm \<Rightarrow> 'a fm \<Rightarrow> prf_trm" where
"from_conj_prf p (And a b) = ConjE (trm_of_fm trm_of_atom) a b (from_conj_prf (from_conj_prf p b) a)" |
"from_conj_prf p (Atom a) = p"

end

context
  fixes trm_of_atom :: "'a \<Rightarrow> trm"
  fixes contr_atom_prf :: "'a list \<Rightarrow> prf_trm option"
begin

fun contr_fm_prf :: "'a fm \<Rightarrow> prf_trm option" where
"contr_fm_prf (Or c d) =
  (case contr_fm_prf c of
    Some p1 \<Rightarrow> map_option (DisjE (trm_of_fm trm_of_atom) c d p1) (contr_fm_prf d)
  | _ \<Rightarrow> None)" |
"contr_fm_prf (And a b) =
  (case contr_atom_prf (conj_list (And a b)) of
    None \<Rightarrow> None
  | Some p \<Rightarrow> Some (from_conj_prf trm_of_atom p (And a b)))" |
"contr_fm_prf (Atom a) = contr_atom_prf [a]"

end

lemma (in prop_fm_system) from_conj_prf_proves:
  assumes "is_conj \<phi>"
  assumes proves_conj_list: "Atom ` set (conj_list \<phi>) \<union> A \<turnstile> p : \<psi>"
  shows "insert \<phi> A \<turnstile> from_conj_prf trm_of_atom p \<phi> : \<psi>"
  using assms
proof(induction p \<phi> arbitrary: A rule: from_conj_prf.induct[of _ trm_of_atom])
  case (1 p a b)
  from "1.IH"[where ?A="Atom ` set (conj_list a) \<union> A"] "1.prems"
  have "Atom ` set (conj_list a) \<union> insert b A \<turnstile> from_conj_prf trm_of_atom p b : \<psi>"
    by (simp add: image_Un Un_commute sup_left_commute)
  from "1.IH"(2)[OF _ this] "1.prems"
  have "insert a (insert b (insert (And a b) A))
    \<turnstile> from_conj_prf trm_of_atom (from_conj_prf trm_of_atom p b) a : \<psi>"
    using proves_weaken[where ?B="insert a (insert b (insert (And a b) A))"]
    by auto
  with "1.prems" show ?case using proves.conjE by simp
next
  case (2 p a)
  then show ?case
    using proves_weaken_Un[where ?B="A" and ?A="{Atom a}"] by simp
qed simp_all


locale contr_fm = prop_fm_system I\<^sub>a M a_convs aneg_convs atom_proves for 
    I\<^sub>a :: "'model \<Rightarrow> 'a \<Rightarrow> bool" and
    M :: 'model and
    a_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
    aneg_convs :: "prf_trm \<Rightarrow> 'a \<Rightarrow> 'a fm \<Rightarrow> bool" and
    atom_proves :: "'a set \<Rightarrow> prf_trm \<Rightarrow> 'a fm \<Rightarrow> bool" +
    
  fixes contr_atom_prf :: "'a list \<Rightarrow> prf_trm option"
  fixes Fls :: 'a
  assumes I\<^sub>a_Fls: "\<not> I\<^sub>a M Fls"
  assumes contr_atom_prf_proves: "contr_atom_prf A = Some p \<Longrightarrow> atom_proves (set A) p (Atom Fls)"
begin

lemma contr_fm_prf_proves:
  assumes "dnormal \<phi>"
  assumes "contr_fm_prf trm_of_atom contr_atom_prf \<phi> = Some p"
  shows "insert \<phi> A \<turnstile> p : Atom Fls"
  using assms
proof(induction \<phi> arbitrary: p)
  case (Atom x)
  then show ?case
    using contr_atom_prf_proves[THEN lift2] proves_weaken_Un by fastforce
next
  case (And \<phi>1 \<phi>2)
  then obtain pa where
    p: "p = from_conj_prf trm_of_atom pa (And \<phi>1 \<phi>2)" and
    pa: "contr_atom_prf (conj_list (And \<phi>1 \<phi>2)) = Some pa"
    by (auto split: option.splits)
  with contr_atom_prf_proves[OF pa]
  have "Atom ` set (conj_list (And \<phi>1 \<phi>2)) \<union> A \<turnstile> pa : (Atom Fls)"
    using lift2 proves_weaken_Un by blast
  from from_conj_prf_proves[OF _ this] \<open>dnormal (And \<phi>1 \<phi>2)\<close> show ?case
    unfolding p by simp
next
  case (Or \<phi>1 \<phi>2)
  then obtain p1 p2 where
    p: "p = DisjE trm_of \<phi>1 \<phi>2 p1 p2" and
    "insert \<phi>1 A \<turnstile> p1 : Atom Fls" "insert \<phi>2 A \<turnstile> p2 : Atom Fls"
    by (auto split: option.splits)
  then have
    "insert \<phi>1 (insert (Or \<phi>1 \<phi>2) A) \<turnstile> p1 : Atom Fls"
    "insert \<phi>2 (insert (Or \<phi>1 \<phi>2) A) \<turnstile> p2 : Atom Fls"
    by (metis insert_commute proves_weaken subset_insertI)+
  from proves.disjE[OF insertI1 this] p show ?case by simp
qed simp

lemma contr_fm_prf_sound:
  assumes "dnormal \<phi>"
  assumes "contr_fm_prf trm_of_atom contr_atom_prf \<phi> = Some p"
  shows "\<not> I M \<phi>"
  using contr_fm_prf_proves[OF assms] I\<^sub>a_Fls proves_sound by fastforce

lemma contr_dnf_fm_prf_proves:
  assumes "nfree \<phi>"
  assumes "map_option (Conv (trm_of_fm trm_of_atom \<phi>) (dnf_fm_prf \<phi>)) 
    (contr_fm_prf trm_of_atom contr_atom_prf (dnf_fm \<phi>)) = Some p"
  shows "insert \<phi> A \<turnstile> p: Atom Fls"
  using assms
  using contr_fm_prf_proves conv[OF _ dnf_fm_conv.dnf_fm_convs]
  by blast

end

lemma (in ATOM) Ex_conj_contr_atom_prf_None:
  assumes "dnormal \<phi>"
  assumes "contr_fm_prf trm_of_atom contr_atom_prf \<phi> = None"
  shows "\<exists>A \<in> set (disj_conj_list \<phi>). contr_atom_prf A = None"
  using assms
  by (induction \<phi>) (auto split: option.splits)

lemma (in ATOM) I_fm_if_I_conj:
  assumes "dnormal \<phi>"
  assumes "A \<in> set (disj_conj_list \<phi>)" "\<forall>a \<in> set A. I\<^sub>a M a"
  shows "I M \<phi>"
  using assms
proof(induction \<phi>)
  case (And \<phi>1 \<phi>2)
  then show ?case using I_disj_conj_list by blast
qed auto

end