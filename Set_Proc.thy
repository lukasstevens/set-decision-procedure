theory Set_Proc
  imports Main
begin

type_synonym var = int

datatype 'a set_expr = Intersect 'a 'a | Union 'a 'a | Diff 'a 'a | Var 'a | Empty

datatype 'a set_atom = Eq 'a "'a set_expr" | NotEq 'a 'a | SubsetEq 'a 'a
print_theorems

fun I\<^sub>s\<^sub>e where
  "I\<^sub>s\<^sub>e v (Intersect x y) = v x \<inter> v y"
| "I\<^sub>s\<^sub>e v (Union x y) = v x \<union> v y"
| "I\<^sub>s\<^sub>e v (Diff x y) = v x - v y"
| "I\<^sub>s\<^sub>e v (Var x) = v x"
| "I\<^sub>s\<^sub>e _ Empty = {}"

fun I\<^sub>s\<^sub>a where
  "I\<^sub>s\<^sub>a v (Eq x e) \<longleftrightarrow> v x = I\<^sub>s\<^sub>e v e"
| "I\<^sub>s\<^sub>a v (NotEq x y) \<longleftrightarrow> v x \<noteq> v y"
| "I\<^sub>s\<^sub>a v (SubsetEq x y) \<longleftrightarrow> v x \<subseteq> v y"

definition "Is\<^sub>s\<^sub>a v C \<equiv> (\<forall>a \<in> C. I\<^sub>s\<^sub>a v a)"

fun place1 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set_atom \<Rightarrow> bool" where
  "place1 p (Eq x (Intersect y z)) \<longleftrightarrow> p x = (p y \<and> p z)"
| "place1 p (Eq x (Union y z)) \<longleftrightarrow> p x = (p y \<or> p z)"
| "place1 p (Eq x (Diff y z)) \<longleftrightarrow> p x = (p y \<and> \<not> p z)"
| "place1 p (Eq x (Var y)) \<longleftrightarrow> p x = p y"
| "place1 p (Eq x Empty) \<longleftrightarrow> p x = False"
| "place1 p (SubsetEq x y) \<longleftrightarrow> (p x \<longrightarrow> p y)"
| "place1 p (NotEq _ _) \<longleftrightarrow> True"

definition "place C p \<equiv> (\<forall>a \<in> C. place1 p a)"

definition "ample C P \<equiv> (\<forall>p \<in> P. place C p) \<and> (\<forall>x y. (NotEq x y \<in> C) \<longrightarrow> (\<exists>p \<in> P. p x \<noteq> p y))"

lemma Ex_ample_if_Is\<^sub>s\<^sub>a: "Is\<^sub>s\<^sub>a v C \<Longrightarrow> \<exists>A. ample C A"
proof -
  assume "Is\<^sub>s\<^sub>a v C"
  define U where "U \<equiv> \<Union>c \<in> C. \<Union>(v ` set_set_atom c)"
  define p where "p \<equiv> (\<lambda>u x. u \<in> v x)"
  have "place C (p u)" if "u \<in> U" for u
  proof (unfold place_def, intro ballI)
    fix a assume "a \<in> C"
    with \<open>Is\<^sub>s\<^sub>a v C\<close> have "I\<^sub>s\<^sub>a v a"
      unfolding Is\<^sub>s\<^sub>a_def by blast
    with \<open>a \<in> C\<close> that show "place1 (p u) a"
      by (induction "p u" a rule: place1.induct) (auto simp: U_def p_def)
  qed
  moreover
  have subset_U: "NotEq x y \<in> C \<Longrightarrow> v x \<subseteq> U \<and> v y \<subseteq> U" for x y
    unfolding U_def by auto
  from \<open>Is\<^sub>s\<^sub>a v C\<close>[unfolded Is\<^sub>s\<^sub>a_def] have "v x \<noteq> v y" if "NotEq x y \<in> C" for x y
    using that by auto
  with subset_U have "\<exists>u \<in> U. p u x \<noteq> p u y" if "NotEq x y \<in> C" for x y
    using that unfolding p_def by (metis psubsetE psubsetI subset_iff)
  ultimately show ?thesis
    unfolding ample_def by (metis mem_Collect_eq)
qed

lemma Is\<^sub>s\<^sub>a_if_Ex_ample: "ample C A \<Longrightarrow> \<exists>v::'a \<Rightarrow> ('a \<Rightarrow> bool) set. Is\<^sub>s\<^sub>a v C"
proof -
  assume "ample C A"
  define v where "v \<equiv> (\<lambda>x. {p \<in> A. p x})"
  have "Is\<^sub>s\<^sub>a v C"
  proof(unfold Is\<^sub>s\<^sub>a_def, intro ballI)
    fix a assume "a \<in> C"
    show "I\<^sub>s\<^sub>a v a"
    proof(cases a)
      case (Eq x e)
      with \<open>a \<in> C\<close> \<open>ample C A\<close> show ?thesis
        unfolding ample_def by (cases e) (fastforce simp: v_def place_def)+
    next
      case (NotEq x y)
      with \<open>a \<in> C\<close> \<open>ample C A\<close> show ?thesis
        unfolding ample_def by (auto simp: v_def)
    next
      case (SubsetEq x y)
      with \<open>a \<in> C\<close> \<open>ample C A\<close> show ?thesis
        unfolding ample_def by (fastforce simp: v_def place_def)
    qed
  qed
  then show ?thesis
    by blast
qed
    
 
end