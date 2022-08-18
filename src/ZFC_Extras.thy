theory ZFC_Extras
  imports ZFC_in_HOL.ZFC_in_HOL
begin

abbreviation "vset \<equiv> ZFC_in_HOL.set"

hide_const (open) ZFC_in_HOL.set
  
instantiation V :: minus
begin
definition "s - t \<equiv> vset (elts s - elts t)"

instance ..
end

lemma small_Diff[intro]: "small s \<Longrightarrow> small (s - t)" 
  by (meson Diff_subset smaller_than_small)

lemma elts_minus[simp]: "elts (t1 - t2) = elts t1 - elts t2"
  unfolding minus_V_def by auto

lemma elts_inf[simp]: "elts (s \<sqinter> t) = elts s \<inter> elts t"
  unfolding inf_V_def
  by (meson down elts_of_set inf_le2)

lemma vset_eq_0_iff: "small X \<Longrightarrow> vset X = 0 \<longleftrightarrow> X = {}"
  using small_iff by force

end