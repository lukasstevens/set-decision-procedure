theory Set_Proc_All
  imports Set_Proc
begin

chapter \<open>Outline of the Formalisation\<close>

text \<open>
  We reference the most important aspects of the formalisation here
  and highlight the (mostly syntactic) differences between the paper
  and the formalisation.
  The sections roughly correspond to the sections in the paper.
\<close>

section \<open>Syntax and Semantics\<close>

subsection \<open>Syntax\<close>
text \<open>
  Datatypes:
    \<^item> Propositional formulae: @{datatype fm}. The formalisation uses constructors like @{term And}
      instead of \<open>\<^bold>\<and>\<close>.
    \<^item> Set terms: @{datatype pset_term}
    \<^item> Set atoms: @{datatype pset_atom}
\<close>
text \<open>
  Important constants:
    \<^item> @{const vars}
    \<^item> @{const atoms}
    \<^item> @{const subterms}
    \<^item> @{const subfms}
    \<^item> @{const is_literal}
\<close>

subsection \<open>Semantics\<close>

text \<open>
  Interpretation functions:
    \<^item> @{const I\<^sub>s\<^sub>t}
    \<^item> @{const I\<^sub>s\<^sub>a}
    \<^item> \<open>\<Turnstile>\<close> corresponds to @{term \<open>interp I\<^sub>s\<^sub>a\<close>}
\<close>

thm I\<^sub>s\<^sub>t.simps I\<^sub>s\<^sub>a.simps interp.simps

section \<open>Tableau Calculus\<close>

text \<open>
  Type of branches @{typ \<open>'a branch\<close>}.
  Closedness @{const bclosed} and Openness @{const bopen}.
\<close>

thm bclosed.intros

text \<open>
  Instead of triangles such as \<open>\<triangleright>\<close>, we use the constant names
  @{const lexpands}, @{const bexpands}, and @{const expandss} for
  linear expansion, branching expansion, and expansion closure, respectively.
  Note that the term-for-term substitution that is denoted by \<open>l{s/t}\<close> in the paper
  corresponds to @{const subst_tlvl}.
  
  Further important constants:
    \<^item> @{const lin_sat}
    \<^item> @{const sat}
    \<^item> @{const wits}
    \<^item> @{const wf_branch}
\<close>

thm lin_sat_def sat_def wits_def wf_branch_def
thm subst_tlvl.simps

section \<open>Abstract Specification of the Decision Procedure\<close>

text \<open>
  Since Hilbert choice (such as @{term \<open>SOME x. P\<close>}) does not allow for refinement,
  we parametrise the abstract specification @{const mlss_proc.mlss_proc_branch} of the
  decision procedure by two choice functions \<open>lexpand\<close> and \<open>bexpand\<close>.
  This parametrisation is realised by the locale @{locale mlss_proc}.
  
  See also: @{const mlss_proc.mlss_proc}.
\<close>

section \<open>Completeness\<close>

text \<open>
  Constants needed for the realisation function:
    \<^item> The terms defined by @{const base_vars} receive special treatment from the realisation function.
      Without typing @{const base_vars} is equal to the pure witnesses @{const pwits}.
    \<^item> Rest of the subterms @{const subterms'}
    \<^item> Realisation graph @{const bgraph}
  In contrast to the paper, we put the the realisation function @{const realisation.realise} into
  a locale @{locale realisation} and prove its properties abstractly.
  Then, we instantiate the locale with the above constants. Since this takes place in the context,
  we put this into the locale @{locale open_branch}.
\<close>

thm base_vars_def pwits_def subterms'_def
thm realisation.realise.simps

subsection \<open>Characterisation of the Pure Witnesses\<close>

thm lemma_2

subsection \<open>Realisation of an Open Branch\<close>
text \<open>
  The assumption that the branch is open is captured by the locale @{locale open_branch}.
  Important theorems:
\<close>
context open_branch
begin
thm realise.simps

thm realisation_if_AT_mem realisation_if_AT_eq
    realisation_if_AF_eq realisation_if_AF_mem
thm realisation_simps
thm I\<^sub>s\<^sub>t_realisation_eq_realisation coherence
end


section \<open>Soundness of the Calculus\<close>

thm bclosed_sound lexpands_sound bexpands_sound


section \<open>Total Correctness of the Procedure\<close>

subsection \<open>Abstract Specification\<close>
thm card_wf_branch_ub

context mlss_proc
begin
thm mlss_proc_branch_dom_if_wf_branch

thm mlss_proc_branch_complete mlss_proc_branch_sound

thm mlss_proc_complete mlss_proc_sound
end

end