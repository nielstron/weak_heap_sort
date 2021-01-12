theory Tree_Exist
imports Main "HOL-Library.Tree"
begin

subsection "Existence of Trees"

text \<open>As the height/size theorem in the weak heap definition is shown
based on a comparison to a complete tree of similar height,
this short proof shows that a complete tree of a given height always exists (constructively)\<close>

find_theorems "\<exists>x. size x = _"

fun build_tree :: "nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"build_tree 0 a = Leaf" |
"build_tree (Suc n) a = \<langle>build_tree n a, a, build_tree n a\<rangle>"

lemma build_height: "height (build_tree n a) = n"
  by (induction n) auto

lemma build_complete: "complete (build_tree n a)"
  by (induction n) auto

lemma Ex_complete_tree_of_height: "\<exists>t. height (t:: 'a tree) = n \<and> complete t"
proof
  show "height (build_tree n undefined) = n \<and> complete (build_tree n undefined)" using build_complete[of n undefined] build_height[of n undefined] by simp
qed

corollary Ex_tree_of_height: "\<exists>t. height (t:: 'a tree) = n"
  using Ex_complete_tree_of_height by auto

end