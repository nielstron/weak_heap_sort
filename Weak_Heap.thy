theory Weak_Heap
   imports Complex_Main "HOL-Library.Tree" "Tree_Exist" "HOL-Data_Structures.Tree_Set"  "HOL-Library.Pattern_Aliases"  "HOL-Library.Multiset" "HOL-Library.Tree_Multiset"
begin
context includes pattern_aliases
begin

subsection "Weak Heaps"

text\<open>Heaps were first studied by R.D. Dutton(93). Their definition and some basic properties are shown in this section.\<close>


text\<open>We first introduce the definition of the nodes of heap trees as introduced by Dutton(93) and then show its equivalence
to a modularized form that is seperated into "almost completeness" and a "right heap" property.
Finally a weak heap is defined equivalently as a node without left child and a right child that is a weak heap node, where the root must also be the minimum of the whole tree.\<close>


(* Here the number of levels of the tree is passed in the definition
   to make sure there is a global notion of "last two layers" *)

fun weak_heap_node_dutton :: "nat  \<Rightarrow> 'a::linorder tree \<Rightarrow> bool" where
"weak_heap_node_dutton n Leaf = (n \<le> 1)" | (* note that this implies that leafs are only found in the last two layers *)
"weak_heap_node_dutton n (Node l a r =: t) = (case n of 0 \<Rightarrow> False | Suc m \<Rightarrow>
   weak_heap_node_dutton m l \<and> weak_heap_node_dutton m r \<and>
   (\<forall>x \<in> set_tree r. a \<le> x)
)"


(* Slightly simplify the definition and seperate right-heap property and almost completeness*)
fun almost_complete :: "nat  \<Rightarrow> 'a tree \<Rightarrow> bool" where
"almost_complete n Leaf = (n \<le> 1)" |
"almost_complete n (Node l a r) = (case n of 0 \<Rightarrow> False | Suc m \<Rightarrow>
   almost_complete m l \<and> almost_complete m r
)"

fun right_heap :: "'a::linorder tree \<Rightarrow> bool" where
"right_heap Leaf = True" |
"right_heap (Node l a r =: t) = (
   right_heap l \<and> right_heap r \<and>
   (\<forall>x \<in> set_tree r. a \<le> x)
)"

fun weak_heap_node :: "nat  \<Rightarrow> 'a::linorder tree \<Rightarrow> bool" where
"weak_heap_node n t = (almost_complete n t \<and> right_heap t)"

(* We show that this is equivalent to the naive formulation *)
lemma "weak_heap_node_dutton n t \<longleftrightarrow> weak_heap_node n t"
   by (induction n t rule: weak_heap_node_dutton.induct) (auto split: nat.splits)

(* a heap then is the root, with only a weak heap node on the right, holding the minimal element *)
fun weak_heap :: "'a::linorder tree \<Rightarrow> bool" where
"weak_heap Leaf = True" |
"weak_heap (Node l a r) = (
  (l = Leaf) \<and> (\<forall>x \<in> set_tree r. a \<le> x) \<and> weak_heap_node (height r) r
)"

(* which is equivalent to 1. whole tree right heap 2. right node weak heap node *)
fun weak_heap_alt :: "'a::linorder tree \<Rightarrow> bool" where
"weak_heap_alt Leaf = True" |
"weak_heap_alt (Node l a r =: t) = (
  (l = Leaf) \<and> right_heap t \<and> weak_heap_node (height r) r
)"

lemma weak_heap_alt_eq: "weak_heap_alt t = weak_heap t"
  apply(cases t)
   apply(auto)
  done

end

(* Examples by Edelkamp (2013) *)
value "weak_heap (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 
value "weak_heap (\<langle>\<langle>\<rangle>, (1::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 8, \<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<langle>\<rangle>, 5, \<langle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 

(* This is a Counter-Example that breaks the "Leaf in last two layers" property *)
value "weak_heap (\<langle>\<langle>\<rangle>, (1::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 8, \<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<rangle>, 7, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 


lemma weak_heap_height: "almost_complete n t \<Longrightarrow> height t = n \<or> height t = n - 1"
  apply(induction n t rule: almost_complete.induct)
   apply(auto split: nat.splits)
  apply(fastforce)+
  done

lemma weak_heap_minheight: "almost_complete n t \<Longrightarrow> min_height t = n \<or> min_height t = n - 1"
  apply(induction n t rule: almost_complete.induct)
   apply(auto split: nat.splits)
  apply(fastforce)+
  done


lemma almost_complete_children: assumes "almost_complete n t" "t = \<langle>l, a, r\<rangle>" shows "height l - height r \<le> 1 \<and> height r - height l \<le> 1"
using assms
proof (cases n)
  case (Suc m)
  then have "almost_complete m r" using assms by auto
  then have h_r: "height r = m \<or> height r = m-1" using weak_heap_height by auto

  from Suc have "almost_complete m l" using assms by auto
  then have h_l: "height l = m \<or> height l = m-1" using weak_heap_height by auto

  from h_r h_l show ?thesis by auto
qed auto


(* We first show an upper bound on the size, following directly from the upper bound on trees in general
   since a complete tree is an almost complete tree as well *)

lemma complete_almost_complete: "complete t \<Longrightarrow> almost_complete (height t) t"
  by (induction t) auto


corollary weak_heap_node_size_upper:
  assumes "almost_complete n t"
  shows "size t \<le> 2^n - 1"
proof -
  from assms have "height t = n \<or> height t = n-1" using weak_heap_height by auto
  then show ?thesis using size_height
      by (metis diff_le_mono diff_le_self one_le_numeral order_trans power_increasing)
qed

corollary weak_heap_size_upper: assumes "weak_heap t" shows "size t \<le> 2^(height t - 1)"
proof (cases t)
  case (Node l a r)
  from Node have "weak_heap_node (height r) r" using assms by auto
  then have r_size: "size r \<le> 2^(height r) - 1" using weak_heap_node_size_upper by auto
  from Node have l_size: "l = Leaf" using assms by simp

  from Node have "size t = size r + 1" using l_size by simp
  also have "\<dots> \<le> 2^(height r)" using r_size by (cases r) auto
  also have "\<dots> = 2^(height t-1)" using Node assms by auto
  finally show ?thesis by simp
qed auto

text\<open>
  Now we show a lower bound on the size of the tree.
  In particular, in the "worst case" of an almost complete tree
  at most the whole last level can be missing (in comparison to a complete tree of similar height).
  In the complete tree, this last level contains as many nodes as all levels above together.
  Hence we show this by a direct comparison with a complete tree of similar height.
\<close>

find_theorems size complete
find_theorems height complete

lemma weak_heap_height_complete: "\<lbrakk>almost_complete n t; complete t'; height t' = n\<rbrakk> \<Longrightarrow> 2*size t + 1 \<ge> size t'"
proof (induction n t  arbitrary: t' rule: almost_complete.induct)
  case (1 n)
  have "n = 1 \<or> n = 0" using weak_heap_height[of n "\<langle>\<rangle>"] 1 by auto
  then show ?case
  proof
    assume "n = 1"
    then have "height t' = 1" using 1 by simp
    then have "size t' = 1" using size_if_complete 1 by fastforce
    then show ?thesis by auto
  next
    assume "n = 0"
    then have "height t' = 0" using 1 by simp
    then have "size t' = 0" using size_if_complete 1 by fastforce
    then show ?thesis by auto
  qed
next
  case (2 n l a r)
  then obtain m where "n = Suc m" by (metis One_nat_def Suc_eq_plus1 diff_is_0_eq' height_tree.elims tree.size(3) tree.size(4) weak_heap_height zero_le_one)
  then obtain l' a' r' where t'_split: "t' = Node l' a' r'" using "2.prems"(3) height_tree.elims by blast

  have l_size: "size l' \<le> 2*size l + 1" using 2 t'_split by auto
  have r_size: "size r' \<le> 2*size r + 1" using 2 t'_split by auto

  have "size t' = (size l' + size r' + 1)" using t'_split by simp
  also have "\<dots> \<le> (2*size l +1 + 2* size r +1 +1)" using l_size r_size by simp
  also have "\<dots> = 2*size \<langle>l,a,r\<rangle> + 1" by simp
  finally show ?case by simp
qed

corollary weak_heap_node_size_lower: assumes "almost_complete n t" shows "size t \<ge> 2^(n-1) - 1"
proof -
  obtain t' where t'_h_c: "height (t'::'a tree) = n \<and> complete t'" using Ex_complete_tree_of_height by auto
  then have "2^n - 1 = size t'" using size_if_complete[of t'] by auto
  also have "\<dots> \<le> 2*size t + 1" using weak_heap_height_complete[of n t t'] t'_h_c assms by auto
  finally have "2^n - 1 \<le> 2*size t + 1" by simp
  then have "2^n \<le> 2*(size t + 1)" by simp
  then have "2^n div 2 \<le> 2*(size t + 1) div 2" by simp
  then have "2^(n-1) \<le> size t + 1" by (metis diff_is_0_eq' max.absorb_iff2 max_def nonzero_mult_div_cancel_left power_eq_if rel_simps(76) trans_le_add2 zero_le_one)
  then show ?thesis by simp
qed

text\<open>A tighter bound is achieved if we make sure n corresponds to the real height and not height t -1 \<close>

lemma weak_heap_node_size_height: 
  assumes  "almost_complete n t" "height t = n" "t \<noteq> Leaf"
  shows  "size t \<ge> 2^ (n-1)"
  using assms
proof (induction t arbitrary: n)
  case (Node l a r)
  let ?t = "Node l a r"
  from Node have "height ?t = 1 \<or> height ?t > 1" by auto
  then show ?case
  proof
    assume h:"height ?t = 1"
    then have "size ?t = 1" by (metis One_nat_def add_diff_cancel_right' height_le_size_tree le_antisym one_add_one power_Suc0_right size_height)
    then show ?thesis using h Node by simp
  next
    from Node have alm_l: "almost_complete (n-1) l" by auto
    from Node have alm_r: "almost_complete (n-1) r" by auto
    assume h:"height ?t > 1"
    then have "height l = n-1 \<or> height r = n-1" using Node by auto
    then show ?thesis
    proof
      assume h_l: "height l = n-1"
      then have "l \<noteq> Leaf" using h Node.prems(2) by auto
      then have s_l: "size l \<ge> 2^(n-2)" using Node(1)[of "n-1"] alm_l h_l
        by (metis diff_diff_left one_add_one)

      have "2^(n-1) = (2::nat)*2^(n-2)"  using h by (metis Node.prems(2) diff_diff_left diff_is_0_eq linorder_not_le one_add_one power_eq_if)
      also have "\<dots> \<le> 2^(n-2) + size l" using s_l by auto
      also have "\<dots> = 2^(n-2) - 1 + size l + 1" by auto
      also have "\<dots> \<le> size r + size l + 1" using weak_heap_node_size_lower[of "n-1" r] alm_r
        by (metis add.commute diff_diff_left nat_add_left_cancel_le one_add_one)
      also have "\<dots> = size ?t" by auto
      finally show ?thesis by simp
    next
      assume h_r: "height r = n-1"
      then have "r \<noteq> Leaf" using h Node.prems(2) by auto
      then have s_r: "size r \<ge> 2^(n-2)" using Node(2)[of "n-1"] alm_r h_r
        by (metis diff_diff_left one_add_one)

      have "2^(n-1) = (2::nat)*2^(n-2)"  using h by (metis Node.prems(2) diff_diff_left diff_is_0_eq linorder_not_le one_add_one power_eq_if)
      also have "\<dots> \<le> 2^(n-2) + size r" using s_r by auto
      also have "\<dots> = 2^(n-2) - 1 + size r + 1" by auto
      also have "\<dots> \<le> size l + size r + 1" using weak_heap_node_size_lower[of "n-1" l] alm_l
        by (metis add.commute diff_diff_left nat_add_left_cancel_le one_add_one)
      also have "\<dots> = size ?t" by auto
      finally show ?thesis by simp
    qed
  qed
qed auto

(* this tighter bound can be used in general for the root since it enforces the height-n equivalence *)
corollary weak_heap_size_lower: assumes "weak_heap t" "height t > 1" shows "size t \<ge> 2 ^(height t-2) + 1"
proof -
  obtain a r where t_split: "t = \<langle>Leaf, a, r\<rangle>" using assms by (metis eq_0_height not_one_less_zero weak_heap.elims(2))
  from t_split have r_alm: "almost_complete (height r) r" using assms by auto
  from t_split have r_height: "height t - 1 = height r" by simp
  then have r_noleaf: "r \<noteq> Leaf" using assms by auto
  then have r_size: "size r \<ge> 2 ^(height r -1)" using weak_heap_node_size_height[of "height r" r] assms t_split r_alm by auto

  from t_split have "size t = size r + 1" by simp
  also have "\<dots> \<ge>  2 ^(height r -1) + 1" using r_size by simp
  also have "2 ^(height r -1) + 1 = 2 ^ (height t - 2) + 1" using r_height by (metis diff_diff_add one_add_one)
  finally show ?thesis by simp
qed


value "height (\<langle>\<langle>\<rangle>, (1::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 8, \<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<langle>\<rangle>, 5, \<langle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 
value "size (\<langle>\<langle>\<rangle>, (1::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 8, \<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 3, \<langle>\<langle>\<langle>\<rangle>, 5, \<langle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 

find_theorems "log 2"
find_theorems "ceiling"


text\<open>These results yield a direct proof of the logarithmic height of weak heaps.\<close>

lemma weak_heap_node_size: assumes "almost_complete (height t) t" "t \<noteq> Leaf" shows "height t = \<lceil>log 2 (size t + 1)\<rceil>"
proof -
  show "height t  = \<lceil>log 2 (size t + 1)\<rceil>"
  proof (rule antisym)
    have "2^(height t-1) \<le> size t" using weak_heap_node_size_height assms by blast
    then have "2^(height t-1) < size t + 1" by linarith
    then have "height t - 1 < log 2 (size t + 1)" using less_log2_of_power by blast
    then show "height t \<le> \<lceil>log 2 (size t + 1)\<rceil>" by linarith
  next
    from assms have "size t \<le> 2^(height t) - 1" using size_height by blast
    then have "size t + 1 \<le> 2^(height t)" by (metis size1_height size1_size)
    then have "log 2 (size t + 1) \<le> height t" using log2_of_power_le assms(2) eq_size_0 by blast
    then show "\<lceil>log 2 (size t + 1)\<rceil> \<le> height t" by linarith
  qed
qed


lemma weak_heap_size: assumes "weak_heap t" "t \<noteq> Leaf" shows "height t = \<lceil>log 2 (size t)\<rceil> + 1"
proof -
  obtain a r where t_split: "t = Node Leaf a r"  using assms weak_heap.elims(2) by blast
  then have "size t = size r + 1" by simp
  
  have "height t = 1 \<or> height t > 1" using assms using linorder_neqE_nat by fastforce
  then show ?thesis
  proof (elim disjE)
    assume h1: "height t = 1"
    then have "r = Leaf" using t_split by simp
    then have "size t = 1" using t_split by simp
    then have "\<lceil>log 2 (size t)\<rceil> + 1 = 1" by simp
    also have "\<dots> = height t" by (simp add: h1)
    finally show ?thesis by simp
  next
    assume hg: "height t > 1"
    then have r_noleaf: "r \<noteq> Leaf" using t_split build_height by auto

    have "height t = height r + 1" using t_split by simp
    also have "\<dots> = \<lceil>log 2 (size r + 1)\<rceil> + 1" using assms(1) t_split weak_heap_node_size r_noleaf by auto
    also have "\<dots> = \<lceil>log 2 (size t)\<rceil> + 1" using assms \<open>size t = size r + 1\<close> by simp
    finally show ?thesis by simp
  qed
qed

text\<open>Some further helper lemmas are shown.
In particular, that the weak heap node property is inherited by left and right childs
and an almost complete tree is always almost complete with respect to its own height.
This yields the fact that the right child of any weak heap, ignoring its left sibling, is a weak heap itself.\<close>


lemma weak_heap_recurseR: "weak_heap_node n \<langle>l, a, r\<rangle> \<Longrightarrow> weak_heap_node (n-1) r"
  apply(induction n r arbitrary: l a rule: almost_complete.induct)
   apply(auto split: nat.splits)
  done

lemma weak_heap_recurseL: "weak_heap_node n \<langle>l, a, r\<rangle> \<Longrightarrow> weak_heap_node (n-1) l"
  apply(induction n l arbitrary: r a rule: almost_complete.induct)
   apply(auto split: nat.splits)
  done

(* A tree is always almost complete wrt its own height if it is almost complete wrt any number *)
lemma almost_complete_height: "almost_complete n t \<Longrightarrow> almost_complete (height t) t"
proof (induction n t rule: almost_complete.induct)
  case (2 n l a r)
  then obtain m where n_m: "n = Suc m" by (cases n) auto
  then have children_almost_complete_m: "almost_complete m l \<and> almost_complete m r" using 2 by auto
  then have children_almost_complete_height: "almost_complete (height l) l \<and> almost_complete (height r) r" using 2 n_m by auto

  let ?t = "\<langle>l, a, r\<rangle>"
  have height_is_max: "height ?t = max (height l) (height r) + 1" by auto

  have "height ?t = n \<or> height ?t = n-1" using weak_heap_height[of n ?t] 2 by auto
  then show ?case
    using children_almost_complete_height
          children_almost_complete_m
          height_is_max
          weak_heap_height
          add_diff_cancel_left' add_le_same_cancel1 almost_complete.simps(2) eq_height_0 max.cobounded1 max.cobounded2 n_m not_one_le_zero plus_1_eq_Suc tree.simps(3)
    by fastforce
qed auto

lemma "weak_heap \<langle>Leaf, a, \<langle>l, b, r\<rangle>\<rangle> \<Longrightarrow> weak_heap \<langle>Leaf, b, r\<rangle>"
  by (auto simp add: weak_heap_recurseR almost_complete_height)


lemma weak_heap_right: "weak_heap t \<Longrightarrow> right_heap t"
  by (induction t) auto


subsection "Operations on Weak Heaps"


text \<open> For the construction and sorting functionality, only an imperative implementation by Dutton is accessible via the internet.
The following functional definitions are therefore based on the work of Edelkamp, Elmasry and Katajainen (2013) as well as Dutton where applicable.
Note that so far, no purely functional implementation of the full weak heap sort was written down comprehensively.
Functions stem partly from different papers and from different people.
We further show functional correctness of the introduced operations.\<close>

text \<open>For simplification we represent a weak heap by its minimum, stored in the root, and the right subtree in the following.\<close>

type_synonym 'a wheap = "'a \<times> 'a tree"

(* The join function is exactly the merge function introduced by Dutton (93) *)
fun join:: "'a::linorder wheap \<Rightarrow> 'a::linorder wheap" where
"join (a, Leaf) = (a, Leaf)" |
"join (ai, \<langle>lj, aj, rj\<rangle>) = (
  if ai \<le> aj then (ai, \<langle>lj, aj, rj\<rangle>) else (aj, \<langle>rj, ai, lj\<rangle>)
)"

(* The sift down and construct functions were introduced in "Weak Heaps Engineered" by Edelkamp (13), however
reformulated here to fit functional definitions *)
fun sift_down::"'a::linorder wheap \<Rightarrow> 'a::linorder wheap" where
 "sift_down (a, Leaf) = (a, Leaf)" |
 "sift_down (a, \<langle>l, b, r\<rangle>) = (let (a', l') = sift_down (a, l) in join (a', \<langle>l', b, r\<rangle>))"

fun construct:: "'a::linorder tree \<Rightarrow> 'a::linorder tree" where
  "construct Leaf = Leaf" |
  "construct \<langle>l, a, r\<rangle> = (let (a', r') = sift_down (a, (construct r)) in \<langle>construct l, a', r'\<rangle>)"

fun tree_of_wheap where "tree_of_wheap (a, w) = w"
fun wheap_of_wheap where "wheap_of_wheap (a, w) = \<langle>Leaf, a, w\<rangle>"

(* These operations preserve the structural invariant *)

lemma almost_complete_join: "\<lbrakk>almost_complete n t\<rbrakk> \<Longrightarrow> almost_complete n (tree_of_wheap (join (a, t)))"
  apply(induction n t arbitrary: a rule: almost_complete.induct)
   apply(auto split: nat.splits)
  done

lemma almost_complete_sift_down: "\<lbrakk>almost_complete n t\<rbrakk> \<Longrightarrow> almost_complete n (tree_of_wheap (sift_down (a, t)))"
  apply(induction n t arbitrary: a rule: almost_complete.induct)
   apply(auto split: nat.splits prod.splits simp add: almost_complete_join)
  by (metis tree_of_wheap.simps)

lemma almost_complete_construct: "almost_complete n t \<Longrightarrow> almost_complete n (construct t)"
  apply(induction n t rule: almost_complete.induct)
   apply(auto split: nat.splits prod.splits simp add: almost_complete_join)
  by (metis almost_complete_sift_down tree_of_wheap.simps)

(* Now we need to show they ensure the heap invariant *)
lemma right_heap_sift_down: "right_heap r \<Longrightarrow> right_heap (wheap_of_wheap (sift_down (a, r)))"
  apply(induction r arbitrary: a rule: right_heap.induct)
   apply(auto split: prod.splits)
      apply (metis right_heap.simps(2) wheap_of_wheap.simps)
     apply (metis right_heap.simps(2) wheap_of_wheap.simps)
    apply (metis right_heap.simps(2) wheap_of_wheap.simps)
   apply (metis right_heap.simps(2) wheap_of_wheap.simps)
  apply (metis dual_order.trans le_cases right_heap.simps(2) wheap_of_wheap.simps)
  done
 (* see 2.4 second paragraph in weak heaps engineered:
    The correctness of the sift-down operation follows from
    the fact that, after each join, the element at location j is less than or equal to every element in the left subtree of the node
    considered in the next join.
  This is handled by sledgehammer automatically
 *)

lemma right_heap_construct: "right_heap (construct t)"
  apply(induction t rule: right_heap.induct)
   apply(auto simp add: right_heap_sift_down split: prod.splits)
   apply (metis right_heap.simps(2) right_heap_sift_down wheap_of_wheap.simps)+
  done

lemma weak_heap_node_construct: "almost_complete n t \<Longrightarrow> weak_heap_node n (construct t)"
  using almost_complete_construct right_heap_construct by auto

fun mset_wheap where "mset_wheap (a, t) = mset_tree t + {#a#}"

lemma mset_eq_sift_down: "mset_wheap x = mset_wheap (sift_down x)"
  apply(induction x rule: sift_down.induct)
   apply(auto split: prod.splits)
  done

lemma mset_eq_construct: "mset_tree t = mset_tree (construct t)"
  apply(induction t)
   apply(auto split: prod.splits)
  by (metis add_mset_add_single mset_eq_sift_down mset_wheap.simps)

lemma height_eq_sift_down: "height t = height (tree_of_wheap (sift_down (a, t)))"
  apply(induction t)
   apply(auto split: prod.splits)
  done

lemma height_eq_construct: "height t = height (construct t)"
  apply(induction t)
   apply(auto split: prod.splits)
  by (metis height_eq_sift_down tree_of_wheap.simps)

lemma size_eq_sift_down: "size t = size (tree_of_wheap (sift_down (a, t)))"
  apply(induction t)
   apply(auto split: prod.splits)
  done

lemma size_eq_construct: "size t = size (construct t)"
  apply(induction t)
   apply(auto split: prod.splits)
  by (metis size_eq_sift_down tree_of_wheap.simps)


corollary "set_tree t = set_tree (construct t)"
  using mset_eq_construct set_mset_tree by metis

(* The main result about the construction function:
    Given a tree that fulfils the structural invariant, a weak heap is obtained by applying the construction function
 *)

lemma weak_heap_construct: assumes "almost_complete n r" "t = \<langle>Leaf, a, r\<rangle>" shows "weak_heap (construct t)"
proof -
  obtain l a' r' where construct_split: "\<langle>l, a', r'\<rangle> = construct t" using assms
    by (metis construct.cases mset_eq_construct mset_tree_empty_iff)
  have "l = Leaf \<and> right_heap \<langle>l, a', r'\<rangle> \<and> almost_complete (height r') r'"
  proof (intro conjI)
    show "right_heap \<langle>l, a', r'\<rangle>" using construct_split right_heap_construct by simp
  next
    from construct_split show "l = Leaf" using assms by (metis construct.simps(1) construct.simps(2) prod.case tree.inject tree_of_wheap.cases)
  next
    have "r' = tree_of_wheap (sift_down (a, construct r))" using construct_split assms construct.simps
      by (metis prod.case tree.inject tree_of_wheap.simps wheap_of_wheap.elims)
    then have "almost_complete n r'" using assms
      by (simp add: almost_complete_construct almost_complete_sift_down)
    then show "almost_complete (height r') r'" using almost_complete_height by blast
  qed
  then show ?thesis using weak_heap_alt_eq
    by (metis construct_split right_heap.simps(2) weak_heap_alt.simps(2) weak_heap_node.simps)
qed

(* Indeed, we do construct weak heaps but not necessarily heaps *)

value "weak_heap (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 
value "construct (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 
value "heap (construct (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>))" 
value "weak_heap (construct (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>))" 

text \<open>We show that the number of comparisons applied in a sift-down operation is logarithmic in the height of the tree.
Applying the masters method one can see that only linearly many comparisons are required for ensuring the weak heap property in an unordered, structurally correct tree.\<close>


fun c_join:: "'a::linorder wheap \<Rightarrow> nat" where
"c_join (a, Leaf) = 0" |
"c_join (ai, \<langle>lj, aj, rj\<rangle>) = 1"

fun c_sift_down::"'a::linorder wheap \<Rightarrow> nat" where
 "c_sift_down (a, Leaf) = 0" |
 "c_sift_down (a, \<langle>l, b, r\<rangle>) = c_sift_down (a, l) + 
  (let (a', l') = sift_down (a, l) in c_join (a', \<langle>l', b, r\<rangle>))"

fun c_construct:: "'a::linorder tree \<Rightarrow> nat" where
  "c_construct Leaf = 0" |
  "c_construct \<langle>l, a, r\<rangle> = c_construct r + c_sift_down (a, construct r) + c_construct l"


value "c_construct (\<langle>\<langle>\<rangle>, (8::nat), \<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 11, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>\<rangle>, 4, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>, 7, \<langle>\<langle>\<langle>\<rangle>, 9, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>\<rangle>)" 

fun lheight where
"lheight Leaf = 0" |
"lheight \<langle>l, a, r\<rangle> = Suc (lheight l)"

lemma c_sift_down_log: "c_sift_down (a, t) = lheight t"
  apply(induction t)
   apply(auto)
  done

lemma construct_lheight_eq: "lheight t = lheight (construct t)"
  apply(induction t)
  apply(auto split: nat.splits)
  by (metis lheight.simps(2) old.prod.case tree_of_wheap.cases)

lemma lheight_height: "lheight t \<le> height t"
  apply(induction t)
   apply(auto)
  done

(* the following lemma is to be shown by future work for some concrete constant logarithmic factor*)
lemma "almost_complete n t \<Longrightarrow> c_construct t \<le> 3.5 * size t + c * (lheight t)^2"
  oops                                   

  text \<open>For implementing a sorting function, we further need a deletion function.
Since the deletion is non-trivial we further need to show, that and what is deleted.
This is to show that the sorting function (repeatedly calling the deletion) terminates eventually.
We are able to show termination and sortedness as well as completeness of the sorting function\<close>


(* For sorting we need the option to delete elements.
   This is established as in 
   The Weak-Heap Data Structure: Variants and Applications by Edelkamp et al
 *)
fun del_right_most_leaf:: "nat \<Rightarrow> 'a::linorder tree \<Rightarrow> ('a::linorder option \<times> 'a::linorder tree)" where
"del_right_most_leaf 0 t = (None, t)" |
"del_right_most_leaf (Suc n) Leaf = (None, Leaf)" |
"del_right_most_leaf (Suc n) \<langle>l, a, r\<rangle> = (if n = 0 then (Some a, Leaf) else (case del_right_most_leaf n r of (Some b, r') \<Rightarrow> (Some b, \<langle>l, a, r'\<rangle>) | (None, _) \<Rightarrow> (let (x, l') = del_right_most_leaf n l in (x, \<langle>l', a, r\<rangle>))))" 

fun del_min:: "'a::linorder tree \<Rightarrow> 'a::linorder \<times> 'a::linorder tree" where
"del_min t = (
    let (x, t') = del_right_most_leaf (height t) t in
      (case x of Some a' \<Rightarrow> sift_down (a', t'))
)"

lemma almost_complete_del_right_most_leaf:"almost_complete n t \<Longrightarrow> almost_complete n (tree_of_wheap (del_right_most_leaf n t))"
  apply(induction n t rule: del_right_most_leaf.induct)
   apply(auto split: nat.splits prod.splits option.splits)
  done

lemma set_del: "set_tree (tree_of_wheap (del_right_most_leaf n t)) \<subseteq> set_tree t"
  apply(induction n t rule: del_right_most_leaf.induct)
    apply(auto split: nat.splits prod.splits option.splits)
  by blast

lemma mset_del: "mset_tree (tree_of_wheap (del_right_most_leaf n t)) \<subseteq># mset_tree t"
  apply(induction n t rule: del_right_most_leaf.induct)
    apply(auto split: nat.splits prod.splits option.splits)
  done


lemma right_heap_del_right_most_leaf: "right_heap t \<Longrightarrow> right_heap (tree_of_wheap (del_right_most_leaf n t))"
  apply(induction n t rule: del_right_most_leaf.induct)
   apply(auto split: nat.splits prod.splits option.splits)
  using set_del by (metis subset_eq tree_of_wheap.simps)

lemma almost_complete_1_leaves: "almost_complete 1 \<langle>l, a, r\<rangle> \<Longrightarrow> l = Leaf \<and> r = Leaf"
  apply(cases l)
   apply(cases r)
    apply(auto)
  done

lemma set_right_most_leaf_almost_complete:"\<lbrakk>almost_complete n t; (x, t') = del_right_most_leaf n t\<rbrakk> \<Longrightarrow> mset_tree t = mset_tree t' + (case x of None \<Rightarrow> {#} | Some a \<Rightarrow> {#a#})"
proof (induction n t arbitrary: x t' rule: del_right_most_leaf.induct)
  case (3 n l a r)
  then have "n = 0 \<or> n \<noteq> 0" by auto
  then show ?case
  proof
    assume "n = 0"
    then have "l = Leaf \<and> r = Leaf" using 3 almost_complete_1_leaves by auto
    then have "mset_tree \<langle>l, a, r\<rangle> = {#a#}" by auto
    then show ?thesis using "3.prems"(2) \<open>n = 0\<close> by auto
  next
    assume ng: "n \<noteq> 0"
    then obtain x r' where del_split: "(x, r') = del_right_most_leaf n r" using 3 by (metis surj_pair)
    then show ?thesis
    proof (cases x)
      case (Some b)
      then have is_del: "(Some b, \<langle>l, a, r'\<rangle>) = del_right_most_leaf (Suc n) \<langle>l, a, r\<rangle>" using 3 del_split del_right_most_leaf.simps(3) ng
        Some by (metis (mono_tags, lifting) case_prod_conv option.simps(5))
      
      have "almost_complete n r" using 3 by auto
      then have "mset_tree r = mset_tree r' + {#b#}" using 3 Some del_split
        by (metis Some ng \<open>\<And>x t'. \<lbrakk>n \<noteq> 0; almost_complete n r; (x, t') = del_right_most_leaf n r\<rbrakk> \<Longrightarrow> mset_tree r = mset_tree t' + (case x of None \<Rightarrow> {#} | Some a \<Rightarrow> {#a#})\<close> \<open>almost_complete n r\<close> del_split option.simps(5))
      then have "mset_tree \<langle>l, a, r\<rangle> = mset_tree \<langle>l, a, r'\<rangle> + {#b#}" by simp
      then show ?thesis using is_del by (metis "3.prems"(2) Pair_inject option.simps(5))
    next
      case None
      then obtain x l' where del_split2: "(x, l') = del_right_most_leaf n l" using 3 by (metis surj_pair)
      then have is_del: "(x, \<langle>l', a, r\<rangle>) = del_right_most_leaf (Suc n) \<langle>l, a, r\<rangle>" using 3 ng None del_right_most_leaf.simps(3) del_split by (metis (no_types, lifting) case_prod_conv option.simps(4))

      have "almost_complete n l" using 3 by auto
      then have "mset_tree l = mset_tree l' + (case x of None \<Rightarrow> {#} | Some c \<Rightarrow> {#c#})" using 3 None del_split del_split2 ng sledgehammer
        using None \<open>\<And>y xa x t'. \<lbrakk>n \<noteq> 0; (x, y) = del_right_most_leaf n r; x = None; almost_complete n l; (xa, t') = del_right_most_leaf n l\<rbrakk> \<Longrightarrow> mset_tree l = mset_tree t' + (case xa of None \<Rightarrow> {#} | Some a \<Rightarrow> {#a#})\<close> \<open>almost_complete n l\<close> del_split del_split2 ng by blast
      then have "mset_tree \<langle>l, a, r\<rangle> = mset_tree \<langle>l', a, r\<rangle> +  (case x of None \<Rightarrow> {#} | Some c \<Rightarrow> {#c#})" by simp
      then show ?thesis using is_del by (metis "3.prems"(2) Pair_inject)
    qed
  qed
qed auto


lemma del_not_None: "\<lbrakk>t \<noteq> Leaf; del_right_most_leaf (height t) t = (x, t')\<rbrakk> \<Longrightarrow> \<exists>b. x = Some b"
proof (induction t arbitrary: x t')
  case Leaf
  then show ?case by auto
next
  case (Node l a r)
  let ?t = "\<langle>l, a, r\<rangle>"
  from Node have "height ?t = 1 \<or> height ?t > 1" by auto
  then show ?case
  proof
    assume "height ?t = 1"
    then show ?thesis 
      by (metis (full_types) Node.prems(2) One_nat_def Pair_inject del_right_most_leaf.simps(3))
  next
    assume hg: "height ?t > 1"
    then obtain m where m_suc: "height ?t = Suc m" by simp
      then have "m \<noteq> 0" using hg by simp
    have "height r = height ?t - 1 \<or> (height l = height ?t - 1 \<and> \<not>(height r = height ?t -1))" by (simp add: max_def)
    then show ?case
    proof
      assume hr: "height r = height ?t - 1"
      then obtain x r' where del_split: "del_right_most_leaf (height r) r = (Some x, r')" using hg
        by (metis (full_types) Node.IH(2) One_nat_def Suc_pred height_tree.simps(1) not_less0 not_less_iff_gr_or_eq option.exhaust tree_of_wheap.cases)

      have "m = height r" using m_suc hr by linarith
      then have "del_right_most_leaf (height ?t) ?t = (Some x, \<langle>l, a, r'\<rangle>)"
        using \<open>m \<noteq> 0\<close> del_split m_suc by auto   
      then show ?thesis using Node.prems(2) by auto
    next
      assume hr: "height l = height ?t - 1 \<and> \<not>(height r = height ?t -1)"
      then obtain x l' where del_split: "del_right_most_leaf (height l) l = (Some x, l')" using hg Node
        by (metis One_nat_def Suc_diff_Suc diff_0_eq_0 diff_Suc_eq_diff_pred height_tree.simps(1) option.exhaust tree_of_wheap.elims zero_neq_one)

      obtain x' r' where "del_right_most_leaf m r = (x', r')" using m_suc by (meson surj_pair)
      then show ?thesis
      proof (cases x')
        case None
        have "m = height l" using m_suc hr by linarith
        then have "del_right_most_leaf (height ?t) ?t = (Some x, \<langle>l', a, r\<rangle>)"
          using \<open>m \<noteq> 0\<close> del_split m_suc None \<open>del_right_most_leaf m r = (x', r')\<close> by auto
        then show ?thesis using Node.prems(2) by auto
      next
        case (Some a)
        then show ?thesis
          by (metis (mono_tags, lifting) Node.prems(2) Pair_inject \<open>del_right_most_leaf m r = (x', r')\<close> del_right_most_leaf.simps(3) m_suc option.simps(5) prod.simps(2))
      qed     
    qed
  qed
qed


corollary del_reduce_mset_almost_complete:
  assumes "almost_complete n t" "t \<noteq> Leaf" "(x, t') = del_right_most_leaf (height t) t"
  shows "\<exists>a. x = Some a \<and> mset_tree t = mset_tree t' + {#a#}"
proof -
  from assms have "almost_complete (height t) t" using almost_complete_height by blast
  then have "mset_tree t = mset_tree t' + (case x of None \<Rightarrow> {#} | Some a \<Rightarrow> {#a#})" using assms set_right_most_leaf_almost_complete by blast

  from assms have "\<exists>a. x = Some a" by (metis del_not_None)
  then show ?thesis
    using \<open>mset_tree t = mset_tree t' + (case x of None \<Rightarrow> {#} | Some a \<Rightarrow> {#a#})\<close> by auto
qed

find_theorems mset_tree size

corollary del_min_reduce_mset_almost_complete:
  assumes "almost_complete n t" "t \<noteq> Leaf" "(a, t') = del_min t"
  shows "mset_tree t = mset_tree t' + {#a#}"
proof -
  from assms obtain b t'' where del_res:"del_right_most_leaf (height t) t = (Some b, t'')" using del_not_None
    by (metis tree_of_wheap.cases)
  then have s_d: "sift_down (b, t'') = (a, t')" by (simp add: assms(3))
  
  from del_res have "mset_tree t = mset_tree t'' + {#b#}" using del_reduce_mset_almost_complete del_res assms(1) by fastforce
  also have "\<dots> = mset_tree t' + {#a#}" using mset_eq_sift_down s_d
    by (metis mset_wheap.simps)
  finally show ?thesis by simp
qed

corollary almost_complete_del_right_size:
  assumes "almost_complete n t" "t \<noteq> Leaf" "(x, t') = del_right_most_leaf (height t) t"
  shows "size t = size t' + 1"
proof -
  from assms obtain a where "x = Some a \<and> mset_tree t = mset_tree t' + {#a#}" using del_reduce_mset_almost_complete by blast
  then have "size (mset_tree t) = size (mset_tree t') + 1" by simp
  then show ?thesis using size_mset_tree by auto
qed

corollary almost_complete_del_min_size:
  assumes "almost_complete n t" "t \<noteq> Leaf" "(a, t') = del_min  t"
  shows "size t = size t' + 1"
proof -
  from assms obtain b t'' where del_res:"del_right_most_leaf (height t) t = (Some b, t'')" using del_not_None
    by (metis tree_of_wheap.cases)
  then have s_d: "sift_down (b, t'') = (a, t')" by (simp add: assms(3))
  
  from del_res have "size t = size t'' + 1" using almost_complete_del_right_size using assms(1) by fastforce
  also have "\<dots> = size t' + 1" using size_eq_sift_down s_d
    by (metis tree_of_wheap.simps)
  finally show ?thesis by simp
qed

(* We also want to show that in general, the size of the tree is decreased for calls with height t *)

lemma del_Some_not_leaf: "del_right_most_leaf n t = (Some b, t') \<Longrightarrow> t \<noteq> Leaf"
  using del_right_most_leaf.elims tree.distinct(1) by force


lemma del_decr: "\<lbrakk>t \<noteq> Leaf; del_right_most_leaf n t = (Some b, t')\<rbrakk> \<Longrightarrow> count (mset_tree t) b > count (mset_tree t') b"
proof (induction n t arbitrary: b t' rule: almost_complete.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n l a r)
  let ?t = "\<langle>l, a, r\<rangle>"
  from 2 have "n = 1 \<or> n > 1"
    by (metis One_nat_def del_right_most_leaf.simps(1) less_SucE linorder_neqE_nat not_less0 old.prod.inject option.distinct(1))
  then show ?case
  proof
    assume "n = 1"
    then show ?thesis by (metis "2.prems"(2) One_nat_def Pair_inject count_empty count_greater_zero_iff del_right_most_leaf.simps(3) mset_tree.simps(1) option.inject set_mset_tree tree.set_intros(2))
  next
    assume hg: "n > 1"
    then obtain m where m_suc: "n = Suc m" using Nat.lessE by blast
    then have "m \<noteq> 0" using hg by simp
    
    obtain x r' where del_split: "del_right_most_leaf m r = (x, r')" by (meson surj_pair)
    then show ?case
    proof (cases x)
      case (Some b)
      then have "del_right_most_leaf n ?t = (Some b, \<langle>l, a, r'\<rangle>)"
        using \<open>m \<noteq> 0\<close> del_split m_suc del_right_most_leaf.simps by simp 
      then show ?thesis using del_Some_not_leaf 2 m_suc del_split by (metis Some add_less_cancel_left count_union mset_tree.simps(2) prod.sel(1) prod.sel(2)) 
    next
      case None
      then obtain x' l' where del_split2: "del_right_most_leaf m l = (x', l')"
        using tree_of_wheap.cases by blast 
         
      then have del_t: "del_right_most_leaf n ?t = (x', \<langle>l', a, r\<rangle>)"
        using \<open>m \<noteq> 0\<close> del_split m_suc None del_split2 del_right_most_leaf.simps by simp
      then obtain c where "x' = Some c" using 2 by auto
      then show ?thesis using 2 del_t del_Some_not_leaf del_split2 m_suc by fastforce 
    qed
  qed
qed

find_theorems count size


corollary del_reduce_mset:
  assumes "t \<noteq> Leaf" "(x, t') = del_right_most_leaf (height t) t"
  shows "\<exists>a. x = Some a \<and> size t > size t'"
proof -
  from assms obtain a where "x = Some a" using del_not_None by metis 
  then have "count (mset_tree t) a > count (mset_tree t') a" using del_decr
    using assms by fastforce 
  then have "size (mset_tree t) > size (mset_tree t')" using mset_del
    by (metis add_eq_0_iff_both_eq_0 assms(2) gr0I in_diff_count plus_1_eq_Suc size_Diff_submset size_Suc_Diff1 tree_of_wheap.simps zero_less_diff zero_neq_one)
  then show ?thesis using del_not_None assms size_mset_tree
    by metis
qed

corollary del_min_decr_size: "t \<noteq> Leaf \<Longrightarrow> \<exists>x t'. del_min t = (x, t') \<and> size t' < size t"
proof -
  assume "t \<noteq> Leaf"
  then obtain x' t' where del_res: "del_right_most_leaf (height t) t = (Some x', t')"
    by (metis del_not_None tree_of_wheap.cases)
  obtain x'' t'' where sift_res: "(x'', t'') = sift_down (x', t')"
    by (metis tree_of_wheap.cases)

  have "del_min t = (x'', t'') \<and> size t > size t''"
  proof
    have "size t'' = size t'" using sift_res
      by (metis size_eq_sift_down tree_of_wheap.simps)
    also have "\<dots> < size t" using del_res del_reduce_mset \<open>t \<noteq> Leaf\<close> by fastforce
    finally show "size t'' < size t" by simp
  next
    show "del_min t = (x'', t'')" using del_res sift_res by auto
  qed
  then show ?thesis by auto
qed


lemma right_heap_del_min: "\<lbrakk>t \<noteq> Leaf; almost_complete n t; right_heap t\<rbrakk> \<Longrightarrow> right_heap (wheap_of_wheap (del_min t))"
  using right_heap_sift_down right_heap_del_right_most_leaf del_reduce_mset_almost_complete
  apply(auto split: option.splits prod.splits)
  apply fastforce by (metis tree_of_wheap.simps)

lemma almost_complete_del_min: "\<lbrakk>t \<noteq> Leaf; almost_complete n t\<rbrakk> \<Longrightarrow> almost_complete (height t) (tree_of_wheap (del_min t))"
  using del_reduce_mset_almost_complete
  apply(auto split: option.splits prod.splits)
  apply fastforce
  using almost_complete_del_right_most_leaf almost_complete_height almost_complete_sift_down by fastforce

lemma weak_heap_del_min: "\<lbrakk>t \<noteq> Leaf; weak_heap_node (height t) t\<rbrakk> \<Longrightarrow> weak_heap (wheap_of_wheap (del_min t))"
proof -
  (* Obviously a metis proof, but I was too lazy to write it down myself *)
  assume a1: "t \<noteq> \<langle>\<rangle>"
  assume a2: "weak_heap_node (height t) t"
  have f3: "\<forall>t. (\<exists>ta a tb. (\<not> weak_heap_node (height tb) tb \<or> \<not> right_heap \<langle>ta, a::'a, tb\<rangle> \<or> \<langle>\<rangle> \<noteq> ta) \<and> \<langle>ta, a, tb\<rangle> = t) \<or> weak_heap_alt t"
    by (metis weak_heap_alt.elims(3))
  have f4: "\<forall>t. (\<exists>ta a tb. (\<not> weak_heap_node (height tb) tb \<or> (\<exists>aa. \<not> (a::'a) \<le> aa \<and> aa \<in> set_tree tb) \<or> \<langle>\<rangle> \<noteq> ta) \<and> \<langle>ta, a, tb\<rangle> = t) \<or> weak_heap t"
    by (metis weak_heap.elims(3))
  have "almost_complete (height (tree_of_wheap (del_min t))) (tree_of_wheap (del_min t))"
    using a2 a1 almost_complete_del_min almost_complete_height by auto
  then show ?thesis
    using f4 f3 a2 a1 by (metis right_heap.simps(2) right_heap_del_min tree.inject tree_of_wheap.simps weak_heap_alt_eq weak_heap_node.simps wheap_of_wheap.elims)
qed

(* We can hence specifiy weak heap sort (and show it terminates) *)

function (sequential) weak_heap_heap_sort:: "'a::linorder \<times> 'a::linorder tree \<Rightarrow> 'a::linorder list" where
 "weak_heap_heap_sort (a, Leaf) = [a]" |
 "weak_heap_heap_sort (a, \<langle>l, b, r\<rangle>) = a#(weak_heap_heap_sort (del_min \<langle>l, b, r\<rangle>))"
by pat_completeness auto
  termination
    apply (relation "measure (%(a,t). size t)") 
     apply(simp)
    using del_min_decr_size
    by (metis in_measure prod.case tree.simps(3))

lemma weak_heap_sort_mset: "weak_heap (wheap_of_wheap (a,t)) \<Longrightarrow> mset_tree (wheap_of_wheap (a,t)) = mset (weak_heap_heap_sort (a,t))"
proof (induction "size t" arbitrary: a t)
  case (Suc n)
  then have alm_t: "almost_complete (height t) t" by simp
  from Suc have "t \<noteq> Leaf" by auto
  
  have "weak_heap (wheap_of_wheap (del_min  t))" by (metis Suc.hyps(2) Suc.prems eq_0_size nat.distinct(1) weak_heap.simps(2) weak_heap_del_min wheap_of_wheap.simps)

  obtain c s where "(c, s) = del_min t" by (metis surj_pair)
  then have "size t = size s + 1" using alm_t almost_complete_del_min_size
    using \<open>t \<noteq> \<langle>\<rangle>\<close> by blast
  then have ih: "mset (weak_heap_heap_sort (c, s)) = mset_tree (wheap_of_wheap (c,s))"
    by (metis Suc.hyps(1) Suc.hyps(2) Suc_eq_plus1 \<open>(c, s) = del_min t\<close> \<open>weak_heap (wheap_of_wheap (del_min t))\<close> add.commute add_left_cancel)

  have "mset (weak_heap_heap_sort (a,t)) = {#a#} + mset (weak_heap_heap_sort (del_min t))" using  \<open>t \<noteq> \<langle>\<rangle>\<close>
    by (metis add.left_neutral height_tree.elims mset.simps(2) union_mset_add_mset_left weak_heap_heap_sort.simps(2))
  also have "\<dots> = {#a#} + mset_tree (wheap_of_wheap (c,s))" using ih
    by (simp add: \<open>(c, s) = del_min t\<close>)
  also have "\<dots> = mset_tree (wheap_of_wheap (a,t))" using del_min_reduce_mset_almost_complete
    by (metis \<open>(c, s) = del_min t\<close> \<open>t \<noteq> \<langle>\<rangle>\<close> add.commute add_mset_add_single alm_t mset_tree.simps(1) mset_tree.simps(2) wheap_of_wheap.simps)
  finally show ?case by auto
qed auto



lemma weak_heap_sort_sorted: "weak_heap (wheap_of_wheap (a,t)) \<Longrightarrow> sorted_wrt (\<le>) (weak_heap_heap_sort (a,t))"
proof (induction "size t" arbitrary: a t)
  case (Suc n)
  then have alm_t: "almost_complete (height t) t" by simp
  from Suc have "t \<noteq> Leaf" by auto
  
  have "weak_heap (wheap_of_wheap (del_min  t))" by (metis Suc.hyps(2) Suc.prems eq_0_size nat.distinct(1) weak_heap.simps(2) weak_heap_del_min wheap_of_wheap.simps)

  obtain c s where "(c, s) = del_min t" by (metis surj_pair)
  then have "size t = size s + 1" using alm_t almost_complete_del_min_size
    using \<open>t \<noteq> \<langle>\<rangle>\<close> by blast
  then have ih: "sorted_wrt (\<le>) (weak_heap_heap_sort (c, s))"
    by (metis Suc.hyps(1) Suc.hyps(2) Suc_eq_plus1 \<open>(c, s) = del_min t\<close> \<open>weak_heap (wheap_of_wheap (del_min t))\<close> add.commute add_left_cancel)

  have eq: "sorted_wrt (\<le>) (weak_heap_heap_sort (a,t)) = (\<forall>x \<in> set (weak_heap_heap_sort (del_min t)). a \<le> x) \<and> sorted_wrt (\<le>) (weak_heap_heap_sort(del_min t))" using  \<open>t \<noteq> \<langle>\<rangle>\<close>
    by (metis \<open>(c, s) = del_min t\<close> height_tree.elims ih sorted_wrt.simps(2) weak_heap_heap_sort.simps(2))

  have "(\<forall>x \<in> set (weak_heap_heap_sort (del_min t)). a \<le> x) \<and> sorted_wrt (\<le>) (weak_heap_heap_sort(del_min t))"
  proof (intro conjI)
    have "mset_tree t = mset_tree (wheap_of_wheap (del_min t))"
      by (metis \<open>(c, s) = del_min t\<close> \<open>t \<noteq> \<langle>\<rangle>\<close> add.commute add_mset_add_single alm_t del_min_reduce_mset_almost_complete mset_tree.simps(1) mset_tree.simps(2) wheap_of_wheap.simps)
    also have "\<dots> = mset (weak_heap_heap_sort (del_min t))" using weak_heap_sort_mset
      by (metis \<open>(c, s) = del_min t\<close> \<open>weak_heap (wheap_of_wheap (del_min t))\<close>)
    finally show "\<forall>x\<in>set (weak_heap_heap_sort (del_min t)). a \<le> x" using Suc.prems
      using set_mset_tree by fastforce (* from wheap property *)
  next
    show "sorted_wrt (\<le>) (weak_heap_heap_sort (del_min t))" using ih by (simp add: \<open>(c, s) = del_min t\<close>)
  qed
  then show ?case using eq Suc by blast
qed auto

end