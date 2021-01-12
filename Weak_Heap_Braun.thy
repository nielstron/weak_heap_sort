theory Weak_Heap_Braun
imports "Priority_Queue_Braun.Priority_Queue_Braun" "Priority_Queue_Braun.Sorting_Braun" Weak_Heap 
begin

subsection "Relation to Braun Trees"

text\<open>Trees fulfilling the structural invariant (almost completeness) are
 also balanced. This follows directly from the properties of n for an almost complete tree of n layers.\<close>


find_theorems size braun
thm balanced_if_braun
find_theorems balanced

lemma balanced_almost_complete: "almost_complete n t \<Longrightarrow> balanced t"
  using weak_heap_height weak_heap_minheight balanced_def by fastforce

text \<open>This simplifies the  proof of logarithmic height.\<close>

find_theorems balanced  height
find_theorems size1 size

hide_fact weak_heap_node_size

lemma weak_heap_node_size: assumes "almost_complete (height t) t" shows "height t = nat \<lceil>log 2 (size1 t)\<rceil>"
  using balanced_almost_complete height_balanced assms by blast

find_theorems min_height height
find_theorems balanced

text \<open>We also show that trees almost complete to their minimal height are complete.\<close>

lemma almost_complete_min_complete: "Weak_Heap.almost_complete (min_height t) t \<Longrightarrow> Tree.complete t"
proof -
  assume "almost_complete (min_height t) t"
  then have "height t = min_height t \<or> height t = min_height t - 1" using weak_heap_height[of "min_height t" t] by simp
  then have "height t = min_height t" by (metis diff_le_self eq_iff min_height_le_height)
  then show ?thesis by (simp add: complete_iff_height)
qed

lemma almost_complete_min_or_height: "almost_complete n t \<Longrightarrow> n = height t \<or> n = min_height t + 1"
  using weak_heap_height weak_heap_minheight by (metis One_nat_def Suc_pred add.commute diff_le_self dual_order.order_iff_strict min_height_le_height order_eq_iff plus_1_eq_Suc zero_order(1))

lemma almost_complete_one_more:"Tree.complete t \<Longrightarrow> almost_complete (height t + 1) t"
  apply(induction t)
   apply(auto)
  done

text \<open>We show that hence the almost complete trees are equivalent to the balanced trees.
That way the braun tree creation from a list could be used to generate the tree that weak_heap_heap_sort will sort.\<close>

lemma almost_complete_balanced: "balanced t \<Longrightarrow> almost_complete (height t) t"
proof (induction t)
  case (Node l a r)
  let ?t = "\<langle>l, a, r\<rangle>"
  have "almost_complete (height ?t - 1) l \<and> almost_complete (height ?t - 1) r"
  proof
    from Node  have "balanced l" by (meson balanced_subtreeL)
    then have "almost_complete (height l) l" using Node by auto
 
    from Node have "height l = height ?t - 1 \<or> (height l = min_height l \<and> height l + 1 = height ?t - 1)"
      by (smt add_leE balanced_def diff_diff_add height_tree.simps(2) le_Suc_eq le_less max_def min_def min_height.simps(2) min_height_le_height not_less one_add_one ordered_cancel_comm_monoid_diff_class.add_diff_inverse ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add plus_1_eq_Suc zero_less_diff)
    then show "almost_complete (height ?t - 1) l"
    proof
      assume "height l = height ?t - 1"
      then show "almost_complete (height ?t - 1) l" using \<open>almost_complete (height l) l\<close> by auto
    next
      assume assms: "height l = min_height l  \<and> height l + 1 = height ?t - 1"
      then have "Tree.complete l" by (simp add: complete_iff_height)
      then have "almost_complete (height l + 1) l" using almost_complete_one_more by auto
      then show "almost_complete (height ?t - 1) l" using assms by auto
    qed
  next
    from Node  have "balanced r" by (meson balanced_subtreeR)
    then have "almost_complete (height r) r" using Node by auto
 
    from Node have "height r = height ?t - 1 \<or> (height r = min_height r \<and> height r + 1 = height ?t - 1)"
      by (smt add_leE balanced_def diff_diff_add height_tree.simps(2) le_Suc_eq le_less max_def min_def min_height.simps(2) min_height_le_height not_less one_add_one ordered_cancel_comm_monoid_diff_class.add_diff_inverse ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add plus_1_eq_Suc zero_less_diff)
    then show "almost_complete (height ?t - 1) r"
    proof
      assume "height r = height ?t - 1"
      then show "almost_complete (height ?t - 1) r" using \<open>almost_complete (height r) r\<close> by auto
    next
      assume assms: "height r = min_height r  \<and> height r + 1 = height ?t - 1"
      then have "Tree.complete r" by (simp add: complete_iff_height)
      then have "almost_complete (height r + 1) r" using almost_complete_one_more by auto
      then show "almost_complete (height ?t - 1) r" using assms by auto
    qed
  qed
  then show ?case by auto
qed auto

lemma balanced_eq_almost_complete: "balanced t = almost_complete (height t) t"
  using almost_complete_balanced balanced_almost_complete by blast

find_theorems heap_of_A
find_theorems braun balanced

text \<open>This means we are able to construct almost complete trees from a list\<close>

lemma "t = heap_of_A l \<Longrightarrow> almost_complete (height t) t"
  using balanced_eq_almost_complete balanced_if_braun braun_heap_of_A by metis

section \<open>We now define the "physical" Weak Heap, always maintaining array order and implicitely structure via reverse bits.
The benefit of that tree is that for all operations, it maintains the braun invariant.\<close>
context includes pattern_aliases
begin

fun ph_right_sub :: "(bool\<times>'a::linorder) tree \<Rightarrow> (bool\<times>'a::linorder) tree" where
  "ph_right_sub Leaf = Leaf" |
  "ph_right_sub \<langle>l, (i,a), r\<rangle> = (if i then l else r)"

fun ph_left_sub :: "(bool\<times>'a::linorder) tree \<Rightarrow> (bool\<times>'a::linorder) tree" where
  "ph_left_sub Leaf = Leaf" |
  "ph_left_sub \<langle>l, (i,a), r\<rangle> = (if i then r else l)"

fun ph_right_heap :: "(bool\<times>'a::linorder) tree \<Rightarrow> bool" where
"ph_right_heap Leaf = True" |
"ph_right_heap (Node l (i,a) r =: t) = (
   ph_right_heap l \<and> ph_right_heap r \<and>
   (\<forall>(ix,x) \<in> set_tree (ph_right_sub t). a \<le> x)
)"

fun ph_weak_heap_node :: "nat  \<Rightarrow> (bool\<times>'a::linorder) tree \<Rightarrow> bool" where
"ph_weak_heap_node n t = (almost_complete n t \<and> ph_right_heap t)"

type_synonym 'a ph_wheap = "'a \<times> (bool\<times>'a) tree"

fun ph_join:: "'a::linorder ph_wheap \<Rightarrow> 'a::linorder ph_wheap" where
"ph_join (a, Leaf) = (a, Leaf)" |
"ph_join (ai, \<langle>lj, (ij, aj), rj\<rangle>) = (
  if ai \<le> aj then (ai, \<langle>lj, (ij,aj), rj\<rangle>) else (aj, \<langle>lj, (\<not>ij,ai), rj\<rangle>)
)"

fun ph_sift_down::"'a::linorder ph_wheap \<Rightarrow> 'a::linorder ph_wheap" where
 "ph_sift_down (a, Leaf) = (a, Leaf)" |
 "ph_sift_down (a, \<langle>l, x, r\<rangle>) = (case x of (False, _) \<Rightarrow>
    (case ph_sift_down (a, l) of (a', l') \<Rightarrow> ph_join (a', \<langle>l', x, r\<rangle>))
| (True, _) \<Rightarrow>
    (case ph_sift_down (a, r) of (a', r') \<Rightarrow>  ph_join (a', \<langle>l, x, r'\<rangle>))
)"

fun ph_construct:: "(bool\<times>'a::linorder) tree \<Rightarrow> (bool\<times>'a::linorder) tree" where
  "ph_construct Leaf = Leaf" |
  "ph_construct \<langle>l, (i,a), r\<rangle> = (if i then
    (case ph_sift_down (a, (ph_construct l)) of (a', l') \<Rightarrow> \<langle>l', (i,a'), (ph_construct r)\<rangle>)
  else
    (case ph_sift_down (a, (ph_construct r)) of (a', r') \<Rightarrow> \<langle>ph_construct l, (i,a'), r'\<rangle>)
)"


fun ph_wheap:: "(bool\<times>'a::linorder) tree \<Rightarrow> ('a::linorder) tree" where
"ph_wheap Leaf = Leaf" |
"ph_wheap (\<langle>l, (i,a), r\<rangle> =: t) = (
  \<langle>ph_wheap (ph_left_sub t), a, (ph_wheap (ph_right_sub t))\<rangle>
)"

abbreviation "ph_wheap_pair \<equiv> (\<lambda>(a,t). (a, ph_wheap t))"

lemma ph_join_eq: "ph_wheap_pair (ph_join (a, t)) = join (a, ph_wheap t)"
  apply (induction t)
   apply auto
  done

lemma ph_sift_down_eq: "ph_wheap_pair (ph_sift_down (a, t)) = sift_down (a, ph_wheap t)"
  apply (induction t)
   apply (auto split!: prod.splits)
  done

lemma ph_construct_eq: "ph_wheap (ph_construct ti) = construct (ph_wheap ti)"
  apply(induction ti)
   apply (auto split!: prod.splits)
     apply (metis Pair_inject old.prod.case ph_sift_down_eq)
    apply (metis Pair_inject old.prod.case ph_sift_down_eq)
   apply (metis Pair_inject old.prod.case ph_sift_down_eq)
  apply (metis Pair_inject old.prod.case ph_sift_down_eq)
  done

end
end