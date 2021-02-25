theory Weak_Heap_Braun
imports "Priority_Queue_Braun.Priority_Queue_Braun" "Priority_Queue_Braun.Sorting_Braun" Weak_Heap 
begin

subsection "Relation to Braun Trees"

text\<open>Trees fulfilling the structural invariant (almost completeness) are
 also balanced. This follows directly from the properties of n for an almost complete tree of n layers.\<close>


find_theorems size braun

lemma balanced_almost_complete: "almost_complete n t \<Longrightarrow> acomplete t"
  apply(induction n t rule: almost_complete.induct)
   apply (auto simp add: acomplete_def split!: nat.splits)
  by (smt (z3) One_nat_def cancel_ab_semigroup_add_class.diff_right_commute diff_is_0_eq max.orderI max_def min_def weak_heap_height weak_heap_minheight)
  
text \<open>This simplifies the  proof of logarithmic height.\<close>

find_theorems balanced  height
find_theorems size1 size

hide_fact weak_heap_node_size

lemma weak_heap_node_size:
  assumes "almost_complete (height t) t"
  shows "height t = nat \<lceil>log 2 (size1 t)\<rceil>"
  using assms balanced_almost_complete height_acomplete by blast

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

lemma almost_complete_balanced: "acomplete t \<Longrightarrow> almost_complete (height t) t"
proof (induction t)
  case (Node l a r)
  let ?t = "\<langle>l, a, r\<rangle>"
  have "almost_complete (height ?t - 1) l \<and> almost_complete (height ?t - 1) r"
  proof
    from Node  have "acomplete l"
      by (meson acomplete_subtreeL)
    then have "almost_complete (height l) l" using Node by auto
 
    from Node have "height l = height ?t - 1 \<or> (height l = min_height l \<and> height l + 1 = height ?t - 1)"
      apply (auto simp add: acomplete_def)
       apply (smt (z3) Suc_le_eq Suc_pred diff_diff_cancel diff_is_0_eq diff_le_self le_Suc_eq le_trans max_def min_def min_height_le_height)+
      done
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
    from Node  have "acomplete r"
      by (meson acomplete_subtreeR)
    then have "almost_complete (height r) r" using Node by auto
 
    from Node have "height r = height ?t - 1 \<or> (height r = min_height r \<and> height r + 1 = height ?t - 1)"
      apply (auto simp add: acomplete_def)
       apply (smt (z3) Node.prems One_nat_def Suc_le_eq Suc_pred \<open>acomplete r\<close> acomplete_def acomplete_subtreeL diff_is_0_eq diff_le_self eq_diff_iff le_Suc_eq max.cobounded2 max_def min.absorb2 weak_heap_minheight)
      apply (smt (verit) Suc_le_eq Suc_pred cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_le_self dual_order.eq_iff le_Suc_eq le_trans le_zero_eq max.cobounded2 min.cobounded2 min_height_le_height)
      done
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

lemma balanced_eq_almost_complete: "acomplete t = almost_complete (height t) t"
  using almost_complete_balanced balanced_almost_complete by blast

find_theorems heap_of_A
find_theorems braun acomplete

text \<open>This means we are able to construct almost complete trees from a list\<close>

lemma heap_of_A_almost_complete: "t = heap_of_A l \<Longrightarrow> almost_complete (height t) t"
  by (simp add: braun_heap_of_A almost_complete_balanced acomplete_if_braun)

section \<open>We now define the "physical" Weak Heap,
 always maintaining array order and implicit structure via reverse bits.
It refines the weak heap data structure.
The benefit of that tree is that for all operations, it maintains the braun invariant.\<close>
context includes pattern_aliases
begin


fun ph_wheap:: "(bool\<times>'a::linorder) tree \<Rightarrow> ('a::linorder) tree" where
"ph_wheap Leaf = Leaf" |
"ph_wheap \<langle>l, (i,a), r\<rangle> = (
  if i then \<langle>ph_wheap r, a, ph_wheap l\<rangle> else \<langle>ph_wheap l, a, ph_wheap r\<rangle>
)"

fun ph_weak_heap :: "nat  \<Rightarrow> (bool\<times>'a::linorder) tree \<Rightarrow> bool" where
"ph_weak_heap n t = (braun t \<and> right_heap (ph_wheap t))"

type_synonym 'a ph_wheap = "'a \<times> (bool\<times>'a) tree"

fun ph_join:: "'a::linorder ph_wheap \<Rightarrow> 'a::linorder ph_wheap" where
"ph_join (a, Leaf) = (a, Leaf)" |
"ph_join (ai, \<langle>lj, (ij, aj), rj\<rangle>) = (
  if ai \<le> aj then (ai, \<langle>lj, (ij,aj), rj\<rangle>) else (aj, \<langle>lj, (\<not>ij,ai), rj\<rangle>)
)"

fun ph_sift_down::"'a::linorder ph_wheap \<Rightarrow> 'a::linorder ph_wheap" where
 "ph_sift_down (a, Leaf) = (a, Leaf)" |
 "ph_sift_down (a, \<langle>l, (i,b), r\<rangle>) = (
case ph_sift_down (a, if i then r else l) of (a', m') \<Rightarrow> ph_join (a', if i then \<langle>l, (i,b), m'\<rangle> else \<langle>m', (i,b), r\<rangle>)
)"

fun ph_construct:: "(bool\<times>'a::linorder) tree \<Rightarrow> (bool\<times>'a::linorder) tree" where
  "ph_construct Leaf = Leaf" |
  "ph_construct \<langle>l, (i,a), r\<rangle> = (if i then
    (case ph_sift_down (a, (ph_construct l)) of (a', l') \<Rightarrow> \<langle>l', (i,a'), (ph_construct r)\<rangle>)
  else
    (case ph_sift_down (a, (ph_construct r)) of (a', r') \<Rightarrow> \<langle>ph_construct l, (i,a'), r'\<rangle>)
)"

lemma "size t = size (ph_wheap t)"
  apply(induction t)
   apply auto
  done


abbreviation "ph_wheap_pair \<equiv> (\<lambda>(a,t). (a, ph_wheap t))"

lemma ph_join_ref: "ph_wheap_pair (ph_join (a, t)) = join (a, ph_wheap t)"
  apply (induction t)
   apply auto
  done

lemma ph_sift_down_ref: "ph_wheap_pair (ph_sift_down (a, t)) = sift_down (a, ph_wheap t)"
  apply (induction t)
   apply (auto split!: prod.splits)
  done

lemma ph_construct_ref: "ph_wheap (ph_construct ti) = construct (ph_wheap ti)"
  apply(induction ti)
   apply (auto split!: prod.splits)
     apply (metis Pair_inject old.prod.case ph_sift_down_ref)+
  done

abbreviation "braun_pair \<equiv> (\<lambda>(a,t). braun t)"
abbreviation "size_pair \<equiv> (\<lambda>(a,t). size t)"

lemma ph_join_braun: "braun t \<Longrightarrow> braun_pair (ph_join (a,t))"
  apply(cases t)
   apply (auto split!: if_splits)
  done

lemma ph_join_size: "size t = size_pair (ph_join (a,t))"
  apply(cases t)
   apply auto
  done

lemma ph_sift_down_size: "size t = size_pair (ph_sift_down (a,t))"
  apply(induction t arbitrary: a)
   apply (auto split!: prod.splits if_splits)
     apply (metis case_prod_conv)+
  done

lemma ph_sift_down_braun: "braun t \<Longrightarrow> braun_pair (ph_sift_down (a,t))"
  apply(induction t arbitrary: a)
   apply (auto split!: prod.splits if_splits simp add: ph_sift_down_size)
             apply (metis case_prod_conv ph_sift_down_size)+
  done

lemma "braun t \<Longrightarrow> braun_pair (ph_sift_down (a,t))"
proof (induction "(a,t)" arbitrary: a t rule: ph_sift_down.induct)
  case (1 a)
  then show ?case by auto
next
  case (2 a l i b r)
  obtain a' m' where sift_down_simp: "ph_sift_down (a, if i then r else l) = (a', m')"
    by (meson surj_pair)
  then have "braun_pair (ph_sift_down (a, if i then r else l))"
    apply(cases i)
    using 2 apply auto
    done
  then have "braun m'"
    by (simp add: sift_down_simp)
  moreover have "size m' = size (if i then r else l)"
    apply(cases i)
     apply (metis (mono_tags, lifting) case_prod_conv ph_sift_down_size sift_down_simp)+
    done
  ultimately show ?case
    using "2.prems" by (auto simp add: sift_down_simp)
qed

end
end