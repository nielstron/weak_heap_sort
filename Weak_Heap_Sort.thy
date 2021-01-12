theory Weak_Heap_Sort
imports "HOL-Library.Tree_Multiset" Weak_Heap Weak_Heap_Braun
begin


text \<open>Using the method for constructing braun trees from lists, we can hence sort a normal list
      by first making it a heap and then converting the heap to a sorted list\<close>

fun heapify:: "'a::linorder list \<Rightarrow> 'a \<times> 'a tree" where
  "heapify (x#xs) = sift_down (x,(construct (heap_of_A xs)))"

definition weak_heap_sort:: "'a::linorder list \<Rightarrow> 'a list" where
  "weak_heap_sort l = (case l of [] \<Rightarrow> [] | x#xs \<Rightarrow> weak_heap_heap_sort (heapify (x#xs)))"

lemma wheap_heapify: "l \<noteq> [] \<Longrightarrow> weak_heap (wheap_of_wheap (heapify l))"
proof -
  assume "l \<noteq> []"
  then obtain x xs where "l = x#xs" by (cases l) auto
  let ?A = "heap_of_A xs"
  have 1: "almost_complete (height ?A) ?A"
    by (simp add: almost_complete_balanced balanced_if_braun braun_heap_of_A)
  then have "almost_complete (height ?A) (construct ?A)" by (simp add: almost_complete_construct)
  then have "almost_complete (height ?A) (tree_of_wheap (sift_down (x, (construct ?A))))"
    by (simp add: almost_complete_sift_down)

  have 2: "right_heap (wheap_of_wheap (sift_down (x, (construct ?A))))"
    by (simp add: right_heap_construct right_heap_sift_down)

  from 1 2 have wheap_sd: "weak_heap (wheap_of_wheap (sift_down (x, (construct ?A))))"
    by (metis construct.simps(1) construct.simps(2) old.prod.case weak_heap_construct wheap_of_wheap.elims)
  then show ?thesis
    by (simp add: \<open>l = x # xs\<close>)
qed

lemma mset_heapify: "l \<noteq> [] \<Longrightarrow> mset_tree (wheap_of_wheap (heapify l)) = mset l"
proof -

  assume "l \<noteq> []"
  then obtain x xs where "l = x#xs" by (cases l) auto
  let ?A = "heap_of_A xs"
  
  have "mset_tree (wheap_of_wheap(heapify (x#xs))) = mset_tree (wheap_of_wheap (sift_down (x, (construct ?A))))"
    unfolding Weak_Heap_Sort.heapify.simps by simp
  also have "\<dots> = {#x#} + (mset_tree (construct ?A))"
    by (metis add.left_neutral add_mset_add_single mset_eq_sift_down mset_tree.simps(1) mset_tree.simps(2) mset_wheap.simps union_mset_add_mset_left wheap_of_wheap.elims)
  also have "\<dots> = {#x#} + (mset_tree ?A)" 
    by (metis mset_eq_construct)
  also have "\<dots> = {#x#} + mset xs"
    by (simp add: mset_tree_heap_of_A)
  also have "\<dots> = mset (x#xs)" by auto
  finally have "mset_tree (wheap_of_wheap(heapify (x#xs))) = mset (x#xs)" by auto
  then show ?thesis using \<open>l = x#xs\<close> by auto
qed

lemma "mset l = mset (weak_heap_sort l)"
proof (cases l)
  case (Cons x xs)
  have "mset (weak_heap_sort (x#xs)) = mset (weak_heap_heap_sort (heapify (x#xs)))"
    unfolding weak_heap_sort_def by simp
  also have "\<dots> = mset_tree (wheap_of_wheap (heapify (x#xs)))"
    using weak_heap_sort_mset Cons wheap_heapify
    by (metis list.distinct(1) wheap_of_wheap.elims)
  also have "\<dots> = mset (x#xs)"
    using Weak_Heap_Sort.mset_heapify by blast
  finally have "mset (weak_heap_sort (x#xs)) = mset (x#xs)" by auto
  then show ?thesis using Cons by auto
qed (simp add: weak_heap_sort_def)

lemma "sorted_wrt (\<le>) (weak_heap_sort l)"
proof (cases l)
  case (Cons x xs)
  then have "sorted_wrt (\<le>) (weak_heap_heap_sort (heapify (x#xs)))"
    using wheap_heapify
    by (metis list.distinct(1) weak_heap_sort_sorted wheap_of_wheap.elims)
  then have "sorted_wrt (\<le>) (weak_heap_sort (x#xs))" by (simp add: weak_heap_sort_def)
  then show ?thesis using Cons by auto
qed (simp add: weak_heap_sort_def)


end