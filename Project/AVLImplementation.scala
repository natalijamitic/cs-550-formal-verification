package project

// ../../stainless/stainless.sh *.scala --watch --timeout=10

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

import project.Tree

object AVL {

    def lookupAVL(tree: Tree, searched: BigInt): Boolean = {
        require(tree.isAVL) 
        tree match {
            case Empty() => false
            case Node(value, left, right) =>
            if (searched == value) {
                true
            } else if(searched < value) {
                lookupAVL(left, searched)
            } else {
                lookupAVL(right, searched)
            }
        }
    }.ensuring(_ == tree.toList.contains(searched))
    
    def BSTSpreadRight(v: BigInt, subtree: Tree): Boolean = {
        require(subtree.checkSmallest(v))
        subtree match {
            case Node(root, left, right) => v<root && left.checkSmallest(v) && right.checkSmallest(v)
            case Empty() => true
        }
    }.holds

    def BSTSpreadLeft(v: BigInt, subtree: Tree): Boolean = {
        require(subtree.checkGreatest(v))
        subtree match {
            case Node(root, left, right) => v>root && left.checkGreatest(v) && right.checkGreatest(v)
            case Empty() => true
        }
    }.holds

    def balanceLeft(n: BigInt, l: Tree, r: Tree): Tree = {
        require( 
            l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL && 
            ((stainless.math.abs(l.height - r.height) <= 1) || ( l.height == r.height + 2)))

        if (l.height == r.height + 2) {
            l match{
                case Node(ln, ll, lr) =>  {
                    if (ll.height < lr.height) {
                        lr match {
                            case Node(lrn, lrl, lrr) => {

                                val n1 = Node(ln,ll,lrl)
                                val n2 = Node(n,lrr,r)

                                // PROVE IS BST
                                //check(lr.checkSmallest(ln) ==> ln<lrn && lrl.checkSmallest(ln))
                                check(BSTSpreadRight(ln, lr))

                                Node( lrn, n1 , n2) 
                                }
                            case Empty() => Empty() // Should never happen
                        }
                    } else {
                        val n1 =  Node(n,lr,r)
                        Node(ln, ll,n1)
                    }
                }
                case Empty() => Empty() // Should never happen
            }
        } else {
            Node(n, l, r)
        }
    }.ensuring(res => res.isAVL  && (res.size == l.size + r.size + 1)  && (res.height == stainless.math.max(l.height, r.height) +1 || res.height == stainless.math.max(l.height, r.height)) && ((l.toSet ++ r.toSet)+ n) == res.toSet)

    def balanceRight(n: BigInt, l: Tree, r: Tree): Tree = {
        require( 
            l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL && 
            (( stainless.math.abs(l.height - r.height) <= 1) || ( r.height == l.height + 2)))

        if (r.height == l.height + 2) {
            r match{
                case Node(rn, rl, rr) =>  {
                    if (rl.height > rr.height) {
                        rl match {
                            case Node(rln, rll, rlr) => {
                                val n1 = Node(n,l,rll)
                                val n2 = Node(rn,rlr,rr)

                                // PROVE IS BST
                                //check(rl.checkGreatest(rn) ==> rn>rln && rlr.checkGreatest(rn))
                                check(BSTSpreadLeft(rn, rl))

                                Node( rln, n1,n2)
                            }
                            case Empty() => Empty() // Should never happen
                        }
                    } else {
                        val n1 = Node(n,l,rl)
                        Node(rn, n1, rr)
                    }
                }
                case Empty() => Empty() // Should never happen
            }
        }else {
            Node(n, l, r)
        }
    }.ensuring(res => res.isAVL && (res.size == l.size + r.size + 1)  && (res.height == stainless.math.max(l.height, r.height) +1 || res.height == stainless.math.max(l.height, r.height)) && ((l.toSet ++ r.toSet)+ n) == res.toSet)


    def insertAVL(tree: Tree, new_key: BigInt): Tree = {
        require(tree.isAVL)
        tree match {
            case Empty() => Node(new_key, Empty(), Empty())
            case Node(k, l, r) => {
                if (new_key == k ){
                    tree
                } else if (new_key < k) {
                    val ll = insertAVL(l, new_key)
                    if(ll.height <= r.height +2) {
                        tree // should never happen
                    } else {
                        balanceLeft(k, ll , r)
                    }
                } else {
                    val rr = insertAVL(r, new_key)
                    if (rr.height <= l.height +2) {
                        tree // should never happen
                    } else {
                        balanceRight(k, l , rr)
                    }
                }
            }
        }
    }.ensuring(res=> res.isAVL && ((res.size == tree.size + 1) || (res.size == tree.size)) && stainless.math.abs(res.height - tree.height) <=1)

    def delete_max(tree: Tree): (BigInt, Tree) = {
        require(tree.size > 0 && tree.isAVL)
        tree match {
            case Node(n, l, r) if r.size == 0 => {
                (n,l)
            }
            case Node(n, l, r) => {
                val (n_prim, r_prim) = delete_max(r)
                (n_prim, balanceLeft(n, l, r_prim))
            }
        }
    }.ensuring(res => res._2.isAVL && (res._2.size + 1 == tree.size) && (res._2.height == tree.height || res._2.height == tree.height - 1) && res._2.checkGreatest(res._1) && tree.toSet.contains(res._1) && res._2.toSet.subsetOf(tree.toSet))

    def delete_root(tree: Tree): Tree = { 
        require(tree.size > 0 && tree.isAVL)
        tree match {
            case Node(n, l, r) if r.size == 0 => l
            case Node(n, l, r) if l.size == 0 => r
            case Node(n, l, r) => {
                val (n_prim, l_prim) = delete_max(l)
                balanceRight(n_prim, l_prim, r)
            }
        }
    }.ensuring(res => res.isAVL && (res.size + 1 == tree.size) && res.toSet.subsetOf(tree.toSet) && (tree.height == res.height || tree.height == res.height + 1))

    def deleteAVL(tree: Tree, key: BigInt): Tree = {
        require(tree.isAVL)
        tree match {
            case Empty() => Empty()
            case Node(n, l, r) => {
                if (key == n) {
                    delete_root(tree)
                } else if (key < n) {
                    val l_prim = deleteAVL(l, key)
                    balanceRight(n, l_prim, r)
                } else {
                    val r_prim = deleteAVL(r, key)
                    balanceLeft(n, l, r_prim)
                }
            }
        }
    }.ensuring(res => res.isAVL && (!tree.toSet.contains(key) ==> (res.size == tree.size)) && (res.toSet.contains(key) ==> (res.size + 1 == tree.size)) && res.toSet.subsetOf(tree.toSet) && (tree.height == res.height || tree.height == res.height + 1) && !res.toSet.contains(key))

    def joinRightAVL(tl: Tree, k: BigInt, tr: Tree): Tree = {
        require(tl.size > 0 && tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k) && tl.height > tr.height + 1)
        tl match {
            case Node(kprim, l, r) => {
                if (r.height <= tr.height + 1) {
                    val tprim = Node(k,r,tr)    
                    balanceRight(kprim,l, tprim)
                }
                else {
                    val tprim = joinRightAVL(r, k, tr)
                    balanceRight(kprim, l, tprim)
                }
            }
        }
    }.ensuring(res => res.isAVL && res.height <= tl.height + 1 && res.height >= tl.height && res.height >= tr.height + 1 && res.size == tl.size + tr.size + 1  && ((tl.toSet ++ tr.toSet)+ k) == res.toSet)

    def joinLeftAVL(tl: Tree, k: BigInt, tr: Tree): Tree = {
        require(tr.size > 0 && tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k) && tl.height + 1 < tr.height)
        tr match {
            case Node(kprim, l, r) => {
                if (l.height <= tl.height + 1) {
                    val tprim = Node(k,tl, l)
                    balanceLeft(kprim,tprim, r)
                }
                else {
                    val tprim = joinLeftAVL(tl, k, l)
                    balanceLeft(kprim, tprim, r)
                }
            }
        }
    }.ensuring(res => res.isAVL && res.height <= tr.height + 1 && res.height >= tr.height && res.height >= tl.height + 1 && res.size == tl.size + tr.size + 1 && tl.toSet.subsetOf(res.toSet) && res.toSet.contains(k) && tr.toSet.subsetOf(res.toSet) && ((tl.toSet ++ tr.toSet)+ k) == res.toSet)

    def joinAVL(tl: Tree, k: BigInt, tr: Tree): Tree = {
        require(tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k))
        if(tl.height > tr.height +1) {
            joinRightAVL(tl, k, tr)
        } else if (tr.height > tl.height + 1) {
            joinLeftAVL(tl, k, tr)
        } else {
            Node(k, tl, tr)
        }
    }.ensuring(res => res.isAVL && res.size == tl.size + tr.size + 1 && tl.toSet.subsetOf(res.toSet) && res.toSet.contains(k) && tr.toSet.subsetOf(res.toSet) &&  ((tl.toSet ++ tr.toSet)+ k) == res.toSet)

    def splitAVL(t: Tree, k: BigInt): (Tree, Boolean, Tree) = {
        require(t.isAVL)
        t match {
            case Empty() => (Empty(), false, Empty())
            case Node(m, l, r) => {
                if (m == k) {
                    (l, true, r)
                } else if(k < m) {
                    val (lprim, b, rprim) = splitAVL(l, k)
                    (lprim, b, joinAVL(rprim, m, r))
                } else  {
                    val (lprim, b, rprim) = splitAVL(r, k)
                    (joinAVL(l, m, lprim), b, rprim)
                }
            }
        }
    }.ensuring((t1, success, t2) => (t1.isAVL && t2.isAVL && t1.checkGreatest(k) && t2.checkSmallest(k) && t1.toSet.subsetOf(t.toSet) && t2.toSet.subsetOf(t.toSet)) && (success ==> t.toSet.contains(k))) 
}