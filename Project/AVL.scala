// ../../stainless/stainless.sh AVL.scala --watch --timeout=10
//> using jar "stainless-library_2.13-0.9.6.jar"

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

object AVL {
    
    case class Node(key: BigInt, left: Tree, right: Tree) extends Tree
    case class Empty() extends Tree

    sealed abstract class Tree {
        lazy val size: BigInt = (this match {
            case Empty() => BigInt(0)
            case Node(_, l, r) => l.size + 1 + r.size
        }).ensuring(_ == getKeyList.length)

        def height: BigInt = (
            this match {
                case Empty() => BigInt(-1)
                case Node(k, l, r) => stainless.math.max(l.height , r.height) + 1
            }
        ).ensuring(_ > -2)

        def getKeySet: Set[BigInt] = this match {
            case Empty() => Set.empty
            case Node(k, l, r) => l.getKeySet ++ Set(k) ++ r.getKeySet
        }

        def getKeyList: List[BigInt] = (this match {
            case Empty() => List.empty[BigInt]
            case Node(k, l, r) => l.getKeyList ++ (k :: r.getKeyList)
        }).ensuring(_.content == this.getKeySet)

        def checkGreatest(v: BigInt): Boolean = {
            forall((x:BigInt) => (this.getKeySet.contains(x) ==> x < v))
        } 

        def checkSmallest(v: BigInt): Boolean = {
            forall((x:BigInt) => (this.getKeySet.contains(x) ==> v < x))
        } 

        def isBalanced: Boolean = {
            decreases(size)
            this match {
                case Empty() => true
                case Node(_, l, r) => (l.height - r.height == 1 || r.height - l.height == 1 || r.height == l.height) && l.isBalanced && r.isBalanced // stainless.math.abs mozda nece da radi
            }
        }

        def isBST: Boolean = {
            this match {
                case Empty() => true
                case Node(k, l, r) => l.checkGreatest(k) && r.checkSmallest(k) && l.isBST && r.isBST 
            }
        }

        def isAVL: Boolean = {
            this match {
                case Empty() => true
                case Node(k, l, r) => isBalanced && isBST && r.isAVL && l.isAVL
            }
        }
    
        def lookupAVL(searched: BigInt): Boolean = {
            require(isAVL)
            this match {
                case Empty() => false
                case Node(value, left, right) =>
                if (searched == value) {
                    true
                } else if(searched < value) {
                    left.lookupAVL(searched)
                } else {
                    right.lookupAVL(searched)
                }
            }
        }.ensuring(res => res == this.getKeyList.contains(searched))

        def balanceLeft(n: BigInt, l:Tree, r:Tree):Tree = {
            require( 
                l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL && 
                ((stainless.math.abs(l.height - r.height) <=1) || ( l.height == r.height+2)))

            if (l.height == r.height + 2) {
                l match{
                    case Node(ln, ll, lr) =>  {
                        if (ll.height < lr.height) {
                            lr match {
                                case Node(lrn, lrl, lrr) => {

                                    val n1 = Node(ln,ll,lrl)
                                    val n2 = Node(n,lrr,r)

                                    // PROVE IS BST

                                    check(lrl.checkGreatest(lrn))
                                    check(ll.checkGreatest(ln))
                                    check(lr.checkSmallest(ln) ==> ln<lrn && lrl.checkSmallest(ln))
                                    check(n2.isBST)
                                    
                                    check(r.checkSmallest(n))
                                    check(l.checkGreatest(n) ==> n>ln && lrr.checkGreatest(n))
                                    check(n1.isBST)

                                    check(l.getKeySet.contains(lrn))
                                    check(lrr.checkSmallest(lrn))

                                    check(n1.checkGreatest(lrn))
                                    check(n2.checkSmallest(lrn))

                                    // PROOVE IS BALANCED
                                    check(stainless.math.abs(n1.height - n2.height)<=1)
                                    check(n1.isBalanced)
                                    check(n2.isBalanced)
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
                check(l.isAVL && r.isAVL)
                check(stainless.math.abs(l.height - r.height) <=1)
                Node(n, l, r)
            }
        }.ensuring (res => res.isAVL  && (res.size == l.size + r.size + 1)  && (res.height == stainless.math.max(l.height, r.height) +1 || res.height == stainless.math.max(l.height, r.height)) && l.getKeySet.subsetOf(res.getKeySet) && res.getKeySet.contains(n) && r.getKeySet.subsetOf(res.getKeySet))

        def balanceRight(n: BigInt, l:Tree, r:Tree):Tree = {
            require( 
                l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL && 
                (( stainless.math.abs(l.height - r.height) <=1) || ( r.height == l.height+2)))

            if (r.height == l.height + 2) {
                r match{
                    case Node(rn, rl, rr) =>  {
                        if (rl.height > rr.height) {
                            rl match {
                                case Node(rln, rll, rlr) => {
                                    val n1 = Node(n,l,rll)
                                    val n2 = Node(rn,rlr,rr)

                                    // PROVE IS BST
                                    check(r.checkSmallest(n) ==> (n<rn && rll.checkSmallest(n)))
                                    check(l.checkGreatest(n))
                                    check(n1.isBST)

                                    check(r.getKeySet.contains(rln))
                                    check(rll.checkGreatest(rln))
                                    check(n1.checkGreatest(rln))

                                    check(rlr.checkSmallest(rln))
                                    check(rr.checkSmallest(rn))
                                    check(rl.checkGreatest(rn) ==> rn>rln && rlr.checkGreatest(rn))
                                    check(n2.isBST)
                                    check(n2.checkSmallest(rln))

                                    // PROOVE IS BALANCED
                                    check(stainless.math.abs(n1.height - n2.height)<=1)
                                    check(n1.isBalanced)
                                    check(n2.isBalanced)
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
                check(l.isAVL && r.isAVL)
                check(stainless.math.abs(l.height - r.height) <=1)
                Node(n, l, r)
            }
        }.ensuring(res=> res.isAVL && (res.size == l.size + r.size + 1)  && (res.height == stainless.math.max(l.height, r.height) +1 || res.height == stainless.math.max(l.height, r.height)) && l.getKeySet.subsetOf(res.getKeySet) && res.getKeySet.contains(n) && r.getKeySet.subsetOf(res.getKeySet))


        def insertAVL(new_key: BigInt):Tree = {
            require(isAVL)
            this match {
                case Empty() => Node(new_key, Empty(), Empty())
                case Node(k, l, r) => {
                    if (new_key == k ){
                        this
                    } else if (new_key < k) {
                        check(l.isAVL)
                        val ll = l.insertAVL(new_key)
                        if(ll.height <= r.height +2) {
                            this // should never happen
                        } else {
                            check(stainless.math.abs(ll.height - l.height) <=1)
                            check(ll.isAVL && r.isAVL)
                            check(stainless.math.abs(l.height - r.height) <=1)
                            check(ll.height <= r.height +2)
                            check(((stainless.math.abs(ll.height - r.height) <=1) || ( ll.height == r.height+2)))
                            balanceLeft(k, ll , r)
                        }
                    } else {
                        check(r.isAVL)
                        val rr = r.insertAVL(new_key)
                        if (rr.height <= l.height +2) {
                            this // should never happen
                        } else {
                            check(stainless.math.abs(rr.height - r.height) <=1)
                            check(rr.isAVL && l.isAVL)
                            check(stainless.math.abs(r.height - l.height) <=1)
                            check(rr.height <= l.height +2)
                            check(((stainless.math.abs(rr.height - l.height) <=1) || ( rr.height == l.height+2)))
                            balanceRight(k, l , rr)
                        }
                    }
                }
            }

        }.ensuring(res=> res.isAVL && ((res.size == old(this).size + 1) || (res.size == old(this).size)) && stainless.math.abs(res.height - old(this).height) <=1)

        def delete_max(): (BigInt, Tree) = {
            require(this.size > 0 && isAVL)
            this match {
                case Node(n, l, r) if r.size == 0 => {
                    check(r.height == -1)
                    check(stainless.math.abs(r.height - l.height)<=1)
                    check(l.height == -1 || l.height == 0)
                    check(l.height == this.height -1)
                    check(r.size == 0 && (l.size + 1) == this.size)
                    (n,l)
                }
                case Node(n, l, r) => {
                    val (n_prim, r_prim) = r.delete_max()
                    check(r.getKeySet.contains(n_prim))
                    check(l.checkGreatest(n) && r_prim.checkSmallest(n))
                    check(r_prim.checkGreatest(n_prim))
                    check(n_prim > n)
                    check(l.isAVL && r_prim.isAVL)
                    check((stainless.math.abs(l.height - r_prim.height) <=1) || ( l.height == r_prim.height+2))
                    (n_prim, balanceLeft(n, l, r_prim))
                }
            }
        }.ensuring(res => res._2.isAVL && (res._2.size + 1 == old(this).size) && (res._2.height == old(this).height || res._2.height == old(this).height - 1) && res._2.checkGreatest(res._1) && this.getKeySet.contains(res._1) && res._2.getKeySet.subsetOf(old(this).getKeySet))

        def delete_root(): Tree = { 
            require(size > 0 && isAVL)
            this match {
                case Node(n, l, r) if r.size == 0 => l
                case Node(n, l, r) if l.size == 0 => r
                case Node(n, l, r) => {
                    val (n_prim, l_prim) = l.delete_max()
                    check(l_prim.size + 1 == l.size)

                    check(l_prim.checkGreatest(n_prim))
                    check(r.checkSmallest(n_prim))
                    check(l_prim.isAVL && r.isAVL)
                    check((stainless.math.abs(l_prim.height - r.height) <=1) || ( l_prim.height +2 == r.height))
                    balanceRight(n_prim, l_prim, r)
                }
            }
        }.ensuring (res=> res.isAVL && (res.size + 1 == old(this).size) && res.getKeySet.subsetOf(old(this).getKeySet) && (old(this).height == res.height || old(this).height == res.height + 1))

        def deleteAVL(key: BigInt): Tree = {
            require(isAVL)
            this match {
                case Empty() => Empty()
                case Node(n, l, r) => {
                    if (key == n) {
                        delete_root()
                    } else if (key < n) {
                        val l_prim = l.deleteAVL(key)
                        check(l_prim.checkGreatest(n)) // skontaj da je l_prim subset l
                        check(r.checkSmallest(n))
                        check(l_prim.isAVL && r.isAVL)
                        check((stainless.math.abs(l_prim.height - r.height) <=1) || ( l_prim.height +2 == r.height))
                        balanceRight(n, l_prim, r)
                    } else {
                        val r_prim = r.deleteAVL(key)
                        check(l.checkGreatest(n) && r_prim.checkSmallest(n)) // skontaj da je r_prim subset r
                        check(l.isAVL && r_prim.isAVL)
                        check((stainless.math.abs(l.height - r_prim.height) <=1) || ( l.height == r_prim.height+2))
                    
                        balanceLeft(n, l, r_prim)
                    }
                }
            }
        }.ensuring(res=> res.isAVL && ((res.size == old(this).size) || (res.size + 1 == old(this).size)) && res.getKeySet.subsetOf(old(this).getKeySet) && (old(this).height == res.height || old(this).height == res.height + 1))

        def joinRightAVL(tl: Tree, k:BigInt, tr:Tree):Tree = {
            require(tl.size > 0 && tr.size > 0 && tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k) && tl.height > tr.height + 1)
            tl match {
                case Node(kprim, l, r) => {
                    if (r.height <= tr.height + 1) {
                        val tprim = Node(k,r,tr)
                        
                        check(l.checkGreatest(kprim))
                        check(r.checkSmallest(kprim) ==>  tprim.checkSmallest(kprim))

                        check(tprim.isAVL)

                        check(l.height <= tr.height + 2)
                        check(tr.height - 1 <= r.height)
                        check(tr.height - 2 <= l.height)
                        check(tr.height + 1 >= r.height)
                        check(tr.height + 2 >= l.height)
                        check(tr.height + 2 >= tprim.height)
                        check(tr.height + 1 <= tprim.height)
                        check((r.height == l.height ==> (l.height == tr.height + 1 && tprim.height == tr.height+2)) ==>  ((stainless.math.abs(l.height - tprim.height) <=1) || ( l.height == tprim.height-2)))
                        check(r.height < l.height ==>(( r.height == l.height-1 && l.height > tr.height && l.height <= tr.height + 2) && (r.height == tr.height || r.height == tr.height +1) && tprim.height == r.height+1))
                        
                        balanceRight(kprim,l, tprim)
                    }
                    else {
                        check(r.size > 0)
                        check(l.checkGreatest(k))
                        check(r.checkGreatest(k))
                        check(r.height > tr.height + 1)
                        val tprim = joinRightAVL(r, k, tr)
                        check(tprim.isAVL)
                        
                        check(((tprim.height >= r.height) && (tprim.height <= r.height + 1) && r.height < l.height) ==> (stainless.math.abs(l.height - tprim.height) <=1))
                        check(((tprim.height <= r.height + 1)  &&  (r.height == l.height)) ==> (stainless.math.abs(l.height - tprim.height) <=1))
                        check(((tprim.height >= r.height) && (tprim.height <= r.height + 1) && r.height > l.height) ==> ((stainless.math.abs(l.height - tprim.height) <=1) || ( l.height == tprim.height-2)))
                        
                        balanceRight(kprim, l, tprim)
                    }
                }
                
            }

        }.ensuring(res=> res.isAVL && res.height <= tl.height + 1 && res.height >= tl.height && res.height >= tr.height + 1 && res.size == tl.size + tr.size + 1 && tl.getKeySet.subsetOf(res.getKeySet) && res.getKeySet.contains(k) && tr.getKeySet.subsetOf(res.getKeySet))


        def joinLeftAVL(tl: Tree, k:BigInt, tr:Tree):Tree = {
            require(tl.size > 0 && tr.size > 0 && tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k) && tl.height + 1 < tr.height)
            tr match {
                case Node(kprim, l, r) => {
                    if (l.height <= tl.height + 1) {
                        val tprim = Node(k,tl, l)
                        
                        check(tl.checkGreatest(k))
                        check(l.checkSmallest(k))
                        check(tprim.isBST)
                        check(tprim.isBalanced)
                        check(tprim.isAVL)


                        check(l.checkSmallest(kprim) ==> tprim.checkGreatest(kprim))
                        check(r.checkSmallest(kprim))
                        check((r.height == l.height ==> (l.height == tl.height + 1 && tprim.height == tl.height+2)) ==>  ((stainless.math.abs(l.height - tprim.height) <=1) || ( l.height == tprim.height-2)))
                        check(l.height < r.height ==>(( l.height == r.height-1 && r.height > tl.height && r.height <= tl.height + 2) && (l.height == tl.height || l.height == tl.height +1) && tprim.height == l.height+1))
                        
                        balanceLeft(kprim,tprim, r)
                    }
                    else {
                        check(l.size > 0)
                        check(l.checkSmallest(k))
                        check(r.checkSmallest(k))
                        check(l.height > tl.height + 1)
                        val tprim = joinLeftAVL(tl, k, l)
                        check(tprim.isAVL)
                        
                        check(((tprim.height >= l.height) && (tprim.height <= l.height + 1) && l.height < r.height) ==> (stainless.math.abs(r.height - tprim.height) <=1))
                        check(((tprim.height <= l.height + 1)  &&  (r.height == l.height)) ==> (stainless.math.abs(r.height - tprim.height) <=1))
                        check(((tprim.height >= l.height) && (tprim.height <= l.height + 1) && l.height > r.height) ==> ((stainless.math.abs(r.height - tprim.height) <=1) || ( r.height == tprim.height-2)))
                        balanceLeft(kprim, tprim, r)
                    }
                }
                
            }

        }.ensuring(res=> res.isAVL && res.height <= tr.height + 1 && res.height >= tr.height && res.height >= tl.height + 1 && res.size == tl.size + tr.size + 1 && tl.getKeySet.subsetOf(res.getKeySet) && res.getKeySet.contains(k) && tr.getKeySet.subsetOf(res.getKeySet))


        def joinAVL(tl : Tree, k:BigInt, tr:Tree): Tree = {
            require(tl.size > 0 && tr.size > 0 && tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k))
            if(tl.height > tr.height +1) {
                joinRightAVL(tl, k, tr)
            } else if (tr.height > tl.height + 1) {
                joinLeftAVL(tl, k, tr)
            } else {
                Node(k, tl, tr)
            }
        }.ensuring(res=> res.isAVL && res.size == tl.size + tr.size + 1 && tl.getKeySet.subsetOf(res.getKeySet) && res.getKeySet.contains(k) && tr.getKeySet.subsetOf(res.getKeySet))

    }
}