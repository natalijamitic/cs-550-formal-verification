// ../../stainless/stainless.sh Resolution.scala --watch --config-file=stainless.conf
//> using jar "stainless-library_2.13-0.9.6.jar"

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._


object AVL {
    // Define binary tree classes
    sealed abstract class Tree {
        // Get all keys
        def getKeySet: Set[BigInt] = this match {
            case Empty() => Set.empty
            case Node(k, l, r, _) => l.getKeySet ++ Set(k) ++ r.getKeySet
        }

        def getKeyList: List[BigInt] = (this match {
            case Empty() => List.empty[BigInt]
            case Node(k, l, r, _) => l.getKeyList ++ (k :: r.getKeyList)
        }).ensuring(_.content == this.getKeySet)
        
        lazy val size: BigInt = (this match {
            case Empty() => BigInt(0)
            case Node(_, l, r, _) => l.size + 1 + r.size
        }) ensuring(_ == getKeyList.length)


        def checkGreatest(v: BigInt): Boolean = {
            forall((x:BigInt) => (this.getKeySet.contains(x) ==> x < v))
        } 

        def checkSmallest(v: BigInt): Boolean = {
            forall((x:BigInt) => (this.getKeySet.contains(x) ==> v < x))
        } 

        def isBST: Boolean = {
            this match {
                case Empty() => true
                case Node(k, l, r, _) => l.checkGreatest(k) && r.checkSmallest(k) && l.isBST && r.isBST 
            }
        }

        def lookup(searched: BigInt): Boolean = {
            require(isBST)
            this match {
                case Empty() => false
                case Node(value, left, right, _) =>
                if (searched == value) {
                    true
                } else if(searched < value) {
                    left.lookup(searched)
                } else {
                    right.lookup(searched)
                }
            }
        } ensuring(res => res == this.getKeyList.contains(searched))

        def insertBST(value: BigInt): Tree = {
            require(isBST)
            this match {
                case Empty() => Node(value, Empty(), Empty(), 0)
                case Node(v, l, r, h) => (if (v < value) {
                    val nr = r.insertBST(value)
                    Node(v, l, nr, getNewHeight(l,r) )
                } else if (v > value) {
                    val nl = l.insertBST(value)
                    Node(v, nl, r, getNewHeight(nl, r))
                } else {
                    this
                })
            }
        } ensuring(res => res.isBST && res.getKeySet == getKeySet ++ Set(value))

        def getNewHeight(l:Tree, r:Tree):BigInt = {
            stainless.math.max(l.height, r.height) + 1
        }

        def height: BigInt = (
            this match {
                case Empty() => BigInt(-1)
                case Node(k, l, r, h) => {
                   stainless.math.max(l.height , r.height) + 1
                }
            }
        )

        // Define AVL properties
        def isBalanced: Boolean = {
            decreases(size)
            this match {
                case Empty() => true
                // case Node(_, l, r, h) => stainless.math.abs(l.height - r.height) <= 1 && l.isBalanced && r.isBalanced
            
                case Node(_, l, r, h) => (l.height - r.height == 1 || r.height - l.height == 1 || r.height == l.height) && l.isBalanced && r.isBalanced
            }
        }

        def isAVL: Boolean = {
            this match {
                case Empty() => true
                case Node(k, l, r, h) => isBalanced && isBST && r.isAVL && l.isAVL
            }
        }


        //    // Helper functions
        def balanceLeft(n: BigInt, l:Tree, r:Tree):Tree = {
            require( 
            l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL
            && ((stainless.math.abs(l.height - r.height) <=1)
            || ( l.height == r.height+2)))

            if (l.height == r.height + 2) {
                l match{
                    case Node(ln, ll, lr, _) =>  {
                        if (ll.height < lr.height) {
                            lr match {
                                case Node(lrn, lrl, lrr, _) => {

                                    val n1 = Node(ln,ll,lrl, getNewHeight(ll,lrl))
                                    val n2 = Node(n,lrr,r, getNewHeight(lrr,r))

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
                                    Node( lrn, n1 , n2, getNewHeight(n1,n2)) 
                                    }
                                case Empty() => Empty() // Should never happen
                            }
                        } else {
                            val n1 =  Node(n,lr,r, getNewHeight(lr,r))
                            // check(ll.isAVL)
                            // check(lr.isAVL)
                            // check(stainless.math.abs(ll.height - n1.height) <=1)
                            Node(ln, ll,n1 ,getNewHeight(ll,n1))
                        }
                    }
                    case Empty() => Empty() // Should never happen
                }
            }else {
                check(l.isAVL && r.isAVL)
                check(stainless.math.abs(l.height - r.height) <=1)
                Node(n, l, r, getNewHeight(l,r))
            }
        } 
        . ensuring (res => res.isAVL)

        def balanceRight(n: BigInt, l:Tree, r:Tree):Tree = {
            require( 
                l.checkGreatest(n) && r.checkSmallest(n) && l.isAVL && r.isAVL
            && (( stainless.math.abs(l.height - r.height) <=1)
            || ( r.height == l.height+2)))
            if (r.height == l.height + 2) {
                r match{
                    case Node(rn, rl, rr, _) =>  {
                        if (rl.height > rr.height) {
                            rl match {
                                case Node(rln, rll, rlr, _) => {
                                    val n1 = Node(n,l,rll, getNewHeight(l,rll))
                                    val n2 = Node(rn,rlr,rr, getNewHeight(rlr, rr))

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
                                    Node( rln, n1,n2, getNewHeight(n1,n2))
                                }
                                case Empty() => Empty() // Should never happen
                            }
                        } else {
                            val n1 = Node(n,l,rl, getNewHeight(l,rl))
                            Node(rn, n1, rr, getNewHeight(n1,rr))
                        }
                    }
                    case Empty() => Empty() // Should never happen
                }
            }else {
                check(l.isAVL && r.isAVL)
                check(stainless.math.abs(l.height - r.height) <=1)
                Node(n, l, r, getNewHeight(l,r))
            }
        }
        .ensuring(res=> res.isAVL)

        def insertAVL(new_key: BigInt):Tree = {
            require(isAVL)
            this match {
                case Empty() => Node(new_key, Empty(), Empty(), 0)
                case Node(k, l, r, _) => {
                    if (new_key == k ){
                        this
                    } else if (new_key < k) {
                        check(l.isAVL)
                        val ll = l.insertAVL(new_key)
                        if(ll.height <= r.height +2) {
                            this // should never happen
                        }
                        else {
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
                        }
                        else {
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

        }. ensuring(res=> res.isAVL && stainless.math.abs(res.height - old(this).height) <=1)
    }
        
    case class Node(key: BigInt, left: Tree, right: Tree, hgt: BigInt) extends Tree
    case class Empty() extends Tree

 
}

