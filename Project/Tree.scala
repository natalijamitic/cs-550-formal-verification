package project

// ../../stainless/stainless.sh Tree.scala --watch --timeout=10

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

case class Node(key: BigInt, left: Tree, right: Tree) extends Tree
case class Empty() extends Tree

sealed abstract class Tree {
    lazy val size: BigInt = (this match {
        case Empty() => BigInt(0)
        case Node(_, l, r) => l.size + BigInt(1) + r.size
    }).ensuring(_ == toList.length)

    def height: BigInt = (this match {
        case Empty() => BigInt(-1)
        case Node(k, l, r) => stainless.math.max(l.height , r.height) + 1
    }).ensuring(_ > -2)

    def toSet: Set[BigInt] = this match {
        case Empty() => Set.empty
        case Node(k, l, r) => l.toSet ++ Set(k) ++ r.toSet
    }

    def toList: List[BigInt] = (this match {
        case Empty() => List.empty[BigInt]
        case Node(k, l, r) => l.toList ++ (k :: r.toList)
    }).ensuring(_.content == this.toSet)

    def checkGreatest(v: BigInt): Boolean = {
        forall((x:BigInt) => (this.toSet.contains(x) ==> x < v))
    } 

    def checkSmallest(v: BigInt): Boolean = {
        forall((x:BigInt) => (this.toSet.contains(x) ==> x > v))
    } 

    def isBalanced: Boolean = {
        decreases(size)
        this match {
            case Empty() => true
            case Node(_, l, r) => (l.height - r.height == 1 || r.height - l.height == 1 || r.height == l.height) && l.isBalanced && r.isBalanced // stainless.math.abs mozda nece da radi
        }
    }

    def isBST: Boolean = this match {
        case Empty() => true
        case Node(k, l, r) => l.checkGreatest(k) && r.checkSmallest(k) && l.isBST && r.isBST 
    }

    def isAVL: Boolean = this match {
        case Empty() => true
        case Node(k, l, r) => isBalanced && isBST && r.isAVL && l.isAVL
    }
}