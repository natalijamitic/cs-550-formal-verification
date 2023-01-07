package project

import stainless.lang._
import stainless.annotation._

import project.AVL._

trait FunctionalAVL {
    def lookup(element: BigInt): Boolean
    def insert(element: BigInt): Tree
    def delete(element: BigInt): Tree

    def join(tl : Tree, k:BigInt, tr:Tree): Tree
    def split(element: BigInt): (Tree, Boolean, Tree)

    def isEmpty: Boolean
    def size: BigInt
    def toSet: Set[BigInt]
}

case class AVLTree private(val tree: Tree) extends FunctionalAVL {
    require(tree.isAVL) 
    
    override def lookup(element: BigInt): Boolean = lookupAVL(tree, element)
    override def insert(element: BigInt): Tree = insertAVL(tree, element)
    override def delete(element: BigInt): Tree = deleteAVL(tree, element)
    
    override def split(element: BigInt): (Tree, Boolean, Tree) = splitAVL(tree, element)
    override def join(tl: Tree, k: BigInt, tr: Tree): Tree = {
        if (tl.isAVL && tr.isAVL && tl.checkGreatest(k) && tr.checkSmallest(k)) then {
            joinAVL(tl, k, tr)
        } else {
            Empty()
        }
    }

    override def isEmpty: Boolean = tree.size == 0
    override def size: BigInt = tree.size
    override def toSet: Set[BigInt] = tree.toSet
}
