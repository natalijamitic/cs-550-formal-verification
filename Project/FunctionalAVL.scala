package project

import stainless.lang._
import stainless.annotation._

import project.AVL._


trait FunctionalAVL {
    def lookup(element: BigInt): Boolean
    def insert(element: BigInt): Tree
    def delete(element: BigInt): Tree

    // def joinToRight(k: BigInt, tr: Tree): Tree
    // def joinToLeft(tl : Tree, k: BigInt): Tree
    // def join(tl : Tree, k:BigInt, tr:Tree): Tree

    def isEmpty: Boolean
    def size: BigInt
    def toSet: Set[BigInt]
}

case class AVLTree private(val tree: Tree) extends FunctionalAVL {
    require(tree.isAVL) 
    
    override def lookup(element: BigInt): Boolean = lookupAVL(tree, element)
    override def insert(element: BigInt): Tree = insertAVL(tree, element)
    override def delete(element: BigInt): Tree = deleteAVL(tree, element)

    // override def join(tl: Tree, k: BigInt, tr: Tree): Tree = {
    //     joinAVL(tl, k, tr)
    // }
    // override def joinToRight(k: BigInt, tr: Tree): Tree = {
    //     require(tree.isAVL && tr.isAVL && tree.checkGreatest(k) && tr.checkSmallest(k))
    //     joinAVL(tree, k, tr)
    // }
    // override def joinToLeft(tl : Tree, k: BigInt): Tree = {
    //     require(tree.isAVL && tl.isAVL && tl.checkGreatest(k) && tree.checkSmallest(k))
    //     join(tl, k, tree)
    // }

    override def isEmpty: Boolean = tree.size == 0
    override def size: BigInt = tree.size
    override def toSet: Set[BigInt] = tree.toSet
}
