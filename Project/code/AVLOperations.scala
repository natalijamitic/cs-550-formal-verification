package project

import stainless.lang._
import stainless.annotation._

import project.Tree

/**
 * This trait represents a set of operations that can be performed on an AVL tree, a self-balancing
 * binary search tree.
 * The `AVLOperations` trait defines methods for inserting and deleting elements, looking up elements,
 * splitting and joining trees, checking if the tree is empty, determining the size of the tree, and
 * converting the tree to a set.
 */
trait AVLOperations {
    /**
     * Looks up an element in the AVL tree.
     * 
     * @param element the element to look up
     * @return true if the element is found in the tree, false otherwise
     */
    def lookup(element: BigInt): Boolean

    /**
     * Inserts an element into the AVL tree.
     * 
     * @param element the element to insert
     * @return the AVL tree with the element inserted
     */
    def insert(element: BigInt): Tree

    /**
     * Deletes an element from the AVL tree.
     * 
     * @param element the element to delete
     * @return the AVL tree with the element deleted
     */
    def delete(element: BigInt): Tree

    /**
     * Splits the AVL tree into three parts: the left tree, a boolean indicating
     * whether the split element is present in the original tree, and the right tree.
     * 
     * @param element the element to split on
     * @return a triple consisting of the left tree, a boolean indicating the presence
     *         of the split element, and the right tree
     */
    def split(element: BigInt): (Tree, Boolean, Tree)

    /**
     * Joins two AVL trees together with a given element as the root of the resulting tree.
     * 
     * @param tl the left AVL tree
     * @param k the element to use as the root of the resulting tree
     * @param tr the right AVL tree
     * @return the joined AVL tree
     */
    def join(tl: Tree, k: BigInt, tr: Tree): Tree

    /**
     * Checks if the AVL tree is empty.
     * 
     * @return true if the tree is empty, false otherwise
     */
    def isEmpty: Boolean

    /**
     * Returns the size of the AVL tree.
     * 
     * @return the number of elements in the tree
     */
    def size: BigInt

    /**
     * Converts the AVL tree to a set of elements.
     * 
     * @return a set containing the elements of the tree
     */
    def toSet: Set[BigInt]
}