// ../../stainless/stainless.sh SubList.scala --watch --config-file=stainless.conf

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.equations._

object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 

  def subListRefl[T](l: List[T]): Unit = {
    l match {
      case(Nil()) => ()
      case(Cons(x, xs)) => subListRefl(xs)
    }
  }.ensuring(_ =>
    subList(l, l)
  )


  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))

    (l1, l2) match {
      case (Nil(), _)                 => ()
      case (_, Nil())                 => ()
      case (Cons(x, xs), Cons(y, ys)) => (if (x == y && subList(xs, ys)) then 
                                            subListLength(xs, ys) 
                                          else 
                                            subListLength(l1, ys))
    }
  }.ensuring(_ =>
    l1.length <= l2.length
  )


  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))

    decreases(l2)

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) => {
        if (subList(l1, l2.tail)) {
          subListTail(l1, l2.tail)
        }
      }
    }
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )


  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    
    subListTail(l1, l2) // subList(l1.tail, l2)

  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )


  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))
    
    (l1, l2, l3) match {
      case (Nil(), _, _)                           => ()
      case (Cons(x, xs), Cons(y, ys), Cons(z, zs)) => {
        if (x == y && y == z && subList(xs, ys) && subList(ys, zs)) then
          subListTails(l1, l2) 
          subListTails(l2, l3)
          subListTrans(xs, ys, zs)
        else {
          if (x != y && x == z && subList(xs, ys)) then
            subListTail(l1, l2)
            subListTrans(xs, l2, zs)
          else {
            if (x!=y && y == z && subList(ys, zs)) then
              subListTails(l2, l3)
              subListTrans(l1, ys, zs) 
            else if (x==y && y!=z) then
              subListTail(l1, l2)
              subListTail(l2, l3)
              subListTrans(l1, l2, zs) 
            else { //(x!=y && y!=z)
              subListTail(l1, l2) 
              subListTail(l2, l3)
              subListTrans(l1, ys, zs)
            }
          } 
        }
      }
    }

  }.ensuring(_ =>
    subList(l1, l3)
  )


  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)
 
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(x, xs), Cons(y, ys)) => {
        subListLength(l1, l2) // l1.length <= l2.length 
        subListEqual(xs, ys)     
      }
    }

  }.ensuring(_ =>
    l1 == l2
  )


  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))

    subListLength(l2,l1) // l2.length <= l1.length (precondition for subListEqual)
    subListEqual(l1,l2)  

  }.ensuring(_ =>
    l1 == l2
  )


  def subListAppend[T](l1: List[T], l2: List[T]): Unit ={
    (l1) match{
      case (Nil()) => ()
      case (Cons(x, xs)) => subListAppend(xs, l2)
    }

  }.ensuring(_ => 
    subList(l1, l1 ++ l2)  
  )


  def subListPrepend[T](l1: List[T], l2: List[T]): Unit = {
    (l1) match {
      case (Nil())          => subListRefl(l2)
      //case (Cons(x,Nil()))  => subListRefl(l2)
      case (Cons(x, xs))    => subListPrepend(xs, l2)
    }

  }.ensuring(_ => 
    subList(l2, l1 ++ l2)  
  )


  def subListConcatLeft[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(subList(l, l2))

    l1 match {
      case (Nil()) => ()
     //case (Cons(x, Nil())) => ()
      case (Cons(x, xs)) => subListConcatLeft(l, xs, l2)
    }

  }.ensuring(_ =>
    subList(l1 ++ l, l1 ++ l2)  
  )

  def prependOneToSubList[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subList(l1, l2))
  }.ensuring(_ => subList(List(t) ++ l1, List(t) ++ l2))


  def appendOneToSubList[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subList(l1, l2))

    (l1, l2) match {
      case (Nil(), _) => subListPrepend(l2, List(t))
      case (_, Nil()) => subListRefl(List(t))
      case (Cons(x, xs), Cons(y, ys)) => 
        if (x == y && subList(xs, ys)) then
          appendOneToSubList(xs, ys, t)
        else 
          appendOneToSubList(l1, ys, t)
    }

  }.ensuring(_ => subList(l1 ++ List(t), l2 ++ List(t)))


  def appendToSuperList[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2))

    subListAppend(l2,l3)
    subListTrans(l1, l2, l2 ++ l3)

  }.ensuring(_ => subList(l1, l2 ++ l3))


  def associativeNil[T](l2: List[T], l3: List[T]): Unit = {
  }.ensuring(_ => Nil() ++ (l2 ++ l3) == (Nil() ++ l2) ++ l3)

  def associative[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    (l1) match {
      case(Nil()) => ()
      case (Cons(x, xs)) => {
        associative(xs, l2, l3)
      }
    }
  }.ensuring(_ => l1 ++ (l2 ++ l3) == (l1 ++ l2) ++ l3)

  def associativeNilSubList[T](l2: List[T], l3: List[T]): Unit = {
    subListRefl(l2++l3)
  }.ensuring(_ => subList(Nil() ++ (l2 ++ l3), (Nil() ++ l2) ++ l3))


  def associativeSubList[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    (l1) match {
      case(Nil()) => associativeNilSubList(l2, l3)
      case (Cons(x, xs)) => {
        associativeSubList(xs, l2, l3)
      }
    }
  }.ensuring(_ => subList(l1 ++ (l2 ++ l3), (l1 ++ l2) ++ l3))


  def subListConcatRight[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(subList(l, l1))

    (l, l1) match {
      case (_, Nil()) => subListRefl(l2)
      case (Nil(), _) => subListPrepend(l1, l2)

      case (Cons(x, xs), Cons(y, ys)) => {
        if (x == y && subList(xs, ys)) then
          subListConcatRight(xs, ys, l2)
        else 
          subListConcatRight(l, ys, l2)
      }

    }

  }.ensuring(_ =>
    subList(l ++ l2, l1 ++ l2)  
  )


  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  } 
}
