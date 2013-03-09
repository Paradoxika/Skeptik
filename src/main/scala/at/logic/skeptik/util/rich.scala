package at.logic.skeptik.util

import language.implicitConversions

object rich {
  class RichIterable[T](val c: Iterable[T]) extends AnyVal {
    def contains(e: T) = if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]].contains(e)
                         else if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]].contains(e)
                         else c.exists(_ == e)
    def diff(that: Iterable[T]) = if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]] diff that.toSet
                         else if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]] diff that.toSeq
                         else c.filterNot(new RichIterable(that).contains(_))
    def intersect(that: Iterable[T]) = if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]] intersect that.toSet
                         else if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]] intersect that.toSeq
                         else throw new Exception("not implemented yet") //ToDo: fix this line
    def union(that: Iterable[T]) = if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]] union that.toSet
                         else if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]] union that.toSeq
                         else c ++ that                        
  }
  object RichIterable {
    implicit def enrichIterable[T](c: Iterable[T]) = new RichIterable(c)
  }
}