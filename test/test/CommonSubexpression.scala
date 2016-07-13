package test

import scala.annotation.Idempotent

object CommonSubexpression {

  @Idempotent def sum(i1: Int, i2: Int) = i1 + i2

  def method1: Int = {
    val a = 1
    val c = sum(sum(1, a), 2)
    val d = sum(sum(1, a), 3)
/*    val c = sum(sum(sum(1, a), 2), 3)
    val d = sum(sum(sum(1, a), 2), 4)*/
    d - c
  }

  def main(args: Array[String]): Unit = {
    println("executing")
    assert(method1 == 1)
  }

}
