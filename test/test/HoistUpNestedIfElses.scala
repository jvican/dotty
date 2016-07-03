package test

object HoistUpNestedIfElses {

  def main(args: Array[String]): Unit = {
    sealed trait Animal
    case class Cat(name: String) extends Animal
    case class Cow(typeOfMilk: String) extends Animal

    sealed trait Food
    case object Meat extends Food
    case object Grass extends Food

    def getFoodFor(a: Animal) = a match {
      case c: Cat => Meat
      case cw: Cow => Grass
    }

    require(getFoodFor(Cat("Garfield")) == Meat)
    require(getFoodFor(Cow("UHV")) == Grass)
  }

}
