package simplifier

import javax.security.auth.login.FailedLoginException

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  //def simplify(node: Node) = node

  def simplify(node: Node): Node = node match {
    case BinExpr(op, left, right) => {
      val leftNode: Node = simplify(left)
      val rightNode: Node = simplify(right)

      op match {
        case "and" => and(leftNode, rightNode)
        case _ => node
      }

    }
    case NodeList(list) => NodeList(list.map{case f => simplify(f)})
    case IfInstr(cond, body) => IfInstr(simplify(cond), simplify(body))
    case _ => node
  }
  def and(left: Node, right: Node):Node = (left, right) match {
    case(_, FalseConst()) => FalseConst()
    case(FalseConst(), _) => FalseConst()
    case(TrueConst(), TrueConst()) => TrueConst()
    case(_, _) => BinExpr("and", left, right)
  }
}
