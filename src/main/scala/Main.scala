package main.scala


import java.io.FileReader
import java.io.FileNotFoundException
import java.io.IOException

import org.antlr.v4.runtime.{ANTLRFileStream, CommonTokenStream}
import parser.{PythonLexer,PythonParser}

import AST.ConcretePythonVisitor
import simplifier.Simplifier

object Main {

  def main(args: Array[String]) {

    if(args.length == 0) {
      println("Usage: sbt \"run filename ...\""); 
      return
    }

    for (arg <- args) {
      try {
          println("Parsing file: " + arg)     
          val lex = new PythonLexer(new ANTLRFileStream(arg))
          val tokens = new CommonTokenStream(lex)
          val parser = new PythonParser(tokens)
          val visitor = new ConcretePythonVisitor

          val tree: AST.Node = parser.program().accept(visitor)
          val simplifiedTree = Simplifier.simplify(tree)

          println("\nAST:")
          println(tree)
          println("\nAST after optimization:")
          println(simplifiedTree)
          println("\nProgram after optimization:")
          println(simplifiedTree.toStr)

      }
      catch {
          case ex: FileNotFoundException => println("Couldn't open file " + arg)
          case ex: IOException => println("Couldn't read file " + arg)
      }
    }
  }
}
