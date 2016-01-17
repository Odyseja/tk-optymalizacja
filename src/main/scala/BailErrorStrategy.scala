package main.scala

import org.antlr.v4.runtime._


class BailErrorStrategy extends DefaultErrorStrategy {

  override def recover(recognizer: Parser, e: RecognitionException) = { throw e }

  override def recoverInline(recognizer: Parser): Token = {
    throw new InputMismatchException(recognizer)
  }
  /** Make sure we don't attempt to recover from problems in subrules. */

  override def sync(recognizer: Parser) = { }

}