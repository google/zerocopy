// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.verifier

import viper.silver.ast._

import scala.annotation.unused

/** Describes the outcome of a verification attempt of a Viper program.

  */
sealed trait VerificationResult {
  def transformedResult(): VerificationResult
}

/** A successful verification. */
object Success extends VerificationResult {
  override def toString = "Verification successful."
  override def transformedResult(): VerificationResult = this
}

/** A non-successful verification.
  *
  * @param errors The errors encountered during parsing, translation or verification.
  */
case class Failure(errors: Seq[AbstractError]) extends VerificationResult {
  override def toString = {
    s"Verification failed with ${errors.size} errors:\n  " +
      (errors map (e => "[" + e.fullId + "] " + e.readableMessage)).mkString("\n  ")
  }
  override def transformedResult(): VerificationResult = Failure(errors.map(_.transformedError()))
}

/**
 * A common super-trait for errors that occur during parsing, translation or verification.
 */
trait AbstractError {
  /** The position where the error occured. */
  def pos: Position

  /** A short and unique identifier for this error. */
  def fullId: String

  /** A readable message describing the error. */
  def readableMessage: String

  /* TODO: Simply looking for pos in message is rather fragile */
  override def toString: String = {
    val msg = readableMessage
    val posStr = pos.toString

    (if (msg contains posStr) s"$msg"
    else s"$msg ($posStr)") +
      (if (cached) " - cached" else "")
  }

  val cached: Boolean = false

  var scope: Option[Member] = None

  /** This method could be used for implementing the scope filed via an offending node.
    * TODO: make scope a mandatory field (do not provide a default value for it). */
  protected def getMemberForNode(ast: Program, node: Node): Member = {
    val members_with_this_node = ast.members.collect {
      case m if m.deepCollect({ case n => n == node }).nonEmpty => m
    }
    assert(members_with_this_node.length == 1)
    members_with_this_node.last
  }

  def transformedError(): AbstractError = this
}

abstract class ParseReport(@unused message: String, @unused pos: Position) extends AbstractError

/** A parser error. */
case class ParseError(message: String, override val pos: Position)
  extends ParseReport(message, pos) {
  def fullId = "parser.error"
  def readableMessage = s"Parse error: $message ($pos)"
}

/** A case class used for treating certain parser reports as non-critical. */
case class ParseWarning(message: String, override val pos: Position)
  extends ParseReport(message, pos) {
  def fullId = "parser.warning"
  def readableMessage = s"Parse warning: $message ($pos)"
}

/** A case class used for treating certain type checker reports as non-critical. */
case class TypecheckerWarning(message: String, override val pos: Position)
  extends AbstractError {
  def fullId = "typechecker.warning"
  def readableMessage = s"Type checker warning: $message ($pos)"
}

/** A case class used for treating certain verifier reports as non-critical. */
case class VerifierWarning(message: String, override val pos: Position)
  extends AbstractError {
  def fullId = "verifier.warning"
  def readableMessage = s"Verifier warning: $message ($pos)"
}

/** An error during consistency-checking an AST node */
case class ConsistencyError(message: String, pos:Position) extends AbstractError {
  def fullId = "consistency.error"
  def readableMessage: String = s"Consistency error: $message ($pos)"
}

/** A typechecker error. */
case class TypecheckerError(message: String, pos: Position) extends AbstractError {
  def fullId = "typechecker.error"
  def readableMessage = s"$message ($pos)"
}

/** An error during command-line option parsing. */
case class CliOptionError(message: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "clioption.error"
  def readableMessage = s"Command-line interface: $message"
}

/** An error indicating that a dependency couldn't be found. */
case class DependencyNotFoundError(message: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "dependencynotfound.error"
  def readableMessage = s"Dependency not found: $message"
}

/* RFC: [Malte] If we want to be more fine-grained, for example, by having a
 *      timeout per method/member, or even per proof obligation, then we should
 *      consider subclassing AbstractVerificationError, or use an Internal error
 *      in combination with a TimeoutReason.
 */
case class TimeoutOccurred(n: Long, units: String) extends AbstractError {
  def pos = NoPosition
  def fullId = "timeout.error"
  def readableMessage = s"Timeout occurred after $n $units"
}

case class AbortedExceptionally(cause: Throwable) extends AbstractError {
  def pos = NoPosition
  def fullId = "exceptional.error"
  def readableMessage = s"Verification aborted exceptionally (${cause.toString()}, ${
    cause.printStackTrace()
    cause.getStackTrace().tail.head.toString()
  })"
}
