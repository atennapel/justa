package surface

import parsley.Parsley
import parsley.token.Lexer as PLexer
import parsley.token.descriptions.{
  LexicalDesc,
  NameDesc,
  SymbolDesc,
  SpaceDesc,
  numeric,
  text
}
import parsley.token.predicate.{Unicode, Basic}

object Lexer:
  private val userOps = "`~!@$%^&*-+=|:/?><,."
  private val userOpsTail = s"$userOps#_;"

  private val desc = LexicalDesc(
    NameDesc.plain.copy(
      identifierStart = Unicode(c => Character.isLetter(c) || c == '_'),
      identifierLetter =
        Unicode(c => Character.isLetterOrDigit(c) || c == '_' || c == '\''),
      operatorStart = Unicode(userOps.contains(_)),
      operatorLetter = Unicode(userOpsTail.contains(_))
    ),
    SymbolDesc.plain.copy(
      hardKeywords = Set("def", "let", "rec", "type", "meta"),
      hardOperators = Set(":=", "=", ":", ";", "^", "`", "$", "\\", "->", "=>")
    ),
    numeric.NumericDesc.plain.copy(
      octalExponentDesc = numeric.ExponentDesc.NoExponents,
      binaryExponentDesc = numeric.ExponentDesc.NoExponents
    ),
    text.TextDesc.plain.copy(
      escapeSequences = text.EscapeDesc.haskell
    ),
    SpaceDesc.plain.copy(
      commentStart = "{-",
      commentEnd = "-}",
      commentLine = "--",
      nestedComments = true,
      space = Basic(_.isWhitespace)
    )
  )

  private val lexer = new PLexer(desc)

  val id = lexer.lexeme.names.identifier
  val userOp = lexer.lexeme.names.userDefinedOperator

  def fully[A](p: Parsley[A]) = lexer.fully(p)

  val implicits = lexer.lexeme.symbol.implicits
