##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A visitor for ANTLR notation ASTs, producing plain text with ellipses.

Somewhat-closely approximates the rendering of the original manual.
"""

from io import StringIO

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor

class TacticNotationsToDotsVisitor(TacticNotationsVisitor):
    def __init__(self):
        self.buffer = StringIO()

    def visitAlternative(self, ctx:TacticNotationsParser.AlternativeContext):
        self.buffer.write("[")
        self.visitChildren(ctx)
        self.buffer.write("]")

    def visitAltsep(self, ctx:TacticNotationsParser.AltsepContext):
        self.buffer.write("|")

    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        separator = ctx.ATOM() or ctx.PIPE()
        self.visitChildren(ctx)
        if ctx.LGROUP().getText()[1] == "+":
            spacer = (separator.getText() + " " if separator else "")
            self.buffer.write(spacer + "…" + spacer)
            self.visitChildren(ctx)

    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        self.buffer.write("{")
        self.visitChildren(ctx)
        self.buffer.write("}")

    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        self.buffer.write(ctx.ATOM().getText())

    def visitPipe(self, ctx:TacticNotationsParser.PipeContext):
        self.buffer.write("|")

    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        self.buffer.write("‘{}’".format(ctx.ID().getText()[1:]))

    def visitEscaped(self, ctx:TacticNotationsParser.EscapedContext):
        self.buffer.write(ctx.ESCAPED().getText().replace("%", ""))

    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        self.buffer.write(" ")

def stringify_with_ellipses(notation):
    vs = TacticNotationsToDotsVisitor()
    vs.visit(parse(notation))
    return vs.buffer.getvalue()
