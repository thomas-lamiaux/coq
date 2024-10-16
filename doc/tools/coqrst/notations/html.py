##########################################################################
##         #      The Rocq Prover / The Rocq Development Team           ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A visitor for ANTLR notation ASTs, producing raw HTML.

Uses the dominate package.
"""

from dominate import tags
from dominate.utils import text

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor

class TacticNotationsToHTMLVisitor(TacticNotationsVisitor):
    def visitAlternative(self, ctx:TacticNotationsParser.AlternativeContext):
        with tags.span(_class='alternative'):
            self.visitChildren(ctx)

    def visitAltblock(self, ctx:TacticNotationsParser.AltblockContext):
        with tags.span(_class='alternative-block'):
            self.visitChildren(ctx)

    def visitAltsep(self, ctx:TacticNotationsParser.AltsepContext):
        tags.span('\u200b', _class="alternative-separator")

    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        with tags.span(_class="repeat-wrapper"):
            with tags.span(_class="repeat"):
                self.visitChildren(ctx)
            repeat_marker = ctx.LGROUP().getText()[1]
            separator = ctx.ATOM()
            tags.sup(repeat_marker)
            if separator:
                tags.sub(separator.getText())

    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        sp = tags.span(_class="curlies")
        sp.add("{")
        with sp:
            self.visitChildren(ctx)
        sp.add("}")

    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        tags.span(ctx.ATOM().getText())

    def visitPipe(self, ctx:TacticNotationsParser.PipeContext):
        text("|")

    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        tags.span(ctx.ID().getText()[1:], _class="hole")
        sub = ctx.SUB()
        if sub:
            tags.sub(sub.getText()[1:])

    def visitEscaped(self, ctx:TacticNotationsParser.EscapedContext):
        tags.span(ctx.ESCAPED().getText().replace("%", ""))

    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        text(" ")

def htmlize(notation):
    """Translate notation to a dominate HTML tree"""
    top = tags.span(_class='notation')
    with top:
        TacticNotationsToHTMLVisitor().visit(parse(notation))
    return top

def htmlize_str(notation):
    """Translate notation to a raw HTML document"""
    # ‘pretty=True’ introduces spurious spaces
    return htmlize(notation).render(pretty=False)

def htmlize_p(notation):
    """Like `htmlize`, wrapped in a ‘p’.
    Does not return: instead, must be run in a dominate context.
    """
    with tags.p():
        htmlize(notation)
