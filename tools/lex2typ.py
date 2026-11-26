#!/usr/bin/env python3
"""Convert Book99/Lexicon.tex to Book99/Lexicon.typ."""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import tex2typ  # noqa: E402

ROOT = tex2typ.ROOT


def items(body):
    """Split a description body into (head, text) pairs."""
    out = []
    for chunk in re.split(r'\\item\s*', body)[1:]:
        chunk = chunk.strip()
        assert chunk.startswith('['), chunk[:40]
        d = 0
        for i, c in enumerate(chunk):
            d += {'[': 1, ']': -1}.get(c, 0)
            if d == 0:
                break
        head, text = chunk[1:i], chunk[i + 1:]
        text = re.sub(r'^\s*:\s*', '', text)
        text = re.sub(r'\\end\{description\}.*', '', text, flags=re.S)
        out.append((head, text))
    return out


def conv(t):
    t = re.sub(r'(?<!\\)%.*', '', t)
    return tex2typ.english(t, {'_used': set()})


def main():
    tex = open(os.path.join(ROOT, 'Book99/Lexicon.tex'), encoding='utf-8').read()
    abbr = re.search(r'ABBREVIATIONS:(.*?)\\baselineskip', tex, re.S).group(1)
    bodies = re.findall(r'\\begin\{description\}(.*?)\\end\{description\}', tex, re.S)
    entries = [e for b in bodies for e in items(b)]
    hdr = tex2typ.greek.convert('STOIQEIWN')
    lines = ['#import "../functions.typ": no-footer, chapter, running-header', '',
             '#chapter([Greek-English Lexicon], [GREEK-ENGLISH LEXICON])', '',
             '#no-footer()', '', '#pagebreak()', '',
             '#set page(header: running-header([%s], [GREEK--ENGLISH LEXICON]))' % hdr, '',
             '#set text(size: 9pt)', '#set par(first-line-indent: 0em, justify: false)',
             '#show terms.item: it => block(spacing: 0.5em, par(hanging-indent: 1em)[#strong(it.term): #it.description])',
             '', '#columns(2)[', '#emph[Abbreviations]: ' + conv(abbr), '']
    for head, text in entries:
        lines.append('/ %s: %s' % (conv(head).replace(':', '\\:'), re.sub(r'^(.*?) :', r'\1:', conv(text))))
    lines.append(']')
    open(os.path.join(ROOT, 'Book99/Lexicon.typ'), 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    print(len(entries), 'entries')


if __name__ == '__main__':
    main()
