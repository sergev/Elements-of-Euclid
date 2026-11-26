#!/usr/bin/env python3
"""Convert a book of Fitzpatrick's Elements from LaTeX to Typst files.

Usage: tex2typ.py BOOK [--write] [--dump]
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import greek  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MARK_RE = r'\$\^\{?(?:\\,)?\s*((?:\\(?:dag|ddag|S|P|ast|flat)\s*)+)\}?\$'
MARK_NC = r'\$\^\{?(?:\\,)?\s*(?:\\(?:dag|ddag|S|P|ast|flat)\s*)+\}?\$'
MARK_SYM = {'dag': '†', 'ddag': '‡', 'S': '§', 'P': '¶', 'ast': '∗', 'flat': '♭'}

GREEK_LETTERS = 'alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi pi rho sigma tau upsilon phi chi psi omega'.split()


def mark_key(s):
    return ''.join(re.findall(r'\\(dag|ddag|S|P|ast|flat)', s))


def braced(s, i):
    """Return (content, end) for the brace group starting at s[i] == '{'."""
    assert s[i] == '{', s[i:i + 20]
    d = 0
    for j in range(i, len(s)):
        if s[j] == '{':
            d += 1
        elif s[j] == '}':
            d -= 1
            if d == 0:
                return s[i + 1:j], j + 1
    raise ValueError('unbalanced')


def sub_cmd(s, cmd, fn):
    """Replace \\cmd{arg} (balanced) by fn(arg)."""
    out = []
    i = 0
    pat = '\\' + cmd + '{'
    while True:
        k = s.find(pat, i)
        if k < 0:
            out.append(s[i:])
            return ''.join(out)
        out.append(s[i:k])
        arg, i = braced(s, k + len(pat) - 1)
        out.append(fn(arg))


def sub_group(s, cmd, fn):
    """Replace {\\cmd text} by fn(text)."""
    while True:
        m = re.search(r'\{\\' + cmd + r'\b\s*', s)
        if not m:
            return s
        arg, end = braced(s, m.start())
        arg = re.sub(r'^\\' + cmd + r'\b\s*', '', arg)
        s = s[:m.start()] + fn(arg) + s[end:]


# ---------------------------------------------------------------- math

def math(t):
    """LaTeX math -> Typst math source (without $)."""
    t = t.strip()
    if re.fullmatch(r'[A-Z]+', t):
        return ' '.join(t)
    t = sub_cmd(t, 'sqrt', lambda a: ' sqrt(' + math(a) + ') ')
    t = sub_cmd(t, 'overline', lambda a: ' overline(' + math(a) + ') ')
    t = sub_cmd(t, 'mbox', lambda a: ' "' + a + '" ')
    t = sub_cmd(t, 'rm', lambda a: ' "' + a + '" ')
    t = re.sub(r'([\^_])\{\s*\\,\s*', r'\1{', t)
    t = re.sub(r'\^\{([^{}]*)\}', lambda m: '^(' + math(m.group(1)) + ')', t)
    t = re.sub(r'_\{([^{}]*)\}', lambda m: '_(' + math(m.group(1)) + ')', t)
    t = t.replace('\\left', '').replace('\\right', '')
    t = t.replace('\\,', ' thin ').replace('\\!', '').replace('\\;', ' med ')
    repl = {'\\ldots': ' dots ', '\\cdots': ' dots.c ', '\\gtreqqless': ' gt.eq.lt ',
            '\\cos': ' cos ', '\\times': ' times ', '\\pm': ' plus.minus ',
            '\\ne': ' eq.not ', '\\leq': ' lt.eq ', '\\geq': ' gt.eq ',
            '\\le': ' lt.eq ', '\\ge': ' gt.eq ', '\\infty': ' infinity '}
    for k, v in repl.items():
        t = re.sub(re.escape(k) + r'(?![a-zA-Z])', v, t)
    for g in GREEK_LETTERS:
        t = re.sub(r'\\' + g + r'(?![a-zA-Z])', ' ' + g + ' ', t)
    # keep '/' as a slash, not a fraction
    t = t.replace('/', ' \\/ ')
    # separate single-letter variables: kX -> k X (but not Typst names)
    names = set(GREEK_LETTERS) | {'sqrt', 'overline', 'thin', 'med', 'dots', 'c', 'cos',
                                  'times', 'plus', 'minus', 'eq', 'not', 'lt', 'gt',
                                  'infinity'}

    def split_word(m):
        w = m.group(0)
        if w in names or '.' in w:
            return w
        return ' '.join(w)
    t = re.sub(r'(?<![\w"])[A-Za-z]{2,}(?![\w"])', split_word, t)
    if '\\' in t.replace('\\/', ''):
        t = 'TODO-MATH ' + t
    return re.sub(r'\s+', ' ', t).strip()


# ---------------------------------------------------------------- text

def escape(t):
    return re.sub(r'([*_#@<>])', r'\\\1', t)


def english(t, notes):
    """LaTeX paragraph (English) -> Typst markup."""
    t = re.sub(r'(?<!\\)%.*', '', t)
    t = re.sub(r'\\\\(\[[^]]*\])?', ' ', t)
    t = t.replace('\\mbox{[}', '[').replace('\\mbox{]}', ']')
    t = t.replace('\\noindent', '').replace('\\spa', ' ')
    t = re.sub(r'\\vspace\*?\{[^}]*\}', '', t)
    t = sub_cmd(t, 'gr', lambda a: '\x02' + greek.convert(a) + '\x03')
    t = sub_cmd(t, 'ggn', lambda a: '\x02' + greek.numeral(int(a)) + '\x03')
    # footnote markers
    t = re.sub(MARK_RE, lambda m: '\x00' + mark_key(m.group(1)) + '\x00', t)
    # math
    parts = re.split(r'(\$[^$]*\$)', t)
    for k, p in enumerate(parts):
        if p.startswith('$') and len(p) > 1:
            parts[k] = '\x04' + math(p[1:-1]) + '\x04'
    t = ''.join(parts)
    t = sub_group(t, 'em', lambda a: '\x05' + a + '\x06')
    t = sub_group(t, 'it', lambda a: '\x05' + a + '\x06')
    t = sub_group(t, 'bf', lambda a: '\x07' + a + '\x08')
    t = t.replace("``", '"').replace("''", '"')
    t = t.replace('\\,', '\u2009').replace('\\ ', ' ').replace('\\&', '&')
    t = t.replace('\\ldots', '...').replace('\\S', '§')
    t = re.sub(r'\s+', ' ', t).strip()
    # escape outside math/greek
    parts = re.split(r'(\x04[^\x04]*\x04|\x02[^\x03]*\x03)', t)
    t = ''.join(p if p[:1] in '\x04\x02' else escape(p) for p in parts)
    t = t.replace('~', ' ')
    t = re.sub(r'\b(Props?|Defs?|Posts?|C\.N|Lemma|Corr?)\. (\d)', r'\1.~\2', t)
    t = re.sub(r'C\.N\.s (\d)', r'C.N.s~\1', t)
    t = t.replace('\x04', '$').replace('\x02', '').replace('\x03', '')
    t = t.replace('\x05', '#emph[').replace('\x06', ']')
    t = t.replace('\x07', '#strong[').replace('\x08', ']')
    t = re.sub(r' +', ' ', t)

    def note(m):
        k = m.group(1)
        if k not in notes:
            return '#content-box-note[TODO-NOTE ' + k + ']'
        notes['_used'].add(k)
        return '#content-box-note[' + notes[k] + ']'
    t = re.sub(r'\x00([a-zA-Z]+)\x00', note, t)
    return t.strip()


def greek_para(t, notes=None):
    t = re.sub(r'(?<!\\)%.*', '', t)
    t = re.sub(r'\\\\(\[[^]]*\])?', ' ', t)
    t = re.sub(r'\\vspace\*?\{[^}]*\}', '', t)
    t = t.replace('\\noindent', '').replace('\\spa', ' ')
    t = t.replace('\\ggn', '\\gn')
    t = re.sub(r'~(?=\\)', ' ', t)
    t = sub_cmd(t, 'ov', lambda a: '\x04' + greek.convert(a) + '\x05')
    t = t.replace('\\gr', '')
    keys = []

    def mark(m):
        keys.append(mark_key(m.group(1)))
        return '\x07%d\x07' % (len(keys) - 1)
    t = re.sub(MARK_RE, mark, t)
    parts = re.split(r'(\$[^$]*\$)', t)
    out = []
    for p in parts:
        if p.startswith('$') and len(p) > 1:
            out.append('\x06' + math(p[1:-1]) + '\x06')
        else:
            out.append(greek.convert(p))
    t = ' '.join(x for x in out if x)
    t = escape(t)
    t = t.replace('\x04', '#overline[').replace('\x05', ']').replace('\x06', '$')

    def note(m):
        k = keys[int(m.group(1))]
        if notes is None or k not in notes:
            return '#content-box-note[TODO-NOTE ' + k + ']'
        notes['_used'].add(k)
        return '#content-box-note[' + notes[k] + ']'
    t = re.sub(r' ?\x07(\d+)\x07', note, t)
    return re.sub(r'\s+', ' ', t).strip()


# ---------------------------------------------------------------- structure

def split_side(s, side):
    """Split one column into elements: ('head', text, mark), ('fig', name, h), ('para', text)."""
    elems = []
    s = re.sub(r'\\vspace\*?\{[^}]*\}', '\n\n', s)

    def head(m):
        mark = m.group(2) or ''
        return '\n\n\x01HEAD' + m.group(1).replace('\n', ' ') + mark + '\x01\n\n'
    s = re.sub(r'\\begin\{center\}(.*?)\\end\{center\}(' + MARK_NC + ')?',
               head, s, flags=re.S)

    def fig(m):
        return '\n\n\x01FIG%s|%s\x01\n\n' % (m.group(2), m.group(1))
    s = re.sub(r'\\epsfysize\s*=\s*([\d.]+in)\s*\\centerline\{\\epsffile\{(?:Book\d+/)?(\w+?)[eg]?\.eps\}\}',
               fig, s, flags=re.S)
    for p in re.split(r'\n\s*\n', s):
        p = p.strip()
        if not p or re.fullmatch(r'(\\\\|\\spa|\\noindent|\s)*', p):
            continue
        for q in re.split(r'(\x01[^\x01]*\x01)', p):
            q = q.strip()
            if not q or re.fullmatch(r'(\\\\|\\spa|\\noindent|\s|\})*', q):
                continue
            if q.startswith('\x01HEAD'):
                elems.append(('head', q[5:-1]))
            elif q.startswith('\x01FIG'):
                name, h = q[4:-1].split('|')
                elems.append(('fig', name, h))
            else:
                elems.append(('para', q))
    return elems


def parse_notes(tail):
    tail = re.split(r'%%%%|\\pdfbookmark|\\begin\{Parallel\}', tail)[0]
    tail = tail.replace('{\\footnotesize', '').replace('\\noindent', '')
    notes = {}
    pieces = re.split('(' + MARK_NC + ')', tail)
    for k in range(1, len(pieces), 2):
        text = pieces[k + 1] if k + 1 < len(pieces) else ''
        text = re.sub(r'(\\\\(\[[^]]*\])?|\}|\{|\s)*$', '', text.strip())
        notes[mark_key(pieces[k])] = text
    return notes


def parse_book(path):
    tex = open(path, encoding='utf-8').read()
    tex = re.sub(r'(?m)^%.*\n', '', tex)
    blocks = []
    for m in re.finditer(r'\\begin\{Parallel\}\{\}\{\}(.*?)\\end\{Parallel\}', tex, re.S):
        body = m.group(1)
        li = body.index('\\ParallelLText{')
        ri = body.index('\\ParallelRText{')
        L, _ = braced(body, li + len('\\ParallelLText'))
        R, _ = braced(body, ri + len('\\ParallelRText'))
        raw_notes = parse_notes(tex[m.end():])
        blocks.append({'L': split_side(L, 'L'), 'R': split_side(R, 'R'),
                       'raw_notes': raw_notes, 'pos': m.start()})
    return blocks


def head_text(h):
    """Heading markup -> (plain latex text, mark key)."""
    mk = ''
    m = re.search(MARK_RE, h)
    if m:
        mk = mark_key(m.group(1))
        h = h[:m.start()] + h[m.end():]
    h = re.sub(r'\\(large|Large|huge|Huge)\b', '', h)
    return h.strip(' {}'), mk


def build(block, warn):
    notes = {}
    raw = block['raw_notes']
    notes['_used'] = set()
    for k, v in raw.items():
        notes[k] = english(v, {'_used': set()})
    L, R = block['L'], block['R']
    lh = [e for e in L if e[0] == 'head']
    rh = [e for e in R if e[0] == 'head']
    lp = [e for e in L if e[0] == 'para']
    rp = [e for e in R if e[0] == 'para']
    lf = [e for e in L if e[0] == 'fig']
    rf = [e for e in R if e[0] == 'fig']
    if len(lh) != len(rh) or len(lp) != len(rp):
        warn('heads %d/%d paras %d/%d' % (len(lh), len(rh), len(lp), len(rp)))
    title, tmark = head_text(rh[0][1])
    gtitle, _ = head_text(lh[0][1])
    out = {'title': title, 'gtitle': greek_para(gtitle), 'items': []}
    if tmark:
        notes['_used'].add(tmark)
        out['note'] = notes.get(tmark, 'TODO-NOTE')
    hi = pi = fi = 0
    for e in R:
        if e[0] == 'head':
            if hi > 0:
                t, mk = head_text(e[1])
                g = greek_para(head_text(lh[hi][1])[0]) if hi < len(lh) else 'TODO-GREEK'
                en = english(t, notes)
                if mk:
                    en += '#content-box-note[' + notes.get(mk, 'TODO-NOTE') + ']'
                    notes['_used'].add(mk)
                out['items'].append(('sub', g, en))
            hi += 1
        elif e[0] == 'para':
            g = greek_para(lp[pi][1], notes) if pi < len(lp) else 'TODO-GREEK'
            out['items'].append(('para', g, english(e[1], notes)))
            pi += 1
        else:
            gname = lf[fi][1] if fi < len(lf) else None
            if gname != e[1]:
                warn('figure mismatch %s %s' % (gname, e[1]))
            out['items'].append(('fig', e[1], e[2]))
            fi += 1
    for e in lp[pi:]:
        out['items'].append(('para', greek_para(e[1]), 'TODO-ENGLISH'))
    unused = set(raw) - notes['_used']
    if unused:
        warn('unused notes %s' % sorted(unused))
    return out


# ---------------------------------------------------------------- output

def numbered(g, e):
    """Strip definition numbers 'αʹ. ' / '1. ' -> (g, e, n)."""
    m = re.match(r'(\d+)\.\s*~?\s*', e)
    if not m:
        return g, e, None
    g = re.sub(r'^\S+ʹ\.\s*', '', g)
    return g, e[m.end():], int(m.group(1))


def render(b, kind, num):
    lines = ['#import "../functions.typ": *', '', '#content-box[']
    if kind == 'prop':
        note = ', note: [%s]' % b['note'] if 'note' in b else ''
        lines.append('  #parallel-proposition(%d%s)' % (num, note))
    else:
        en = b['title']
        if 'note' in b:
            en += '#content-box-note[%s]' % b['note']
        lines += ['  #chapter(', '    [%s],' % b['title'], '    parallel(',
                  '      [%s],' % b['gtitle'].rstrip('.') + '.' if False else '      [%s],' % b['gtitle'],
                  '      [%s]' % en, '    ),', '    depth: 2,', '  )']
    for it in b['items']:
        if it[0] == 'fig':
            h = '%gin' % float(it[2][:-2])
            lines.append('  #parallel-image("%s", %s)' % (it[1], h))
        elif it[0] == 'sub':
            lines.append('  #parallel-subheading([%s], [%s])' % (it[1], it[2]))
        else:
            g, e = it[1], it[2]
            n = None
            if kind == 'defs':
                g, e, n = numbered(g, e)
            lines.append('  #parallel(')
            lines.append('    [%s],' % g)
            lines.append('    [%s],' % e)
            if n is not None:
                lines.append('    n: %d,' % n)
            lines.append('  )')
    lines.append(']')
    return '\n'.join(lines) + '\n'


def book_file(book, tex, files):
    sub = re.search(r'\{\\huge\\it\s+(.*?)\}', tex, re.S)
    sub = re.sub(r'\s+', ' ', sub.group(1)).strip() if sub else ''
    hdr = greek.convert('STOIQEIWN') + ' ' + greek.numeral(book) + '.'
    out = ['#import "../functions.typ": parallel, no-footer, chapter, content-box, content-box-note', '',
           '#chapter([Book %d], [ELEMENTS BOOK %d])' % (book, book), '',
           '== _%s_' % sub, '', '#no-footer()', '', '#pagebreak()', '',
           '#set page(', '  header: [#grid(', '    columns: (1fr, 1fr),', '    align: (left, right),',
           '    [%s], [ELEMENTS BOOK %d]' % (hdr, book), '  )',
           '  #line(length: 100%, stroke: 0.85pt)]', ')', '']
    prev = None
    for fn, kind, num, b in files:
        if prev == 'defs' and kind == 'prop':
            out.append('')
            out.append('#pagebreak()')
            out.append('')
        out.append('#include "%s"' % fn)
        prev = kind
    return '\n'.join(out) + '\n'


def main():
    book = int(sys.argv[1])
    d = os.path.join(ROOT, 'Book%02d' % book)
    path = os.path.join(d, 'Book%d.tex' % book)
    blocks = parse_book(path)
    width = 3 if book == 10 else 2
    files = []
    ndefs = 0
    for k, blk in enumerate(blocks):
        msgs = []
        b = build(blk, msgs.append)
        t = b['title']
        m = re.match(r'Proposition\s*(\d+)', t)
        if m:
            kind, num = 'prop', int(m.group(1))
            fn = 'Prop%0*d.typ' % (width, num)
        elif t.startswith('Definitions'):
            ndefs += 1
            kind, num = 'defs', ndefs
            fn = 'Definitions.typ' if ndefs == 1 else 'Definitions%d.typ' % ndefs
        elif t.startswith('Postulates'):
            kind, num, fn = 'defs', 0, 'Postulates.typ'
        elif t.startswith('Common'):
            kind, num, fn = 'defs', 0, 'CommonNotions.typ'
        else:
            kind, num, fn = 'other', 0, 'Block%d.typ' % k
        # figure paths are absolute from the project root
        b['items'] = [('fig', '/Book%02d/%s' % (book, it[1]), it[2]) if it[0] == 'fig' else it
                      for it in b['items']]
        for msg in msgs:
            print('%s: %s' % (fn, msg), file=sys.stderr)
        files.append((fn, kind, num, b))
        if '--dump' in sys.argv:
            print('==', fn)
            for it in b['items']:
                print('  ', it)
    if '--write' in sys.argv:
        for fn, kind, num, b in files:
            open(os.path.join(d, fn), 'w', encoding='utf-8').write(render(b, kind, num))
        tex = open(path, encoding='utf-8').read()
        open(os.path.join(d, 'Book%d.typ' % book), 'w', encoding='utf-8').write(book_file(book, tex, files))
    return files


if __name__ == '__main__':
    main()
