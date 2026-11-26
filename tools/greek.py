"""Convert babel/teubner Greek transliteration (as in \\gr{...}) to Unicode."""
import re
import unicodedata

LOWER = dict(zip('abgdezhjiklmnxoprstufqywc',
                 'αβγδεζηθικλμνξοπρστυφχψως'))
UPPER = dict(zip('ABGDEZHJIKLMNXOPRSTUFQYWC',
                 'ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩΣ'))

# Combining marks, in the order NFC needs them composed.
MARKS = {'"': '\u0308', '>': '\u0313', '<': '\u0314',
         "'": '\u0301', '`': '\u0300', '~': '\u0342'}
ORDER = '"><\'`~'
IOTA_SUB = '\u0345'
ANO_TELEIA = '\u0387'
ELISION = '\u1fbf'
KERAIA = '\u0374'


def clean(s):
    s = re.sub(r'\\kern\s*-?[\d.]+pt\s?', '', s)
    s = s.replace('\\-', '').replace('\\mbox{[}', '[').replace('\\mbox{]}', ']')
    s = s.replace('\\ ', ' ').replace('~\\', ' \\')
    s = re.sub(r'\\gn\{(\d+)\}', lambda m: numeral(int(m.group(1))), s)
    s = s.replace('{', '').replace('}', '')
    return s


def numeral(n):
    """Greek numeral with keraia, e.g. 46 -> μϛʹ (as 'μστʹ' in LaTeX output)."""
    units = ['', 'α', 'β', 'γ', 'δ', 'ε', 'ϛ', 'ζ', 'η', 'θ']
    tens = ['', 'ι', 'κ', 'λ', 'μ', 'ν', 'ξ', 'ο', 'π', 'ϟ']
    hund = ['', 'ρ', 'σ', 'τ', 'υ', 'φ', 'χ', 'ψ', 'ω', 'ϡ']
    return hund[n // 100 % 10] + tens[n // 10 % 10] + units[n % 10] + KERAIA


def convert(s):
    s = clean(s)
    out = []
    pending = []
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == 'v':                      # ligature breaker
            i += 1
            continue
        if ch in MARKS:
            nxt = s[i + 1] if i + 1 < len(s) else ''
            if ch == '>' and not (nxt in MARKS or nxt in LOWER or nxt in UPPER):
                out.append(ELISION)        # elision: kat> , ep>
                i += 1
                continue
            if ch == '~' and not (nxt in MARKS or nxt in LOWER or nxt in UPPER):
                out.append(' ')            # tie
                i += 1
                continue
            pending.append(ch)
            i += 1
            continue
        if ch in LOWER or ch in UPPER:
            letter = LOWER.get(ch) or UPPER[ch]
            if ch == 's':
                nxt = s[i + 1] if i + 1 < len(s) else ''
                if not (nxt in LOWER or nxt in MARKS or nxt == '|' or nxt == 'v'):
                    letter = 'ς'
            marks = ''.join(MARKS[m] for m in sorted(pending, key=ORDER.index))
            pending = []
            out.append(letter + marks)
            i += 1
            continue
        if ch == '|':
            out.append(IOTA_SUB)
            i += 1
            continue
        if pending:                        # marks with no letter: keep as spacing forms
            out.append(''.join(pending))
            pending = []
        if ch == ';':
            out.append('\x01')
        elif ch == '?':
            out.append(';')
        else:
            out.append(ch)
        i += 1
    t = unicodedata.normalize('NFC', ''.join(out))
    t = re.sub(r'[ \t\n]+', ' ', t)
    return t.replace('\x01', ANO_TELEIA).strip()


if __name__ == '__main__':
    import sys
    print(convert(sys.stdin.read()))
