import re, sys
SCRATCH='/private/tmp/claude-501/-Users-eric-Documents-GitHub-verso-workspace/6956f628-1d4c-4197-879c-1c5aac95b285/scratchpad'
before_lines = open('/Users/eric/Documents/GitHub/verso-workspace/hopf-problem/.deps-dump.txt').read().split('\n')
count = int(before_lines[0].split()[1]); before = before_lines[1:1+count]
after = [l for l in open('/Users/eric/Documents/GitHub/verso-workspace/hopf-problem/.names-after.txt').read().split('\n') if l]
def norm(n):
    n = re.sub(r'^_private\.[^.]+(\.[^.]+)*?\.0\.', '_private.', n)   # drop module path in private mangling
    return n
def keep(n):
    return 'unexpand' not in n and '«term_' not in n
B = {norm(n) for n in before if keep(n)}; A = {norm(n) for n in after if keep(n)}
print('before:', len(B), 'after:', len(A))
missing = sorted(B - A); extra = sorted(A - B)
print('MISSING after split:', len(missing)); [print('  -', m) for m in missing[:40]]
print('EXTRA after split:', len(extra)); [print('  +', e) for e in extra[:40]]
sys.exit(0 if not missing else 1)
